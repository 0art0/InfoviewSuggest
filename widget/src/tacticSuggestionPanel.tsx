/**
 * A panel for displaying a list of tactic suggestions to the user.
 * The suggestions are all tried in the background in parallel, and by default,
 * only ones that are found valid are displayed to the user.
 * 
 * The code here heavily relies on the widget code in https://github.com/BartoszPiotrowski/lean-premise-selection/tree/main/widget.
 */
import {
  InteractiveCode,
  CodeWithInfos,
  EditorContext,
  Name,
  MessageData,
  InteractiveMessageData,
  TaggedText,
  useRpcSession,
  EditorConnection,
  RpcPtr
} from "@leanprover/infoview";
import React from "react";
import { JSX } from "react/jsx-runtime";
import { DocumentUri, Range, TextEdit } from "vscode-languageserver-protocol";

type ExprWithCtx = RpcPtr<'ProofWidgets.ExprWithCtx'>
type SelectionMetadata = RpcPtr<'SELECTION_METADATA'> // HACK: this is a pointer to the `SelectionMetadata` on the Lean side
/** Options that control which sections are shown in the UI. */
interface ValidationOptions {
  showFailed: boolean;
  showPending: boolean;
  filterResults: boolean;
  showNames: boolean;
}

// TODO: Create a component for this context
const ValidationOptionsContext = React.createContext<ValidationOptions>({
  showFailed: false,
  showPending: true,
  filterResults: true,
  showNames: false
});

/** Strips the tags from a `TaggedText` object to extract the underlying plain text. */
function stripTags<T>(text: TaggedText<T>): string {
  if ("text" in text) {
    return text.text;
  } else if ("append" in text) {
    return text.append.map(stripTags).join("");
  } else if ("tag" in text) {
    return stripTags(text.tag[1]);
  } else {
    throw new Error("Invalid `TaggedText` structure");
  }
}

/** A *premise* is the name of a local hypothesis or a result from the library
 *  that can be used in a proof, together with a pretty-printed form for rendering.
 * 
 *  HACK: While the interface defined in this file has only a two fields containing the name of the result and its pretty-printed form,
 *  the compiled JavaScript code with all types erased will work equally well for any interface that extends this one. 
 */
interface Premise {
  name: Name
  prettyLemma: CodeWithInfos,
}

/** The props for the tactic suggestions panel. */
interface TacticSuggestionPanelProps {
  /** The metadata of the selection, containing auxilliary information about the selection indicating its location within the proof state. */
  selectionMetadata: SelectionMetadata,
  /** The list of premises to display in the panel. */
  premises: Premise[],
  /** The name of the Lean function to use to validate a premise. */
  validationMethod: Name,
  /** The location in the editor where the suggestions are inserted. */
  range: Range,
  /** The URI of the current working document. */
  documentUri: DocumentUri
}

interface PremiseWithMetadata {
  selectionMetadata: SelectionMetadata
  premise: Premise
}

interface ValidationSuccessResult {
  tactic: string,
  replacementText: CodeWithInfos,
  extraGoals: CodeWithInfos[],
  inFilteredView: boolean // TODO: integrate this into the code
}

interface ValidationErrorResult {
  error: MessageData
}

interface ValidationResetResult {
  premises: Premise[]
}

type PremiseValidationResult =
  { kind: "success", result: ValidationSuccessResult } |
  { kind: "error", result: ValidationErrorResult } |
  { kind: "reset", result: ValidationResetResult }

type PremiseWithValidationResult =
  { kind: "success", result: (Premise & ValidationSuccessResult) } |
  { kind: "error", result: (Premise & ValidationErrorResult) } |
  { kind: "reset", result: ValidationResetResult }

interface TacticSuggestionPanelState {
  successes: (Premise & ValidationSuccessResult)[],
  failures: (Premise & ValidationErrorResult)[],
  pending: Premise[]
}

function addPremiseToValidationResult(premise: Premise, result: PremiseValidationResult): PremiseWithValidationResult {
  if (result.kind === "success") {
    return { kind: "success", result: { ...result.result, ...premise } };
  } else if (result.kind === "error") {
    return { kind: "error", result: { ...result.result, ...premise } };
  } else {
    return result;
  }
}

/** Whether one suggestion is more relevant than another, and therefore should be prioritized in the list of suggestions.
 * The ranking is according to
 * - the number of side goals (the fewer goals the better)
 * - the length of the replacement string (suggestions creating less complicated expressions in the tactic state are favoured)
 * - the tactic string (shorter strings are likely to be more idiomatic and preferable to have in a proof script)
 */
function isMoreRelevantResult(result: ValidationSuccessResult, reference: ValidationSuccessResult): boolean {
  return (result.extraGoals.length < reference.extraGoals.length) || (result.extraGoals.length === reference.extraGoals.length &&
    (result.tactic.length < reference.tactic.length || (result.tactic.length === reference.tactic.length &&
      stripTags(result.replacementText).length < stripTags(reference.replacementText).length)));
}

/** Whether two suggestions are equivalent, in the sense of having the same effect on the tactic state.
 *  This function checks whether the two suggestions have the same replacement and lists of extra goals,
 *  all treated as strings. */
function isEquivalent(result: ValidationSuccessResult, reference: ValidationSuccessResult): boolean {
  return stripTags(result.replacementText) === stripTags(reference.replacementText) &&
    result.extraGoals.length === reference.extraGoals.length &&
    // TODO (Jacob): Sort goals as strings before comparing 
    result.extraGoals.every((goal, index) => stripTags(goal) === stripTags(reference.extraGoals[index]));
}

/** From a *sorted* list of validation success results, 
 * remove suggestions that are equivalent to others in the list. */
function eraseEquivalentEntries(results: (Premise & ValidationSuccessResult)[]): (Premise & ValidationSuccessResult)[] {
  const filtered: (Premise & ValidationSuccessResult)[] = [];
  let previous: (Premise & ValidationSuccessResult) | undefined = undefined;

  for (let i = 0; i < results.length; i++) {
    const current = results[i];

    if (!previous || !isEquivalent(current, previous)) {
      filtered.push(current);
      previous = current;
    }
  }

  return filtered;
}

function reducer(state: TacticSuggestionPanelState, action: PremiseWithValidationResult): TacticSuggestionPanelState {
  if (action.kind === "success") {
    const successes = state.successes;
    const index = successes.findIndex(r => isMoreRelevantResult(action.result, r));
    if (index === -1) {
      successes.push(action.result);
    } else {
      successes.splice(index, 0, action.result);
    }
    return { successes, failures: state.failures, pending: state.pending.filter(result => result.name !== action.result.name) };
  } else if (action.kind === "error") {
    return { successes: state.successes, failures: [...state.failures, action.result], pending: state.pending.filter(result => result.name !== action.result.name) };
  } else {
    return { successes: [], failures: [], pending: action.result.premises };
  }
}

async function applyEdit(edit: TextEdit, documentUri: DocumentUri, ec: EditorConnection) {
  await ec.api.applyEdit({
    changes: {
      [documentUri]: [edit]
    }
  })
}

function renderSuccessResult(ec: EditorConnection, result: Premise & ValidationSuccessResult, showName: boolean, range: Range, documentUri: DocumentUri): JSX.Element {
  // const [isHovered, setIsHovered] = React.useState(false);

  const handleTryThis = async () => {
    const edit: TextEdit = {
      range: range,
      newText: result.tactic
    };
    await applyEdit(edit, documentUri, ec);
  };

  return (
    <div 
      style={{
        display: 'flex',
        gap: '12px',
        padding: '16px',
        marginBottom: '12px',
        backgroundColor: '#f8f9fa', // isHovered ? '#f8f9fa' : '#ffffff',
        borderRadius: '8px',
        border: '1px solid #e1e4e8',
        transition: 'all 0.2s ease',
        boxShadow: '0 2px 8px rgba(0,0,0,0.08)' // isHovered ? '0 2px 8px rgba(0,0,0,0.08)' : '0 1px 3px rgba(0,0,0,0.04)',
      }}
      // onMouseEnter={() => setIsHovered(true)}
      // onMouseLeave={() => setIsHovered(false)}
    >
      <button
        onClick={handleTryThis}
        style={{
          flexShrink: 0,
          padding: '8px 16px',
          backgroundColor: '#0969da',
          color: 'white',
          border: 'none',
          borderRadius: '6px',
          fontSize: '14px',
          fontWeight: '500',
          cursor: 'pointer',
          transition: 'all 0.2s ease',
          height: 'fit-content',
          alignSelf: 'flex-start',
        }}
        // onMouseEnter={(e) => {
        //   e.currentTarget.style.backgroundColor = '#0860ca';
        //   e.currentTarget.style.transform = 'translateY(-1px)';
        //   e.currentTarget.style.boxShadow = '0 2px 8px rgba(9, 105, 218, 0.3)';
        // }}
        // onMouseLeave={(e) => {
        //   e.currentTarget.style.backgroundColor = '#0969da';
        //   e.currentTarget.style.transform = 'translateY(0)';
        //   e.currentTarget.style.boxShadow = 'none';
        // }}
      >
        Try this
      </button>

      <div style={{ flex: 1, minWidth: 0 }}>
        {/* Replacement Text - Prominent Display */}
        <div style={{
          marginBottom: '12px',
          padding: '12px',
          backgroundColor: '#f6f8fa',
          borderRadius: '6px',
          border: '1px solid #d0d7de',
        }}>
          <InteractiveCode fmt={result.replacementText} />
        </div>

        {/* Extra Goals */}
        {result.extraGoals.length > 0 && (
          <div style={{ marginBottom: '12px' }}>
            <div style={{
              fontSize: '12px',
              fontWeight: '600',
              color: '#57606a',
              marginBottom: '8px',
              textTransform: 'uppercase',
              letterSpacing: '0.5px',
            }}>
              Additional Goals
            </div>
            {result.extraGoals.map((goal, index) => (
              <div 
                key={index}
                style={{
                  marginBottom: '8px',
                  padding: '10px 12px',
                  backgroundColor: '#fff8e5',
                  borderLeft: '3px solid #f59e0b',
                  borderRadius: '4px',
                  fontSize: '14px',
                }}
              >
                <strong className="goal-vdash">⊢ </strong>
                <InteractiveCode fmt={goal} />
              </div>
            ))}
          </div>
        )}

        {/* Pretty Lemma Name */}
        {showName && (
          <div style={{
            padding: '10px 12px',
            backgroundColor: '#e6f3ff',
            borderRadius: '6px',
            border: '1px solid #b3d9ff',
            fontSize: '13px',
            color: '#0550ae',
          }}>
            <span style={{ fontWeight: '600', marginRight: '6px' }}>Lemma:</span>
            <InteractiveCode fmt={result.prettyLemma} />
          </div>
        )}
      </div>
    </div>
  );
}

function renderErrorResult(result: Premise & ValidationErrorResult): JSX.Element {
  return (
    <div style={{
      padding: '12px 16px',
      marginBottom: '8px',
      backgroundColor: '#fff1f0',
      borderLeft: '3px solid #d73a49',
      borderRadius: '4px',
    }}>
      <div style={{
        display: 'flex',
        alignItems: 'center',
        gap: '8px',
        marginBottom: '8px',
      }}>
        <span style={{
          fontSize: '16px',
          color: '#d73a49',
        }}>✗</span>
        <span style={{
          fontSize: '14px',
          color: '#24292f',
          fontFamily: 'monospace',
          fontWeight: '600',
        }}>
          <InteractiveCode fmt={result.prettyLemma} />
        </span>
      </div>
      <div style={{
        paddingLeft: '24px',
        fontSize: '13px',
        color: '#57606a',
        lineHeight: '1.5',
      }}>
        <InteractiveMessageData msg={result.error} />
      </div>
    </div>
  );
}

function renderPendingResult(result: Premise): JSX.Element {
  return (
    <div style={{
      padding: '12px 16px',
      marginBottom: '8px',
      backgroundColor: '#f6f8fa',
      borderLeft: '3px solid #8b949e',
      borderRadius: '4px',
      display: 'flex',
      alignItems: 'center',
      gap: '8px',
    }}>
      <span style={{
        fontSize: '14px',
        color: '#8b949e',
        animation: 'spin 1s linear infinite',
      }}>⟳</span>
      <span style={{
        fontSize: '14px',
        color: '#57606a',
        fontFamily: 'monospace',
      }}>
        <InteractiveCode fmt={result.prettyLemma} />
      </span>
      <style>{`
        @keyframes spin {
          from { transform: rotate(0deg); }
          to { transform: rotate(360deg); }
        }
      `}</style>
    </div>
  );
}

function renderValidationState(ec: EditorConnection, state: TacticSuggestionPanelState, range: Range, documentUri: DocumentUri): JSX.Element {
  // const { showFailed, showPending, filterResults, showNames } = React.useContext(ValidationOptionsContext);
  const showFailed = true;
  const showPending = true;
  const filterResults = true;
  const showNames = true;

  const successes = filterResults ? eraseEquivalentEntries(state.successes) : state.successes;

  return (
    <div>
      {showPending && state.pending.map((p, i) => (
        <div key={`pending-${i}`}>{renderPendingResult(p)}</div>
      ))}

      {showFailed && state.failures.map((f, i) => (
        <div key={`fail-${i}`}>{renderErrorResult(f)}</div>
      ))}

      {successes.map((s, i) => (
        <div key={`succ-${i}`}>{renderSuccessResult(ec, s, showNames, range, documentUri)}</div>
      ))}
    </div>
  );
}

/**
 * The `TacticSuggestionsPanel` component. 
 */
export default function TacticSuggestionsPanel(props: TacticSuggestionPanelProps): JSX.Element {
  const [state, updateState] = React.useReducer(reducer, {
    successes: [],
    failures: [],
    pending: props.premises
  });
  const r = React.useRef(0);
  const rs = useRpcSession();
  const ec = React.useContext(EditorContext);


  async function e() {
    r.current += 1;
    const id = r.current;
    updateState({ kind: "reset", result: { premises: props.premises } });
    for (let i = 0; i < props.premises.length; i++) {
      const premise = props.premises[i];
      const result = await rs.call<PremiseWithMetadata, PremiseValidationResult>(props.validationMethod, { selectionMetadata: props.selectionMetadata, premise });
      if (r.current !== id) {
        return;
      }
      updateState(addPremiseToValidationResult(premise, result));
    }
  }

  React.useEffect(() => {
    e()
  }, [rs, props.premises.map(p => p.name).join(",")]); // TODO: think about why this is necessary, and remove if it is not

  return (
      renderValidationState(ec, state, props.range, props.documentUri)
  );
}