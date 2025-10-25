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
  await ec.revealPosition({ line: edit.range.start.line, character: edit.range.start.character + edit.newText.length, uri: documentUri });
}

function renderSuccessResult(ec: EditorConnection, result: Premise & ValidationSuccessResult, showName: boolean, range: Range, documentUri: DocumentUri): JSX.Element {
  const handleTryThis = async () => {
    const edit: TextEdit = {
      range: range,
      newText: result.tactic
    };
    await applyEdit(edit, documentUri, ec);
  };

  return (
    <div style={{
      display: 'flex',
      gap: '12px',
      padding: '12px',
      backgroundColor: '#f8fafc',
      borderRadius: '8px',
      border: '1px solid #e2e8f0',
      transition: 'all 0.2s ease',
      boxShadow: '0 1px 2px rgba(0,0,0,0.05)',
    }}>
      <div style={{ flex: 1, minWidth: 0 }}>
        {/* Replacement Text */}
        <div style={{
          display: 'flex',
          alignItems: 'center',
          gap: '8px',
          marginBottom: showName || result.extraGoals.length > 0 ? '8px' : 0
        }}>
          <button
            onClick={handleTryThis}
            style={{
              padding: '6px 12px',
              backgroundColor: '#0969da',
              color: 'white',
              border: 'none',
              borderRadius: '4px',
              fontSize: '13px',
              fontWeight: '500',
              cursor: 'pointer',
              transition: 'all 0.2s ease',
              flexShrink: 0,
              alignSelf: 'flex-start'
            }}
            onMouseEnter={(e) => {
              e.currentTarget.style.backgroundColor = '#0860ca';
              e.currentTarget.style.transform = 'translateY(-1px)';
            }}
            onMouseLeave={(e) => {
              e.currentTarget.style.backgroundColor = '#0969da';
              e.currentTarget.style.transform = 'translateY(0)';
            }}
          >
            Try this
          </button>
          <div style={{
            fontSize: '14px',
            fontFamily: 'monospace',
            overflow: 'hidden',
            textOverflow: 'ellipsis',
            whiteSpace: 'nowrap',
            marginBottom: showName || result.extraGoals.length > 0 ? '8px' : 0
          }}>
            <InteractiveCode fmt={result.replacementText} />
          </div>
        </div>

        {/* Extra Goals */}
        {result.extraGoals.length > 0 && (
          <div style={{ 
            marginBottom: showName ? '8px' : 0,
            display: 'flex',
            flexDirection: 'column',
            gap: '4px' 
          }}>
            {result.extraGoals.map((goal, index) => (
              <div key={index} style={{
                padding: '4px 8px',
                backgroundColor: '#f1f5f9',
                borderLeft: '2px solid var(--vscode-lean4-infoView\\.turnstile)',
                borderRadius: '4px',
                fontSize: '13px',
                display: 'flex',
                alignItems: 'center',
                gap: '6px'
              }}>
                <span style={{ 
                  color: 'var(--vscode-lean4-infoView\\.turnstile)',
                  fontWeight: '500',
                  userSelect: 'none'
                }}>⊢</span>
                <span style={{
                  flex: 1,
                  overflow: 'hidden',
                  textOverflow: 'ellipsis',
                  whiteSpace: 'nowrap'
                }}>
                  <InteractiveCode fmt={goal} />
                </span>
              </div>
            ))}
          </div>
        )}

        {/* Lemma Name */}
        {showName && (
          <div>
            <hr style={{
              border: 'none',
              borderTop: '1px solid #e2e8f0',
              margin: '12px 0 12px 0'
            }} />
            <div style={{
              display: 'flex',
              alignItems: 'center',
              gap: '8px',
              fontSize: '12px',
              color: '#64748b'
            }}>
              <span style={{ 
                fontWeight: '600',
                textTransform: 'uppercase',
                letterSpacing: '0.025em',
                fontSize: '11px',
                color: '#475569'
              }}>Lemma</span>
              <span style={{
                flex: 1,
                overflow: 'hidden',
                textOverflow: 'ellipsis',
                whiteSpace: 'nowrap'
              }}>
                <InteractiveCode fmt={result.prettyLemma} />
              </span>
              <button
                onClick={() => navigator.clipboard.writeText(result.name.toString())}
                style={{
                  background: 'none',
                  border: 'none',
                  padding: '4px',
                  cursor: 'pointer',
                  color: '#64748b',
                  opacity: 0.7,
                  transition: 'all 0.2s ease',
                  display: 'flex',
                  alignItems: 'center',
                  flexShrink: 0,
                  fontSize: '14px'
                }}
                title="Copy lemma name"
                onMouseEnter={e => e.currentTarget.style.opacity = '1'}
                onMouseLeave={e => e.currentTarget.style.opacity = '0.7'}
              >
                {/* Using a different clipboard icon */}
                📋
              </button>
            </div>
          </div>
        )}
      </div>
    </div>
  );
}

function renderErrorResult(result: Premise & ValidationErrorResult): JSX.Element {
  const handleCopy = () => {
    navigator.clipboard.writeText(result.name.toString());
  };

  return (
    <div style={{
      padding: '8px 12px',
      marginBottom: '6px',
      background: 'linear-gradient(to right, #fef2f2, #fee2e2)',
      border: '1px solid #fecaca',
      borderRadius: '6px',
      display: 'flex',
      alignItems: 'center',
      gap: '8px',
    }}>
      {/* Content Container */}
      <div style={{
        flex: 1,
        display: 'flex',
        flexDirection: 'column',
        gap: '4px',
        minWidth: 0
      }}>
        {/* Lemma */}
        <div style={{
          fontSize: '14px',
          color: '#991b1b',
          fontFamily: 'monospace',
          overflow: 'hidden',
          textOverflow: 'ellipsis',
          whiteSpace: 'nowrap'
        }}>
          <InteractiveCode fmt={result.prettyLemma} />
        </div>

        {/* Error Message */}
        <div style={{
          fontSize: '12px',
          color: '#7f1d1d',
          lineHeight: '1.4'
        }}>
          <InteractiveMessageData msg={result.error} />
        </div>
      </div>

      {/* Copy Button */}
      <button
        onClick={handleCopy}
        style={{
          background: 'none',
          border: 'none',
          padding: '4px',
          cursor: 'pointer',
          color: '#dc2626',
          opacity: 0.6,
          transition: 'opacity 0.2s ease',
          display: 'flex',
          alignItems: 'center',
          flexShrink: 0
        }}
        title="Copy lemma name"
        onMouseEnter={e => e.currentTarget.style.opacity = '1'}
        onMouseLeave={e => e.currentTarget.style.opacity = '0.6'}
      >
        📋
      </button>
    </div>
  );
}

function renderPendingResult(result: Premise): JSX.Element {
  const handleCopy = () => {
    navigator.clipboard.writeText(result.name);
  };

  return (
    <div style={{
      padding: '8px 12px',
      marginBottom: '6px',
      background: 'linear-gradient(to right, #fffbeb, #fef9c3)',
      border: '1px solid #fde68a',
      borderRadius: '6px',
      display: 'flex',
      alignItems: 'center',
      gap: '8px',
      position: 'relative',
      transition: 'all 0.2s ease',
    }}>
      {/* Spinning Circle */}
      <div style={{
        width: '16px',
        height: '16px',
        borderRadius: '50%',
        borderTop: '2px solid #d97706',
        borderRight: '2px solid transparent',
        animation: 'spin 0.8s linear infinite',
        flexShrink: 0
      }} />

      {/* Lemma Content */}
      <div style={{
        flex: 1,
        fontSize: '14px',
        color: '#92400e',
        fontFamily: 'monospace',
        overflow: 'hidden',
        textOverflow: 'ellipsis',
        whiteSpace: 'nowrap',
      }}>
        <InteractiveCode fmt={result.prettyLemma} />
      </div>

      {/* Copy Button */}
      <button
        onClick={handleCopy}
        style={{
          background: 'none',
          border: 'none',
          padding: '4px',
          cursor: 'pointer',
          color: '#b45309',
          opacity: 0.6,
          transition: 'opacity 0.2s ease',
          display: 'flex',
          alignItems: 'center',
        }}
        title="Copy lemma name"
        onMouseEnter={e => e.currentTarget.style.opacity = '1'}
        onMouseLeave={e => e.currentTarget.style.opacity = '0.6'}
      >
        📋
      </button>

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
  <div style={{
    backgroundColor: 'white',
    border: '1px solid #e1e4e8',
    borderRadius: '8px',
    padding: '16px',
    boxShadow: '0 1px 3px rgba(0,0,0,0.04)'
  }}>
    {/* Successes Section */}
    {successes.length > 0 && (
      <div style={{ marginBottom: '16px' }}>
        {successes.map((s, i) => (
          <div key={`succ-${i}`} style={{ marginBottom: '8px' }}>
            {renderSuccessResult(ec, s, showNames, range, documentUri)}
          </div>
        ))}
      </div>
    )}

    {/* Failures Section */}
    {state.failures.length > 0 && (
      <details style={{ marginBottom: '16px' }}>
        <summary style={{
          padding: '8px 12px',
          cursor: 'pointer',
          userSelect: 'none',
          display: 'flex',
          alignItems: 'center',
          gap: '8px',
          borderRadius: '4px',
          backgroundColor: '#fff5f5',
          marginBottom: '8px'
        }}>
          <span style={{ color: '#e11d48', fontSize: '16px' }}>✕</span>
          <span style={{ fontWeight: 500 }}>
            Failures ({state.failures.length})
          </span>
        </summary>
        {state.failures.map((f, i) => (
          <div key={`fail-${i}`} style={{ marginBottom: '8px' }}>{renderErrorResult(f)}</div>
        ))}
      </details>
    )}

    {/* Pending Section */}
    {state.pending.length > 0 && (
      <details open style={{ marginBottom: '16px' }}>
        <summary style={{
          padding: '8px 12px',
          cursor: 'pointer',
          userSelect: 'none',
          display: 'flex',
          alignItems: 'center',
          gap: '8px',
          borderRadius: '4px',
          backgroundColor: '#fefce8',
          marginBottom: '8px'
        }}>
          <span style={{ 
            color: '#ca8a04',
            fontSize: '16px',
            display: 'inline-block',
            animation: 'spin 2s linear infinite'
          }}>⌚</span>
          <span style={{ fontWeight: 500 }}>
            In Progress ({state.pending.length})
          </span>
        </summary>
        {state.pending.map((p, i) => (
          <div key={`pending-${i}`} style={{ marginBottom: '8px' }}>{renderPendingResult(p)}</div>
        ))}
      </details>
    )}

    <style>{`
      @keyframes spin {
        from { transform: rotate(0deg); }
        to { transform: rotate(360deg); }
      }
      
      details > summary {
        list-style: none;
      }
      details > summary::-webkit-details-marker {
        display: none;
      }
      details > summary::before {
        content: '▶';
        margin-right: 8px;
        transition: transform 0.2s;
        display: inline-block;
      }
      details[open] > summary::before {
        transform: rotate(90deg);
      }
      details summary:hover {
        background-color: rgba(0,0,0,0.03);
      }
    `}</style>
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