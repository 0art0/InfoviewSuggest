import { jsx as _jsx, jsxs as _jsxs } from "react/jsx-runtime";
/**
 * A panel for displaying a list of tactic suggestions to the user.
 * The suggestions are all tried in the background in parallel, and by default,
 * only ones that are found valid are displayed to the user.
 *
 * The code here heavily relies on the widget code in https://github.com/BartoszPiotrowski/lean-premise-selection/tree/main/widget.
 */
import { InteractiveCode, EditorContext, InteractiveMessageData, useRpcSession } from "@leanprover/infoview";
import React from "react";
// TODO: Create a component for this context
const ValidationOptionsContext = React.createContext({
    showFailed: false,
    showPending: true,
    filterResults: true,
    showNames: false
});
/** Strips the tags from a `TaggedText` object to extract the underlying plain text. */
function stripTags(text) {
    if ("text" in text) {
        return text.text;
    }
    else if ("append" in text) {
        return text.append.map(stripTags).join("");
    }
    else if ("tag" in text) {
        return stripTags(text.tag[1]);
    }
    else {
        throw new Error("Invalid `TaggedText` structure");
    }
}
function addPremiseToValidationResult(premise, result) {
    if (result.kind === "success") {
        return { kind: "success", result: { ...result.result, ...premise } };
    }
    else if (result.kind === "error") {
        return { kind: "error", result: { ...result.result, ...premise } };
    }
    else {
        return result;
    }
}
/** Whether one suggestion is more relevant than another, and therefore should be prioritized in the list of suggestions.
 * The ranking is according to
 * - the number of side goals (the fewer goals the better)
 * - the length of the replacement string (suggestions creating less complicated expressions in the tactic state are favoured)
 * - the tactic string (shorter strings are likely to be more idiomatic and preferable to have in a proof script)
 */
function isMoreRelevantResult(result, reference) {
    return (result.extraGoals.length < reference.extraGoals.length) || (result.extraGoals.length === reference.extraGoals.length &&
        (result.tactic.length < reference.tactic.length || (result.tactic.length === reference.tactic.length &&
            stripTags(result.replacementText).length < stripTags(reference.replacementText).length)));
}
/** Whether two suggestions are equivalent, in the sense of having the same effect on the tactic state.
 *  This function checks whether the two suggestions have the same replacement and lists of extra goals,
 *  all treated as strings. */
function isEquivalent(result, reference) {
    return stripTags(result.replacementText) === stripTags(reference.replacementText) &&
        result.extraGoals.length === reference.extraGoals.length &&
        // TODO (Jacob): Sort goals as strings before comparing 
        result.extraGoals.every((goal, index) => stripTags(goal) === stripTags(reference.extraGoals[index]));
}
/** From a *sorted* list of validation success results,
 * remove suggestions that are equivalent to others in the list. */
function eraseEquivalentEntries(results) {
    const filtered = [];
    let previous = undefined;
    for (let i = 0; i < results.length; i++) {
        const current = results[i];
        if (!previous || !isEquivalent(current, previous)) {
            filtered.push(current);
            previous = current;
        }
    }
    return filtered;
}
function reducer(state, action) {
    if (action.kind === "success") {
        const successes = state.successes;
        const index = successes.findIndex(r => isMoreRelevantResult(action.result, r));
        if (index === -1) {
            successes.push(action.result);
        }
        else {
            successes.splice(index, 0, action.result);
        }
        return { ...state, successes };
    }
    else if (action.kind === "error") {
        return { ...state, failures: [...state.failures, action.result] };
    }
    else {
        return { successes: [], failures: [], pending: action.result.premises };
    }
}
async function applyEdit(edit, documentUri, ec) {
    await ec.api.applyEdit({
        changes: {
            [documentUri]: [edit]
        }
    });
}
function renderSuccessResult(ec, result, showName, range, documentUri) {
    // const [isHovered, setIsHovered] = React.useState(false);
    const handleTryThis = async () => {
        const edit = {
            range: range,
            newText: result.tactic
        };
        await applyEdit(edit, documentUri, ec);
    };
    return (_jsxs("div", { style: {
            display: 'flex',
            gap: '12px',
            padding: '16px',
            marginBottom: '12px',
            backgroundColor: '#f8f9fa', // isHovered ? '#f8f9fa' : '#ffffff',
            borderRadius: '8px',
            border: '1px solid #e1e4e8',
            transition: 'all 0.2s ease',
            boxShadow: '0 2px 8px rgba(0,0,0,0.08)' // isHovered ? '0 2px 8px rgba(0,0,0,0.08)' : '0 1px 3px rgba(0,0,0,0.04)',
        }, children: [_jsx("button", { onClick: handleTryThis, style: {
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
                }, children: "Try this" }), _jsxs("div", { style: { flex: 1, minWidth: 0 }, children: [_jsx("div", { style: {
                            marginBottom: '12px',
                            padding: '12px',
                            backgroundColor: '#f6f8fa',
                            borderRadius: '6px',
                            border: '1px solid #d0d7de',
                        }, children: _jsx(InteractiveCode, { fmt: result.replacementText }) }), result.extraGoals.length > 0 && (_jsxs("div", { style: { marginBottom: '12px' }, children: [_jsx("div", { style: {
                                    fontSize: '12px',
                                    fontWeight: '600',
                                    color: '#57606a',
                                    marginBottom: '8px',
                                    textTransform: 'uppercase',
                                    letterSpacing: '0.5px',
                                }, children: "Additional Goals" }), result.extraGoals.map((goal, index) => (_jsxs("div", { style: {
                                    marginBottom: '8px',
                                    padding: '10px 12px',
                                    backgroundColor: '#fff8e5',
                                    borderLeft: '3px solid #f59e0b',
                                    borderRadius: '4px',
                                    fontSize: '14px',
                                }, children: [_jsx("strong", { className: "goal-vdash", children: "\u22A2 " }), _jsx(InteractiveCode, { fmt: goal })] }, index)))] })), showName && (_jsxs("div", { style: {
                            padding: '10px 12px',
                            backgroundColor: '#e6f3ff',
                            borderRadius: '6px',
                            border: '1px solid #b3d9ff',
                            fontSize: '13px',
                            color: '#0550ae',
                        }, children: [_jsx("span", { style: { fontWeight: '600', marginRight: '6px' }, children: "Lemma:" }), _jsx(InteractiveCode, { fmt: result.prettyLemma })] }))] })] }));
}
function renderErrorResult(result) {
    return (_jsxs("div", { style: {
            padding: '12px 16px',
            marginBottom: '8px',
            backgroundColor: '#fff1f0',
            borderLeft: '3px solid #d73a49',
            borderRadius: '4px',
        }, children: [_jsxs("div", { style: {
                    display: 'flex',
                    alignItems: 'center',
                    gap: '8px',
                    marginBottom: '8px',
                }, children: [_jsx("span", { style: {
                            fontSize: '16px',
                            color: '#d73a49',
                        }, children: "\u2717" }), _jsx("span", { style: {
                            fontSize: '14px',
                            color: '#24292f',
                            fontFamily: 'monospace',
                            fontWeight: '600',
                        }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) })] }), _jsx("div", { style: {
                    paddingLeft: '24px',
                    fontSize: '13px',
                    color: '#57606a',
                    lineHeight: '1.5',
                }, children: _jsx(InteractiveMessageData, { msg: result.error }) })] }));
}
function renderPendingResult(result) {
    return (_jsxs("div", { style: {
            padding: '12px 16px',
            marginBottom: '8px',
            backgroundColor: '#f6f8fa',
            borderLeft: '3px solid #8b949e',
            borderRadius: '4px',
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
        }, children: [_jsx("span", { style: {
                    fontSize: '14px',
                    color: '#8b949e',
                    animation: 'spin 1s linear infinite',
                }, children: "\u27F3" }), _jsx("span", { style: {
                    fontSize: '14px',
                    color: '#57606a',
                    fontFamily: 'monospace',
                }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("style", { children: `
        @keyframes spin {
          from { transform: rotate(0deg); }
          to { transform: rotate(360deg); }
        }
      ` })] }));
}
function renderValidationState(ec, state, range, documentUri) {
    // const { showFailed, showPending, filterResults, showNames } = React.useContext(ValidationOptionsContext);
    const showFailed = true;
    const showPending = true;
    const filterResults = true;
    const showNames = true;
    const successes = filterResults ? eraseEquivalentEntries(state.successes) : state.successes;
    return (_jsxs("div", { children: [showPending && state.pending.map((p, i) => (_jsx("div", { children: renderPendingResult(p) }, `pending-${i}`))), showFailed && state.failures.map((f, i) => (_jsx("div", { children: renderErrorResult(f) }, `fail-${i}`))), successes.map((s, i) => (_jsx("div", { children: renderSuccessResult(ec, s, showNames, range, documentUri) }, `succ-${i}`)))] }));
}
/**
 * The `TacticSuggestionsPanel` component.
 */
export default function TacticSuggestionsPanel(props) {
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
            const result = await rs.call(props.validationMethod, { selectionMetadata: props.selectionMetadata, premise });
            if (r.current !== id) {
                return;
            }
            updateState(addPremiseToValidationResult(premise, result));
        }
    }
    React.useEffect(() => {
        e();
    }, [rs, props.premises.map(p => p.name).join(",")]); // TODO: think about why this is necessary, and remove if it is not
    return (renderValidationState(ec, state, props.range, props.documentUri));
}
