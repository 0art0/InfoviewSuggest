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
        return { successes, failures: state.failures, pending: state.pending.filter(result => result.name !== action.result.name) };
    }
    else if (action.kind === "error") {
        return { successes: state.successes, failures: [...state.failures, action.result], pending: state.pending.filter(result => result.name !== action.result.name) };
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
    await ec.revealPosition({ line: edit.range.start.line, character: edit.range.start.character + edit.newText.length, uri: documentUri });
}
function renderSuccessResult(ec, result, showName, range, documentUri) {
    const handleTryThis = async () => {
        const edit = {
            range: range,
            newText: result.tactic
        };
        await applyEdit(edit, documentUri, ec);
    };
    return (_jsx("div", { style: {
            display: 'flex',
            gap: '12px',
            padding: '12px',
            backgroundColor: '#f8fafc',
            borderRadius: '8px',
            border: '1px solid #e2e8f0',
            transition: 'all 0.2s ease',
            boxShadow: '0 1px 2px rgba(0,0,0,0.05)',
        }, children: _jsxs("div", { style: { flex: 1, minWidth: 0 }, children: [_jsxs("div", { style: {
                        display: 'flex',
                        alignItems: 'center',
                        gap: '8px',
                        marginBottom: showName || result.extraGoals.length > 0 ? '8px' : 0
                    }, children: [_jsx("button", { onClick: handleTryThis, style: {
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
                            }, onMouseEnter: (e) => {
                                e.currentTarget.style.backgroundColor = '#0860ca';
                                e.currentTarget.style.transform = 'translateY(-1px)';
                            }, onMouseLeave: (e) => {
                                e.currentTarget.style.backgroundColor = '#0969da';
                                e.currentTarget.style.transform = 'translateY(0)';
                            }, children: "Try this" }), _jsx("div", { style: {
                                fontSize: '14px',
                                fontFamily: 'monospace',
                                overflow: 'hidden',
                                textOverflow: 'ellipsis',
                                whiteSpace: 'nowrap',
                                marginBottom: showName || result.extraGoals.length > 0 ? '8px' : 0
                            }, children: _jsx(InteractiveCode, { fmt: result.replacementText }) })] }), result.extraGoals.length > 0 && (_jsx("div", { style: {
                        marginBottom: showName ? '8px' : 0,
                        display: 'flex',
                        flexDirection: 'column',
                        gap: '4px'
                    }, children: result.extraGoals.map((goal, index) => (_jsxs("div", { style: {
                            padding: '4px 8px',
                            backgroundColor: '#f1f5f9',
                            borderLeft: '2px solid var(--vscode-lean4-infoView\\.turnstile)',
                            borderRadius: '4px',
                            fontSize: '13px',
                            display: 'flex',
                            alignItems: 'center',
                            gap: '6px'
                        }, children: [_jsx("span", { style: {
                                    color: 'var(--vscode-lean4-infoView\\.turnstile)',
                                    fontWeight: '500',
                                    userSelect: 'none'
                                }, children: "\u22A2" }), _jsx("span", { style: {
                                    flex: 1,
                                    overflow: 'hidden',
                                    textOverflow: 'ellipsis',
                                    whiteSpace: 'nowrap'
                                }, children: _jsx(InteractiveCode, { fmt: goal }) })] }, index))) })), showName && (_jsxs("div", { children: [_jsx("hr", { style: {
                                border: 'none',
                                borderTop: '1px solid #e2e8f0',
                                margin: '12px 0 12px 0'
                            } }), _jsxs("div", { style: {
                                display: 'flex',
                                alignItems: 'center',
                                gap: '8px',
                                fontSize: '12px',
                                color: '#64748b'
                            }, children: [_jsx("span", { style: {
                                        fontWeight: '600',
                                        textTransform: 'uppercase',
                                        letterSpacing: '0.025em',
                                        fontSize: '11px',
                                        color: '#475569'
                                    }, children: "Lemma" }), _jsx("span", { style: {
                                        flex: 1,
                                        overflow: 'hidden',
                                        textOverflow: 'ellipsis',
                                        whiteSpace: 'nowrap'
                                    }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("button", { onClick: () => navigator.clipboard.writeText(result.name.toString()), style: {
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
                                    }, title: "Copy lemma name", onMouseEnter: e => e.currentTarget.style.opacity = '1', onMouseLeave: e => e.currentTarget.style.opacity = '0.7', children: "\uD83D\uDCCB" })] })] }))] }) }));
}
function renderErrorResult(result) {
    const handleCopy = () => {
        navigator.clipboard.writeText(result.name.toString());
    };
    return (_jsxs("div", { style: {
            padding: '8px 12px',
            marginBottom: '6px',
            background: 'linear-gradient(to right, #fef2f2, #fee2e2)',
            border: '1px solid #fecaca',
            borderRadius: '6px',
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
        }, children: [_jsxs("div", { style: {
                    flex: 1,
                    display: 'flex',
                    flexDirection: 'column',
                    gap: '4px',
                    minWidth: 0
                }, children: [_jsx("div", { style: {
                            fontSize: '14px',
                            color: '#991b1b',
                            fontFamily: 'monospace',
                            overflow: 'hidden',
                            textOverflow: 'ellipsis',
                            whiteSpace: 'nowrap'
                        }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("div", { style: {
                            fontSize: '12px',
                            color: '#7f1d1d',
                            lineHeight: '1.4'
                        }, children: _jsx(InteractiveMessageData, { msg: result.error }) })] }), _jsx("button", { onClick: handleCopy, style: {
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
                }, title: "Copy lemma name", onMouseEnter: e => e.currentTarget.style.opacity = '1', onMouseLeave: e => e.currentTarget.style.opacity = '0.6', children: "\uD83D\uDCCB" })] }));
}
function renderPendingResult(result) {
    const handleCopy = () => {
        navigator.clipboard.writeText(result.name);
    };
    return (_jsxs("div", { style: {
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
        }, children: [_jsx("div", { style: {
                    width: '16px',
                    height: '16px',
                    borderRadius: '50%',
                    borderTop: '2px solid #d97706',
                    borderRight: '2px solid transparent',
                    animation: 'spin 0.8s linear infinite',
                    flexShrink: 0
                } }), _jsx("div", { style: {
                    flex: 1,
                    fontSize: '14px',
                    color: '#92400e',
                    fontFamily: 'monospace',
                    overflow: 'hidden',
                    textOverflow: 'ellipsis',
                    whiteSpace: 'nowrap',
                }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("button", { onClick: handleCopy, style: {
                    background: 'none',
                    border: 'none',
                    padding: '4px',
                    cursor: 'pointer',
                    color: '#b45309',
                    opacity: 0.6,
                    transition: 'opacity 0.2s ease',
                    display: 'flex',
                    alignItems: 'center',
                }, title: "Copy lemma name", onMouseEnter: e => e.currentTarget.style.opacity = '1', onMouseLeave: e => e.currentTarget.style.opacity = '0.6', children: "\uD83D\uDCCB" }), _jsx("style", { children: `
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
    const showNames = false;
    const successes = filterResults ? eraseEquivalentEntries(state.successes) : state.successes;
    return (_jsxs("div", { style: {
            backgroundColor: 'white',
            border: '1px solid #e1e4e8',
            borderRadius: '8px',
            padding: '16px',
            boxShadow: '0 1px 3px rgba(0,0,0,0.04)'
        }, children: [successes.length > 0 && (_jsx("div", { style: { marginBottom: '16px' }, children: successes.map((s, i) => (_jsx("div", { style: { marginBottom: '8px' }, children: renderSuccessResult(ec, s, showNames, range, documentUri) }, `succ-${i}`))) })), state.failures.length > 0 && (_jsxs("details", { style: { marginBottom: '16px' }, children: [_jsxs("summary", { style: {
                            padding: '8px 12px',
                            cursor: 'pointer',
                            userSelect: 'none',
                            display: 'flex',
                            alignItems: 'center',
                            gap: '8px',
                            borderRadius: '4px',
                            backgroundColor: '#fff5f5',
                            marginBottom: '8px'
                        }, children: [_jsx("span", { style: { color: '#e11d48', fontSize: '16px' }, children: "\u2715" }), _jsxs("span", { style: { fontWeight: 500 }, children: ["Failures (", state.failures.length, ")"] })] }), state.failures.map((f, i) => (_jsx("div", { style: { marginBottom: '8px' }, children: renderErrorResult(f) }, `fail-${i}`)))] })), state.pending.length > 0 && (_jsxs("details", { open: true, style: { marginBottom: '16px' }, children: [_jsxs("summary", { style: {
                            padding: '8px 12px',
                            cursor: 'pointer',
                            userSelect: 'none',
                            display: 'flex',
                            alignItems: 'center',
                            gap: '8px',
                            borderRadius: '4px',
                            backgroundColor: '#fefce8',
                            marginBottom: '8px'
                        }, children: [_jsx("span", { style: {
                                    color: '#ca8a04',
                                    fontSize: '16px',
                                    display: 'inline-block',
                                    animation: 'spin 2s linear infinite'
                                }, children: "\u231A" }), _jsxs("span", { style: { fontWeight: 500 }, children: ["In Progress (", state.pending.length, ")"] })] }), state.pending.map((p, i) => (_jsx("div", { style: { marginBottom: '8px' }, children: renderPendingResult(p) }, `pending-${i}`)))] })), _jsx("style", { children: `
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
    ` })] }));
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
