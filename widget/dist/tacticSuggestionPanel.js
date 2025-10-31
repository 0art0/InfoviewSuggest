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
    return (_jsxs("div", { style: {
            display: 'flex',
            gap: '6px',
            padding: '6px 6px',
            /* remove boxed background; use a subtle left accent instead */
            backgroundColor: 'transparent',
            border: 'none',
            boxShadow: 'none',
            alignItems: 'stretch',
            borderLeft: '2px solid var(--accent-blue)'
        }, children: [_jsx("div", { style: { display: 'flex', alignItems: 'center', flexShrink: 0 }, children: _jsx("span", { role: "button", tabIndex: 0, title: "Paste suggestion into the editor", "aria-label": "Paste suggestion into the editor", className: "link pointer mh2 dim codicon codicon-insert", style: { display: 'inline-flex', alignItems: 'center', justifyContent: 'center', padding: '4px' }, onClick: () => { handleTryThis(); }, onKeyDown: (e) => { if (e.key === 'Enter' || e.key === ' ') {
                        e.preventDefault();
                        handleTryThis();
                    } }, onMouseEnter: (e) => {
                        const t = e.currentTarget;
                        t.style.opacity = '0.9';
                        t.style.transform = 'translateY(-1px)';
                    }, onMouseLeave: (e) => {
                        const t = e.currentTarget;
                        t.style.opacity = '';
                        t.style.transform = '';
                    } }) }), _jsxs("div", { style: { flex: 1, minWidth: 0 }, children: [_jsx("div", { style: {
                            display: 'flex',
                            alignItems: 'center',
                            gap: '6px',
                            marginBottom: showName || result.extraGoals.length > 0 ? '4px' : 0
                        }, children: _jsx("div", { style: {
                                fontSize: '12px',
                                fontFamily: 'monospace',
                                overflow: 'hidden',
                                textOverflow: 'ellipsis',
                                whiteSpace: 'nowrap',
                            }, children: _jsx(InteractiveCode, { fmt: result.replacementText }) }) }), result.extraGoals.length > 0 && (_jsx("div", { style: {
                            marginBottom: showName ? '6px' : 0,
                            display: 'flex',
                            flexDirection: 'column',
                            gap: '3px'
                        }, children: result.extraGoals.map((goal, index) => (_jsxs("div", { style: {
                                padding: '2px 6px',
                                backgroundColor: 'var(--bg-extra)',
                                borderLeft: '2px solid var(--turnstile)',
                                borderRadius: '3px',
                                fontSize: '11px',
                                display: 'flex',
                                alignItems: 'center',
                                gap: '4px'
                            }, children: [_jsx("span", { style: {
                                        color: 'var(--turnstile)',
                                        fontWeight: 500,
                                        userSelect: 'none'
                                    }, children: "\u22A2" }), _jsx("span", { style: {
                                        flex: 1,
                                        overflow: 'hidden',
                                        textOverflow: 'ellipsis',
                                        whiteSpace: 'nowrap'
                                    }, children: _jsx(InteractiveCode, { fmt: goal }) })] }, index))) })), showName && (_jsxs("div", { children: [_jsx("hr", { style: {
                                    border: 'none',
                                    borderTop: '1px solid var(--border-default)',
                                    margin: '6px 0'
                                } }), _jsxs("div", { style: {
                                    display: 'flex',
                                    alignItems: 'center',
                                    gap: '6px',
                                    fontSize: '11px',
                                    color: 'var(--text-muted)'
                                }, children: [_jsx("span", { style: {
                                            fontWeight: 600,
                                            textTransform: 'uppercase',
                                            letterSpacing: '0.025em',
                                            fontSize: '10px',
                                            color: 'var(--text-muted)'
                                        }, children: "Lemma" }), _jsx("span", { style: {
                                            flex: 1,
                                            overflow: 'hidden',
                                            textOverflow: 'ellipsis',
                                            whiteSpace: 'nowrap'
                                        }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) })] })] }))] })] }));
}
function renderErrorResult(result) {
    return (_jsx("div", { style: {
            padding: '4px 6px',
            marginBottom: '3px',
            /* remove boxed background and border */
            backgroundColor: 'transparent',
            border: 'none',
            borderRadius: 0,
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
            borderLeft: '2px solid var(--error-fg)'
        }, children: _jsxs("div", { style: {
                flex: 1,
                display: 'flex',
                flexDirection: 'column',
                gap: '4px',
                minWidth: 0
            }, children: [_jsx("div", { style: {
                        fontSize: '12px',
                        color: 'var(--text-default)',
                        fontFamily: 'monospace',
                        overflow: 'hidden',
                        textOverflow: 'ellipsis',
                        whiteSpace: 'nowrap'
                    }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("div", { style: {
                        fontSize: '11px',
                        color: 'var(--error-fg)',
                        lineHeight: '1.25'
                    }, children: _jsx(InteractiveMessageData, { msg: result.error }) })] }) }));
}
function renderPendingResult(result) {
    return (_jsxs("div", { style: {
            padding: '4px 6px',
            marginBottom: '3px',
            /* remove boxed background and border */
            backgroundColor: 'transparent',
            border: 'none',
            borderRadius: 0,
            display: 'flex',
            alignItems: 'center',
            gap: '8px',
            position: 'relative',
            transition: 'all 0.12s ease',
            borderLeft: '2px solid var(--accent-yellow)'
        }, children: [_jsx("div", { style: {
                    width: '12px',
                    height: '12px',
                    borderRadius: '50%',
                    borderTop: '2px solid var(--accent-yellow)',
                    borderRight: '2px solid transparent',
                    animation: 'spin 0.8s linear infinite',
                    flexShrink: 0
                } }), _jsx("div", { style: {
                    flex: 1,
                    fontSize: '12px',
                    color: 'var(--accent-yellow)',
                    fontFamily: 'monospace',
                    overflow: 'hidden',
                    textOverflow: 'ellipsis',
                    whiteSpace: 'nowrap',
                }, children: _jsx(InteractiveCode, { fmt: result.prettyLemma }) }), _jsx("style", { children: `
        @keyframes spin {
          from { transform: rotate(0deg); }
          to { transform: rotate(360deg); }
        }
      ` })] }));
}
function renderValidationState(ec, state, range, documentUri) {
    const filterResults = true; // TODO: get from context
    const successes = filterResults ? eraseEquivalentEntries(state.successes) : state.successes;
    return (_jsxs("div", { style: {
            backgroundColor: 'var(--panel-background, white)',
            border: '1px solid var(--border-default, #e1e4e8)',
            borderRadius: '6px',
            /* remove bottom padding and keep compact vertical spacing */
            padding: '10px 12px 0 12px',
            boxShadow: '0 1px 2px rgba(0,0,0,0.03)'
        }, children: [successes.length > 0 && (_jsx("div", { style: { marginBottom: '6px' }, children: successes.map((s, i) => (_jsx("div", { style: { marginBottom: '4px' }, children: renderSuccessResult(ec, s, !filterResults, range, documentUri) }, `succ-${i}`))) })), state.failures.length > 0 && (_jsxs("details", { style: { marginBottom: '8px' }, children: [_jsxs("summary", { style: {
                            padding: '6px 10px',
                            cursor: 'pointer',
                            userSelect: 'none',
                            display: 'flex',
                            alignItems: 'center',
                            gap: '6px',
                            borderRadius: '4px',
                            backgroundColor: 'var(--bg-error)',
                            marginBottom: '6px'
                        }, children: [_jsx("span", { style: { color: 'var(--accent-red)', fontSize: '16px' }, children: "\u2715" }), _jsxs("span", { style: { fontWeight: 500 }, children: ["Failures (", state.failures.length, ")"] })] }), state.failures.map((f, i) => (_jsx("div", { style: { marginBottom: '6px' }, children: renderErrorResult(f) }, `fail-${i}`)))] })), state.pending.length > 0 && (_jsxs("details", { open: true, style: { marginBottom: '8px' }, children: [_jsxs("summary", { style: {
                            padding: '6px 10px',
                            cursor: 'pointer',
                            userSelect: 'none',
                            display: 'flex',
                            alignItems: 'center',
                            gap: '6px',
                            borderRadius: '4px',
                            backgroundColor: 'var(--bg-pending)',
                            marginBottom: '6px'
                        }, children: [_jsx("span", { style: {
                                    color: 'var(--accent-yellow)',
                                    fontSize: '14px',
                                    display: 'inline-block',
                                    animation: 'spin 2s linear infinite'
                                }, children: "\u231A" }), _jsxs("span", { style: { fontWeight: 500 }, children: ["In Progress (", state.pending.length, ")"] })] }), state.pending.map((p, i) => (_jsx("div", { style: { marginBottom: '6px' }, children: renderPendingResult(p) }, `pending-${i}`)))] })), _jsx("style", { children: `
      :root {
        /* Theme-aware variables with sensible fallbacks */
        --border-default: var(--vscode-editorWidget-border, #e1e4e8);
        --panel-background: var(--vscode-editorWidget-background, white);
        --bg-success: var(--vscode-input-background, #f8fafc);
        --bg-error: var(--vscode-editorError-background, #fef2f2);
        --bg-pending: var(--vscode-editorWarning-background, #fffbeb);
        --bg-extra: var(--vscode-editorBackground, #f1f5f9);
        --accent-blue: var(--vscode-button-background, #0969da);
        --accent-blue-strong: #0860ca;
          --accent-red: var(--vscode-editorError-foreground, #dc2626);
          --error-fg: var(--vscode-editorError-foreground, var(--accent-red));
          --error-bg-subtle: var(--vscode-editorError-background, #fef2f2);
          --turnstile: var(--vscode-lean4-infoView\\.turnstile, #6b7280);
        --accent-yellow: var(--vscode-editorWarning-foreground, #ca8a04);
        --text-default: var(--vscode-editor-foreground, #1f2937);
        --text-muted: var(--vscode-descriptionForeground, #6b7280);
      }

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
        const promises = props.premises.map(async (premise) => {
            const result = await rs.call(props.validationMethod, { selectionMetadata: props.selectionMetadata, premise });
            // If a newer run started, abort processing this result
            if (r.current !== id)
                return;
            updateState(addPremiseToValidationResult(premise, result));
        });
        await Promise.all(promises);
    }
    ;
    React.useEffect(() => { e(); }, [rs, props.premises.map(p => p.name).join(",")]); // TODO: think about why this is necessary, and remove if it is not
    return (renderValidationState(ec, state, props.range, props.documentUri));
}
