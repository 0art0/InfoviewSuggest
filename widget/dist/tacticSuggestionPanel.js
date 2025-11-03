import { Fragment as _Fragment, jsx as _jsx, jsxs as _jsxs } from "react/jsx-runtime";
import * as React from "react";
// import { Html } from "./htmlDisplay"
// import HtmlDisplay from "./htmlDisplay"
// import * as React from 'react';
import { EnvPosContext, importWidgetModule, mapRpcError, useAsyncPersistent, useRpcSession } from '@leanprover/infoview';
/**
 * Render a HTML tree into JSX, resolving any dynamic imports corresponding to `component`s along
 * the way.
 *
 * This guarantees that the resulting React tree is exactly as written down in Lean. In particular,
 * there are no extraneous {@link DynamicComponent} nodes which works better with some libraries
 * that directly inspect the children nodes.
 */
export async function renderHtml(rs, pos, html) {
    if ('text' in html) {
        return _jsx(_Fragment, { children: html.text });
    }
    else if ('element' in html) {
        const [tag, attrsList, cs] = html.element;
        const attrs = {};
        for (const [k, v] of attrsList) {
            attrs[k] = v;
        }
        const children = await Promise.all(cs.map(async (html) => await renderHtml(rs, pos, html)));
        if (tag === "hr") {
            // React is greatly concerned by <hr/>s having children.
            return _jsx("hr", {});
        }
        else if (children.length === 0) {
            return React.createElement(tag, attrs);
        }
        else {
            return React.createElement(tag, attrs, children);
        }
    }
    else if ('component' in html) {
        const [hash, export_, props, cs] = html.component;
        const children = await Promise.all(cs.map(async (html) => await renderHtml(rs, pos, html)));
        const dynProps = { ...props, pos };
        const mod = await importWidgetModule(rs, pos, hash);
        if (!(export_ in mod))
            throw new Error(`Module '${hash}' does not export '${export_}'`);
        if (children.length === 0) {
            return React.createElement(mod[export_], dynProps);
        }
        else {
            return React.createElement(mod[export_], dynProps, children);
        }
    }
    else {
        return _jsxs("span", { className: "red", children: ["Unknown HTML variant: ", JSON.stringify(html)] });
    }
}
function HtmlDisplay({ html }) {
    const rs = useRpcSession();
    const pos = React.useContext(EnvPosContext);
    const state = useAsyncPersistent(() => renderHtml(rs, pos, html), [rs, pos, html]);
    if (state.state === 'resolved')
        return state.value;
    else if (state.state === 'rejected')
        return _jsxs("span", { className: "red", children: ["Error rendering HTML: ", mapRpcError(state.error).message] });
    return _jsx(_Fragment, {});
}
export default function RefreshComponent(props) {
    const rs = useRpcSession();
    const [html, setHtml] = React.useState(props.initial);
    // Repeatedly call Lean to update
    React.useEffect(() => {
        // Set the html to the initial value at the start of each re-render
        setHtml(props.initial);
        let cancelled = false;
        async function loop() {
            const result = await rs.call("ProofWidgets.awaitRefresh", props.state);
            if (cancelled)
                return;
            if (result.html) {
                setHtml(result.html);
                if (result.refresh)
                    loop();
            }
        }
        loop();
        return () => {
            cancelled = true;
            if (props.cancelTk) {
                rs.call("ProofWidgets.cancelRefresh", props.cancelTk);
            }
        };
    }, [props]);
    return _jsx(HtmlDisplay, { html: html });
}
