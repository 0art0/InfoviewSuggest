import {
  // useRpcSession,
  Name,
  RpcPtr
} from "@leanprover/infoview";
import * as React from "react";
// import { Html } from "./htmlDisplay"
// import HtmlDisplay from "./htmlDisplay"

// import * as React from 'react';
import { DocumentPosition, EnvPosContext, RpcSessionAtPos, importWidgetModule, mapRpcError,
    useAsyncPersistent, useRpcSession } from '@leanprover/infoview';
import type { DynamicComponent } from '@leanprover/infoview';

export type Html =
    | { element: [string, [string, any][], Html[]] }
    | { text: string }
    | { component: [string, string, any, Html[]] }

/**
 * Render a HTML tree into JSX, resolving any dynamic imports corresponding to `component`s along
 * the way.
 *
 * This guarantees that the resulting React tree is exactly as written down in Lean. In particular,
 * there are no extraneous {@link DynamicComponent} nodes which works better with some libraries
 * that directly inspect the children nodes.
 */
export async function renderHtml(rs: RpcSessionAtPos, pos: DocumentPosition, html: Html):
        Promise<JSX.Element> {
    if ('text' in html) {
        return <>{html.text}</>
    } else if ('element' in html) {
        const [tag, attrsList, cs] = html.element
        const attrs: any = {}
        for (const [k,v] of attrsList) {
            attrs[k] = v
        }
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        if (tag === "hr") {
            // React is greatly concerned by <hr/>s having children.
            return <hr/>
        } else if (children.length === 0) {
            return React.createElement(tag, attrs)
        } else {
            return React.createElement(tag, attrs, children)
        }
    } else if ('component' in html) {
        const [hash, export_, props, cs] = html.component
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        const dynProps = {...props, pos}
        const mod = await importWidgetModule(rs, pos, hash)
        if (!(export_ in mod)) throw new Error(`Module '${hash}' does not export '${export_}'`)
        if (children.length === 0) {
            return React.createElement(mod[export_], dynProps)
        } else {
            return React.createElement(mod[export_], dynProps, children)
        }
    } else {
        return <span className="red">Unknown HTML variant: {JSON.stringify(html)}</span>
    }
}

function HtmlDisplay({html} : {html: Html}): JSX.Element {
    const rs = useRpcSession()
    const pos = React.useContext(EnvPosContext)!
    const state = useAsyncPersistent(() => renderHtml(rs, pos, html), [rs, pos, html])
    if (state.state === 'resolved')
        return state.value
    else if (state.state === 'rejected')
        return <span className="red">Error rendering HTML: {mapRpcError(state.error).message}</span>
    return <></>
}

export interface RefreshPanelProps {
  /** The initial HTML to display */
  initial: Html
  /** A Lean task for iteratively refreshing the HTML display */
  refresh: RpcPtr<'RefreshTask'>
  cancelTk? : RpcPtr<'IO.CancelToken'>
}

export interface RefreshResultProps {
  /** The new HTML to display */
  html? : Html
  refresh? : RpcPtr<'RefreshTask'>
}

export default function RefreshPanel(props: RefreshPanelProps): JSX.Element {
  const rs = useRpcSession()
  const [html, setHtml] = React.useState<Html>(props.initial)

  // Repeatedly call Lean to update
  React.useEffect(() => {
    // Set the html to the given initial value at the start of each re-render
    setHtml(props.initial)
    let cancelled = false
    async function loop(refresh: RpcPtr<'RefreshTask'>) {
        const result = await rs.call<RpcPtr<'RefreshTask'>, RefreshResultProps> ("ProofWidgets.awaitRefresh", refresh)
        if (cancelled) return
        if (result.html) {
            setHtml(result.html)
            if (result.refresh) loop(result.refresh)
        }
    }
    loop(props.refresh)
    return () => {
        cancelled = true
        if (props.cancelTk) {
            rs.call<RpcPtr<'IO.CancelToken'>, void> ("ProofWidgets.cancelRefresh", props.cancelTk) 
        }
    }
  }, [props])
  return <HtmlDisplay html={html}/>
}
