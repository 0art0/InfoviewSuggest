import ProofWidgets

namespace ProofWidgets

open Lean Server
open scoped Jsx

/-- The result returned by one step of a refresh task. -/
inductive RefreshResult where
  | none
  | last (html : Html)
  | cont (html : Html) (task : Task RefreshResult)

/-- A task that can be queried by a `RefreshComponent` to refresh the display. -/
def RefreshTask := Task RefreshResult

/-- Create a `RefreshTask` from an `IO` computation. -/
def RefreshTask.ofIO (k : IO RefreshResult) : BaseIO RefreshTask :=
  BaseIO.asTask do
    return match ← k.toBaseIO with
    | .error e => .last <| .text s!"Error refreshing this component: {e.toString}"
    | .ok result => result

/-- Create a `RefreshTask` from a `CoreM` computation. -/
def RefreshTask.ofCoreM (k : CoreM RefreshResult) : CoreM RefreshTask := do
  let k := k.run' (← read) (← get)
  BaseIO.asTask do
    match ← k.toBaseIO with
    | .ok result => return result
    | .error e =>
      if let .internal id _ := e then
        if id == interruptExceptionId then
          return .last <| .text "This component was cancelled"
      return .last <|
        <span>
          Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
        </span>

/-- Create a `RefreshTask` from a `MetaM` computation. -/
def RefreshTask.ofMetaM (k : MetaM RefreshResult) : MetaM RefreshTask := do
  RefreshTask.ofCoreM <| k.run' (← read) (← get)


instance : TypeName RefreshTask := unsafe .mk RefreshTask ``RefreshTask

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure RefreshResultProps where
  /-- The new `Html` that will replace the current `Html`.
  If it is `none`, then the value of `refresh` is ignored,
  and the `RefreshComponent` stops refreshing. -/
  html : Option Html := none
  /-- The computation that computes the next refresh.
  If it is `none`, then the `RefreshComponent` stops refreshing. -/
  refresh : Option (WithRpcRef RefreshTask) := none
  deriving RpcEncodable, Inhabited

/-- `awaitRefresh` is called through RPC by `RefreshComponent` to obtain the next `Html` to display.
It uses `Task.get` to await the result, blocking the thread until the result is ready. -/
@[server_rpc_method]
partial def awaitRefresh (task : WithRpcRef RefreshTask) : RequestM (RequestTask RefreshResultProps) :=
  RequestM.asTask do
    match task.val.get with
    | .none => return {}
    | .last html => return { html }
    | .cont html task => loop html task
where
  /-- We implement the following optimization in `awaitRefresh`:
  If the next task has already finished executing, instead of returning it,
  we evaluate it, and repeat. -/
  loop (html : Html) (task : RefreshTask) : BaseIO RefreshResultProps := do
    if ← IO.hasFinished task then
      match task.get with
      | .none => return { html }
      | .last html => return { html }
      | .cont html task => loop html task
    else
      return { html, refresh := ← WithRpcRef.mk task }


deriving instance TypeName for IO.CancelToken

/-- `cancelRefresh` is called through RPC by `RefreshComponent` upon cancellation.
It sets the cancel token for the task(s) on the Lean side. -/
@[server_rpc_method]
def cancelRefresh (cancelTk : WithRpcRef IO.CancelToken) : RequestM (RequestTask String) :=
  RequestM.asTask do cancelTk.val.set; return "ok"

/-- The arguments passed to `RefreshComponent`. -/
structure RefreshComponentProps where
  /-- The initial `Html` that is displayed. Usually this is a "loading..." kind of message. -/
  initial : Html
  /-- The refresh task that is queried for updating the display. -/
  refresh : WithRpcRef RefreshTask
  /-- The cancel token that will be set when the component is unloaded/reloaded. -/
  cancelTk : Option (WithRpcRef IO.CancelToken)
  deriving RpcEncodable

/-- Display an inital `Html`, and repeatedly update the display with new `Html` objects
as they are computed by the given `RefreshTask`.

Warning: if the `RefreshComponent` doesn't have enough time to load, it might not call `cancelRefresh`.
So, it is recommended to not rely only on `cancelRefresh` for cancelling outdated refresh tasks. -/
@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / "widget" / "dist" / "tacticSuggestionPanel.js"

end ProofWidgets
