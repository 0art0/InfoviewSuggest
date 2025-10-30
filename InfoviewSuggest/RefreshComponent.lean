import ProofWidgets

namespace ProofWidgets

open Lean Server
open scoped Jsx

mutual

structure RefreshTask where
  task : Task RefreshResult
  deriving TypeName

inductive RefreshResult where
  | none
  | last (html : Html)
  | cont (html : Html) (task : RefreshTask)

end

structure RefreshResultProps where
  html : Option Html := none
  refresh : Option (WithRpcRef RefreshTask) := none
  deriving RpcEncodable, Inhabited

deriving instance TypeName for IO.CancelToken

structure RefreshComponentProps where
  initial : Html
  refresh : WithRpcRef RefreshTask
  cancelTk : Option (WithRpcRef IO.CancelToken)
  deriving RpcEncodable


@[inline]
def RefreshTask.ofIO (k : IO RefreshResult) : BaseIO RefreshTask :=
  (⟨·⟩) <$> BaseIO.asTask do
    return match ← k.toBaseIO with
    | .error e => .last <| .text s!"Error refreshing this component: {e.toString}"
    | .ok result => result

@[inline]
def RefreshTask.ofCoreM (k : CoreM RefreshResult) : CoreM RefreshTask := do
  let k := k.run' (← read) (← get)
  (⟨·⟩) <$> BaseIO.asTask do
    match ← k.toBaseIO with
    | .error e =>
      if let .internal id _ := e then
        if id == interruptExceptionId then
          return .last <| .text "This component was cancelled"
      return .last <|
        <span>
          Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
        </span>
    | .ok result => return result

@[inline]
def RefreshTask.ofMetaM (k : MetaM RefreshResult) : MetaM RefreshTask := do
  RefreshTask.ofCoreM <| k.run' (← read) (← get)

/-- `awaitRefresh` is called through RPC by the `RefreshComponent` to obtain the next `Html` from Lean.
`awaitRefresh` uses `Task.get` to await the result, blocking the thread until the result is ready. -/
@[server_rpc_method]
partial def awaitRefresh (task : WithRpcRef RefreshTask) : RequestM (RequestTask RefreshResultProps) :=
  RequestM.asTask do
    match task.val.task.get with
    | .none => return {}
    | .last html => return { html }
    | .cont html task => loop html task
where
  /-- We implement the following optimization in `awaitRefresh`:
  If the next task has already finished executing, instead of returning it,
  we evaluate it, and repeat. -/
  loop (html : Html) (task : RefreshTask) : BaseIO RefreshResultProps := do
    if ← IO.hasFinished task.task then
      match task.task.get with
      | .none => return { html }
      | .last html => return { html }
      | .cont html task => loop html task
    else
      return { html, refresh := ← WithRpcRef.mk task }

/-- `cancelRefresh` is called through RPC by the `RefreshComponent` upon cancellation.
It sets the cancel token for the task(s) on the Lean side.

Warning: when the `RefreshComponent` doesn't have enough time to load,
it might not actually call `cancelRefresh`. -/
@[server_rpc_method]
def cancelRefresh (cancelTk : WithRpcRef IO.CancelToken) : RequestM (RequestTask String) :=
  RequestM.asTask do cancelTk.val.set; return "ok"


@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / "widget" / "dist" / "tacticSuggestionPanel.js"

end ProofWidgets
