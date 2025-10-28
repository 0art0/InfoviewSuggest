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
  deriving RpcEncodable

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
    | .error e => return .last <|
      <span>
        Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
      </span>
    | .ok result => return result

@[inline]
def RefreshTask.ofMetaM (k : MetaM RefreshResult) : MetaM RefreshTask := do
  RefreshTask.ofCoreM <| k.run' (← read) (← get)


@[server_rpc_method]
def awaitRefresh (task : WithRpcRef RefreshTask) : RequestM (RequestTask RefreshResultProps) :=
  RequestM.asTask do
    match task.val.task.get with
    | .none => return {}
    | .last html => return { html }
    | .cont html task => return { html, refresh := ← WithRpcRef.mk task}

@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / "widget" / "dist" / "tacticSuggestionPanel.js"

end ProofWidgets
