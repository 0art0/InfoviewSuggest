import ProofWidgets

namespace ProofWidgets

open ProofWidgets Lean Server Jsx

structure RefreshTask where
  go : Task (Option Html × Option RefreshTask)
deriving TypeName

structure RefreshResult where
  html : Option Html
  refresh : Option (WithRpcRef RefreshTask)
  deriving RpcEncodable

@[inline]
def RefreshTask.ofIO (k : IO (Option Html × Option RefreshTask)) : BaseIO RefreshTask :=
  (⟨·⟩) <$> BaseIO.asTask do
    match ← k.toBaseIO with
    | .error e => pure (Html.text s!"Error refreshing this component: {e.toString}", none)
    | .ok go => pure go

@[inline]
def RefreshTask.ofCoreM (k : CoreM (Option Html × Option RefreshTask)) : CoreM RefreshTask := do
  let k := k.run' (← read) (← get)
  (⟨·⟩) <$> BaseIO.asTask do
    match ← k.toBaseIO with
    | .error e => pure (some
      <span>
        Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
      </span>, none)
    | .ok go => pure go

@[inline]
def RefreshTask.ofMetaM (k : MetaM (Option Html × Option RefreshTask)) : MetaM RefreshTask := do
  RefreshTask.ofCoreM <| k.run' (← read) (← get)

@[server_rpc_method]
def runRefresh (task : WithRpcRef RefreshTask) : RequestM (RequestTask RefreshResult) :=
  RequestM.asTask do
    let (html, go) := task.val.go.get
    return { html, refresh := ← go.mapM (WithRpcRef.mk ·) }

structure RefreshComponentProps where
  initial : Html
  next : Name
  refresh : WithRpcRef RefreshTask
deriving RpcEncodable

@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / "widget" / "dist" / "tacticSuggestionPanel.js"


#eval 3

end ProofWidgets
