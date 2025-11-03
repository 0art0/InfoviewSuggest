import ProofWidgets

namespace ProofWidgets

open Lean Server
open scoped Jsx

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure RefreshStepProps where
  /-- The new `Html` that will replace the current `Html`.
  If it is `none`, then the value of `refresh` is ignored,
  and the `RefreshComponent` stops refreshing. -/
  html : Option Html := none
  /-- Whether the `RefreshComponent` should continue to refresh. -/
  refresh : Bool := false
  deriving RpcEncodable, Inhabited

inductive RefreshState where
  | result (result : RefreshStepProps)
  | inProgress
  | waiting (promise : IO.Promise RefreshStepProps)
  deriving Inhabited

def RefreshRef := IO.Ref RefreshState
instance : TypeName RefreshRef := unsafe .mk RefreshRef ``RefreshRef

/-- `awaitRefresh` is called through RPC by `RefreshComponent` to obtain the next `Html` to display.
If the result is not yet available, it creates an `IO.Promise`, and uses `Task.map` to return as soon as
the promise is resolved. -/
@[server_rpc_method]
partial def awaitRefresh (ref : WithRpcRef RefreshRef) : RequestM (RequestTask RefreshStepProps) := do
  let ref := ref.val
  match ← unsafe ref.take with
  | .result result =>
    ref.set .inProgress
    return .pure result
  | .inProgress =>
    let promise ← IO.Promise.new
    ref.set <| .waiting promise
    dbg_trace "awaiting a new promise"
    return .mapCheap (t := ⟨promise.result?⟩) fun
      | none => .ok { html := Html.text "Internal error: awaited promise was dropped" }
      | some result => .ok result
  | s@(.waiting _) =>
    ref.set s
    return .pure { html := Html.text "Internal error: tried to await a refresh that was already being awaited." }


deriving instance TypeName for IO.CancelToken

/-- `cancelRefresh` is called through RPC by `RefreshComponent` upon cancellation.
It sets the cancel token for the task(s) on the Lean side. -/
@[server_rpc_method]
def cancelRefresh (cancelTk : WithRpcRef IO.CancelToken) : RequestM (RequestTask String) :=
  RequestM.asTask do cancelTk.val.set; return "ok"


def RefreshRef.new : BaseIO RefreshRef := IO.mkRef .inProgress

abbrev RefreshT := ReaderT RefreshRef

def RefreshT.run {m α} (ref : RefreshRef) (x : RefreshT m α) : m α := x ref

inductive RefreshResult (m : Type → Type) where
  | none
  | last (html : Html)
  | cont (html : Html) (cont : RefreshT m Unit)
  deriving Inhabited

@[inline]
def refresh {m} [Monad m] [MonadLiftT BaseIO m] (k : RefreshResult m) : RefreshT m Unit := do
  let ref ← read
  match k with
  | .none => update ref {}
  | .last html => update ref { html }
  | .cont html cont => update ref { html, refresh := true }; cont
where
  update (ref : RefreshRef) (step : RefreshStepProps) : BaseIO Unit := do
    match ← unsafe ref.take with
    | .waiting promise => ref.set .inProgress; promise.resolve step
    | _ => ref.set (.result step)

def refreshM {m} [Monad m] [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m]
    (k : m (RefreshResult m)) : RefreshT m Unit := do
  have : MonadExceptOf _ m := MonadAlwaysExcept.except
  refresh <| ←
    try k
    catch e =>
      if let .internal id _ := e then
        if id == interruptExceptionId then
          return .last <| .text "This component was cancelled"
      return .last
        <span>
          Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
        </span>

/-- The arguments passed to `RefreshComponent`. -/
structure RefreshComponentProps where
  /-- The initial `Html` that is displayed. Usually this is a "loading..." kind of message. -/
  initial : Html
  /-- The refresh state that is queried for updating the display. -/
  state : WithRpcRef RefreshRef
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
