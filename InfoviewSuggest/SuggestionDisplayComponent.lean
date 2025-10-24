import ProofWidgets

open Lean Elab Meta ProofWidgets Widget Server

structure TacticSuggestionPanelProps (α β : Type) [instRpcEncodableα : RpcEncodable α] [instTypeNameβ : TypeName β] where
  /-- `selectionMetadata` contains the information needed to process a single `premise`,
  for example, it might contain an `ExprWithInfo` describing the rewrite target. -/
  selectionMetadata : WithRpcRef β
  premises : Array α
  /-- `validationMethod` should be a function tagged with `@[server_rpc_method]`
  of type `β × α → RequestM (RequestTask PremiseValidationResult)`-/
  validationMethod : Name
  range : Lsp.Range
  documentUri : Lsp.DocumentUri
deriving RpcEncodable

structure ValidationSuccessResult where
  tactic : String
  -- TODO: for an `apply?` tactic, we don't have a `replacementText`. Possible solutions:
  -- 1. make this an `Option CodeWithInfos`
  -- 2. make a single `CodeWIthInfos`/`Html` for `replacementText` and `extraGoals`
  replacementText : CodeWithInfos
  extraGoals : Array CodeWithInfos
  prettyLemma : CodeWithInfos
  inFilteredView : Bool
deriving RpcEncodable

structure ValidationErrorResult where
  error : WithRpcRef MessageData
  prettyLemma : CodeWithInfos
deriving RpcEncodable

inductive PremiseValidationResult
  | success (result : ValidationSuccessResult)
  | error (result : ValidationErrorResult)

open Json in
instance : RpcEncodable PremiseValidationResult where
  rpcEncode
    | .success result =>
      return json% {kind: "success", result: $(← rpcEncode result) }
    | .error result   =>
      return json% {kind: "error", result: $(← rpcEncode result) }
  rpcDecode j := ExceptT.run do
    match (← j.getObjVal? "kind") with
    | "success" => .success <$> rpcDecode (← j.getObjVal? "result")
    | "error"   => .error <$> rpcDecode (← j.getObjVal? "result")
    | kind      => throw <| s!"Unknown `PremiseValidationResult` kind: {kind}"

def TacticSuggestionPanel (α β : Type) [instRpcEncodableα : RpcEncodable α] [instTypeNameβ : TypeName β] : Component (TacticSuggestionPanelProps α β) where
  javascript := include_str ".." / "widget" / "dist" / "tacticSuggestionPanel.js"
