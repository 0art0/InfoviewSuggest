import InfoviewSuggest.Apply
import InfoviewSuggest.LibraryRewrite

namespace InfoviewSuggest
open Lean Meta Server Widget ProofWidgets Jsx


inductive SectionState where
  | rw (s : Rw.SectionState)
  | apply (s : Apply.SectionState)

def SectionState.isFinished : SectionState → Bool
  | .rw s => s.pending.isEmpty
  | .apply s => s.pending.isEmpty

def SectionState.hasProgressed : SectionState → BaseIO Bool
  | .rw s => s.pending.anyM IO.hasFinished
  | .apply s => s.pending.anyM IO.hasFinished

/-- While the suggestions are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionState`. -/
structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionState
  /-- The errors that appeared in evaluating . -/
  exceptions : Array Html
  /-- The HTML shown at the top of the suggestions. -/
  header : Html

/-- Look a all of the pending `Task`s and if any of them gave a result, add this to the state. -/
def updateWidgetState (state : WidgetState) : MetaM WidgetState := do
  let mut sections := #[]
  let mut exceptions := state.exceptions
  for s in state.sections do
    match s with
    | .rw s =>
      let (exs, s) ← Rw.updateSectionState s
      sections := sections.push <| .rw s
      exceptions := exceptions ++ exs
    | .apply s =>
      let (exs, s) ← Apply.updateSectionState s
      sections := sections.push <| .apply s
      exceptions := exceptions ++ exs
  return { state with sections, exceptions }

def renderWidget (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) : Html :=
  <FilterDetails
    summary={state.header}
    all={render false state unfolds? rewriteTarget}
    filtered={render true state unfolds? rewriteTarget}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of rewrite results -/
  render (filter : Bool) (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) : Html :=
    let htmls := state.sections.filterMap fun
      | .rw s => Rw.renderSection filter s
      | .apply s => Apply.renderSection filter s
    let htmls := match unfolds? with
      | some html => #[html] ++ htmls
      | none => htmls
    let htmls := match renderExceptions state.exceptions with
      | some html => htmls.push html
      | none => htmls
    if htmls.isEmpty then
      <p> No rewrites found for <InteractiveCode fmt={rewriteTarget}/> </p>
    else
      .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls

  /-- Render the error messages -/
  renderExceptions (exceptions : Array Html) : Option Html := do
    if exceptions.isEmpty then none else
    some <|
      <details «open»={true}>
        <summary className="mv2 pointer">
          <span «class»="error"> Error messages: </span>
        </summary>
        {Html.element "ul" #[("style", json% { "padding-left" : "30px"})] exceptions}
      </details>


private inductive Candidates where
  | rw (arr : Array Rw.RewriteLemma)
  | apply (arr : Array Apply.ApplyLemma)

private def Candidates.generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (kind : PremiseKind) :
    Candidates → MetaM SectionState
  | .rw arr => do
    let arr ← arr.mapM (Rw.generateSuggestion expr pasteInfo)
    return .rw { kind, results := #[], pending := arr }
  | .apply arr => do
    let arr ← arr.mapM (Apply.generateSuggestion expr pasteInfo.toPasteInfo)
    return .apply { kind, results := #[], pending := arr }

def initializeWidgetState (expr : Expr) (pasteInfo : RwPasteInfo)
    (exceptFVarId : Option FVarId) : MetaM WidgetState := do
  Core.checkSystem "rw!?"
  let mut sections := #[]

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← Rw.getHypothesisCandidates expr exceptFVarId).elts.map fun _ => (·.map Candidates.rw))
    ((← Apply.getHypothesisCandidates expr exceptFVarId).elts.map fun _ => (·.map Candidates.apply))
  for (_, cand) in cand do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis)

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← Rw.getModuleCandidates expr).elts.map fun _ => (·.map Candidates.rw))
    ((← Apply.getModuleCandidates expr).elts.map fun _ => (·.map Candidates.apply))
  for (_, cand) in cand do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis)

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← Rw.getImportCandidates expr).elts.map fun _ => (·.map Candidates.rw))
    ((← Apply.getImportCandidates expr).elts.map fun _ => (·.map Candidates.apply))
  for (_, cand) in cand do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis)

  return {
    sections, exceptions := #[]
    header := <span> Rewrite suggestions for <InteractiveCode fmt={← ppExprTagged expr}/>: </span> }


/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
partial def waitAndUpdate (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) :
    MetaM (RefreshComponent.RefreshStep MetaM) := do
  -- If there is nothing to compute, return the final (empty) display
  if state.sections.all (·.isFinished) then
    return .last (renderWidget state unfolds? rewriteTarget)
  loop state
where
  loop (state : WidgetState) : MetaM (RefreshComponent.RefreshStep MetaM) := do
    Core.checkSystem "rw!?"
    -- Wait until some task has finished
    while !(← liftM <| state.sections.anyM (·.hasProgressed)) do
      IO.sleep 10
      Core.checkSystem "rw!?"
    let state ← updateWidgetState state
    if state.sections.all (·.isFinished) then
      return .last (renderWidget state unfolds? rewriteTarget)
    else
      return .cont (renderWidget state unfolds? rewriteTarget) (loop state)

structure TacticInsertionProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
deriving RpcEncodable

def suggestionWidget (props : TacticInsertionProps) (loc : SubExpr.GoalsLocation) : RequestM Html := do
  let doc ← RequestM.readDoc
  if loc.loc matches .hypValue .. then
    return .text "rw!?: cannot rewrite in the value of a let variable."
  let some goal := props.goals[0]? | return .text "rw!?: there is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    -- TODO: if the user select some other goal, then use the `on_goal n =>` tactic to rewrite there.
    return .text "rw!?: the selected expression should be in the main goal."
  mkGoalRefreshComponent goal (.text "rw!? is searching for rewrite lemmas...") do
    let rootExpr ← loc.rootExpr
    -- TODO: instead of rejecting terms with bound variables, and rejecting terms with a bad motive,
    -- use `simp_rw` as the suggested tactic instead of `rw`.
    -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
    -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
    let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr rootExpr loc.pos |
      return .last <| .text "rw!?: expressions with bound variables are not yet supported"
    unless ← kabstractIsTypeCorrect rootExpr subExpr loc.pos do
      return .last <| .text "rw!?: the selected expression cannot be rewritten, \
        because the motive is not type correct. \
        This usually occurs when trying to rewrite a term that appears as a dependent argument."
    let location ← loc.fvarId?.mapM FVarId.getUserName
    let pasteInfo := { «meta» := doc.meta, replaceRange := props.replaceRange, occ, hyp? := location }
    let state ← initializeWidgetState subExpr pasteInfo loc.fvarId?
    -- Computing the unfold is cheap enough that it doesn't need a separate thread.
    -- However, we do this after the parallel computations have already been spawned by `initializeWidgetState`.
    let unfolds? ← InteractiveUnfold.renderUnfolds subExpr occ location pasteInfo.toPasteInfo
    waitAndUpdate state unfolds? (← ppExprTagged subExpr)

@[server_rpc_method]
private def tacticRpc (props : TacticInsertionProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let some loc := props.selectedLocations.back? |
    return .text "rw!?: Please shift-click an expression you would like to rewrite."
  suggestionWidget props loc

/-- The component called by the `rw!?` tactic -/
@[widget_module]
def LibraryRewriteComponent : Component TacticInsertionProps :=
  mk_rpc_widget% tacticRpc

@[server_rpc_method]
private def commandRpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let some loc := props.selectedLocations.back? |
    return .text ""
  suggestionWidget { props with replaceRange := ⟨props.pos, props.pos⟩ } loc

/-- The component called by the `rw!?` tactic -/
@[widget_module]
def InfoviewSuggestComponent : Component PanelWidgetProps :=
  mk_rpc_widget% commandRpc

/--
`rw!?` is an interactive tactic that suggests rewrites for any expression selected by the user.
To use it, shift-click an expression in the goal or a hypothesis that you want to rewrite.
Clicking on one of the rewrite suggestions will paste the relevant rewrite tactic into the editor.

The rewrite suggestions are grouped and sorted by the pattern that the rewrite lemmas match with.
Rewrites that don't change the goal and rewrites that create the same goal as another rewrite
are filtered out, as well as rewrites that have new metavariables in the replacement expression.
To see all suggestions, click on the filter button (▼) in the top right.
-/
elab stx:"rw!?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewriteComponent.javascript)
    (pure <| json% { replaceRange: $replaceRange }) stx

private def withTreeCtx (ctx : Core.Context) : Core.Context :=
  { ctx with maxHeartbeats := 0, diag := getDiag ctx.options }

open Mathlib Tactic RefinedDiscrTree Lean
elab "#infoview_suggest" : command => do
  have : Inhabited (IO.Ref (Option (RefinedDiscrTree Rw.RewriteLemma))) := ⟨← IO.mkRef none⟩
  let ref := Rw.importedRewriteLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) Rw.addRewriteEntry 5000 256
    ref.set tree
  have : Inhabited (IO.Ref (Option (RefinedDiscrTree Apply.ApplyLemma))) := ⟨← IO.mkRef none⟩
  let ref := Apply.importedApplyLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) Apply.addApplyEntry 5000 256
    ref.set tree
  Elab.Command.elabCommand <| ← `(show_panel_widgets [InfoviewSuggestComponent])
