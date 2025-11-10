import InfoviewSuggest.LibraryRewrite

namespace InfoviewSuggest
open Lean Meta RefinedDiscrTree Widget Server ProofWidgets LibraryRewrite Jsx

namespace Apply

structure ApplyLemma where
  name : Premise

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addApplyEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (ApplyLemma × List (Key × LazyEntry))) := do
  setMCtx {} -- recall that the metavariable context is not guaranteed to be empty at the start
  let (_, _, e) ← forallMetaTelescope cinfo.type
  if isBadMatch e then
    return []
  else
    return [({ name := .const name }, ← initializeLazyEntryWithEta e)]

/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
def addLocalApplyEntry (decl : LocalDecl) :
    MetaM (List (ApplyLemma × List (Key × LazyEntry))) :=
  withReducible do
  let (_, _, e) ← forallMetaTelescope decl.type
  return [(⟨.fvar decl.fvarId⟩, ← initializeLazyEntryWithEta e)]

initialize importedApplyLemmasExt : EnvExtension (IO.Ref (Option (RefinedDiscrTree ApplyLemma))) ←
  registerEnvExtension (IO.mkRef none)

/-- Get all potential apply lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded. -/
def getImportCandidates (e : Expr) : MetaM (MatchResult ApplyLemma) := do
  findImportMatches importedApplyLemmasExt addApplyEntry
    /-
    5000 constants seems to be approximately the right number of tasks
    Too many means the tasks are too long.
    Too few means less cache can be reused and more time is spent on combining different results.

    With 5000 constants per task, we set the `HashMap` capacity to 256,
    which is the largest capacity it gets to reach.
    -/
    (constantsPerTask := 5000) (capacityPerTask := 256) e

/-- Get all potential apply lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getModuleCandidates (e : Expr) : MetaM (MatchResult ApplyLemma) := do
  let moduleTreeRef ← createModuleTreeRef addApplyEntry
  findModuleMatches moduleTreeRef e

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree ApplyLemma) := do
  let mut tree : PreDiscrTree ApplyLemma := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalApplyEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis applications for `e`. Similar to `getImportCandidates`. -/
def getHypothesisCandidates (e : Expr) (except : Option FVarId) :
    MetaM (MatchResult ApplyLemma) := do
  let (candidates, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  MonadExcept.ofExcept candidates


/-! ### Checking apply lemmas -/

structure ApplicationInfo where
  numGoals : Nat
  nameLenght : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

/-- A apply lemma that has been applied to an expression. -/
structure Application extends ApplyLemma where
  /-- The proof of the application -/
  proof : Expr
  /-- The extra goals created by the application -/
  newGoals : Array (MVarId × BinderInfo)
  /-- Whether any of the new goals contain another a new metavariable -/
  makesNewMVars : Bool
  info : ApplicationInfo

/-- If `thm` can be used to apply to `e`, return the applications. -/
def checkApplication (lem : ApplyLemma) (target : Expr): MetaM (Option Application) := do
  let thm ← match lem.name with
    | .const name => mkConstWithFreshMVarLevels name
    | .fvar fvarId => pure (.fvar fvarId)
  withTraceNodeBefore `infoview_suggest (return m!"applying {thm} to {target}") do
  let (mvars, binderInfos, e) ← forallMetaTelescope (← inferType thm)
  let unifies ← withTraceNodeBefore `infoview_suggest (return m! "unifying {e} =?= {target}")
    (withReducible (isDefEq e target))
  unless unifies do return none
  try synthAppInstances `infoview_suggest default mvars binderInfos false false catch _ => return none
  let mut newGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (mvar.mvarId!, bi)

  let makesNewMVars ← newGoals.anyM fun goal => do
    let type ← instantiateMVars <| ← goal.1.getType
    return (type.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  let info := {
    numGoals := newGoals.size
    nameLenght := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr (← g.1.getType)).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM fun g => do abstractMVars (← g.1.getType)
  }
  return some { lem with proof, newGoals, makesNewMVars, info }

def ApplicationInfo.lt (a b : ApplicationInfo) : Bool :=
  Ordering.isLT <|
  (compare a.1 b.1).then <|
  (compare a.2 b.2).then <|
  (compare a.3 b.3).then <|
  (compare a.4 b.4)

def ApplicationInfo.isDuplicate (a b : ApplicationInfo) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
def tacticSyntax (app : Application) : MetaM (TSyntax `tactic) := do
  let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $proof)

/-- `ApplyResult` stores the information from an apply lemma that was successful. -/
structure ApplyResult where
  /-- `filtered` will be shown in the filtered view. -/
  filtered : Option Html
  /-- `unfiltered` will be shown in the unfiltered view. -/
  unfiltered : Html
  /-- `info` is used for sorting and comparing apply theorems. -/
  info : ApplicationInfo
  /-- The `pattern` of the first lemma in a section is shown in the header of that section. -/
  pattern : CodeWithInfos
deriving Inhabited

instance : LT ApplyResult where
  lt a b := a.info.lt b.info

instance : DecidableLT ApplyResult := fun a b => by
  dsimp [LT.lt]; infer_instance

/-- Construct the `Result` from an `Application`. -/
def Application.toResult (app : Application) (pasteInfo : PasteInfo) :
    MetaM ApplyResult := do
  let tactic ← tacticPasteString (← tacticSyntax app) pasteInfo.replaceRange
  let mut newGoals := #[]
  for (mvarId, bi) in app.newGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      newGoals := newGoals.push (← ppExprTagged (← mvarId.getType))
  let prettyLemma ← ppPremiseTagged app.name
  let html (showNames : Bool) : Html :=
    let button :=
      -- TODO: let's see if this works, and if we can add any hover information to the button.
      <span className="font-code"> {
        Html.ofComponent MakeEditLink
          (.ofReplaceRange pasteInfo.meta pasteInfo.replaceRange tactic)
            #[<a className={"link pointer mh2 dim codicon codicon-filter"}/>] }
      </span>
    let newGoals := newGoals.flatMap fun extraGoal =>
      #[<br/>, <strong className="goal-vdash">⊢ </strong>, <InteractiveCode fmt={extraGoal}/>];
    <li>
      { .element "p" #[] <|
        #[button] ++ newGoals ++
          if showNames then #[<br/>, <InteractiveCode fmt={prettyLemma}/>] else #[] }
    </li>
  let lemmaType ← match app.name with
    | .const name => (·.type) <$> getConstInfo name
    | .fvar fvarId => inferType (.fvar fvarId)
  return {
    filtered := if !app.makesNewMVars then html false else none
    unfiltered := html true
    info := app.info
    pattern := ← forallTelescope lemmaType fun _ e => ppExprTagged e
  }

/-- `generateSuggestion` is called in parallel for all apply lemmas.
- If the lemma succeeds, return a `ApplyResult`.
- If the lemma fails, return `none`
- If the attempt throws an error, return the error as `Html`.

Note: we use two `try`-`catch` clauses, because we rely on `ppConstTagged`
in the first `catch` branch, which could (in principle) throw an error again.
-/
def generateSuggestion (expr : Expr) (pasteInfo : PasteInfo) (lem : ApplyLemma) :
    MetaM <| Task (Except Html <| Option ApplyResult) := do
  BaseIO.asTask <| EIO.catchExceptions (← dropM do
    have : MonadExceptOf _ MetaM := MonadAlwaysExcept.except
    try .ok <$> withNewMCtxDepth do
      Core.checkSystem "infoview_suggest"
      let some app ← checkApplication lem expr | return none
      some <$> app.toResult pasteInfo
    catch e =>
      return .error
        <li>
          An error occurred when processing apply lemma <InteractiveCode fmt={← ppPremiseTagged lem.name}/>:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>)
    fun e =>
      return .error
        <li>
          An error occurred when pretty printing apply lemma {.text lem.1.toString}:
          <br/>
          <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
        </li>



/-- `SectionState` is the part of `WidgetState` corresponding to each section of suggestions. -/
structure SectionState where
  /-- Whether the applications are using a local hypothesis, a local theorem, or an imported theorem. -/
  kind : PremiseKind
  /-- The results of the theorems that successfully apply. -/
  results : Array ApplyResult
  /-- The computations for apply theorems that have not finished evaluating. -/
  pending : Array (Task (Except Html <| Option ApplyResult))

def updateSectionState (s : SectionState) : MetaM (Array Html × SectionState) := do
  let mut pending := #[]
  let mut results := s.results
  let mut exceptions := #[]
  for t in s.pending do
    if !(← IO.hasFinished t) then
      pending := pending.push t
    else
      match t.get with
      | .error e => exceptions := exceptions.push e
      | .ok none => pure ()
      | .ok (some result) =>
        if let some idx ← findDuplicate result results then
          if result < results[idx]! then
            results := results.modify idx ({ · with filtered := none })
            results := results.binInsert (· < ·) result
          else
            results := results.binInsert (· < ·) { result with filtered := none }
        else
          results := results.binInsert (· < ·) result
  return (exceptions, { s with pending, results })
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : ApplyResult) (results : Array ApplyResult) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      pure res.filtered.isSome <&&> res.info.isDuplicate result.info

/-- Render one section of rewrite results. -/
def renderSection (filter : Bool) (s : SectionState) : Option Html := do
  let head ← s.results[0]?
  let suffix := match s.kind with
    | .hypothesis => " (local hypotheses)"
    | .fromFile => " (lemmas from current file)"
    | .fromCache => ""
  let suffix := if s.pending.isEmpty then suffix else suffix ++ " ⏳"
  let htmls := if filter then s.results.filterMap (·.filtered) else s.results.map (·.unfiltered)
  guard (!htmls.isEmpty)
  return <details «open»={true}>
    <summary className="mv2 pointer">
      Pattern <InteractiveCode fmt={head.pattern}/> {.text suffix}
    </summary>
    {.element "ul" #[("style", json% { "padding-left" : "30px"})] htmls}
  </details>

end Apply






inductive SectionState where
  | rw (s : LibraryRewrite.SectionState)
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
      let (exs, s) ← updateSectionState s
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
    let htmls := state.sections.filterMap fun | .rw s => renderSection filter s | .apply s => Apply.renderSection filter s
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
  | rw (arr : Array RewriteLemma)
  | apply (arr : Array Apply.ApplyLemma)

private def Candidates.generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (kind : PremiseKind) :
    Candidates → MetaM SectionState
  | .rw arr => do
    let arr ← arr.mapM (LibraryRewrite.generateSuggestion expr pasteInfo)
    return .rw { kind, results := #[], pending := arr }
  | .apply arr => do
    let arr ← arr.mapM (Apply.generateSuggestion expr pasteInfo.toPasteInfo)
    return .apply { kind, results := #[], pending := arr }

def initializeWidgetState (expr : Expr) (pasteInfo : RwPasteInfo)
    (exceptFVarId : Option FVarId) : MetaM WidgetState := do
  Core.checkSystem "rw!?"
  let mut sections := #[]

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← getHypothesisCandidates expr exceptFVarId).elts.map fun _ => (·.map Candidates.rw))
    ((← Apply.getHypothesisCandidates expr exceptFVarId).elts.map fun _ => (·.map Candidates.apply))
  for (_, cand) in cand do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis)

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← getModuleCandidates expr).elts.map fun _ => (·.map Candidates.rw))
    ((← Apply.getModuleCandidates expr).elts.map fun _ => (·.map Candidates.apply))
  for (_, cand) in cand do
    for cand in cand do
      sections := sections.push (← cand.generateSuggestion expr pasteInfo .hypothesis)

  let cand := Std.TreeMap.mergeWith (fun _ a b => a ++ b)
    ((← getImportCandidates expr).elts.map fun _ => (·.map Candidates.rw))
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
  have : Inhabited (IO.Ref (Option (RefinedDiscrTree RewriteLemma))) := ⟨← IO.mkRef none⟩
  let ref := LibraryRewrite.importedRewriteLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) addRewriteEntry 5000 256
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
