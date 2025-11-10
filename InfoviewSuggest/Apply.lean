import InfoviewSuggest.Util

namespace InfoviewSuggest
open Lean Meta RefinedDiscrTree Widget Server ProofWidgets Jsx

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
