/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.Widget.InteractiveUnfold
import InfoviewSuggest.RefreshComponent

/-!
# Point & click library rewriting

This file defines `rw!?`, an interactive tactic that suggests rewrites for any expression selected
by the user.

`rw!?` uses a (lazy) `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas.
It excludes lemmas that are automatically generated.
Each lemma is then checked one by one to see whether it is applicable.
For each lemma that works, the corresponding rewrite tactic is constructed
and converted into a `String` that fits inside mathlib's 100 column limit,
so that it can be pasted into the editor when selected by the user.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections. The sections are ordered by this score.
Within each section, the lemmas are sorted by
- rewrites with fewer extra goals come first
- left-to-right rewrites come first
- shorter lemma names come first
- shorter replacement expressions come first (when taken as a string)
- alphabetically ordered by lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

## TODO

Ways to improve `rw!?`:
- Improve the logic around `nth_rw` and occurrences,
  and about when to pass explicit arguments to the rewrite lemma.
  For example, we could only pass explicit arguments if that avoids using `nth_rw`.
  Performance may be a limiting factor for this.
  Currently, the occurrence is computed by `viewKAbstractSubExpr`.
- Modify the interface to allow creating a whole `rw [.., ..]` chain, without having to go into
  the editor in between. For this to work, we will need a more general syntax,
  something like `rw [..]??`, which would be pasted into the editor.
- We could look for rewrites of partial applications of the selected expression.
  For example, when clicking on `(f + g) x`, there should still be an `add_comm` suggestion.

Ways to extend `rw!?`:
- Support generalized rewriting (`grw`)
- Integrate rewrite search with the `calc?` widget so that a `calc` block can be created using
  just point & click.

-/

/-! ### Caching -/

namespace InfoviewSuggest.LibraryRewrite

open Lean Meta RefinedDiscrTree Mathlib.Tactic

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
deriving BEq, Inhabited, ToJson, FromJson

structure RewriteLemmaWithDisplay extends RewriteLemma where
  prettyLemma : Widget.CodeWithInfos
deriving Server.RpcEncodable

instance : ToFormat RewriteLemma where
  format lem := f! "{if lem.symm then "← " else ""}{lem.name}"

/-- Return `true` if `s` and `t` are equal up to changing the `MVarId`s. -/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some swaps
    | .sort _           , .sort _            => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some swaps
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
          some <| (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _                 , _                  => none
  else
    guard (t == s); some swaps

/-- Extract the left and right hand sides of an equality or iff statement. -/
@[inline] def eqOrIff? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (RewriteLemma × List (Key × LazyEntry))) := do
  -- we start with a fast-failing check to see if the lemma has the right shape
  let .const head _ := cinfo.type.getForallBody.getAppFn | return []
  unless head == ``Eq || head == ``Iff do return []
  setMCtx {} -- recall that the metavariable context is not guaranteed to be empty at the start
  let (_, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := eqOrIff? eqn | return []
  let badMatch e :=
    e.getAppFn.isMVar ||
    -- this extra check excludes general equality lemmas that apply at any equality
    -- these are almost never useful, and there are very many of them.
    e.eq?.any fun (α, l, r) =>
      α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r
  if badMatch lhs then
    if badMatch rhs then
      return []
    else
      return [({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]
  else
    let result := ({ name, symm := false }, ← initializeLazyEntryWithEta lhs)
    if badMatch rhs || isMVarSwap lhs rhs then
      return [result]
    else
      return [result, ({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]


/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
def addLocalRewriteEntry (decl : LocalDecl) :
    MetaM (List ((FVarId × Bool) × List (Key × LazyEntry))) :=
  withReducible do
  let (_, _, eqn) ← forallMetaTelescope decl.type
  let some (lhs, rhs) := eqOrIff? eqn | return []
  let result := ((decl.fvarId, false), ← initializeLazyEntryWithEta lhs)
  return [result, ((decl.fvarId, true), ← initializeLazyEntryWithEta rhs)]

private abbrev ExtState := IO.Ref (Option (RefinedDiscrTree RewriteLemma))

private initialize ExtState.default : ExtState ←
  IO.mkRef none

private instance : Inhabited ExtState where
  default := ExtState.default

private initialize importedRewriteLemmasExt : EnvExtension ExtState ←
  registerEnvExtension (IO.mkRef none)



/-! ### Computing the Rewrites -/

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded. -/
def getImportCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let matchResult ← findImportMatches importedRewriteLemmasExt addRewriteEntry
    /-
    5000 constants seems to be approximately the right number of tasks
    Too many means the tasks are too long.
    Too few means less cache can be reused and more time is spent on combining different results.

    With 5000 constants per task, we set the `HashMap` capacity to 256,
    which is the largest capacity it gets to reach.
    -/
    (constantsPerTask := 5000) (capacityPerTask := 256) e
  return matchResult.flatten

/-- Get all potential rewrite lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getModuleCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let moduleTreeRef ← createModuleTreeRef addRewriteEntry
  let matchResult ← findModuleMatches moduleTreeRef e
  return matchResult.flatten


/-- A rewrite lemma that has been applied to an expression. -/
structure Rewrite where
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)
  /-- Whether the rewrite introduces a new metavariable in the replacement expression -/
  makesNewMVars : Bool
  /-- Whether the rewrite is reflexive -/
  isRefl : Bool

/-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
def getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType.isForall do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push bi
  return result

/-- Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal. -/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      isDefEq tArgs[i]! sArgs[i]!

/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
def checkRewrite (thm e : Expr) (symm : Bool) : MetaM (Option Rewrite) := do
  withTraceNodeBefore `rw!? (return m!
    "rewriting {e} by {if symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := eqOrIff? eqn | return none
  let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
  let unifies ← withTraceNodeBefore `rw!? (return m! "unifying {e} =?= {lhs}")
    (withReducible (isDefEq lhs e))
  unless unifies do return none
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  try synthAppInstances `rw!? default mvars binderInfos false false catch _ => return none
  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars := (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  let isRefl ← isExplicitEq e replacement
  return some { symm, proof, replacement, extraGoals, makesNewMVars, isRefl }

initialize
  registerTraceClass `rw!?

structure RewriteInfo where
  numGoals : Nat
  symm : Bool
  nameLenght : Nat
  replacementSize : Nat
  name : Name
  replacement : AbstractMVarsResult
deriving Inhabited

def RewriteInfo.lt (a b : RewriteInfo) : Bool :=
  Ordering.isLT <|
  (compare a.1 b.1).then <|
  (compare a.2 b.2).then <|
  (compare a.3 b.3).then <|
  (compare a.4 b.4).then <|
  (a.5.cmp b.5)

def RewriteInfo.isDuplicate (a b : RewriteInfo) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

def Rewrite.toInfo (rw : Rewrite) (name : Name) : MetaM RewriteInfo := do
  return {
    numGoals := rw.extraGoals.size
    symm := rw.symm
    nameLenght := name.toString.length
    replacementSize := (← ppExpr rw.replacement).pretty.length
    name
    replacement := ← abstractMVars rw.replacement
  }

/-! ### Rewriting by hypotheses -/

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree (FVarId × Bool)) := do
  let mut tree : PreDiscrTree (FVarId × Bool) := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalRewriteEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getImportRewrites`. -/
def getHypothesisCandidates (e : Expr) (except : Option FVarId) :
    MetaM (Array (Array (FVarId × Bool))) := do
  let (candidates, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  return (← MonadExcept.ofExcept candidates).flatten


/-! ### User interface -/

open Widget ProofWidgets Jsx Server

/-- The information required for pasting a suggestion into the editor -/
structure PasteInfo where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  range : Lsp.Range

/-- The information required for constructing the rewrite tactic syntax that will be
pasted into the editor. -/
structure RwPasteInfo extends PasteInfo where
  /-- The occurence at which to rewrite, to be used as `nth_rw n` -/
  occ : Option Nat
  /-- The hypothesis at which to rewrite, to be used as `at h` -/
  hyp? : Option Name

/-- Return the rewrite tactic that performs the rewrite. -/
def tacticSyntax (rw : Rewrite) (pasteInfo : RwPasteInfo) :
    MetaM (TSyntax `tactic) := withoutModifyingMCtx do
  -- we want the new metavariables to be printed as `?_` in the tactic syntax
  for (mvarId, _) in rw.extraGoals do mvarId.setTag .anonymous
  let proof ← withOptions (pp.mvars.anonymous.set · false) (PrettyPrinter.delab rw.proof)
  mkRewrite pasteInfo.occ rw.symm proof pasteInfo.hyp?

/-- The kind of rewrite -/
inductive Kind where
  /-- A rewrite with a local hypothesis -/
  | hypothesis
  /-- A rewrite with a lemma from the current file -/
  | fromFile
  /-- A rewrite with a lemma from an imported file -/
  | fromCache

/-- Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results. -/
def pattern (type : Expr) (symm : Bool) : MetaM CodeWithInfos := do
  forallTelescope type fun _ e => do
    let some (lhs, rhs) := eqOrIff? e | throwError "Expected equation, not {indentExpr e}"
    ppExprTagged <| if symm then rhs else lhs

structure Result where
  filtered : Option Html
  unfiltered : Html
  info : RewriteInfo
  pattern : CodeWithInfos
deriving Inhabited

/-- Pretty print the given constant, making sure not to print the `@` symbol. -/
def ppConstTagged (name : Name) : MetaM CodeWithInfos := do
  return match ← ppExprTagged (← mkConstWithLevelParams name) with
    | .tag tag _ => .tag tag (.text s!"{name}")
    | code => code

/-- Construct the `Result` from a `Rewrite`. -/
def Rewrite.toResult (rw : Rewrite) (name : Name ⊕ FVarId) (pasteInfo : RwPasteInfo) : MetaM Result := do
  let tactic ← tacticPasteString (← tacticSyntax rw pasteInfo) pasteInfo.range
  let replacementString := Format.pretty (← ppExpr rw.replacement)
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    if bi.isExplicit then
      extraGoals := extraGoals.push (← ppExprTagged (← mvarId.getType))
  let prettyLemma ← match name with
    | .inl name => ppConstTagged name
    | .inr fvarId => ppExprTagged (.fvar fvarId)
  let html (showNames : Bool) : Html :=
    let button :=
      <span className="font-code"> {
        Html.ofComponent MakeEditLink
          (.ofReplaceRange pasteInfo.meta pasteInfo.range tactic)
          #[.text replacementString] }
      </span>
    let extraGoals := extraGoals.flatMap fun extraGoal =>
      #[<br/>, <strong className="goal-vdash">⊢ </strong>, <InteractiveCode fmt={extraGoal}/>];
    <li>
      { .element "p" #[] <|
        #[button] ++ extraGoals ++
          if showNames then #[<br/>, <InteractiveCode fmt={prettyLemma}/>] else #[] }
    </li>
  let lemmaType ← match name with
    | .inl name => (return (← getConstInfo name).type)
    | .inr fvarId => inferType (.fvar fvarId)
  return {
    filtered := if !rw.isRefl && !rw.makesNewMVars then html false else none
    unfiltered := html true
    info := ← rw.toInfo (match name with | .inl name => name | .inr fvarId => fvarId.name)
    pattern := ← pattern lemmaType rw.symm
  }

/-- Helper function to generate a `Task` from a `CoreM` function. -/
def CoreM.asTask {α} (k : CoreM α) (e : IO.Error → BaseIO α) : CoreM (Task α) := do
  BaseIO.asTask <| EIO.catchExceptions ((·.1) <$> k.toIO (← read) (← get)) e

/-- Helper function to generate a `Task` from a `MetaM` function. -/
def MetaM.asTask {α} (k : MetaM α) (e : IO.Error → BaseIO α) : MetaM (Task α) := do
  CoreM.asTask (k.run' (← read) (← get)) e

/-- `generateSuggestion` will be called for different theorems `lem` in parallel. -/
def generateSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (lem : RewriteLemma) :
    MetaM <| Task (Except Html <| Option Result) :=
  MetaM.asTask (
    tryCatchRuntimeEx (.ok <$>
      withNewMCtxDepth do
        let thm ← mkConstWithFreshMVarLevels lem.name
        let some rewrite ← checkRewrite thm expr lem.symm | return none
        some <$> rewrite.toResult (.inl lem.name) pasteInfo)
      fun e => do
        return .error
          <li>
            An error occurred when processing theorem
            <InteractiveCode fmt={← ppConstTagged lem.name}/>:
            <br/>
            <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
          </li>)
    fun e =>
      return .error
        <li>
          An error occurred when processing hypothesis
          {.text lem.1.toString}:
          <br/>
          {.text e.toString}
        </li>

/-- The same as `generateSuggestion`, but for local hypotheses. -/
def generateLocalSuggestion (expr : Expr) (pasteInfo : RwPasteInfo) (lem : FVarId × Bool) :
    MetaM <| Task (Except Html <| Option Result) :=
  MetaM.asTask (
    tryCatchRuntimeEx (.ok <$>
      withNewMCtxDepth do
        let some rewrite ← checkRewrite (.fvar lem.1) expr lem.2 | return none
        some <$> rewrite.toResult (.inr lem.1) pasteInfo)
      fun e => do
        return .error
          <li>
            An error occurred when processing hypothesis
            <InteractiveCode fmt={← ppExprTagged (.fvar lem.1)}/>:
            <br/>
            <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData} />
          </li>)
    fun e =>
      return .error
        <li>
          An error occurred when processing hypothesis
          {.text lem.1.name.toString}:
          <br/>
          {.text e.toString}
        </li>

/-- `SectionState` is the part of `WidgetState` corresponding to each section of suggestions. -/
structure SectionState where
  /-- Whether the rewrites are using a local hypothesis, a local theorem, or an imported theorem. -/
  kind : Kind
  /-- The results of the theorems that successfully rewrite. -/
  results : Array Result
  /-- The computations for rewrite theorems that have not finished evaluating. -/
  pending : Array (Task (Except Html <| Option Result))

/-- When the rewrite results are computed, `WidgetState` is used to keep track of the progress.
Initially, it contains a bunch of unfinished `Task`s, and with each round of `updateWidgetState`,
the finished tasks are stored as results in each `SectionState`. -/
structure WidgetState where
  /-- The states of the sections in the widget. -/
  sections : Array SectionState
  /-- The errors that appeared in evaluating . -/
  exceptions : Array Html



def initializeWidgetState (expr : Expr) (pasteInfo : RwPasteInfo)
    (exceptFVarId : Option FVarId) : MetaM WidgetState := do
  Core.checkInterrupted
  let mut sections := #[]

  for candidates in ← getHypothesisCandidates expr exceptFVarId do
    let pending ← candidates.mapM (generateLocalSuggestion expr pasteInfo)
    sections := sections.push { kind := .hypothesis, results := #[], pending }

  for candidates in ← getModuleCandidates expr do
    let pending ← candidates.mapM (generateSuggestion expr pasteInfo)
    sections := sections.push { kind := .fromFile, results := #[], pending }

  for candidates in ← getImportCandidates expr do
    let pending ← candidates.mapM (generateSuggestion expr pasteInfo)
    sections := sections.push { kind := .fromCache, results := #[], pending }

  return { sections, exceptions := #[] }

/-- Look a all of the pending `Task`s and if any of them gave a result, add this to the state. -/
def updateWidgetState (state : WidgetState) : StateRefT Bool MetaM WidgetState := do
  unless ← liftM <| state.sections.anyM (·.pending.anyM IO.hasFinished) do
    return state
  let mut sections := #[]
  let mut exceptions := state.exceptions
  for s in state.sections do
    let mut remaining := #[]
    let mut results := s.results
    for t in s.pending do
      if !(← IO.hasFinished t) then
        remaining := remaining.push t
      else
        match t.get with
        | .error e => exceptions := exceptions.push e
        | .ok none => pure ()
        | .ok (some result) =>
          set true
          if let some idx ← findDuplicate result results then
            if result.info.lt results[idx]!.info then
              results := results.modify idx ({ · with filtered := none })
              results := results.binInsert (lt := (·.info.lt ·.info)) result
            else
              results := results.binInsert (lt := (·.info.lt ·.info)) { result with filtered := none }
          else
            results := results.binInsert (lt := (·.info.lt ·.info)) result
    sections := sections.push { s with
      pending := remaining
      results := results.insertionSort (lt := (·.info.lt ·.info))
    }
  return { sections, exceptions }
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : Result) (results : Array Result) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      pure res.filtered.isSome <&&> res.info.isDuplicate result.info

def renderWidget (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) : IO Html := do
  return <FilterDetails
    -- TODO: actually say what expression these suggestions are for
    summary={.text "Rewrite suggestions:"}
    all={← render false state unfolds? rewriteTarget}
    filtered={← render true state unfolds? rewriteTarget}
    initiallyFiltered={true} />
where
  /-- Render all of the sections of rewrite results -/
  render (filter : Bool) (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) : IO Html := do
    let htmls := state.sections.filterMap (renderSection filter)
    let htmls := match unfolds? with
      | some html => #[html] ++ htmls
      | none => htmls
    let htmls := match renderExceptions state.exceptions with
      | some html => htmls.push html
      | none => htmls
    if htmls.isEmpty then
      return <p> No rewrites found for <InteractiveCode fmt={rewriteTarget}/> </p>
    else
      return .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls

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

  /-- Render one section of rewrite results. -/
  renderSection (filter : Bool) (s : SectionState) : Option Html := do
    let head ← s.results[0]?
    let suffix := match s.kind with
      | .hypothesis => " (local hypotheses)"
      | .fromFile => " (lemmas from current file)"
      | .fromCache => ""
    return <details «open»={true}>
      <summary className="mv2 pointer">
        Pattern <InteractiveCode fmt={head.pattern}/> {.text suffix}
      </summary>
      {renderSectionCore filter s.results}
    </details>

  /-- Render the list of rewrite results in one section. -/
  renderSectionCore (filter : Bool) (sec : Array Result) : Html :=
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
      if filter then sec.filterMap (·.filtered) else sec.map (·.unfiltered)

/-- Repeatedly run `updateWidgetState` until there is an update, and then return the result. -/
partial def waitAndUpdate (state : WidgetState) (unfolds? : Option Html) (rewriteTarget : CodeWithInfos) :
    MetaM RefreshResult := do
  Core.checkInterrupted
  if state.sections.all (·.pending.isEmpty) then
    return .last <| ← renderWidget state unfolds? rewriteTarget
  let (state, anyUpdate) ← (updateWidgetState state).run false
  if anyUpdate then
    return .cont
      (← renderWidget state unfolds? rewriteTarget)
      (← RefreshTask.ofMetaM (waitAndUpdate state unfolds? rewriteTarget))
  -- To avoid wasting computation, we wait a bit before we try again.
  -- The time of 50ms was chosen somewhat arbitrarily.
  -- A wait of 50ms is probably not noticeable to a human?
  IO.sleep 50
  waitAndUpdate state unfolds? rewriteTarget


structure TacticInsertionProps extends PanelWidgetProps where
  replaceRange : Option Lsp.Range := none
  msg : Option String := none
deriving RpcEncodable

@[server_rpc_method_cancellable]
private def rpc (props : TacticInsertionProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "rw!?: Please shift-click an expression you would like to rewrite."
  if loc.loc matches .hypValue .. then
    return .text "rw!?: cannot rewrite in the value of a let variable."
  let some goal := props.goals[0]? | return .text "rw!?: there is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "rw!?: the selected expression should be in the main goal."
  let cancelTk ← IO.CancelToken.new
  let task ← goal.ctx.val.runMetaM {} do withTheReader Core.Context ({ · with cancelTk? := cancelTk }) do
    RefreshTask.ofMetaM do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do

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

      let range : Lsp.Range :=
        if let .some range := props.replaceRange then
          range
        else
          ⟨props.pos, props.pos⟩

      let pasteInfo := { «meta» := doc.meta, range, occ, hyp? := location }
      let state ← initializeWidgetState subExpr pasteInfo loc.fvarId?
      -- Computing the unfold is cheap enough that it doesn't need a separate thread.
      -- However, we do this after the parallel computations have already been spawned by `initializeWidgetState`.
      let unfolds? ← InteractiveUnfold.renderUnfolds subExpr occ location range doc
      waitAndUpdate state unfolds? (← ppExprTagged subExpr)

  return <RefreshComponent
    initial={.text "rw!? is searching for rewrite lemmas..."}
    refresh={← WithRpcRef.mk task}
    cancelTk={← WithRpcRef.mk cancelTk} />

/-- The component called by the `rw!?` tactic -/
@[widget_module]
def LibraryRewriteComponent : Component TacticInsertionProps :=
  mk_rpc_widget% LibraryRewrite.rpc

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
  let some range := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewriteComponent.javascript)
    (pure <| json% { replaceRange: $range }) stx

private def withTreeCtx (ctx : Core.Context) : Core.Context :=
  { ctx with maxHeartbeats := 0, diag := getDiag ctx.options }

open Mathlib Tactic RefinedDiscrTree Lean
elab "#infoview_suggest" : command => do
  let ref := importedRewriteLemmasExt.getState (← getEnv)
  if (← ref.get).isNone then
    let tree ← Elab.Command.liftCoreM do
      let ngen ← getNGen
      let (cNGen, ngen) := ngen.mkChild
      setNGen ngen
      withTheReader Core.Context withTreeCtx do
          createImportedDiscrTree cNGen (← getEnv) addRewriteEntry 5000 256
    ref.set tree
  Elab.Command.elabCommand <| ← `(show_panel_widgets [LibraryRewriteComponent])
