import ProofWidgets
import Mathlib.Tactic.NthRewrite
import Mathlib.Lean.Meta.RefinedDiscrTree

namespace InfoviewSuggest

open Lean Meta Widget ProofWidgets Jsx Server

initialize
  registerTraceClass `infoview_suggest

/-- Determine whether the match `e` is too generic to be useful for insertion in
a discrimination tree of all imported theorems. -/
def isBadMatch (e : Expr) : Bool :=
  e.getAppFn.isMVar ||
  -- this extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r

instance {α} : Append (RefinedDiscrTree.MatchResult α) where
  append a b := ⟨a.elts.mergeWith (fun _ a b => a ++ b) b.elts⟩

def _root_.Lean.Meta.RefinedDiscrTree.MatchResult.map {α β} (f : α → β)
    (r : RefinedDiscrTree.MatchResult α) : RefinedDiscrTree.MatchResult β :=
  ⟨r.elts.map fun _ a => a.map (·.map f)⟩

/-- The kind of library lemma -/
inductive PremiseKind where
  /-- A local hypothesis -/
  | hypothesis
  /-- A lemma from the current file -/
  | fromFile
  /-- A lemma from an imported file -/
  | fromCache

inductive Premise where
  | const (declName : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited

def Premise.toString : Premise → String
  | .const name | .fvar ⟨name⟩ => name.toString

def Premise.length (premise : Premise) : Nat :=
  premise.toString.length

/-- Pretty print the given constant, making sure not to print the `@` symbol.
This is a HACK and there should be a more principled way to do this. -/
def ppConstTagged (name : Name) : MetaM CodeWithInfos := do
  return match ← ppExprTagged (← mkConstWithLevelParams name) with
    | .tag tag _ => .tag tag (.text s!"{name}")
    | code => code

def ppPremiseTagged : Premise → MetaM CodeWithInfos
  | .const name => ppConstTagged name
  | .fvar fvarId => ppExprTagged (.fvar fvarId)

/-- The information required for pasting a suggestion into the editor -/
structure PasteInfo where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  replaceRange : Lsp.Range


/-- Return syntax for the rewrite tactic `rw [e]`. -/
def mkRewrite (occ : Option Nat) (symm : Bool) (e : Term) (loc : Option Name) :
    CoreM (TSyntax `tactic) := do
  let loc ← loc.mapM fun h => `(Lean.Parser.Tactic.location| at $(mkIdent h):term)
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  match occ with
  | some n => `(tactic| nth_rw $(Syntax.mkNatLit n):num [$rule] $(loc)?)
  | none => `(tactic| rw [$rule] $(loc)?)

/-- Given tactic syntax `tac` that we want to paste into the editor, return it as a string.
This function respects the 100 character limit for long lines. -/
def tacticPasteString (tac : TSyntax `tactic) (range : Lsp.Range) : CoreM String := do
  let column := range.start.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

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
      withNewMCtxDepth <| isDefEq tArgs[i]! sArgs[i]!
