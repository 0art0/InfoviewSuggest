import ProofWidgets
import Mathlib.Tactic.NthRewrite

namespace InfoviewSuggest

open Lean Meta Widget ProofWidgets Jsx Server

/-- The information required for pasting a suggestion into the editor -/
structure PasteInfo where
  /-- The current document -/
  «meta» : DocumentMeta
  /-- The range that should be replaced.
  In tactic mode, this should be the range of the suggestion tactic.
  In infoview mode, the start and end of the range should both be the cursor position. -/
  range : Lsp.Range


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
      isDefEq tArgs[i]! sArgs[i]!
