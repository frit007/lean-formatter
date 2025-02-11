import Lean
import annotations
open Lean Meta PrettyPrinter Elab Term


-- def a (f:Nat):=
--   f * 2


-- def altA (f:Nat):Nat :=
--   f * 2

-- elab "elabAST " t:term : term => do
--   let env ← getEnv
--   let e ← elabTerm t none  -- Elaborate the term into an `Expr`
--   logInfo m!"Elaborated Expression:\n{e}"
--   return e


def compareAst (l: List Expr) (r:List Expr) :=
  l == r


def getAst (parsed: (Array CommandSyntax × Environment)) : MetaM (List Expr) := do
  let commands := parsed.fst
  let env' := parsed.snd
  -- let commands ← parseModule "" "test.lean"



  let elabs ← commands.foldlM (fun (acc : List Expr) (command : CommandSyntax) => do
    let elabbed ← (withEnv env') do
      (withOptions (fun _ => command.options)) do
      (elabTerm command.stx none).run' {} {}
    return elabbed :: acc
  ) []

  let elabs ← commands.foldlM (fun (acc : List Expr) (command : CommandSyntax) => do
    let elabbed ← (withEnv env') do
      (withOptions (fun _ => command.options)) do
      (Command.elabCommandTopLevel command.stx)
    return elabbed :: acc
  ) []

  -- let first : Expr := elabs.get! 0
  return elabs


def compareAsts (before:(Array CommandSyntax × Environment)) (after : (Array CommandSyntax × Environment)) : MetaM Bool := do
  let beforeAst ← getAst before
  let afterAst ← getAst after
  return compareAst beforeAst afterAst

def test : MetaM Bool := do
  let before ← parseModule (← IO.FS.readFile "test.lean") "test.lean"
  let after ← parseModule (← IO.FS.readFile "test2.lean") "test2.lean"
  compareAsts before after

#eval test
