import annotations
import Lean

-- #eval getFunctionsWithFormatAttribute

open Lean
open Lean.Meta
open Lean.Elab.Command



def callFunctionByName : MetaM (Option Expr) := do
  let env ← getEnv
  match env.find? `mul_two with
  | some i =>
    let x := mkApp (i.value!) (mkNatLit 9)
    let res ← whnf (x)
    IO.println s!"{res}"
    return some i.value!
  | none => pure none

#eval callFunctionByName
