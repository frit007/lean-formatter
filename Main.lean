import SimpleMeta

import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Expr
open Server

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

-- -- Function to get the syntax/AST of another function
-- def getFunctionAST (fnName : Name) : MetaM Syntax :=
--   do
--     -- Retrieve the declaration of the function by its name
--     let some decl ← getConstInfo? fnName
--       | throwError s!"Function {fnName} not found"
--     -- Extract and return the syntax (if available)
--     pure decl.value!

-- #eval show CoreM Unit from do
--   -- Example: Get the AST for the `main` function
--   let env ← getEnv
--   let fnName := `main
--   IO.println s!"AST for {fnName}: {← MetaM.run' (getFunctionAST fnName)}"


-- elab "#help" : command => do command

-- Macros
-- macro x:ident ":" t:term " ↦ " y:term : term => do
--   `(fun $x : $t => $y)

-- #eval (x : Nat ↦ x + 2) 2 -- 4

-- macro x:ident " ↦ " y:term : term => do
--   `(fun $x  => $y)

-- #eval (x ↦  x + 2) 2 -- 4


elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

-- info: success
-- #assertType 5 : Nat

/--
error: type mismatch
  []
has type
  List ?m.3211 : Type ?u.3210
but is expected to have type
  Nat : Type
-/
-- #assertType [] : Nat


inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
-- Arith.mul (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + "y" ⟫
-- Arith.add (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + 20 ⟫
-- Arith.add (Arith.var "x") (Arith.nat 20) : Arith

#check ⟪ "x" + "y" * "z" ⟫ -- precedence
-- Arith.add (Arith.var "x") (Arith.mul (Arith.var "y") (Arith.var "z")) : Arith

#check ⟪ "x" * "y" + "z" ⟫ -- precedence
-- Arith.add (Arith.mul (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith

#check ⟪ ("x" + "y") * "z" ⟫ -- brackets
-- Arith.mul (Arith.add (Arith.var "x") (Arith.var "y")) (Arith.var "z")


open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_comm`



-- XOR, denoted \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

open Lean Elab Command

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

blue -- finally, blue!


--------- MetaM -------------
-- def x (y:Nat) : Nat :=
--   y * 2

-- #check ppExpr (x)

open Lean
open Lean.Meta
open Lean.Elab

def hello2 (x:Nat)  (y:Nat) : Nat:=
  x * y

-- -- Function to retrieve the syntax/AST of another function by its name
-- def getFunctionSyntax (fnName : Name) : MetaM Expr :=
--   do
--     -- Fetch the declaration for the given function name
--     let some decl ← getConstInfo fnName
--       | throwError s!"Function {fnName} not found"
--     -- Return the body of the function as an expression
--     match decl.value? with
--     | some expr => return expr
--     | none => throwError s!"Function {fnName} has no body (possibly an axiom or opaque)"

-- -- Example usage
-- #eval show MetaM Unit from do
--   -- Get the syntax of a specific function
--   let s ← getFunctionSyntax `hello2
--   IO.println s!"Syntax for List.map: {s}"

open Lean.Parser
