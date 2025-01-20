import Lean
import PrettyFormat

open Lean
open Lean.Meta
open Lean.Elab.Command

-- Define the custom attribute


-- Retrieve all annotated functions


-- -- Example usage
-- def printFunctionsWithFormatAttribute : IO Unit := do
--   MetaM.run' do
--     let entries ← getFunctionsWithFormatAttribute
--     for (declName, paramName) in entries do
--       IO.println s!"Function: {declName}, Format ID: {paramName}"


-- Annotated functions
@[format myId]
def some_func (x : Syntax) : Syntax :=
  x

@[format myId]
def mul_two (x : Nat) : Nat :=
  x * 2

@[format otherId]
def another_func (x : Syntax) : Syntax :=
  x


def getFunctionsWithFormatAttribute : MetaM (Array (Name × Name)) := do
  let env ← getEnv

  let decls := env.constants.map₁.toArray -- Get all constants in the environment
  let annotatedDecls ← decls.filterMapM fun (declName, _) => do
    match formatAttr.getParam? env declName with
    | some paramName => pure (some (declName, paramName)) -- Keep annotated decls
    | none => pure none -- Skip non-annotated decls
  pure annotatedDecls






def what : MetaM (Nat) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray.map (fun (a,b) => a)|>.toList|>.length
  pure decls




#eval getFunctionsWithFormatAttribute

-- -- Retrieve annotated declarations
-- open Lean in
-- def getAnnotatedDecls : CoreM (Array Name) := do
--   let env ← getEnv
--   let x ← formatAttr.getParam? env `app.otherId
--   pure ([])



-- -- Example usage
-- def printAnnotatedDecls : IO Unit := do
--   IO.println "Retrieving annotated functions..."
--   MetaM.run' do
--     let decls ← getAnnotatedDecls
--     for decl in decls do
--       IO.println s!"Found annotated function: {decl}"

-- #eval printAnnotatedDecls
