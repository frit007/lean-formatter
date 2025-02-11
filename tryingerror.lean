import Lean
import Lean.MonadEnv  -- Required for lift

open Lean

def handle (res : Except String Nat) : String :=
  match res with
  | Except.ok n => s!"Success: {n}"
  | Except.error msg => s!"Error: {msg}"

def a : Except String Nat := do
  throw ""

#eval handle (Except.ok 2)  -- "Success: 42"
#eval handle (Except.error "what???")  -- "Error: Something went wrong"
