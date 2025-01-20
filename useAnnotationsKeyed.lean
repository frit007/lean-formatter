import Lean
import annotations_keyed

open Lean
open Lean.Meta
open Lean.Elab

@[pFormat some]
def return_a_state : formatPPL:= do
    let x <- get
    pure 1

def getem: MetaM Nat:= do
    let env ← getEnv
    let something := pFormatAttr.getValues env `some
    IO.println s!"hello {something.length}"
    pure 1

#eval getem

-- -- #eval (app_pFormat some)

-- @[builtin_pFormat a]
-- def a : PFState:= {a:= 1, b:= 3}
