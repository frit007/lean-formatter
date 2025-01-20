import Lean
import Lean.CoreM

open Lean
open Lean.Meta

structure FormatState where
  hasStartedComment : Bool -- Keep track of whether a comment has been started

-- def one: MonadState FormatState := do
--   let s <- get
--   let a: FormatState := {FormatState.hasStartedComment:= false}


set_option diagnostics true

structure Context where
  options : Options

structure State where
  /-- Textual content of `stack` up to the first whitespace (not enclosed in an escaped ident). We assume that the textual
  content of `stack` is modified only by `pushText` and `pushLine`, so `leadWord` is adjusted there accordingly. -/
  leadWord : String := ""
  /-- When the `leadWord` is nonempty, whether it is an identifier. Identifiers get space inserted between them. -/
  leadWordIdent : Bool := false
  /-- Whether the generated format begins with the result of an ungrouped category formatter. -/
  isUngrouped : Bool := false
  /-- Whether the resulting format must be grouped when used in a category formatter.
  If the flag is set to false, then categoryParser omits the fill+nest operation. -/
  mustBeGrouped : Bool := true
  /-- Stack of generated Format objects, analogous to the Syntax stack in the parser.
  Note, however, that the stack is reversed because of the right-to-left traversal. -/
  stack    : Array Format := #[]
  nextId : Nat := 0


abbrev FormatterM := ReaderT Context $ StateRefT State CoreM

abbrev Formatter := FormatterM Nat

-- Function using MonadState
def resetCommentState [Monad m] [MonadState FormatState m] : m Unit := do
  let s ← get -- Access the current state
  let newState : FormatState := { hasStartedComment := false }
  -- let _ ← set newState -- Update the state
  pure ()


def getNextUniqueValue : Formatter := do
  let current <- get   -- Retrieve the current state
  let _ <- set ({current with nextId:= current.nextId + 1})    -- Update the state
  pure 1
  -- return current             -- Return the current value as the result

-- -- Run the stateful computation
-- def runUniqueValueGenerator : List Nat :=
--   let initialState := 0        -- Start with an initial state (e.g., 0)
--   let (values, _) := State.run (do
--     let v1 <- getNextUniqueValue
--     let v2 <- getNextUniqueValue
--     let v3 <- getNextUniqueValue
--     return [v1, v2, v3]
--   ) initialState
--   values

-- def main : IO Unit :=
--   IO.println s!"Generated values: {runUniqueValueGenerator}"


def exampleMetaComputation : MetaM Unit :=
  do
    let expr ← mkFreshExprMVar none
    logInfo m!"Created a fresh expression: {expr}"

-- Running MetaM from IO
def runMetaExample : IO Unit := do
  MetaM.run'
  IO.println <| (← MetaM.run' exampleMetaComputation)


-- def resetCommentState [MonadState FormatState m] : m Unit :=
--     do
--     let s ← get -- Access the current state
--     let newState : FormatState := { hasStartedComment := false }
--     -- newState -- Update the state
--     pure ()

-- def toggleCommentState [MonadState FormatState m] : m Unit := id.run do
--   modify fun s => { s with hasStartedComment := !s.hasStartedComment }

-- def example : StateT FormatState IO Unit := do
--   let initialState := { hasStartedComment := true }
--   IO.println s!"Initial State: {← get}"
--   resetCommentState
--   IO.println s!"Updated State: {← get}"


-- Output: ("Final state: 30", 30)

-- #eval one (FormatState.mk false)
