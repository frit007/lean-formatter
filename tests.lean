import PrettyFormat
import annotations

open Lean Meta

syntax (name := formatCmd)
  "#format" ppLine command : command

open Lean Elab Parser Command

@[command_elab formatCmd]
unsafe def elabFormatCmd : CommandElab
  | `(command|#format $cmd) => liftTermElabM do
    let env ← getEnv
    logInfo s!"\n{cmd.raw.prettyPrint}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"


/--
info:
def x := do 10 + 12
-/
#guard_msgs in
#format
  def x := do 10 + 12 -- hi?



/-- info: "done" -/
#guard_msgs in
#eval "done"

