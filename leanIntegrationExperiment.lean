import runner
import PFMT

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System


/-- info: false -/
#guard_msgs in
#eval false

def add (a b:Nat) : Nat := a + b



syntax (name := formatCmd)
  "#format" ppLine command : command



def revealTrailingWhitespace (s : String) : String :=
  s.replace "⏎\n" "⏎⏎\n" |>.replace "\t\n" "\t⏎\n" |>.replace " \n" " ⏎\n"

-- open CodeAction Server RequestM in
-- @[command_code_action Lean.Parser.Command.declaration]
-- def DeclarationCodeAction : CommandCodeAction := fun p sn info node => do
--   let .node i ts := node | return #[]

--   let res := ts.findSome? fun
--     | .node (.ofCustomInfo { stx, value }) _ => return stx
--     | _ => none

--   let opts := info.options
--   let stx :Syntax := i.stx

--   let doc ← readDoc
--   let eager :Lsp.CodeAction := {
--     title := "Format code"
--     kind? := "quickfix"
--     isPreferred? := true
--   }
--   pure #[{
--     eager
--     lazy? := some do
--       let r :String.Range := stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!
--       let start := r.start
--       let tail := r.stop
--       let kind := stx.getKind

--       let newText := s!"proof of concept formatted code"


--       pure { eager with
--         edit? := some <|.ofTextEdit doc.versionedIdentifier {
--           -- range := p.range
--           range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
--           newText
--         }
--       }
--   }]

def test : Nat :=
  add 1 2






-- @[command_elab formatCmd]
-- unsafe def elabFormatCmd : CommandElab
--   | `(command|#format $cmd) => liftTermElabM do
--     let env ← getEnv
--     let opts ← getOptions
--     let stx := cmd.raw

--     match (stx.getPos?, stx.getTailPos?) with
--     | (some pos, some tailPos) => logInfo s!"{pos} {tailPos}"
--     | _ => logInfo s!"no pos"

--     -- let leadingUpdated := stx.updateLeading |>.getArgs
--     let leadingUpdated := stx|>.getArgs
--     let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [env], options := ← getOptions, stx := []})
--     let introduceState := introduceContext.run' {nextId := 0}
--     let ppl ← introduceState.run

--     let result :=
--     match ppl with
--     | .ok ppl =>
--       let doc := toDoc [] ppl

--       doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
--       -- let result ← prettifyPPL "elab" ppl
--       -- formattedCode.set result -- I think we can't execute IO in cmd, therefore we do the work here and use the work later

--     | _ => s!"Failed formatting: {stx.getKind}"
--     formattedCode.set result

--     -- -- logInfo s!"\n{getPFLineLength opts}"

--     -- let result := "hello"
--     -- logInfo s!"{result}"
--   | stx => logError m!"Syntax tree?: {stx.getKind}"



open CodeAction Server RequestM in
-- @[command_code_action]
@[command_code_action Lean.Parser.Command.declaration]
def formatCmdCodeAction : CommandCodeAction := fun p sn info node => do
  let .node i ts := node | return #[]

  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => return stx
    | _ => none

  let opts := info.options
  let stx :Syntax := i.stx
  let doc ← readDoc
  let eager :Lsp.CodeAction := {
    title := "Format code"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let r :String.Range := stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!
      let start := r.start
      let tail := r.stop
      let kind := stx.getKind
      let newText ← formattedCode.get


      let leadingUpdated := stx
      let ppl ← pfTopLevelWithDebug (stx) [info.env] opts
      let newText := toDoc [] ppl |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)

      -- let leadingUpdated := stx.getArgs
      -- let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [info.env], options := info.options, stx := []})
      -- let introduceState := introduceContext.run' {nextId := 0}
      -- let newText := match ← introduceState.run with
      -- | .ok (ppl) =>
      --   let doc := toDoc [] ppl
      --   doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
      -- | _ => ""

      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]



-- set_option pf.debugSyntax 1
-- set_option pf.debugMissingFormatters 1
-- set_option pf.debugSyntaxAfter 1 -- TODO:
-- set_option pf.debugErrors 1
-- set_option pf.debugPPL 1
-- #format

def test2  : Nat :=
  add 2 3

private def b(y:Nat):Nat:=
  3 * y
