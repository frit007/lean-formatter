import runner
import PFMT

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System



#guard_msgs in
#eval false

def add (a b:Nat) : Nat := a + b







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
