import PrettyFormat
import annotations

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System


def runPrettyExpressive (fileName : String) : IO Unit := do
  let child ← IO.Process.spawn { cmd := s!"./prettyExpressive.bat", args := #[fileName]}

  let exitCode ← child.wait
  if exitCode == 0 then
    IO.println "success"
  else
    IO.println "failure"

unsafe def prettifyPPL (filename:String) (ppl: PPL) : IO String := do

  let template ← IO.FS.readFile "template.ml"
  let ocamlOutput := toOcaml ppl
  let templateWithConttent := template.replace "$$$FORMAT$$$" (ocamlOutput)
  let ocamlFile := filename++".lean.ml"
  IO.FS.writeFile ocamlFile templateWithConttent
  IO.println "done"
  let _ ← runPrettyExpressive filename
  let result ← IO.FS.readFile (filename++".out.lean")
  -- IO.FS.writeFile (filename++".out.lean") result
  return result

unsafe def mainOutputPPL (args : List String) : MetaM (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile (fileName++".lean")

  let (moduleStx, env) ← parseModule input fileName
  let options ← getOptions
  IO.println (getPFLineLength options)
  let values := pFormatAttr.getValues env `«arith_+_»

  IO.println s!"lengths? {values.length}"

  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let withComments := introduceCommentsToTheCST leadingUpdated

  -- The Env of the program that reformats the other program. In case that the formatted code does not include the standard annotations
  let currentEnv := (← getEnv)
  -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
  let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [currentEnv, env] })
  let introduceState := introduceContext.run' {nextId := 0}
  let ppl ← introduceState

  IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")

  let _ ← prettifyPPL fileName ppl

  return leadingUpdated

unsafe def mainInterpret (args : List String) : MetaM (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile (fileName++".lean")

  let template ← IO.FS.readFile "template.ml"
  let (env) ← interpretFormat input fileName

  return #[]

partial def tellMeAbout (kind: SyntaxNodeKind) (args: Array Syntax): MetaM (Array Syntax) := do
  let o ← getOptions

  let res : MetaM (Option (Array Syntax)) := args.foldlM (fun (acc: Option (Array Syntax)) (arg : Syntax) => do
    match acc with
    | some p => return some p
    | none =>
        match arg with
        | Syntax.node _ k args => do
          if k == kind then
            return some args
          else
            try
              let result ← tellMeAbout kind args
              return some result
            catch _ =>
              return none
        | _ => return none
      ) none
  match ← res with
  | some p => return p
  | none => failure



    -- IO.println s!"{arg}"


unsafe def mainWithInfo (kind: SyntaxNodeKind) (args : List String) : MetaM (Array Syntax) := do
  let x ← mainOutputPPL args
  let info ← tellMeAbout kind x
  IO.println s!"parts {info.size}"
  return info


-- #eval mainWithInfo `Lean.Parser.Term.letIdDecl ["./test"]

-- #eval mainOutputPPL ["./test"]
-- #eval mainInterpret ["./test"]

-- #eval mainOutputPPL ["./test_with_custom_syntax"]




/-- info: false -/
#guard_msgs in
#eval false

def add (a b:Nat) : Nat := a + b



syntax (name := formatCmd)
  "#format" ppLine command : command

@[command_elab formatCmd]
unsafe def elabFormatCmd : CommandElab
  | `(command|#format $cmd) => liftTermElabM do
    let env ← getEnv
    let opts ← getOptions
    let stx := cmd.raw

    match (stx.getPos?, stx.getTailPos?) with
    | (some pos, some tailPos) => logInfo s!"{pos} {tailPos}"
    | _ => logInfo s!"no pos"

    -- let leadingUpdated := stx.updateLeading |>.getArgs
    let leadingUpdated := stx|>.getArgs
    let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [env]})
    let introduceState := introduceContext.run' {nextId := 0}
    let ppl ← introduceState

    -- logInfo s!"\n{getPFLineLength opts}"
    let result ← prettifyPPL "elab" ppl
    logInfo s!"{result}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"




def revealTrailingWhitespace (s : String) : String :=
  s.replace "⏎\n" "⏎⏎\n" |>.replace "\t\n" "\t⏎\n" |>.replace " \n" " ⏎\n"

open CodeAction Server RequestM in
@[command_code_action Lean.Parser.Command.declaration]
def guardMsgsCodeAction : CommandCodeAction := fun p sn _ node => do
  -- p.
  let .node i ts := node | return #[]
  -- IO.println s!"nodes: {i.stx.getKind}"

  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => return stx
    | _ => none



  -- match res with
  -- | some _ => IO.println "some"
  -- | none => IO.println "none"

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
      -- let some start := stx.getPos? true | return eager
      -- let some tail := stx.setArg 0 mkNullNode |>.getPos? true | return eager
      -- let start := p.range.start
      -- let tail := p.range.end
      let r :String.Range := stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!
      let start := r.start
      let tail := r.stop
      let res := "some weird string"
      -- let newText := if res.isEmpty then
      --   ""
      -- else if res.length ≤ 100-7 && !res.contains '\n' then -- TODO: configurable line length?
      --   s!"/-- aaa -/\n"
      -- else
      --   s!"/--\n bbb \n-/\n"
      -- let kind := pf stx.run
      let kind := stx.getKind
      let newText := s!"kind: {kind}"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          -- range := p.range
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]




def test : Nat :=
  add 1 2

-- #format
--   def test2 : Nat := add 2 3







-- #eval runPrettyExpressive "test"
