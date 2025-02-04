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

  return result

unsafe def mainOutputPPL (args : List String) : MetaM (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile (fileName++".lean")

  let (moduleStx, env) ← parseModule input fileName
  for {options,..} in moduleStx do
    let length := PrettyFormat.getPFLineLength options
    IO.println s!"line length{length}"
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
  let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [currentEnv, env], options:= options })
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

#eval mainOutputPPL ["./test"]

-- #eval mainInterpret ["./test"]

-- #eval mainOutputPPL ["./test_with_custom_syntax"]
