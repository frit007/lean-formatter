import PrettyFormat
import annotations

open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open System

def runPrettyExpressive (fileName : String) : IO Unit := do
  let child ← IO.Process.spawn { cmd := s!"./prettyExpressive.bat", args := #[fileName]}

  let exitCode ← child.wait
  if exitCode == 0 then
    IO.println "success"
  else
    IO.println "failure"

unsafe def mainOutputPPL (args : List String) : MetaM (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile (fileName++".lean")

  let template ← IO.FS.readFile "template.ml"
  let (moduleStx, env) ← parseModule input fileName

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

  IO.println "what?"


  IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")
  let ocamlOutput := toOcaml ppl
  let templateWithConttent := template.replace "$$$FORMAT$$$" (ocamlOutput)
  let ocamlFile := fileName++".lean.ml"
  IO.FS.writeFile ocamlFile templateWithConttent
  IO.println "done"
  let _ ← runPrettyExpressive fileName
  let result ← IO.FS.readFile (fileName++".out.lean")

  IO.FS.writeFile (fileName++".out.lean") result
  return leadingUpdated
    -- return "|"


partial def tellMeAbout (kind: SyntaxNodeKind) (args: Array Syntax): MetaM (Array Syntax) := do
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

#eval mainOutputPPL ["./test_with_custom_syntax"]











-- #eval runPrettyExpressive "test"
