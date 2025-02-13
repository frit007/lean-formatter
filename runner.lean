import PrettyFormat
import annotations

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System


def runPrettyExpressive (fileName : String) : IO Unit := do
  IO.println s!"tryingToRun : {fileName}"
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

partial def findAllLeanFilesInProject (projectFolder:String) : IO (List String) := do
  IO.println projectFolder
  let files ← System.FilePath.readDir projectFolder
  files.foldlM (fun (acc:List String) file => do
    if ← file.path.isDir then
      return (← findAllLeanFilesInProject (file.path.toString)) ++ acc
    else
      if file.path.extension.any (fun e => e == "lean") then
        return file.path.toString :: acc
      else
        return acc
  ) []
  -- let files ← System



unsafe def mainOutputPPL (args : List String) : MetaM (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  IO.println "loading file ???"
  let input ← IO.FS.readFile (fileName++".lean")
  IO.println "loading file !!!"

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
  let initialState : FormatState := {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
  let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [currentEnv, env], options:= options, stx:=[]})

  let introduceState := introduceContext.run initialState
  let a := introduceState.run
  let ppl ← introduceState.run
  match ppl with
  | .ok (ppl, state) =>
    IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")


    for key in (state.diagnostic).missingFormatters.keys do
      IO.println s!"missing formatter for: {key}"

    let doc := toDoc ppl
    let pretty := doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
    IO.println "START"
    IO.println ""
    IO.println s!"{pretty}"
    IO.println ""
    IO.println ""
    IO.println "END"


    let _ ← prettifyPPL fileName ppl

    return leadingUpdated
  | .error e =>
    IO.println s!"fail {repr e}"
    return #[]



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
--
-- #eval mainOutputPPL ["./../tmp/greeting-lean/Main"]

-- #eval mainOutputPPL ["../../lean4/src/Init/Coe"]

-- #eval findAllLeanFilesInProject "../../lean4/src"

-- #eval mainOutputPPL ["./test"]

-- #eval mainInterpret ["./test"]

-- #eval mainOutputPPL ["./test_with_custom_syntax"]
