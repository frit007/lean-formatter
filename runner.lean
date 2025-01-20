import read2

open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open System

def runPrettyExpressive (fileName : String) : IO Unit := do
  let child ← IO.Process.spawn { cmd := s!"./prettyExpressive.bat", args := #[fileName]}

  let exitCode ← child.wait

unsafe def mainOutputPPL (args : List String) : MetaM (String) := do
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


  -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
  let introduceContext := ((pfCombineWithSeparator nl leadingUpdated).run { tmp:= 0 })
  let introduceState := introduceContext.run' {nextId := 0, otherEnv := env}
  let ppl ← introduceState
  -- let ppl := ((pfCombineWithSeparator nl leadingUpdated).run { tmp:= 0 }).run' {nextId := 0, otherEnv := env})

  -- let ppl := syntaxArrToPPLWithNewLines empty leadingUpdated
  let ocamlOutput := toOcaml ppl
  let templateWithConttent := template.replace "$$$FORMAT$$$" (ocamlOutput)
  let ocamlFile := fileName++"lean.ml"
  IO.FS.writeFile ocamlFile templateWithConttent
  IO.println "done"
  let _ ← runPrettyExpressive fileName
  let result ← IO.FS.readFile (fileName++".out.lean")

  -- IO.FS.writeFile (fileName++".out.lean") result
  return result ++ "\n\n" ++ ocamlOutput

#eval mainOutputPPL ["./test"]
