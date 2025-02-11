import PrettyFormat
import annotations

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System

unsafe def run (dir fileName:String) : MetaM (String):= do

  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile (fileName)

  let (moduleStx, env) ← parseModule input fileName

  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let withComments := introduceCommentsToTheCST leadingUpdated

  -- The Env of the program that reformats the other program. In case that the formatted code does not include the standard annotations
  -- let currentEnv := (← getEnv)
  -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}

  -- let x ←


  -- TODO add logic to determine how different items are combined, for example theorems might want no spacing between them


  let ppl ← moduleStx.foldlM (fun (ppl:PPL) (s:CommandSyntax) => do
    let introduceContext := ((pf s.stx).run { envs:= [s.env], options:= s.options })
    let introduceState := introduceContext.run' {nextId := 0}
    let ppl ← introduceState
    return ppl <> PPL.nl <> ppl
  ) (PPL.text "")


  IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")

  let doc := toDoc [] ppl
  let pretty := Pfmt.Doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100) doc
  return pretty

  -- IO.println "START"
  -- IO.println ""
  -- IO.println s!"{pretty}"
  -- IO.println ""
  -- IO.println ""
  -- IO.println "END"
