import PrettyFormat
import CoreFormatters

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

inductive Output
  | replace
  -- copy with extension
  | copy : String → Output
  | none

structure InputArguments where
  fileName : Option String := none
  folder : Option String := none
  -- outputFileName : Option String := none
  output : Output := Output.copy ".formatted" -- TODO: This must change to replace, when the formatter is reliable
  includeFolders : List String := []
  opts : Options := {}

def parseArguments (args:List String) : Except String InputArguments := do
  match args with
  | [] => return {}
  | "-oCopy"::outputFileExtension::xs =>
    return { (← parseArguments xs) with output := Output.copy outputFileExtension }
  | "-oNone":: xs =>
    return { (← parseArguments xs) with output := Output.none }
  | "-oReplace"::xs =>
    return { (← parseArguments xs) with output := Output.replace }
  | "-noWarnCST"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.warnCSTmismatch 0 }
  | "-debugSyntax"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.debugSyntax 1 }
  | "-debugSyntaxAfter"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.debugSyntaxAfter 1 }
  | "-debugErrors"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.debugErrors 1 }
  | "-debugMissingFormatters"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.debugMissingFormatters 1 }
  | "-debugPPL"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.debugPPL 1 }
  | "-warnMissingFormatters"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setInt `pf.warnMissingFormatters 1 }
  | "-lineLength"::length::xs =>
    let res ← parseArguments xs
    match length.toNat? with
    | some l => return { res with  opts := (res.opts).setInt `pf.lineLength l }
    | none => throw "lineLength must be a number"
  | "-include"::dir::xs =>
    let res ← parseArguments xs
    return { res with includeFolders := dir::res.includeFolders }
  | "-file"::fileName::xs =>
    return { (←  parseArguments xs) with  fileName := fileName }
  | "-folder"::folderName::xs =>
    return { (←  parseArguments xs) with  folder := folderName }
  | x::_ => throw s!"unknown argument: {x}"



-- unsafe def mainOutputPPL (args : List String) : MetaM (Array Syntax) := do
--   let [fileName] := args | failWith "Usage: reformat file"
--   initSearchPath (← findSysroot)
--   IO.println "loading file ???"
--   let input ← IO.FS.readFile (fileName++".lean")
--   IO.println "loading file !!!"

--   let (moduleStx, env) ← parseModule input fileName
--   let options ← getOptions
--   IO.println (getPFLineLength options)
--   let values := pFormatAttr.getValues env `«arith_+_»

--   IO.println s!"lengths? {values.length}"

--   -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
--   let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
--   -- let withComments := introduceCommentsToTheCST leadingUpdated

--   -- The Env of the program that reformats the other program. In case that the formatted code does not include the standard annotations
--   let currentEnv := (← getEnv)
--   -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
--   let initialState : FormatState := {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
--   let introduceContext := ((pfCombineWithSeparator (PPL.nl<>PPL.nl) leadingUpdated).run { envs:= [currentEnv, env], options:= options})

--   let introduceState := introduceContext.run initialState
--   let (ppl, state) := introduceState.run
--   IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")


--   for key in (state.diagnostic).missingFormatters.keys do
--     IO.println s!"missing formatter for: {key}"

--   let doc := toDoc ppl
--   let pretty := doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
--   IO.println "START"
--   IO.println ""
--   IO.println s!"{pretty}"
--   IO.println ""
--   IO.println ""
--   IO.println "END"


  -- let _ ← prettifyPPL fileName ppl

  -- return leadingUpdated

unsafe def formatASingleFile (fileName : String) (args : InputArguments): IO (String × FormatReport) := do
  let ((moduleStx, env), timeReadAndParse) ← measureTime do
    let input ← IO.FS.readFile (fileName)
    parseModule input fileName
  let options := args.opts

  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let withComments := introduceCommentsToTheCST leadingUpdated

  -- The Env of the program that reformats the other program. In case that the formatted code does not include the standard annotations
  -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
  let mut formatted := ""
  let mut report : FormatReport := {}

  for a in leadingUpdated do
    let formatters ← getFormatters env
    let result ← pfTopLevelWithDebug a env formatters options fileName

    formatted := formatted ++ "\n\n" ++ result.formattedPPL
    report := report.combineReports ({result.toReport with formattedCommands := if result.cstDifferenceError.isNone then 1 else 0, totalCommands := 1})


  let fileName := match args.output with
  | .copy ext => some (fileName ++ ext)
  | .replace => some fileName
  | .none => none

  if let some f := fileName then
    IO.FS.writeFile (f) (s!"{formatted}")

  return ("", {report with timeReadAndParse})


unsafe def formatFolder (folderName : String) (args : InputArguments)  : IO (List (FormatReport)) := do
  let files ← findAllLeanFilesInProject folderName

  let mut report' : FormatReport := {}
  for file in files do
    IO.println s!"before {file}"
    let (_, report) ← formatASingleFile file args
    report' := report'.combineReports report
    -- reports := report::reports
  return [report']

-- def main (args : List String) : IO (Unit):= do
--   let inputArgs := parseArguments args
--   match inputArgs with
--   | Except.error e => IO.println e
--   | Except.ok args => do
--     match args.fileName with
--     | some fileName => do
--       let a := (formatASingleFile fileName args)
--       let b := a.toIO
--       -- let b := a.run'
--       -- let c := b.run' {fileName := fileName, fileMap := {source := "", positions := #[0]}}
--       -- let d := c {}
--       let _ ← (formatASingleFile fileName args) |>.run' |>.run' {fileName := fileName, fileMap := {source := "", positions := #[0]}}
--       -- let _ ← (formatASingleFile fileName args) |>.run' |>.run' {fileName := fileName, fileMap}
--     | none => match args.folder with
--       | some folder => do
--         let files ← findAllLeanFilesInProject folder
--         for file in files do
--           formatASingleFile file args
--       | none => IO.println "No file or folder specified"
--   return ()

def printReport (report : FormatReport) : IO Unit := do
  IO.println s!"Managed to format {report.formattedCommands} out of commands {report.totalCommands}"

  IO.println s!"Time readAndParse: {report.timeReadAndParse} pf: {report.timePF} doc: {report.timeDoc} reparse: {report.timeReparse}"
  IO.println s!"Missing Formatters ({report.missingFormatters.keys.length}):"
  let sortedList := report.missingFormatters.toArray |>.insertionSort (fun (_,a) (_,b) => a < b) |>.reverse
  for (formatter, count) in sortedList do
    IO.println s!"missing formatter for: {formatter} ({count})"

def printUsage : IO Unit := do
  IO.println "Usage: reformat -file <file> -folder <folder> -o <outputFileName> -noWarnCST -debugSyntax -debugSyntaxAfter -debugErrors -debugMissingFormatters -debugPPL -warnMissingFormatters -lineLength <length>"

unsafe def main (args : List String) : IO (Unit) := do
  -- let (_,coreEnv) ← parseModule (← IO.FS.readFile "PrettyFormat/CoreFormatters.lean") "PrettyFormat/CoreFormatters.lean"
  -- let _ ← coreEnv.displayStats
  -- let a := pFormatAttr.getValues coreEnv `Lean.Parser.Command.declId
  -- IO.println s!"found formatters: {a.length}"

  let inputArgs := parseArguments args

  -- initSearchPath (← findSysroot)
  match inputArgs with
  | Except.error e =>
    IO.println e
    printUsage
  | Except.ok args => do

    initSearchPath (← findSysroot) (args.includeFolders.map (fun c => FilePath.mk c))
    -- let coreEnv ← importModules #[{module := `CoreFormatters}] {}  -- Load Lean’s core environment
    let (_,coreEnv) ← parseModule (← IO.FS.readFile "PrettyFormat/ImportCoreFormatters.lean") "PrettyFormat/ImportCoreFormatters.lean"

    let a := pFormatAttr.getValues coreEnv `Lean.Parser.Command.declId
    IO.println s!"found it?{a.length}"

    match args.fileName with
    | some fileName => do
      let (_,report) ← (formatASingleFile fileName args)
      printReport report
    | none => match args.folder with
      | some folder => do
        let reports ← formatFolder folder args
        let combined := reports.foldl (fun acc report => report.combineReports acc) {}
        -- for report in reports do
        printReport combined
      | none =>
        IO.println "No file or folder specified"
        printUsage

unsafe def mainLog (args : List String) : IO (Unit) := do
  try
    main args
  catch e =>
    IO.println e

-- set_option maxRecDepth 10000000

-- def deepRec (n : Nat) : Nat :=
--   if n = 0 then 0 else deepRec (n - 1) + 1

-- #eval deepRec 10000  -- Might fail without increasing recursion depth

-- set_option trace.profiler true
-- #eval mainLog ["-file", "../../batteries/Batteries/Logic.lean", "-include", "../../batteries/.lake/build/lib"]
-- #eval mainLog ["-file", "../../batteries/Batteries/Logic.lean",]
-- #eval main []
-- #eval main ["-file", "../../lean4/src/Init/Tactics.lean"]
-- #eval main ["-file", "../../lean4/src/Std/Time.lean"]
-- #eval main ["-file", "../../lean4/src/Lean/Attributes.lean"]
-- #eval main ["-folder", "../../lean4/src/Std"]

-- def main2 (args : List String) : MetaM (Unit):= do
--   -- Get all declarations with `myAttr`
--   let decls := (pFormatAttr.getValues (← getEnv) `Lean.Parser.Term.letIdDecl)
--   let _ ← IO.println s!"{decls.length}"

-- #eval main2 ["hello"]

-- unsafe def mainInterpret (args : List String) : MetaM (Array Syntax) := do
--   let [fileName] := args | failWith "Usage: reformat file"
--   initSearchPath (← findSysroot)
--   let input ← IO.FS.readFile (fileName++".lean")

--   let template ← IO.FS.readFile "template.ml"
--   let (env) ← interpretFormat input fileName

--   return #[]

def main3 : IO Unit := do
  let mut a : Std.HashMap Nat String := {}
  for i in [1:50001] do
    a := a.insert (i) (toString i)


#eval measureTime main3


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


declare_syntax_cat fmtCase
syntax num : fmtCase
syntax "| " term " => " term: fmtCase
syntax "| " term " => " term fmtCase: fmtCase


syntax (name:=coreFmCmd)"#coreFm " ident fmtCase : command


initialize IO.println "helllo"

macro_rules
| `(#coreFm $i:ident $a:fmtCase) =>
  -- `(initialize IO Unit := IO.mkref fun a => 2)
  -- let ccc := match a with
  -- | `("| " $a:term " => " $b:term) => 2
  -- | _ => 3

  `(initialize IO.println "some commend??aarst")


#coreFm name
| `($a + $b) => IO.println "what"


macro_rules
| `($a + $b) => `(println! "matched addition!")


macro_rules
| `(command | #coreFmt ppline ($a:term) ) => `("matched repeated addition")

#eval 1 + 2
