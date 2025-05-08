import PrettyFormat
import CoreFormatters

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System
open IO IO.Process

def runPrettyExpressive (fileName : String) : IO Unit := do
  IO.println s!"tryingToRun : {fileName}"
  let child ← IO.Process.spawn { cmd := s!"./prettyExpressive.bat", args := #[fileName]}

  let exitCode ← child.wait
  if exitCode == 0 then
    IO.println "success"
  else
    IO.println "failure"

-- unsafe def prettifyPPL (filename:String) (ppl: PPL) : IO String := do
--   let template ← IO.FS.readFile "template.ml"
--   let ocamlOutput := toOcaml ppl
--   let templateWithConttent := template.replace "$$$FORMAT$$$" (ocamlOutput)
--   let ocamlFile := filename++".lean.ml"
--   IO.FS.writeFile ocamlFile templateWithConttent
--   IO.println "done"
--   let _ ← runPrettyExpressive filename
--   let result ← IO.FS.readFile (filename++".out.lean")

--   return result

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

inductive PPLOutput
  | replace
  -- copy with extension
  | copy : String → PPLOutput
  | none

structure InputArguments where
  files : Option (List String) := none
  folder : Option String := none
  workers : Nat := 4
  filesPrWorker : Nat := 7
  -- outputFileName : Option String := none
  output : PPLOutput := PPLOutput.copy ".formatted" -- TODO: This must change to replace, when the formatter is reliable
  includeFolders : List String := []
  opts : Options := {}
  serializedOutput : Bool := false

def parseArguments (args:List String) : Except String InputArguments := do
  match args with
  | [] => return {}
  | "-oCopy"::outputFileExtension::xs =>
    return { (← parseArguments xs) with output := PPLOutput.copy outputFileExtension }
  | "-oNone":: xs =>
    return { (← parseArguments xs) with output := PPLOutput.none }
  | "-oReplace"::xs =>
    return { (← parseArguments xs) with output := PPLOutput.replace }
  | "-noWarnCST"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.warnCSTmismatch false }
  | "-debugSyntax"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugSyntax true }
  | "-debugSyntaxAfter"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugSyntaxAfter true }
  | "-serializedOutput"::xs =>
    let res ← parseArguments xs
    return { res with serializedOutput := true }
  | "-debugErrors"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugErrors true }
  | "-debugMissingFormatters"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugMissingFormatters true }
  | "-debugPPL"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugPPL true }
  | "-warnMissingFormatters"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.warnMissingFormatters true }
  | "-lineLength"::length::xs =>
    let res ← parseArguments xs
    match length.toNat? with
    | some l =>
      if l == 0 then
        throw "lineLength must be positive"
      return { res with  opts := (res.opts).setInt `pf.lineLength l }
    | none => throw "lineLength must be a number"
  | "-cacheDistance"::distance ::xs =>
    let res ← parseArguments xs
    match distance.toNat? with
    | some d =>
      if d == 0 then
        throw "cacheDistance must be positive"
      return { res with  opts := (res.opts).setInt `pf.cacheDistance d }
    | none => throw "cacheDistance must be a number"
  | "-include"::dir::xs =>
    let res ← parseArguments xs
    return { res with includeFolders := dir::res.includeFolders }
  | "-file"::fileName::xs =>
    let res ←  parseArguments xs
    let files := match res.files with
    | some files => fileName :: files
    | _ => [fileName]
    return { (←  parseArguments xs) with  files := files }
  | "-folder"::folderName::xs =>
    return { (←  parseArguments xs) with  folder := folderName }
  | "-workers"::workers::xs =>
    let workers := match workers.toNat? with
    | some n => n
    | _ => panic! s!"workers must be a positive natural number {workers}"
    if workers == 0 then
      panic! s!"workers must be a positive natural number {workers}"
    return { (←  parseArguments xs) with workers := workers }
  | "-filesPrWorker"::filesPrWorker::xs =>
    let filesPrWorker := match filesPrWorker.toNat? with
    | some n => n
    | _ => panic! s!"filesPrWorker must be a positive natural number {filesPrWorker}"
    if filesPrWorker == 0 then
      panic! s!"filesPrWorker must be a positive natural number {filesPrWorker}"
    return { (←  parseArguments xs) with filesPrWorker := filesPrWorker }
  | x::_ => throw s!"unknown argument: {x}"

-- we want to pass on the arguments to the next process
def cleanArguments (args : List String) : List String:= Id.run do
  let removedParams := [("-workers",1), ("-filesPrWorker",1), ("-folder", 1)]
  let mut newParams := []
  let mut skipping := 0
  for a in args do
    if skipping > 0 then
      skipping := skipping - 1
    else
      match removedParams.find? (fun (r,_) => r == a) with
      | some (_, s) => skipping := s
      | _ => newParams := a::newParams
  return newParams.reverse


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

unsafe def formatFile (fileName : String) (args : InputArguments): IO (String × FormatReport) := do
  let ((moduleStx, env), timeReadAndParse) ← measureTime (fun _ => do
    let input ← IO.FS.readFile (fileName)
    parseModule input fileName
  )
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

    formatted := formatted ++ (result.reportAsComment ++ result.formattedPPL) ++ "\n\n"
    report := report.combineReports ({result.toReport with formattedCommands := if result.cstDifferenceError.isNone then 1 else 0, totalCommands := 1})

  let fileName := match args.output with
  | .copy ext => some (fileName ++ ext)
  | .replace => some fileName
  | .none => none

  if report.totalCommands - report.formattedCommands ≠ 0 then
    IO.println s!"{fileName} successfully formatted {report.formattedCommands} / {report.totalCommands}"

  if let some f := fileName then
    IO.FS.writeFile (f) (s!"{formatted}")

  return ("", {report with timeReadAndParse})

abbrev ChildI := Child { stdout := .piped, stderr := .piped, stdin := .null }
structure RunningProcess where
  process : ChildI
  arguments : String
  timeOutAtNs : Nat
  errorStream : Task (Except IO.Error String)
  outputStream : Task (Except IO.Error String)

structure RunnerState where
  running : List RunningProcess := []
  remainingFiles : List String := []
  results : FormatReport := {}
  errs : List String := []
  maxWorkers : Nat := 4
  filesPrWorker : Nat := 3
  includeFolders : List String := []
  configArguments : List String


partial def RunnerState.waitUntilAtLeastOneProcessIsDone (state : RunnerState) : IO RunnerState := do
  let mut stillRunning := []
  -- let mut results := procs.running
  let mut state := state
  let mut foundOne := false

  -- IO.println "wait one..."
  let now ← IO.monoNanosNow
  for p in state.running do
    let child := p.process
    -- foundOne := true
    -- IO.println "fake run?"
    -- state := {state with re}
    if p.timeOutAtNs < now then
      IO.println s!"kill {p.arguments}"
      let output ← IO.ofExcept p.outputStream.get
      IO.println s!"it would have the following output {output}"
      -- p.process.kill
    else
      match ← child.tryWait with
      | some code =>
        -- IO.println "yay success"
        -- let output ← IO.asTask (IO.FS.Handle.readToEnd (child.stdout)) Task.Priority.dedicated
        -- let output ← IO.FS.Handle.readToEnd (child.stdout)
        let output ← IO.ofExcept p.outputStream.get
        -- let output ← p.outputStream

        let serializedString := "serialized: "
        let updatedResults := output.split (fun c => c == '\n')
          |>.filter (fun s => s.startsWith serializedString)
          |>.map (fun s => s.drop serializedString.length)
          |>.foldl (fun acc s => (FormatReport.deserialize s).combineReports acc) state.results
        -- IO.println s!"sss:{output.split (fun c => c == '\n')
          -- |>.filter (fun s => s.startsWith serializedString)}"

        let stderr ← IO.ofExcept p.errorStream.get
        -- let stderr ← child.stderr.readToEnd
        if stderr != "" then
          IO.println s!"err ({p.arguments})\n: {stderr}"
        -- IO.println s!"output: {output}"
        -- let report := FormatReport.deserialize output
        state := { state with
          results := updatedResults
          errs := (if code != 0 then p.arguments :: state.errs else state.errs)
        }
        foundOne := true
      | none => stillRunning := p :: stillRunning

  state := {
    state with
    running := stillRunning
  }
  if foundOne then
    return state
  else
    -- Wait a bit before polling again (avoid busy looping)
    IO.sleep 100
    state.waitUntilAtLeastOneProcessIsDone

partial def RunnerState.startUpToNProcesses (state : RunnerState) : IO RunnerState := do
  if state.running.length < state.maxWorkers && state.remainingFiles.length > 0 then

    let args := state.remainingFiles.take state.filesPrWorker |>.flatMap (fun s => ["-file", s.replace "\\" "/"])
    let args := args.append (state.includeFolders.flatMap (fun s => ["-include", s]) )
    let args := args.append state.configArguments
    let args := "-serializedOutput"::args

    let arguments := s!".lake/build/bin/Format.exe {String.join (args|>.intersperse " ")}"
    -- IO.println s!"command: {arguments}"
    -- let child :ChildI ← IO.Process.spawn {cmd := "lake", args := ("exe" :: "Format" :: args).toArray, stdout := .piped, stderr := .piped, stdin := .null}
    -- let child :ChildI ← IO.Process.spawn {cmd := "lake", args := ("exe" :: "Format" :: args).toArray, stdout := .piped, stderr := .piped, stdin := .null}
    -- let child :ChildI ← IO.Process.spawn {cmd := "cat", args := (args).toArray, stdout := .piped, stderr := .piped, stdin := .null}
    -- let child :ChildI ← IO.Process.spawn {cmd := "cmd", args := ["/c", "echo", "findable.txt"].toArray, stdout := .piped, stderr := .piped, stdin := .null}
    let child :ChildI ← IO.Process.spawn {cmd := ".lake/build/bin/Format.exe", args := args.toArray, stdout := .piped, stderr := .piped, stdin := .null}
    -- let child ← spawn { cmd := "cmd.exe", args := #["/c", "echo", "1 1"], stdout := .piped, stderr := .piped, stdin := .null }

    -- Start reading the output from child processes, to avoid child processes being blocked by writing to a buffer that is not being cleared
    let readOutput ← IO.asTask (IO.FS.Handle.readToEnd (child.stdout)) Task.Priority.dedicated
    let readError ← IO.asTask (IO.FS.Handle.readToEnd (child.stderr)) Task.Priority.dedicated

    let state := {
      state with
      remainingFiles := state.remainingFiles.drop state.filesPrWorker
      running := {process:=child, arguments := arguments, timeOutAtNs := (← IO.monoNanosNow) + 300 * 1000_000_000, outputStream := readOutput, errorStream := readError} :: state.running
    }

    state.startUpToNProcesses
  else
    return state


def RunnerState.isDone (state : RunnerState) : Bool := state.running.length == 0 && state.remainingFiles.length == 0

/--
Run workers in parallel to speed-up formatting files
the speed-up is partially due to running in parallel
but primarily due to reducing the memory pressure caused by parsing files (Which means we are primarily hiding memory leaks)
-/
partial def RunnerState.delegateWork (state : RunnerState) : IO RunnerState := do
  if state.isDone then
    return state
  else
    let state ← state.startUpToNProcesses
    let state ← state.waitUntilAtLeastOneProcessIsDone
    state.delegateWork

-- #eval do
--   let a : RunnerState := {remainingFiles := ["a.lean"]}
--   let res ← a.delegateWork 2
--   return res.results.serialize

-- def maina : IO Unit := do
--   -- IO.println "simple"
--   let child ← spawn { cmd := "lake", args := #["exe", "Format"], stdin :=.null, stderr := .piped, stdout:=.piped}
--   -- let child ← spawn { cmd := "cmd.exe", args := #["/C", "echo.exe", "hello world"], stdin :=.null, stderr := .piped, stdout:=.piped}

--   IO.sleep 1

--   let result ← child.tryWait
--   match result with
--   | some code =>
--     IO.println s!"Exited with code {code}"
--     let s ← IO.FS.Handle.readToEnd child.stdout
--     let e ← IO.FS.Handle.readToEnd child.stderr
--     IO.println s!"s:{s} {e}"
--   | none      => IO.println "Still running!"

-- #eval maina

unsafe def formatFolder (folderName : String) (args : InputArguments) (cleanedArguments : List String) : IO (List (FormatReport)) := do
  let files ← findAllLeanFilesInProject folderName
  let before ← IO.monoNanosNow
  let r : RunnerState := {
    maxWorkers := args.workers
    filesPrWorker := args.filesPrWorker
    remainingFiles := files
    includeFolders := args.includeFolders
    configArguments := cleanedArguments
  }
  let r ← r.delegateWork
  let after ← IO.monoNanosNow
  IO.println s!"Total time: {((after-before).toFloat / 1000_000_000)}s"
  IO.println s!"error files: {r.errs |>.intersperse "\n" |> String.join}"

  return [r.results]
  -- let mut report' : FormatReport := {}
  -- for file in files do
  --   IO.println s!"before {file}"
  --   let (_, report) ← formatFile file args
  --   report' := report'.combineReports report
  --   -- reports := report::reports
  -- return [report']

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

def nanoToS (ns:Nat) : Float :=
  (ns.toFloat) / 1000000000.0

def printReport (report : FormatReport) : IO Unit := do
  IO.println s!"Managed to format {report.formattedCommands} out of commands {report.totalCommands}"

  IO.println s!"Time readAndParse: {nanoToS report.timeReadAndParse} pf: {nanoToS report.timePF} doc: {nanoToS report.timeDoc} reparse: {nanoToS report.timeReparse}"
  IO.println s!"Missing Formatters ({report.missingFormatters.keys.length}):"
  let sortedList := report.missingFormatters.toArray |>.insertionSort (fun (_,a) (_,b) => a < b) |>.reverse
  for (formatter, count) in sortedList do
    IO.println s!"missing formatter for: {formatter} ({count})"


def printUsage : IO Unit := do
  IO.println "Usage: reformat -file <file> -folder <folder> -o <outputFileName> -noWarnCST -debugSyntax -debugSyntaxAfter -debugErrors -debugMissingFormatters -debugPPL -warnMissingFormatters -lineLength <length>"

-- #eval FormatReport.deserialize "22,22,924900,5504600,463198000,70178900,Lean.guardMsgsCmd;:;:;PrettyFormat.┬½term_<_>_┬╗;:;:;Lean.Parser.Term.letDecl;:;:;┬½term#[_,]┬╗;:;:;PrettyFormat.┬½term_<$$>_┬╗;:;:;str;:;:;Lean.Parser.Term.letRecDecl;:;:;Lean.Parser.Term.cdot;:;:;Lean.Parser.Command.eoi;:;:;┬½termΓêà┬╗;:;:;formatCmd;:;:;PrettyFormat.┬½term_<>_┬╗;:;:;Lean.Parser.Term.structInstLVal;:;:;PrettyFormat.┬½term_<?_┬╗"

unsafe def main (originalArgs : List String) : IO (Unit) := do
  -- let (_,coreEnv) ← parseModule (← IO.FS.readFile "PrettyFormat/CoreFormatters.lean") "PrettyFormat/CoreFormatters.lean"
  -- let _ ← coreEnv.displayStats
  -- let a := pFormatAttr.getValues coreEnv `Lean.Parser.Command.declId
  -- IO.println s!"found formatters: {a.length}"

  let inputArgs := parseArguments originalArgs

  -- initSearchPath (← findSysroot)
  match inputArgs with
  | Except.error e =>
    IO.println e
    printUsage
  | Except.ok args => do

    initSearchPath (← findSysroot) (args.includeFolders.map (fun c => FilePath.mk c))

    match args.files with
    | some files => do
      for file in files do
        let (_,report) ← (formatFile file args)
        if args.serializedOutput then
          IO.println s!"serialized: {report.serialize}"
        else
          printReport report

    | none => match args.folder with
      | some folder => do
        let reports ← formatFolder folder args (cleanArguments originalArgs)
        let combined := reports.foldl (fun acc report => report.combineReports acc) {}

        if args.serializedOutput then
          IO.println s!"serialized: {combined.serialize}"
        else
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


-- #eval measureTime (fun _ => main3)


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


-- declare_syntax_cat fmtCase
-- syntax num : fmtCase
-- syntax "| " term " => " term: fmtCase
-- syntax "| " term " => " term fmtCase: fmtCase


-- syntax (name:=coreFmCmd)"#coreFm " ident fmtCase : command


-- initialize IO.println "helllo"

-- macro_rules
-- | `(#coreFm $i:ident $a:fmtCase) =>
--   -- `(initialize IO Unit := IO.mkref fun a => 2)
--   -- let ccc := match a with
--   -- | `("| " $a:term " => " $b:term) => 2
--   -- | _ => 3

--   `(initialize IO.println "some commend??aarst")


-- #coreFm name
-- | `($a + $b) => IO.println "what"


-- macro_rules
-- | `($a + $b) => `(println! "matched addition!")


-- macro_rules
-- | `(command | #coreFmt ppline ($a:term) ) => `("matched repeated addition")

-- #eval 1 + 2
