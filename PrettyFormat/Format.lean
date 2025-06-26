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
  cst : Option String := none
  workers : Nat := 4
  filesPrWorker : Nat := 7
  output : PPLOutput := PPLOutput.copy ".formatted" -- TODO: This must change to replace, when the formatter is reliable
  includeFolders : List String := []
  opts : Options := {}
  serializedOutput : Bool := false


def parseArguments (args:List String) : Except String InputArguments := do
  match args with
  | [] =>
    let a : InputArguments := {}
    let a := {a with opts := a.opts.setBool `pf.debugMode false}

    return a
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
  | "-debugNoSolution"::xs =>
    let res ← parseArguments xs
    return { res with  opts := (res.opts).setBool `pf.debugNoSolution true }
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
  | "-cst"::cst::xs =>
    return { (←  parseArguments xs) with  cst := cst }
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
  let mut formatted := ""
  let mut report : FormatReport := {}


  for a in leadingUpdated do
    let formatters ← getFormatters env
    let result ← pfTopLevelWithDebug a env formatters options fileName

    formatted := formatted ++ ((← result.reportAsComment) ++ result.formattedPPL) ++ "\n\n"
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

  let now ← IO.monoNanosNow
  for p in state.running do
    let child := p.process
    if p.timeOutAtNs < now then
      IO.println s!"kill {p.arguments}"
      let output ← IO.ofExcept p.outputStream.get
      IO.println s!"it would have the following output {output}"
    else
      match ← child.tryWait with
      | some code =>
        let output ← IO.ofExcept p.outputStream.get

        let serializedString := "serialized: "
        let updatedResults := output.split (fun c => c == '\n')
          |>.filter (fun s => s.startsWith serializedString)
          |>.map (fun s => s.drop serializedString.length)
          |>.foldl (fun acc s => (FormatReport.deserialize s).combineReports acc) state.results

        let stderr ← IO.ofExcept p.errorStream.get
        if stderr != "" then
          IO.println s!"err ({p.arguments})\n: {stderr}"

        IO.println s!"all: {output}"

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
    IO.sleep 10
    state.waitUntilAtLeastOneProcessIsDone

partial def RunnerState.startUpToNProcesses (state : RunnerState) : IO RunnerState := do
  if state.running.length < state.maxWorkers && state.remainingFiles.length > 0 then

    let args := state.remainingFiles.take state.filesPrWorker |>.flatMap (fun s => ["-file", s.replace "\\" "/"])
        let args := args.append (state.includeFolders.flatMap (fun s => ["-include", s]) )
    let args := args.append state.configArguments
    let args := "-serializedOutput"::args

    let exe := if System.Platform.isWindows then ".lake/build/bin/ProjectFormat.exe" else ".lake/build/bin/ProjectFormat"
    let arguments := s!"{exe} {String.join (args|>.intersperse " ")}"
    let child :ChildI ← IO.Process.spawn {cmd := exe, args := args.toArray, stdout := .piped, stderr := .piped, stdin := .null}

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
  IO.println "Usage: reformat -file <file> -folder <folder> -o <outputFileName> -noWarnCST -debugSyntax -debugSyntaxAfter -debugErrors -debugMissingFormatters -debugNoSolution -warnMissingFormatters -lineLength <length>"

def formatSyntax (cst:String) (inputArgs : InputArguments): IO (Unit) := do
  -- IO.println s!"path:{cst}"
  let cst ← IO.FS.readFile cst
  -- IO.println s!"cst:{cst}"
  let stx := Base64.decodeSyntax cst
  -- IO.println s!"stx:{stx}"
  let opts := inputArgs.opts
  let coreFormatters : Name → (Option Rule) ← getCoreFormatters
  let formatters := [coreFormatters]

  let ((doc, state), _) ← measureTime (fun _ => do
    return pfTopLevel stx formatters)
  let (formattedPPL, _) ← measureTime (fun _ => do
    return doc.prettyPrint DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPageWidth opts) (computationWidth := PrettyFormat.getComputationWidth opts)
  )
  -- IO.println ("formatedppl:::"++formattedPPL)
  IO.println (Base64.encode64Str formattedPPL)
  return

unsafe def formatMain (originalArgs : List String) : IO (Unit) := do

  let inputArgs := parseArguments originalArgs

  match inputArgs with
  | Except.error e =>
    IO.println e
    printUsage
  | Except.ok args => do

    initSearchPath (← findSysroot) (args.includeFolders.map (fun c => FilePath.mk c))
    match args.cst with
    | some cst =>
      formatSyntax cst args
    | _ =>
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
