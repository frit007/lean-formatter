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

structure InputArguments where
  fileName : Option String := none
  folder : Option String := none
  outputFileName : Option String := none
  opts : Options := {}

def parseArguments (args:List String) : Except String InputArguments := do
  match args with
  | [] => return {}
  | "-o"::outputFileName::xs =>
    return { (← parseArguments xs) with outputFileName := outputFileName }
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
  | "-fileName"::fileName::xs =>
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

def formatASingleFile (fileName : String) (args : InputArguments) : MetaM Unit := do
  initSearchPath (← findSysroot)
  IO.println "loading file ???"
  let input ← IO.FS.readFile (fileName++".lean")
  IO.println "loading file !!!"

  let (moduleStx, env) ← parseModule input fileName
  let options := args.opts
  IO.println (getPFLineLength options)
  let values := pFormatAttr.getValues env `«arith_+_»

  IO.println s!"lengths? {values.length}"

  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let withComments := introduceCommentsToTheCST leadingUpdated

  -- The Env of the program that reformats the other program. In case that the formatted code does not include the standard annotations
  let currentEnv := ← getEnv
  -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
  let initialState : FormatState := {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
  let introduceContext := ((pfCombineWithSeparator (PPL.nl<>PPL.nl) leadingUpdated).run { envs:= [currentEnv, env], options:= options})

  let introduceState := introduceContext.run initialState
  let (ppl, state) := introduceState.run
  IO.FS.writeFile (fileName++".lean.syntax") (s!"{leadingUpdated}")

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


def main (args : List String) : IO (Unit):= do
  let env ← importModules #[{module := `Init}] {}  -- Load Lean’s core environment

  -- Get all declarations with `myAttr`
  let a ← coreFormatters.get
  let formatter ← getCoreFormatter `Lean.Parser.Term.app
  let _ ← IO.println s!"{a.size}"

  let decls := (pFormatAttr.getValues env `Lean.Parser.Term.letIdDecl)
  let _ ← IO.println s!"{decls.length}"

#eval main ["hello"]

def main2 (args : List String) : MetaM (Unit):= do
  -- Get all declarations with `myAttr`
  let decls := (pFormatAttr.getValues (← getEnv) `Lean.Parser.Term.letIdDecl)
  let _ ← IO.println s!"{decls.length}"

#eval main2 ["hello"]

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


-- unsafe def mainWithInfo (kind: SyntaxNodeKind) (args : List String) : MetaM (Array Syntax) := do
--   let x ← mainOutputPPL args
--   let info ← tellMeAbout kind x
--   IO.println s!"parts {info.size}"
--   return info


-- #eval mainWithInfo `Lean.Parser.Term.letIdDecl ["./test"]

-- #eval mainOutputPPL ["./test"]
--
-- #eval mainOutputPPL ["./../tmp/greeting-lean/Main"]

-- #eval mainOutputPPL ["../../lean4/src/Init/Coe"]

-- #eval findAllLeanFilesInProject "../../lean4/src"

-- #eval mainOutputPPL ["./test"]

-- #eval mainInterpret ["./test"]

-- #eval mainOutputPPL ["./test_with_custom_syntax"]


syntax (name := formatCmd)
  "#format" ppLine command : command

@[command_elab formatCmd]
unsafe def elabFormatCmd : CommandElab
  | `(command|#format $cmd) => liftTermElabM do
    let env ← getEnv
    let opts ← getOptions
    let stx := cmd.raw
    let leadingUpdated := stx|>.getArgs
    let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [env], options := ← getOptions})
    let introduceState := introduceContext.run' {nextId := 0}
    let ppl := introduceState.run

    let doc := toDoc ppl
    let result := doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)

    logInfo s!"{result}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"


def findLineEnd (source:String) (pos:String.Pos) : String.Pos:= Id.run do
  let mut currentPos := pos
  while (source.get? currentPos).isSome do
    if (source.get! currentPos) == '\n' then
      return currentPos
    currentPos := source.next currentPos
  return currentPos

def extractLine (source:String) (pos:String.Pos) : String:= Id.run do
  let startOfLine := source.findLineStart pos
  let mut endOfLine := findLineEnd source pos
  let line := source.extract startOfLine endOfLine
  return line

partial def findStartOfDebugComment (source:String) (pos:String.Pos) : Option (String.Pos):= do
  let endPos ← findEndOfComment source (pos |> source.prev |> source.prev)
  let startPos ← findStartOfComment source (endPos |> source.prev)
  -- endPos
  -- match (← findStrPosRev source pos "DEBUG" (fun _ => true)) with
  -- | some c => some pos
  -- | _ => none
  -- findStrPosRev source pos "DEBUG" (fun _ => true)
  match strMatch source startPos "/-FORMAT DEBUG:" with
  | true => some startPos
  | _ => none
  -- startPos
where
  strMatch (source:String) (pos:String.Pos) (str:String) : Bool := Id.run do
    let mut currPos := pos
    let mut strPos := String.Pos.mk 0
    for _ in [0:str.length] do
      match source.get? (currPos) with
      | none => return false
      | some c => if c != str.get! strPos then return false
      currPos := source.next currPos
      strPos := str.next strPos
    return true

  findStrPosRev (source:String) (pos:String.Pos) (pattern:String) (allowed : Char → Bool) : Option (String.Pos) := do
    let p ← source.get? pos
    if allowed p then
      if strMatch source pos pattern then
        return pos
      else
        findStrPosRev source (source.prev pos) pattern allowed
    else
      none

  findEndOfComment (s:String) (pos:String.Pos) :Option (String.Pos):= do
    findStrPosRev s pos "-/" (fun c => c == '\n' || c == '\r' || c == ' ' || c == '-' || c == '/')

  findStartOfComment (s:String) (pos:String.Pos) :Option (String.Pos):= do
    findStrPosRev s pos "/-" (fun _ => true)

open CodeAction Server RequestM in
-- @[command_code_action]
@[command_code_action Lean.Parser.Command.declaration]
def formatCmdCodeAction : CommandCodeAction := fun p sn info node => do
  let .node i ts := node | return #[]

  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => return stx
    | _ => none

  -- let fileName ← getFileName
  -- p.textDocument.uri

  let opts := info.options
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
      let r :String.Range := stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!

      let source := info.fileMap.source
      let start := match findStartOfDebugComment source r.start with
        | some pos => pos
        | none => r.start
      let tail := r.stop


      let result ← pfTopLevelWithDebug (stx) [info.env] opts p.textDocument.uri

      let newText := result.reportAsComment ++ result.formattedPPL

      -- let newText := toDoc ppl |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
      -- let newText := "newText"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]



set_option pf.debugErrors 1

-- /--
-- info: def test (n :Nat):=
--   fail
--   fail
-- -/
-- #guard_msgs in
-- #format
-- def test (n:Nat) :=
--   add 2 3

-- set_option pf.debugSyntax 1
-- set_option pf.debugMissingFormatters 1
-- set_option pf.debugErrors 1
-- set_option pf.debugSyntaxAfter 1
-- set_option pf.debugPPL 1
-- #format

-- #fmt Lean.Parser.Term.app fun
-- | #[functionName, arguments]  => do
--   return (← pf functionName) <> text " " <> (← pfCombineWithSeparator (text " ") arguments.getArgs)
-- | _ => failure
-- @[pFormat Lean.Parser.Term.app]
-- def formatApp : Rule
-- | #[functionName, arguments]  => do
--   return (← pf functionName) <> text " " <> (← pfCombineWithSeparator (text " ") arguments.getArgs)
-- | _ => failure

def add (x y:Nat):Nat:=
  x + y


def test2 : Nat :=
  add 2 3
where
  add (x y:Nat):Nat:=
    x + y


private def b(y:Nat):Nat:=
  3 * y
