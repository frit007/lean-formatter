import Lean

open Lean
open Lean.Parser
open Lean.Elab
open Frontend
open Command PrettyPrinter
open Lean Meta
-- parseCommand throws comments away :/

set_option diagnostics true

/--
  Doc comments are kept
-/
def prettyPrintSourceInfo : SourceInfo → String
  | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) => s!"original l:{leading} pos: {pos} trailing: {trailing} endPos: {endPos}"
  | .synthetic (pos : String.Pos) (endPos : String.Pos) (canonical) => s!"synthetic: pos:{pos} endPos: {endPos}: cannonical: {canonical}"
  | .none => "none"


partial def prettyPrint : Syntax → String
  | .missing => "missing"
  | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    (args.map prettyPrint |>.toList |> " ".intercalate) ++ prettyPrintSourceInfo info
  | .atom (info : SourceInfo) (val : String) => s!"{val}"
  | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) => s!"{val}"



def printCommand  : FrontendM Unit := do
  let s <- get
  IO.println s!"cmdPos? {s.cmdPos}"
  let _ <- processCommand
  let s <- get
  IO.println s!"the command! {prettyPrint s.commands[0]!}"
  let lastCommand := s.commands[s.commands.size -1]!
  IO.println s!"?? {prettyPrint lastCommand}"
  pure ()

-- Function to get the syntax of an entire file
def parseFile (filePath : System.FilePath) : IO Unit :=
  do
    -- Read the file content
    let fileContent ← IO.FS.readFile filePath
    -- Parse the file content into syntax
    let inputCtx := Parser.mkInputContext fileContent filePath.toString

    IO.println s!"{inputCtx.fileMap.positions}"

    -- let inputCtx := mkInputContext contents fname
    let (header, state, messages) ← parseHeader inputCtx
    IO.println s!"header {prettyPrint header} {state.pos}"

    let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx
    -- (printCommand {inputCtx := inputCtx}.run'

    let mainModuleName := Name.anonymous -- FIXME
    let env := env.setMainModule mainModuleName

    let _ <- (printCommand {inputCtx := inputCtx}).run {commandState := mkState env, parserState:=state, cmdPos:= 0 }

    pure ()

def parseMaybe (filePath: System.FilePath) : IO Unit := do
  let mainModuleName := Name.anonymous -- FIXME
  let fileContent ← IO.FS.readFile filePath
  let inputCtx := Parser.mkInputContext fileContent filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx 1024
  let env := env.setMainModule mainModuleName
  let env0 := env

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode

structure CommandSyntax where
  env : Environment
  currNamespace : Name := Name.anonymous
  openDecls : List OpenDecl := []
  stx : Syntax

def parseModule (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
    IO <| Array CommandSyntax := do
  let mainModuleName := Name.anonymous -- FIXME
  let fileContent ← IO.FS.readFile <| System.FilePath.mk fileName
  let inputCtx := Parser.mkInputContext fileContent fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName
  let env0 := env
  let s ← IO.processCommands inputCtx parserState
    { Command.mkState env messages opts with infoState := { enabled := true } }
  let topLevelCmds : Array CommandSyntax ← s.commandState.infoState.trees.toArray.mapM fun
    | InfoTree.context i
        (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
        match i with
        | .commandCtx { env, currNamespace, openDecls, .. } =>
          pure {env, currNamespace, openDecls, stx}
        | _ =>
          failWith "unknown info tree"
    | _ =>
      failWith "unknown info tree"

  IO.println "Hello ?"
  -- let x := topLevelCmds[0]!

  return #[{ env := env0, stx := header : CommandSyntax }] ++ topLevelCmds

def parseFileEverything (inputCtx: InputContext) (modCtx: ParserModuleContext) (state: ModuleParserState) (msgs : MessageLog) (gas :Nat): IO (List Syntax) :=
  match gas with
  | 0 => return []
  | n +1 =>
    do
      match Parser.parseCommand inputCtx modCtx state msgs with
      | (stx, state, msgs) =>
        IO.println s!"syntax{stx}"
        if isTerminalCommand stx then
          return []
        else
          let c ← parseFileEverything inputCtx modCtx state msgs n
          return stx::c

def parseFileEverythingIntro (filePath: System.FilePath): IO (List Syntax) :=
  do
    -- Read the file content
    let fileContent ← IO.FS.readFile filePath
    -- Parse the file content into syntax
    let inputCtx := Parser.mkInputContext fileContent filePath.toString
    -- let inputCtx := mkInputContext contents fname
    let (header, state, messages) ← parseHeader inputCtx
    let env ← Lean.mkEmptyEnvironment --

    parseFileEverything inputCtx { env := env, options := {} } state messages 8
    -- match Parser.parseCommand inputCtx { env := env, options := {} } state messages with
    -- | (stx, state, msgs) =>
    --   IO.println s!"syntax{stx}"
    --   return stx

-- Example usage


-- def a (b:String) (c:String) :=
--   b ++c
-- #reduce PrettyPrinter.ppExpr a

-- #eval do
--   let filePath := "./test.lean"
--   let s ← parseModule filePath {} 1024
  -- let s := match s[0]? with
  -- | some x =>
  --   prettyPrint (x.stx)
  -- | none =>
  --   "err"
  -- IO.println s
  -- let first ← s[0]?
  -- IO.println <| prettyPrint (first.stx)
  -- let _ ← s.forM (fun c w => IO.println <| prettyPrint (c.stx))
  -- let first := s.forM

-- #eval do
--   let filePath := System.FilePath.mk "./test.lean"
--   let s ← parseFile filePath

  -- IO.println s!"Parsed s:\n{s}"
