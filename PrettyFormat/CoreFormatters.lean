import Lean
import PrettyFormat
import BaseFormatter
import Lean.Language.Lean
import Lean.Util.Profile
import Lean.Server.References
import Lean.Util.Profiler

open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open Lean.Elab
open System
open Frontend


partial def getCommands (cmds : Syntax) : StateT (Array Syntax) Id Unit := do
  if cmds.getKind == nullKind || cmds.getKind == ``Parser.Module.header then
    for cmd in cmds.getArgs do
      getCommands cmd
  else
    modify (·.push cmds)

partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ _ args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.line.joinSep args

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

def printCommands (cmds : Syntax) : CoreM Unit := do
  for cmd in getCommands cmds |>.run #[] |>.2 do
    try
      IO.println (← ppCommand ⟨cmd⟩).pretty
    catch e =>
      IO.println f!"/-\ncannot print: {← e.toMessageData.format}\n{reprint cmd}\n-/"

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode



def prettyPrintSourceInfo : SourceInfo → String
  | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) => s!"leading:{leading} pos: {pos} trailing: {trailing} endPos: {endPos}"
  | .synthetic (pos : String.Pos) (endPos : String.Pos) (canonical) => s!"synthetic: pos:{pos} endPos: {endPos}: cannonical: {canonical}"
  | .none => "nosource"


partial def prettyPrintSyntax : Syntax → String
  | .missing => "missing"
  | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    (args.map prettyPrintSyntax |>.toList |> " ".intercalate)
  | .atom (info : SourceInfo) (val : String) => s!"{val}"
  | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) => s!"{val}"



-- source reformat.lean
def parseModule (input : String) (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
    IO <| (Array CommandSyntax × Environment) := do
  -- let mainModuleName := Name.anonymous -- FIXME
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx


  IO.println s!"{prettyPrintSyntax header}"
  -- printall error messages and exit
  if messages.hasErrors then
    for msg in messages.toList do
      IO.println s!"{← msg.toString}"
    failWith "error in header"
  else
    IO.println "no errors in header"
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  -- let env := env.setMainModule mainModuleName

  if messages.hasErrors then
    for msg in messages.toList do
      IO.println s!"{← msg.toString}"
    failWith "error in process header"
  else
    IO.println "no errors in process header"
  -- let env0 := env
  let s ← IO.processCommands inputCtx parserState -- TODO: learn about this line
    { Command.mkState env messages opts with infoState := { enabled := true } }

  let topLevelCmds : Array CommandSyntax ← extractTopLevelCommands s

  return (#[{ env := s.commandState.env, options:= opts, stx := header : CommandSyntax }] ++ topLevelCmds, s.commandState.env)

def parseModule' (fileName : String) (opts : Options) : IO (Array CommandSyntax × Environment):= do
  let input ← IO.FS.readFile fileName
  parseModule input fileName opts

partial def interpretFormat' (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) (commandState : Command.State) (old : Option IncrementalState) (n:Nat): IO Unit := do
  if n == 0 then
    return ()
  IO.println s!"{commandState.traceState.traces.size}"
  IO.println s!"next macro scope{commandState.nextMacroScope}"
  IO.println s!"size of tree:{commandState.infoState.trees.size}"
  let run : IncrementalState ← IO.processCommandsIncrementally inputCtx parserState commandState old
  let s : Frontend.State := run.toState
  let st :=s.commandState
  let aa:InfoTree := st.infoState.trees.toArray.get! 0

  match aa with
  | InfoTree.context (a:Lean.Elab.PartialContextInfo) (b:InfoTree) =>

    IO.println "works!"
  | _ => IO.println "unknown"

  -- match aa with
  -- | context => IO.println "ctx"
  -- /-- The children contain information for nested term elaboration and tactic evaluation -/
  -- | node => IO.println "node"
  -- /-- The elaborator creates holes (aka metavariables) for tactics and postponed terms -/
  -- | hole => IO.println "hold"

  -- match aa with
  -- |



  IO.println s!"pos:{run.commands.size}"
  interpretFormat' inputCtx run.parserState run.commandState run (n - 1)

  -- getPFLineLength  run.parserState.
  -- commandState.infoState.trees[commandState.infoState.trees.size - 1]
  return ()

-- partial def testFrontEnd : FrontEnd :=

partial def processCommandsIncrementally (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (commandState : Command.State)
    (old? : Option IncrementalState) :
    BaseIO IncrementalState := do
  let task ← Language.Lean.processCommands inputCtx parserState commandState
    (old?.map fun old => (old.inputCtx, old.initialSnap))
  go task.get task #[]
where
  go initialSnap t commands :=
    let snap := t.get
    let commands := commands.push snap.data.stx
    if let some next := snap.nextCmdSnap? then
      go initialSnap next.task commands
    else
      -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
      -- all snapshots
      let messages := Lean.Language.ToSnapshotTree.toSnapshotTree initialSnap
        |>.getAll.map (·.diagnostics.msgLog)
        |>.foldl (· ++ ·) {}
      let trees := Lean.Language.ToSnapshotTree.toSnapshotTree initialSnap
        |>.getAll.map (·.infoTree?) |>.filterMap id |>.toPArray'
      return {
        commandState := { snap.data.finishedSnap.get.cmdState with messages, infoState.trees := trees }
        parserState := snap.data.parserState
        cmdPos := snap.data.parserState.pos
        inputCtx, initialSnap, commands
      }

def processPartialContext (t : PartialContextInfo) : String :=
  match t with
  | .commandCtx (info : CommandContextInfo) =>
    let opt := info.options.getNat `pf.lineLength
    s!"{opt}"
  | .parentDeclCtx (parentDecl : Name) => s!"parent decl {parentDecl}"

def processInfoTree (t : InfoTree) : String :=
  match t with
  | InfoTree.context i subTree =>
      s!"Context node with PartialContextInfo and subtree: {processInfoTree subTree} maybe option? {processPartialContext i}"
  | InfoTree.node i children =>
      s!"Node with info and {children.size} children"
  | InfoTree.hole mvarId =>
      s!"Hole with MVarId: {mvarId.name}"

def interpretFormat (input : String) (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
    IO <| (Environment) := do
  let mainModuleName := Name.anonymous -- FIXME
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName
  let env0 := env
  let s ← IO.processCommands inputCtx parserState -- TODO: learn about this line
    { Command.mkState env messages opts with infoState := { enabled := true } }



  let x := s.commandState.infoState.trees.toArray[0]!
  IO.println s!"{processInfoTree x}"
  -- let y := x.context
  -- match y with
  -- | (commandCtx { env, currNamespace, openDecls, .. }) (a) =>
  --   IO.println s!"{openDecls.size}"
  -- match x.context with
  -- | commandCtx (info : CommandContextInfo) => IO.println s!"{info.openDecls.size}"
  -- | parentDeclCtx (parentDecl : Name) => IO.println s"parent decl {parentDecl}"
  -- s.commandState.infoState.trees.
  -- x.findInfo?


  -- let a ← IO.processCommandsIncrementally inputCtx parserState
  --   { Command.mkState env messages opts with infoState := { enabled := true } } none
  let a ← interpretFormat' inputCtx parserState
    { Command.mkState env messages opts with infoState := { enabled := true } } none 100

  IO.println s!"what?{s.commandState.infoState.trees.size}"

  -- let topLevelCmds : Array CommandSyntax ← s.commandState.infoState.trees.toArray.mapM fun
  --   | InfoTree.context i
  --       (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
  --       match i with
  --       | .commandCtx { env, currNamespace, openDecls, .. } =>
  --         pure {env, currNamespace, openDecls, stx}
  --       | _ =>
  --         failWith "not a commandCtx"
  --   | _ =>
  --     failWith "unknown info tree"
  return (env)


-- def getStx : FormatPPLM Syntax:= do
--   let state ← get
--   pure state.stx

-- def updateStx (stx: Syntax) : FormatPPLM Unit:= do
--   let state ← get
--   let _ ← set {state with stx := stx}
--   pure ()

def genId : RuleM String := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  pure (s!"v{state.nextId}")

def blank : Rule
| stx => do
  pure (text "")

def nullNode : Syntax := Syntax.node (Lean.SourceInfo.none) `null #[]


partial def addSpaceOrNewLine (stx: Syntax) : RuleM PPL := do
  return (text " " <^> PPL.nl) <> (← pf stx)

partial def followWithSpaceIfNonEmpty (ppl : PPL) : PPL :=
  if isEmpty [] ppl then
    text ""
  else
    ppl <> (text " ")


/-
function declaration
-/

#fmt Lean.Parser.Command.declaration fun
| s =>
  pfCombine s

partial def pfDeclId :Rule
| args => do
  -- optionally insert a new line before the next line
  let first ← pf (args[0]!)
  let var1 ← genId
  let var2 ← genId
  let rest ← pfCombine (args.toList|>.drop 1|>.toArray)

  return text " " <> PPL.letExpr var2 rest (PPL.letExpr var1 first ((v var1 <> v var2) <^> ((v var1 <$> v var2)))) <> text " "


#fmt Lean.Parser.Command.declId pfDeclId


#fmt Lean.Parser.Command.optDeclSig fun
| #[arguments, returnVal] => do
  let returnVal ← (pf returnVal)
  let args ← (pfCombineWithSeparator (text " " <^> PPL.nl) arguments.getArgs)
  if isEmpty [] returnVal then
    return args
  else
    return args <> (text " "<^> PPL.nl) <> (followWithSpaceIfNonEmpty returnVal)
| _ => failure


#fmt Lean.Parser.Command.declVal fun
| args => do
  if args.size == 0 then
    return text ""
  else
    return (← pfCombineWithSeparator (text " ") args)


#fmt Lean.Parser.Term.typeSpec fun
|a => pfCombineWithSeparator (text " ") a


#fmt Lean.Parser.Command.definition fun
| args => do
  return PPL.nest 2 (← (pfCombineWithSeparator ((text "") <^> PPL.nl) args))


#fmt Lean.Parser.Command.declValSimple fun
| a => pfCombineWithSeparator PPL.nl a


#fmt Lean.Parser.Term.explicitBinder fun
-- | args => do
--   -- no spacing between parenthesis and the first and last character in the binder
--   let first := args.get! 0
--   let last := args.get! (args.size - 1)
--   let rest := args.extract 1 (args.size - 2)
--   return (← pf first) <>(← pfCombineWithSeparator (text " ") rest) <> (← pf last)
| #[firstParen, vars, typeDecl, unknown1, lastParen] => do
  let _ ← assumeMissing unknown1
  return (← pf firstParen)
    <> (← pfCombineWithSeparator (text " ") vars.getArgs)
    <> text " "
    <> (← pfCombineWithSeparator (text " ") typeDecl.getArgs)
    <>(← pf lastParen)
| _ => failure


#fmt Lean.Parser.Module.header fun
| s => pfCombine s


#fmt Lean.Parser.Module.import fun
| args => do
  return (← pfCombineWithSeparator (text " ") args) <> PPL.nl


#fmt Lean.Parser.Command.declModifiers fun
| args => do
  let mut modifiers ← pfCombineWithSeparator (text " ") args
  if !isEmpty [] modifiers then
    modifiers := modifiers <> text " "
  return modifiers

/-
let operator
-/

#fmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, unknown1, after] => do
  let _ := (← assumeMissing unknown1)
  return (← pf letSymbol) <> text " " <> (← pf declaration) <> (← pf unknown1) <> PPL.nl <> (← pf after)
| _ => failure


#fmt Lean.Parser.Term.letIdDecl fun
| #[var, unknown1, typeInfo, assignOperator, content] => do
  let _ := (← assumeMissing unknown1)
  -- return (← pf var) <> text " " <> (← pf unknown1) <> (← pf typeInfo) <> (← pf assignOperator) <> (← nest 2 (do (text " " <^> PPL.nl)<>(← pf content)))
  return (← pf var) <> text " " <> (← pf unknown1) <> (followWithSpaceIfNonEmpty (← pf typeInfo)) <> (← pf assignOperator) <> (← nest 2 (addSpaceOrNewLine content))
| a => do
  failure

-- TODO: figure out what the suffix is used for.

#fmt Lean.Parser.Termination.suffix fun
| #[unknown1, unknown2] => do
  let _ := (← assumeMissing unknown1)
  let _ := (← assumeMissing unknown2)
  return text ""
| a => do
  failure


#fmt Lean.Parser.Term.app fun
| #[functionName, arguments]  => do
  return (← pf functionName) <> text " " <> (← pfCombineWithSeparator (text " ") arguments.getArgs)
| _ => failure

-- initialize registerCoreFormatter `Lean.Parser.Term.app fun
--   | #[a] => do return text "app?"
--   | _ => failure

-- #fmt Lean.Parser.Term.app fun
--   | #[a] => do return text "app?"
--   | _ => failure

@[pFormat Lean.Parser.Command.declId]
def formatLetIdDecl : Rule
  | a => return text "hello"



#eval IO.println "hello"
-- #eval isEmpty [] (text ""<>text "")
