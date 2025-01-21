import Lean
import PrettyFormat

open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open System


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

structure CommandSyntax where
  env : Environment
  currNamespace : Name := Name.anonymous
  openDecls : List OpenDecl := []
  stx : Syntax


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
  let mainModuleName := Name.anonymous -- FIXME
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName
  let env0 := env
  let s ← IO.processCommands inputCtx parserState -- TODO: learn about this line
    { Command.mkState env messages opts with infoState := { enabled := true } }
  let topLevelCmds : Array CommandSyntax ← s.commandState.infoState.trees.toArray.mapM fun
    | InfoTree.context i
        (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
        match i with
        | .commandCtx { env, currNamespace, openDecls, .. } =>
          pure {env, currNamespace, openDecls, stx}
        | _ =>
          failWith "not a commandCtx"
    | _ =>
      failWith "unknown info tree"
  return (#[{ env := env0, stx := header : CommandSyntax }] ++ topLevelCmds, env)


-- def getStx : formatPPLM Syntax:= do
--   let state ← get
--   pure state.stx

-- def updateStx (stx: Syntax) : formatPPLM Unit:= do
--   let state ← get
--   let _ ← set {state with stx := stx}
--   pure ()

def genId : formatPPLM String := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  pure (s!"v{state.nextId}")

def blank : formatPPL
| stx => do
  let state ← get
  pure (text "")

-- @[format `Lean.Parser.Term.letIdDecl]

/--
At the moment I assume there is a pretty general solution for this problem

challenges
- (easy) I want to handle match statements
- I want to split
-/





-- unsafe def main (args : List String) : IO Unit := do
--   let [fileName] := args | failWith "Usage: reformat file"
--   initSearchPath (← findSysroot)
--   let input ← IO.FS.readFile fileName
--   let moduleStx ← parseModule input fileName
--   let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
--   let mut first := true
--   for {env, currNamespace, openDecls, ..} in moduleStx, stx in leadingUpdated do
--     if first then first := false else IO.print "\n"
--     let _ ← printCommands stx |>.toIO {fileName, fileMap := FileMap.ofString input, currNamespace, openDecls} {env}

-- #eval do
--   let _ ← main ["./test.lean"]



-- #eval main2 ["./test.lean"]

-- elab "runMeta" : command =>
--   runMeta do
--     let expr ← mkFreshExprMVar none
--     logInfo m!"Created a fresh expression: {expr}"

def nullNode : Syntax := Syntax.node (Lean.SourceInfo.none) `null #[]

@[pFormat Lean.Parser.Term.letIdDecl]
def formatLetIdDecl : formatPPL
  | #[varName, probablyDecl, probablyDecl2, assignAtom, value] => do
    if (probablyDecl == nullNode) && probablyDecl2 == nullNode then
      -- return ((← (pf varName)) <> text " " <> (← pf assignAtom) <> (← nest 2 do
      --     let formattedValue ← pf value
      --     return (text " " <^> nl) <> formattedValue)
      --     )
      return text ""
    else
      failure
  | _ => failure

@[pFormat Lean.Parser.Command.declaration]
def formatDeclaration : formatPPL := pfCombine

partial def pfDeclId :formatPPL
| args => do
  -- optionally insert a new line before the next line
  let first ← pf (args[0]!)
  let var1 ← genId
  let var2 ← genId
  let rest ← pfCombine (args.toList|>.drop 1|>.toArray)

  return PPL.letExpr var2 rest (PPL.letExpr var1 first ((v var1 <> v var2) <^> ((v var1 <$> v var2)))) <> text " "

@[pFormat Lean.Parser.Command.declId]
def formatDeclId : formatPPL := pfDeclId

@[pFormat Lean.Parser.Command.optDeclSig]
def formatOptDeclId : formatPPL := pfDeclId

@[pFormat Lean.Parser.Command.definition]
def formatDefinition : formatPPL
| args => do
  return PPL.nest 2 (← (pfCombineWithSeparator ((text " ") <^> nl) args))

@[pFormat Lean.Parser.Command.declValSimple]
def formatDeclValSimple : formatPPL := pfCombineWithSeparator nl

@[pFormat Lean.Parser.Term.let]
def formatLet : formatPPL
| args => do
  return nl <> (← pfCombine args)

@[pFormat Lean.Parser.Module.header]
def formatHeader : formatPPL := pfCombineWithSeparator nl

@[pFormat Lean.Parser.Module.import]
def formatImport : formatPPL
| args => do
  return (← pfCombineWithSeparator (text " ") args) <> nl




-- #eval isEmpty [] (text ""<>text "")
