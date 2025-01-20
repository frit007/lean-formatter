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

/--
I want comments to be part of the AST
Ideally I would like to be able to move inline comments
maybe If I give comments an unique id it would be possible
In my opinion comments should be placed after if short
def t (x:Nat):Nat:=
  x + 2 -- short comment
but if the comment is too long then it should be moved before the line

def t (x:Nat):Nat:=
  -- A long comment that would exceed the width
  x + 2

And ideally these long comments should automatically be split into multiple lines
-/
def syntaxSourceInfo : Syntax → SourceInfo
| .missing => SourceInfo.none
| .node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) => info
| .atom   (info : SourceInfo) (val : String) => info
| .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) => info

namespace PreviousImplementation
partial def findPatternStartAux (s pattern : String) : Option String :=
  if s.length < pattern.length then none
  else if s.take pattern.length == pattern then some (s.drop pattern.length)
  else findPatternStartAux (s.drop 1) pattern

def findPatternStart (s pattern : String) : Option String :=
  findPatternStartAux s pattern


def makeCommentNode (s:String) : Syntax:=
  let kind := `PrettyFormat.Comment
  Syntax.mkLit kind s

def stringComments (s:String) : List Syntax :=
  s.split (fun c => c == '\n')
  |>.filterMap (fun s => findPatternStart s "--")
  |>.filter (fun (s:String) => s.trim.length > 0)
  |>.map (fun (s:String) => makeCommentNode ("-- " ++ s.trim))

def stringCommentsStr (s:String) : List String :=
  s.split (fun c => c == '\n')
  |>.filterMap (fun s => findPatternStart s "--")
  |>.filter (fun (s:String) => s.trim.length > 0)
  |>.map (fun (s:String) => "-- " ++ s.trim)

def stringToPPL (s:String) (p: PPL) : PPL :=
  stringCommentsStr s |>.foldl (fun p' c => p' <> commentText c <> nl) p


def expandIntoComments (curr: Syntax ) : List Syntax :=
  match syntaxSourceInfo curr with
  | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
    (stringComments (leading.toString)) ++ [curr] ++ (stringComments (trailing.toString))
  | .synthetic (pos : String.Pos) (endPos : String.Pos) (canonical : Bool) => [curr]
  | .none => [curr]

partial def introduceCommentsToTheCST (curr: Array Syntax ) : Array Syntax :=
  curr.toList.foldl (
    fun (acc: List Syntax) stx =>

      let l := match stx with
      -- recursively alter the
      | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) => Syntax.node info kind (introduceCommentsToTheCST args)
      | _ => stx

      (expandIntoComments l).foldl (fun (acc': List Syntax) (stx': Syntax) => acc'++[stx']) acc
  ) []
  |>.toArray

unsafe def main (args : List String) : IO Unit := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile fileName
  let (moduleStx, env) ← parseModule input fileName


  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  let withComments := introduceCommentsToTheCST leadingUpdated
  IO.println <| prettyPrintSyntax withComments[0]!
  IO.println "\n\n "
  let mut first := true
  for {env, currNamespace, openDecls, ..} in moduleStx, stx in withComments do
    IO.println ""
    -- IO.println <| prettyPrintSyntax stx
    -- if first then first := false else IO.print "\n"
    -- let _ ← printCommands stx |>.toIO {fileName, fileMap := FileMap.ofString input, currNamespace, openDecls} {env}


def surroundWithComments (info : SourceInfo) (p:PPL) (f : PPL → PPL): PPL:=
  match info with
  | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
    stringToPPL leading.toString p
    |> f
    |> stringToPPL trailing.toString
  | _ => f p

mutual
  partial def syntaxLetAssignment (p: PPL) (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : PPL :=
    let lefts := [`«term_/_», `«term_*_», `«term_+_», `«term_-_»]
    -- let formatted
    -- <^>
    let simpleVersion := simpleNode (text "") info kind args
    p <> text " " <>(simpleVersion <^> simpleVersion) <> nl

  -- partial def declModifiers (p: PPL) (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : PPL :=


  partial def syntaxDeclId (p: PPL) (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : PPL :=
    -- optionally insert a new line before the next line
    let first := syntaxToPPL (text "") (args[0]!)
    let rest := syntaxArrToPPLWithSpaces (text "") (args.toList|>.drop 1|>.toArray)
    p <> PPL.letExpr "b" rest (PPL.letExpr "a" first ((v "a" <> v "b") <^> ((v "a" <$> v "b")))) <> text " "

  partial def simpleNode (p: PPL) (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : PPL :=
    args.foldl (fun p' a => syntaxToPPL p' a) p

  partial def simpleIdent (p:PPL) (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) : PPL :=
    surroundWithComments info p (fun p => p <> text rawVal.toString)

  -- when dealing with unknown symbols we are going to keep everything the same
  partial def unknownIdent (p: PPL) (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) : PPL :=
    surroundWithComments info p (fun p => p <> text rawVal.toString)

  partial def syntaxArrToPPL (p: PPL) (stx: Array Syntax) : PPL :=
    stx.foldl syntaxToPPL p

  partial def syntaxArrToPPLWithSpaces (p: PPL) (stx: Array Syntax) : PPL :=
    stx.foldl (fun p' s' =>
    let inner := (syntaxToPPL empty s')
    if isEmpty [] inner then
      p'
    else
      p' <> (syntaxToPPL empty s') <> text " "
    )
    p

  partial def syntaxArrToPPLWithNewLines (p: PPL) (stx: Array Syntax) : PPL :=
    stx.foldl (fun p' s' =>
    let inner := (syntaxToPPL empty s')
    if isEmpty [] inner then
      p'
    else
      p' <> (syntaxToPPL empty s') <> nl
    )
    p

  partial def syntaxDeclValSimple (p: PPL) (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : PPL :=
    -- TODO: handle by
    syntaxArrToPPLWithNewLines p args

  partial def syntaxToPPL (p: PPL) (stx: Syntax) : PPL :=
    match stx with
    | .missing => p
    | .node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
      match kind with
      | `Lean.Parser.Term.letIdDecl => syntaxLetAssignment p info kind args
      | `Lean.Parser.Command.declaration => syntaxArrToPPLWithSpaces (p <> nl) args
      | `Lean.Parser.Command.declId => syntaxDeclId p info kind args
      | `Lean.Parser.Command.optDeclSig => syntaxDeclId p info kind args
      | `Lean.Parser.Command.definition => PPL.nest 2 (syntaxArrToPPLWithSpaces p args)
      | `Lean.Parser.Command.declValSimple => syntaxDeclValSimple p info kind args
      | `Lean.Parser.Term.let => syntaxArrToPPL (p<>nl) args
      -- | `Lean.Parser.Term.explicitBinder =>
      -- | `Lean.Parser.Command.declModifiers => declModifiers p info kind args
      | _ => simpleNode p info kind args
    | .atom   (info : SourceInfo) (val : String) => surroundWithComments info p (fun p => p <> text val)
    | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
      match val with
      | _ => simpleIdent p info rawVal val preresolved

end

end PreviousImplementation

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

unsafe def main2 (args : List String) : IO (Array Syntax) := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile fileName
  let (moduleStx, env) ← parseModule input fileName

  -- leadUpdated update trailing and leading. And the characters the content is assigned to atoms and ident
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let withComments := introduceCommentsToTheCST leadingUpdated
  return leadingUpdated





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







-- #eval isEmpty [] (text ""<>text "")
