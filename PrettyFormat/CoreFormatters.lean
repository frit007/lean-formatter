import Lean
import PrettyFormat
import BaseFormatter
import Lean.Language.Lean
import Lean.Util.Profile
import Lean.Server.References
import Lean.Util.Profiler
import Lean.Elab.Command

open Lean.Parser.Command
open Lean.Parser.Term


open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open Lean.Elab
open System
open Frontend




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

-- partial def processCommandsIncrementally (inputCtx : Parser.InputContext)
--     (parserState : Parser.ModuleParserState) (commandState : Command.State)
--     (old? : Option IncrementalState) :
--     BaseIO IncrementalState := do
--   let task ← Language.Lean.processCommands inputCtx parserState commandState
--     (old?.map fun old => (old.inputCtx, old.initialSnap))
--   go task.get task #[]
-- where
--   go initialSnap t commands :=
--     let snap := t.get
--     let commands := commands.push snap.data.stx
--     if let some next := snap.nextCmdSnap? then
--       go initialSnap next.task commands
--     else
--       -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
--       -- all snapshots
--       let messages := Lean.Language.ToSnapshotTree.toSnapshotTree initialSnap
--         |>.getAll.map (·.diagnostics.msgLog)
--         |>.foldl (· ++ ·) {}
--       let trees := Lean.Language.ToSnapshotTree.toSnapshotTree initialSnap
--         |>.getAll.map (·.infoTree?) |>.filterMap id |>.toPArray'
--       return {
--         commandState := { snap.data.finishedSnap.get.cmdState with messages, infoState.trees := trees }
--         parserState := snap.data.parserState
--         cmdPos := snap.data.parserState.pos
--         inputCtx, initialSnap, commands
--       }

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

-- def interpretFormat (input : String) (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
--     IO <| (Environment) := do
--   let mainModuleName := Name.anonymous -- FIXME
--   let inputCtx := Parser.mkInputContext input fileName
--   let (header, parserState, messages) ← Parser.parseHeader inputCtx
--   let (env, messages) ← processHeader header opts messages inputCtx trustLevel
--   let env := env.setMainModule mainModuleName
--   let env0 := env
--   let s ← IO.processCommands inputCtx parserState -- TODO: learn about this line
--     { Command.mkState env messages opts with infoState := { enabled := true } }

--   let x := s.commandState.infoState.trees.toArray[0]!
--   IO.println s!"{processInfoTree x}"
--   -- let y := x.context
--   -- match y with
--   -- | (commandCtx { env, currNamespace, openDecls, .. }) (a) =>
--   --   IO.println s!"{openDecls.size}"
--   -- match x.context with
--   -- | commandCtx (info : CommandContextInfo) => IO.println s!"{info.openDecls.size}"
--   -- | parentDeclCtx (parentDecl : Name) => IO.println s"parent decl {parentDecl}"
--   -- s.commandState.infoState.trees.
--   -- x.findInfo?


--   -- let a ← IO.processCommandsIncrementally inputCtx parserState
--   --   { Command.mkState env messages opts with infoState := { enabled := true } } none
--   let a ← interpretFormat' inputCtx parserState
--     { Command.mkState env messages opts with infoState := { enabled := true } } none 100

--   IO.println s!"what?{s.commandState.infoState.trees.size}"

--   -- let topLevelCmds : Array CommandSyntax ← s.commandState.infoState.trees.toArray.mapM fun
--   --   | InfoTree.context i
--   --       (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
--   --       match i with
--   --       | .commandCtx { env, currNamespace, openDecls, .. } =>
--   --         pure {env, currNamespace, openDecls, stx}
--   --       | _ =>
--   --         failWith "not a commandCtx"
--   --   | _ =>
--   --     failWith "unknown info tree"
--   return (env)


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



def nullNode : Syntax := Syntax.node (Lean.SourceInfo.none) `null #[]


partial def addSpaceOrNewLine (r : RuleRec) (stx: Syntax) : RuleM PPL := do
  return (text " " <^> PPL.nl) <> (← r stx)

partial def followWithSpaceIfNonEmpty (ppl : PPL) : PPL :=
  if isEmpty ppl then
    text ""
  else
    ppl <> (text " ")




/-
function declaration
-/

#coreFmt Lean.Parser.Command.declaration fun
| s =>
  return combineArgs "" s

partial def pfDeclId : Rule
| args => do
  -- optionally insert a new line before the next line
  let first := toPPL args[0]!
  let var1 ← genId
  let var2 ← genId
  let rest := combine "" (args.getArgs.toList|>.drop 1|>.toArray)

  return text " " <> PPL.letExpr var2 rest (PPL.letExpr var1 first ((v var1 <> v var2) <^> ((v var1 <$> v var2)))) <> text " "


#coreFmt Lean.Parser.Command.declId pfDeclId



#coreFmt Lean.Parser.Command.optDeclSig fun
  | `($arguments:term $returnValue:term) => do
    -- (← read)
    -- let aaaa := formatThen returnValue.raw (text "aa")
    let returnVal := toPPL returnValue
    let args := (combine (text " " <^> PPL.nl) arguments.raw.getArgs)
    if isEmpty returnVal then
      return args
    else
      if isEmpty args then
        return (followWithSpaceIfNonEmpty returnVal)
      else
        return args <> (text " "<^> PPL.nl) <> (followWithSpaceIfNonEmpty returnVal)
  | _ => failure


#coreFmt Lean.Parser.Command.declVal fun
| stx =>
  let args := stx.getArgs
  if args.size == 0 then
    return text ""
  else
    return combine " " args


#coreFmt Lean.Parser.Term.typeSpec fun
| a =>
  return combine " " a.getArgs


#coreFmt Lean.Parser.Command.definition fun
| args => do
  return PPL.nest 2 (combineArgs ("" <^> PPL.nl) args)


#coreFmt Lean.Parser.Command.declValSimple (combineArgs' PPL.nl)

#coreFmt Lean.Parser.Term.explicitBinder fun
| `($lparen $var:term $typeDecl:term $binder:term $rparen) => do
  return lparen
    <> combine " " #[var, typeDecl, binder]
    <> rparen
| _ => failure


-- #coreFmt Lean.Parser.Term.explicitBinder fun
-- | `($lparen $var:term $typeDecl:term $binder:term $rparen) => do
--   return lparen
--     <> combine (text " ") #[var, typeDecl, binder]
--     <> rparen
-- | _ => failure

-- #coreFmt Lean.Parser.Term.explicitBinder fun
-- -- | args => do
-- --   -- no spacing between parenthesis and the first and last character in the binder
-- --   let first := args.get! 0
-- --   let last := args.get! (args.size - 1)
-- --   let rest := args.extract 1 (args.size - 2)
-- --   return (← pf first) <>(← pfCombineWithSeparator (text " ") rest) <> (← pf last)
-- -- | #[firstParen, vars, typeDecl, unknown1, lastParen] => do
-- | `($lparen $var:term $typeDecl:term $binder:term $rparen) => do
--   -- let _ ← assumeMissing unknown1
--   return (← format lparen)
--     <> (← format var)
--     <> text " "
--     <> (← format typeDecl)
--     <>(← format rparen)

-- | _ => failure


#coreFmt Lean.Parser.Module.header combineArgs' (PPL.nl)

#coreFmt Lean.Parser.Module.import  fun
| args => do
  return combineArgs " " args <> PPL.nl


#coreFmt Lean.Parser.Command.declModifiers fun
| `($docComment:term $attributes:term $visibility:term $noncomputableS:term $unsafeS:term $partialS:term) => do
  let modifiers := combine " " #[attributes, visibility, noncomputableS, unsafeS, partialS]
  return docComment <> modifiers ?> text " "
| _ => failure

/-
---- let operator ----
-/

#coreFmt Lean.Parser.Term.let fun
| `($letSymbol $declaration $unknown1 $after) =>
  return (letSymbol <> text " " <> declaration <> unknown1 <> PPL.nl <> after)
| _ => failure


#coreFmt Lean.Parser.Term.letIdDecl fun
| `($var $unknown1 $typeInfo $assignOperator $content) => do
  let _ := (← assumeMissing unknown1)
  -- return (← pf var) <> text " " <> (← pf unknown1) <> (← pf typeInfo) <> (← pf assignOperator) <> (← nest 2 (do (text " " <^> PPL.nl)<>(← pf content)))
  return var <> text " " <> unknown1 <> (typeInfo ?> " ") <> assignOperator <> PPL.nest 2 ((" " <^> PPL.nl) <> content)
| _ => do
  failure

-- TODO: figure out what the suffix is used for.

#coreFmt Lean.Parser.Termination.suffix fun
| `($unknown1 $unknown2) => do
  let _ := (← assumeMissing unknown1)
  let _ := (← assumeMissing unknown2)
  return text ""
| a => do
  failure


#coreFmt Lean.Parser.Term.app fun
| `($functionName $arguments)  => do
  return functionName <> " " <> (combineArgs " " arguments)
| _ => failure

#coreFmt Term.app fun
| `($functionName $arguments)  => do
  return functionName <> " " <> combineArgs " " arguments
| _ => failure

def termOperator : Rule := fun
| `($left + $right) =>
  return left <> (PPL.nl <^> " ") <> "+ " <> right
| _ => failure
-- | `($left $operator $right) =>
--   return left <> (PPL.nl <^> " ") <> operator <> " " <> right
-- | _ => failure

#coreFmt «term_*_» termOperator
#coreFmt «term_/_» termOperator
#coreFmt «term_-_» termOperator
#coreFmt «term_+_» termOperator

#coreFmt «term{}» combineArgs' ""


#coreFmt Lean.Parser.Command.instance fun
| `($kind $instanceAtom $unknown1 $unknown2 $decl $whereStructInst) => do
  assumeMissing unknown1
  assumeMissing unknown2
  let declaration := PPL.nest 4 (combine " " #[kind, instanceAtom, decl])
  let struct := PPL.nest 2 (toPPL whereStructInst)
  return declaration <> text " " <> struct
| _ => failure

#coreFmt Lean.Parser.Command.whereStructInst combineArgs' PPL.nl

#coreFmt Lean.Parser.Term.structInstFields combineArgs' PPL.nl

#coreFmt Lean.Parser.Term.structInstFieldDef fun
| args => return PPL.nest 2 <| combineArgs (" " <^> PPL.nl) args

#coreFmt Lean.Parser.Term.fun fun
| args => return combineArgs " " args

#coreFmt Lean.Parser.Term.structInstField combineArgs' " "

#coreFmt Lean.Parser.Term.basicFun fun
| `($args $unknown1 $arrowAtom $content) => do
  assumeMissing unknown1
  let argsFormatted := combineArgs " " args
  if isEmpty argsFormatted then
    failure
  else
    return argsFormatted <> text " " <> arrowAtom <> text " " <> content
| _ => failure

#coreFmt Lean.Parser.Term.typeAscription fun
| `($firstParen $vars $atom $type $lastParen) => do
  return firstParen <> (combine " " #[vars, atom, type]) <> lastParen
| _ => failure

#coreFmt Lean.Parser.Term.proj combineArgs' ""

#coreFmt Lean.Parser.Command.declSig combineArgs' " "

#coreFmt Lean.Parser.Command.docComment fun
| args => return (combineArgs (PPL.nl) args) <> PPL.nl
-- #coreFmt Lean.Parser.Command.declSig fun (r : RuleRec) => fun
-- | args => pfCombineWithSeparator (text " ") r args


-- TODO: think more about choice, at the moment we just take the first option
#coreFmt choice fun
| args => return toPPL (args.getArgs.get! 0)

#coreFmt Lean.Parser.Term.paren combineArgs' ""

#coreFmt Lean.Parser.Command.namespace combineArgs' " "

#coreFmt Lean.Parser.Command.end combineArgs' " "
