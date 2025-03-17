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
  return combine "" s

partial def pfDeclId : Rule
| args => do
  -- optionally insert a new line before the next line
  let first := toPPL args[0]!
  let rest := combine "" (args.toList|>.drop 1|>.toArray)
  return first <> ("" <^> PPL.nl ) <> rest


#coreFmt Lean.Parser.Command.declId pfDeclId



#coreFmt Lean.Parser.Command.optDeclSig fun
  | #[arguments, returnValue] => do
    let returnVal := toPPL returnValue
    let args := (combine (text " " <^> PPL.nl) arguments.getArgs)
    if isEmpty returnVal then
      return args
    else
      if isEmpty args then
        return returnVal
      else
        return args <> (text " " <^> PPL.nl) <> returnVal
  | _ => failure


#coreFmt Lean.Parser.Command.declVal fun
| stx =>
  let args := stx
  if args.size == 0 then
    return text ""
  else
    return combine " " args


#coreFmt Lean.Parser.Term.typeSpec combine' (" " <^> PPL.nl)


#coreFmt Lean.Parser.Command.definition fun
| args => do
  return PPL.nest 2 (combine (" " <^> PPL.nl) args)



-- TODO: handle do/by notation
#coreFmt Lean.Parser.Command.declValSimple fun
| args => do
  let symbol := args.get! 0
  let rest := combine " " (args.toList|>.drop 1|>.toArray)
  return symbol <> ((" " <> flatten rest) <^> (PPL.nl <> rest))

#coreFmt Lean.Parser.Term.explicitBinder fun
| #[lparen, var, typeDecl, binder, rparen] => do
  return flatten (lparen
    <> combine " " #[
        (combine " " var.getArgs),
        (combine " " typeDecl.getArgs),
        combine " " binder.getArgs
      ]
    <> rparen)
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


#coreFmt Lean.Parser.Module.header combine' (PPL.nl)

#coreFmt Lean.Parser.Module.import  fun
| args => do
  return combine " " args <> PPL.nl


#coreFmt Lean.Parser.Command.declModifiers fun
| #[docComment, attributes, visibility, noncomputableS, unsafeS, partialS] => do
  let modifiers := combine " " #[attributes, visibility, noncomputableS, unsafeS, partialS]
  return docComment <> modifiers ?> text " "
| _ => failure

/-
---- let operator ----
-/

#coreFmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, unknown1, after] =>
  return (letSymbol <> text " " <> declaration <> unknown1 <> PPL.nl <> after)
| _ => failure


#coreFmt Lean.Parser.Term.letIdDecl fun
| #[var, unknown1, typeInfo, assignOperator, content] => do
  let _ := (← assumeMissing unknown1)
  -- return (← pf var) <> text " " <> (← pf unknown1) <> (← pf typeInfo) <> (← pf assignOperator) <> (← nest 2 (do (text " " <^> PPL.nl)<>(← pf content)))
  return var <> text " " <> unknown1 <> (typeInfo) <> assignOperator <> PPL.nest 2 ((" " <^> PPL.nl) <> content)
| _ => do
  failure

-- TODO: figure out what the suffix is used for.

#coreFmt Lean.Parser.Termination.suffix fun
| #[unknown1, unknown2] => do
  let _ := (← assumeMissing unknown1)
  let _ := (← assumeMissing unknown2)
  return text ""
| a => do
  failure


#coreFmt Lean.Parser.Term.app fun
| #[functionName, arguments]  => do
  return functionName <> " " <> (combine " " arguments.getArgs)
| _ => failure

#coreFmt Term.app fun
| #[functionName, arguments]  => do
  return functionName <> " " <> combine " " arguments.getArgs
| _ => failure

def termOperator : Rule := fun
| #[left, operator, right] =>
  return left <> (PPL.nl <^> " ") <> operator <> " " <> right
| _ => failure

#coreFmt «term_*_» termOperator
#coreFmt «term_/_» termOperator
#coreFmt «term_-_» termOperator
#coreFmt «term_+_» termOperator
#coreFmt «term_=_» termOperator
#coreFmt «term_<_» termOperator
#coreFmt «term_>_» termOperator
#coreFmt «term_∧_» termOperator

#coreFmt «term{}» combine' ""


#coreFmt Lean.Parser.Command.instance fun
| #[kind, instanceAtom, unknown1, unknown2, decl, whereStructInst] => do
  assumeMissing unknown1
  assumeMissing unknown2
  let declaration := PPL.nest 4 (combine " " #[kind, instanceAtom, decl])
  let struct := PPL.nest 2 (toPPL whereStructInst)
  return declaration <> text " " <> struct
| _ => failure

#coreFmt Lean.Parser.Command.whereStructInst combine' PPL.nl

#coreFmt Lean.Parser.Term.structInstFields combine' PPL.nl

#coreFmt Lean.Parser.Term.structInstFieldDef fun
| args => return PPL.nest 2 <| combine (" " <^> PPL.nl) args


#coreFmt Lean.Parser.Term.fun combine' (" " <^> PPL.nl)

#coreFmt Lean.Parser.Term.structInstField combine' " "

-- TODO: Fix double space issue
#coreFmt Lean.Parser.Term.basicFun fun
| #[args, typeDecl, arrowAtom, content] => do
  -- return toPPL "??????????"
  -- assumeMissing unknown1
  let argsFormatted := combine " " args.getArgs
  return combine " " #[argsFormatted, flatten (toPPL typeDecl), toPPL arrowAtom] <> ((PPL.nest 2 (PPL.nl <> content)) <^> (" " <> (flatten (toPPL content))))
    -- return argsFormatted <> text " " <> arrowAtom <> ((text " " <> flatten (toPPL content)) <^> (PPL.nl <> content))
| _ => failure

#coreFmt Lean.Parser.Term.typeAscription fun
| #[firstParen, vars, atom, type, lastParen] => do
  return firstParen <> (combine " " #[vars, atom, type]) <> lastParen
| _ => failure

#coreFmt Lean.Parser.Term.proj combine' ""

#coreFmt Lean.Parser.Command.declSig fun
| #[explicitBinders, typeSpec] =>
  return combine (" " <^> PPL.nl) #[((combine (" " <^> PPL.nl)) explicitBinders.getArgs), toPPL typeSpec]
| _ => failure

#coreFmt Lean.Parser.Command.docComment fun
| args => return (flatten (combine (PPL.nl) args) <^> (combine (PPL.nl) args)) <> PPL.nl
-- #coreFmt Lean.Parser.Command.declSig fun (r : RuleRec) => fun
-- | args => pfCombineWithSeparator (text " ") r args


-- TODO: think more about choice, at the moment we just take the first option
#coreFmt choice fun
| args => return toPPL (args.get! 0)

#coreFmt Lean.Parser.Term.paren combine' ""

#coreFmt Lean.Parser.Command.namespace combine' " "

#coreFmt Lean.Parser.Command.end combine' " "

-- @[inherit_doc ite] syntax (name := termIfThenElse)
--   ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
--     ppDedent(ppSpace) ppRealFill("else " term)) : term
#coreFmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let content := ifAtom <> " " <> condition <> " " <> thenAtom <> PPL.nest 2 (PPL.nl <> positiveBody) <> PPL.nl <> elseAtom <> PPL.nest 2 (PPL.nl <> negativeBody)
  return (PPL.flatten content) <^> content
| _ => failure

--- Inductive ---
#coreFmt Lean.Parser.Command.inductive fun
| #[inductiveAtom, decl, optDeclSig, whereContainer, terms, unknown1, derive] => do
  assumeMissing unknown1
  return (combine " " #[toPPL inductiveAtom, toPPL decl, toPPL optDeclSig, combine " " whereContainer.getArgs])
    <> (PPL.nest 2 (PPL.nl <> combine PPL.nl terms.getArgs)) <> (PPL.nl <? derive)
| _ => failure

#coreFmt Lean.Parser.Command.ctor fun
| #[docComment, barAtom, declModifiers, ident, optDeclSig] =>
  return docComment <> barAtom <> " " <> combine " " #[declModifiers, ident, optDeclSig]
| _ => failure

#coreFmt Lean.Parser.Command.optDeriving fun
| #[args] => return combine (" " <^> PPL.nl) args.getArgs
| _ => failure

--- TACTICS ---
-- #coreFmt Lean.Parser.Term.byTactic combine' (PPL.nl)

#coreFmt Lean.Parser.Command.theorem fun
| #[theoremAtom, ident, typeSignature, content] =>
  return PPL.nest 4 (theoremAtom <> (" " <^> PPL.nl) <> ident <> (" " <^> PPL.nl) <> (typeSignature ?> " ")) <> (PPL.nest 2 (PPL.stx content))
| _ => failure

#coreFmt Lean.Parser.Tactic.simpLemma combine' " "
#coreFmt Lean.Parser.Attr.simp combine' " "
#coreFmt Lean.Parser.Term.attributes combine' ""
#coreFmt Lean.Parser.Term.attrInstance combine' " "

def addSpaceAfterCommas : Array Syntax → RuleM PPL
| args =>
  return args.foldl (fun (acc : PPL) (p : Syntax) =>
    match p with
    | .atom _ (val : String) =>
      if val == "," then
        (acc <> p <> text " ")
      else
        (acc <> p)
    | _ => acc <> p
  ) (PPL.text "")

def formatSimpleProof : Array Syntax → RuleM PPL
| #[] => return text ""
| #[lparen, proofs, rparen] => do
  return lparen <> (← addSpaceAfterCommas proofs.getArgs) <> rparen
| _ => failure

-- TODO: missing
#coreFmt Lean.Parser.Tactic.simp fun
| #[simpAtom, config, unknown1, unknown2, proof, unknown3] => do
  assumeMissing unknown1
  assumeMissing unknown2
  assumeMissing unknown3
  return flatten (combine " " #[toPPL simpAtom, toPPL config, ← formatSimpleProof proof.getArgs])
| _ => failure

#coreFmt Lean.Parser.Term.have fun
| #[haveAtom, haveDecl, unknown1, content] => do
  assumeMissing unknown1
  return haveAtom <> " " <> haveDecl <> (PPL.nl <> content)
| _ => failure

#coreFmt Lean.Parser.Term.haveDecl combine' " "
#coreFmt Lean.Parser.Term.haveIdDecl combine' " "
#coreFmt Lean.Parser.Term.arrow combine' " "

#coreFmt Lean.Parser.Term.show combine' " "
#coreFmt Lean.Parser.Term.fromTerm combine' " "

#coreFmt Lean.Parser.Term.haveId combine' " "
#coreFmt Lean.Parser.Term.prop combine' " "

#coreFmt Lean.Parser.Command.open combine' " "
#coreFmt Lean.Parser.Command.openSimple fun
| #[args] => return combine " " args.getArgs
| _ => failure


#coreFmt Tactic.tacticSeq fun
| #[tactics] => return toPPL "tacticSeq"
| _ => failure
