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





def nullNode : Syntax := Syntax.node (Lean.SourceInfo.none) `null #[]


/-
function declaration
-/

#coreFmt Lean.Parser.Command.declaration fun
| s =>
  let v := combine (. <> Doc.provide (bridgeAny ||| bridgeImmediate) <> .) s
  return v

partial def pfDeclId : Rule
| args => do
  -- optionally insert a new line before the next line
  let first := args[0]!
  let rest := combine (.<>.) (args.toList|>.drop 1|>.toArray)
  return first <**> rest


#coreFmt Lean.Parser.Command.declId pfDeclId



#coreFmt Lean.Parser.Command.optDeclSig fun
  | #[arguments, returnValue] => do
    let returnVal := toDoc returnValue
    let args := (combine (.<**>.) arguments.getArgs)
    if isEmpty returnVal then
      return args
    else
      if isEmpty args then
        return returnVal
      else
        return args <**> returnVal
  | _ => failure


#coreFmt Lean.Parser.Command.declVal fun
| stx =>
  return combine (.<**>.) stx


#coreFmt Lean.Parser.Term.typeSpec combine' (.<_>.)





-- TODO: handle do/by notation


#coreFmt Lean.Parser.Term.explicitBinder fun
| #[lparen, var, typeDecl, binder, rparen] => do
  return lparen <> ( combine (.<_>.) #[
        (combine (.<_>.) var.getArgs),
        (combine (.<_>.) typeDecl.getArgs),
        combine (.<_>.) binder.getArgs
      ]
    <> rparen).flatten
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


#coreFmt Lean.Parser.Module.header combine' (.<$$>.)

#coreFmt Lean.Parser.Module.import  fun
| args => do
  return combine (.<_>.) args <> Doc.nl


#coreFmt Lean.Parser.Command.declModifiers fun
| #[docComment, attributes, visibility, noncomputableS, unsafeS, partialS] => do
  let modifiers := combine (.<_>.) #[visibility, noncomputableS, unsafeS, partialS]
  return docComment <> (attributes ?> (Doc.provide bridgeHardNl)) <> modifiers
| _ => failure

/-
---- let operator ----
-/

#coreFmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, unknown1, after] =>
  -- should we require a newline before let?
  return (letSymbol <_> declaration <> unknown1 <$$> after)
| _ => failure


-- TODO: figure out what the suffix is used for.

-- #coreFmt Lean.Parser.Termination.suffix fun
-- | #[unknown1, unknown2] => do
--   assumeMissing unknown1
--   assumeMissing unknown2
--   return text ""
-- | a => do
--   failure



#coreFmt Lean.Parser.Term.whereDecls fun
| #[whereAtom, decl] =>
  return whereAtom <> Doc.nest 2 ("" <$$$> decl)
| _ => failure


#coreFmt Lean.Parser.Term.app fun
| #[functionName, arguments]  => do
  return functionName <_> (combine (.<**>.) arguments.getArgs)
| _ => failure

#coreFmt Term.app fun
| #[functionName, arguments]  => do
  return functionName <_> combine (.<_>.) arguments.getArgs
| _ => failure

def trivialPPL : Rule := fun
| args => do
  assert! (args.size == 1)
  return toDoc (args.get! 0)

def termOperator : Rule := fun
| #[left, operator, right] => do
  let left ← formatStx left
  let right ← formatStx right
  return (left <**> operator <_> right)
    <^> (left <_> operator <> bridgeImmediate !> right)
| _ => failure

#coreFmt «term_*_» termOperator
#coreFmt «term_/_» termOperator
#coreFmt «term_-_» termOperator
#coreFmt «term_+_» termOperator
#coreFmt «term_=_» termOperator
#coreFmt «term_<_» termOperator
#coreFmt «term_>_» termOperator
#coreFmt «term_∧_» termOperator
#coreFmt List.«term_<+~_» termOperator
#coreFmt List.«term_~_» termOperator
#coreFmt List.«term_<+_» termOperator
#coreFmt «term_::_» termOperator
#coreFmt «term_↔_» termOperator
#coreFmt «term_⊆_» termOperator
#coreFmt «term_$__» termOperator
#coreFmt «term_∈_» termOperator
#coreFmt «term_<|_» termOperator
#coreFmt «term_∉_» termOperator
#coreFmt «term_++_» termOperator
#coreFmt «term_==_» termOperator
#coreFmt «term_∪_» termOperator
#coreFmt «term_∩_» termOperator
#coreFmt «term_<$>_» termOperator
#coreFmt «term_≤_» termOperator
#coreFmt «term_×_» termOperator
#coreFmt «term_∘_» termOperator
#coreFmt «term_<<<_» termOperator
#coreFmt «term_⊕'_» termOperator
#coreFmt «term_^_» termOperator
#coreFmt «term_>>_» termOperator
#coreFmt «term_≠_» termOperator
#coreFmt «term_×__1» termOperator

#coreFmt «term{}» combine' (.<>.)

#coreFmt Lean.Parser.Term.hole trivialPPL
#coreFmt Lean.Parser.Tactic.rcasesPatMed trivialPPL
#coreFmt Lean.binderIdent trivialPPL
#coreFmt fieldIdx trivialPPL
#coreFmt Lean.explicitBinders trivialPPL
#coreFmt Lean.Parser.Term.ellipsis trivialPPL
#coreFmt Lean.Parser.Tactic.tacticRfl trivialPPL
#coreFmt num trivialPPL
#coreFmt Lean.Parser.Term.doExpr trivialPPL
#coreFmt Lean.Parser.Command.protected trivialPPL


-- #coreFmt Lean.Parser.Command.whereStructInst combine' (.<$$>.)
#coreFmt Lean.Parser.Command.whereStructInst fun
| #[whereAtom, structInst, unknown1] => do
  assumeMissing unknown1
  return whereAtom <> (Doc.nest 2 ("" <$$> structInst))
| _ => failure



-- #coreFmt Lean.Parser.Term.fun combine' (" " <^> PPL.nl)
#coreFmt Lean.Parser.Term.fun fun
| #[funAtom, content] => do
  let content ← formatStx content
  return (funAtom <**> content)
    -- pass through immediately value
    <^> (bridgeImmediate <! " " <> funAtom <> bridgeImmediate !> content)
| _ => failure


-- #coreFmt Lean.Parser.Term.structInstField combine' (. <_> .)


-- TODO: Fix double space issue
#coreFmt Lean.Parser.Term.basicFun fun
| #[args, typeDecl, arrowAtom, content] => do
  let content ← formatStx content
  let typeDecl ← formatStx typeDecl
  -- assumeMissing unknown1
  let argsFormatted := combine (· <_> ·) args.getArgs
  return (bridgeImmediate <! combine (. <_> .) #[argsFormatted, flattenDoc (toDoc typeDecl), toDoc arrowAtom] <> (Doc.nl <> content))
   <^> (
    combine (· <_> ·) #[argsFormatted, flattenDoc (toDoc typeDecl), toDoc arrowAtom] <> ((Doc.nest 2 (Doc.nl <> content)) <^> (" " <> (flattenDoc (toDoc content))))
   )
  -- return combine " " #[argsFormatted, flatten (toPPL typeDecl), toPPL arrowAtom] <> ((Doc.nest 2 (PPL.nl <> content)) <^> (" " <> (flatten (toPPL content))))
    -- return argsFormatted <> text " " <> arrowAtom <> ((text " " <> flatten (toPPL content)) <^> (PPL.nl <> content))
| _ => failure

#coreFmt Lean.Parser.Term.typeAscription fun
| #[firstParen, vars, atom, type, lastParen] => do
  return firstParen <> (combine (· <_> ·) #[vars, atom, type]) <> lastParen
| _ => failure

#coreFmt Lean.Parser.Term.proj combine' (· <> ·)

#coreFmt Lean.Parser.Command.declSig fun
| #[explicitBinders, typeSpec] =>
  return combine (·<**>·) #[((combine (·<**>·)) explicitBinders.getArgs), toDoc typeSpec]
| _ => failure



-- TODO: think more about choice, at the moment we just take the first option
#coreFmt choice fun
| args => return toDoc (args.get! 0)

#coreFmt Lean.Parser.Term.paren combine' (.<>.)

#coreFmt Lean.Parser.Command.namespace combine' (.<_>.)

#coreFmt Lean.Parser.Command.end combine' (.<_>.)

-- @[inherit_doc ite] syntax (name := termIfThenElse)
--   ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
--     ppDedent(ppSpace) ppRealFill("else " term)) : term
#coreFmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let condition ← formatStx condition
  let positiveBody ← formatStx positiveBody
  let negativeBody ← formatStx negativeBody

  let content := " " <> condition <> " " <> thenAtom <> Doc.nest 2 ("" <$$> positiveBody) <$$> elseAtom <> Doc.nest 2 ("" <$$> negativeBody)
  return ifAtom <> ((content.flatten) <^> content)
| _ => failure

--- Inductive ---
-- #coreFmt Lean.Parser.Command.inductive fun
-- | #[inductiveAtom, decl, optDeclSig, whereContainer, terms, unknown1, derive] => do
--   assumeMissing unknown1
--   return (combine (.<_>.) #[toPPL inductiveAtom, toPPL decl, toPPL optDeclSig, combine (.<_>.) whereContainer.getArgs])
--     <> (Doc.nest 2 ("" <$$> combine (.<$$>.) terms.getArgs) <> (PPL.nl <? derive))
-- | _ => failure

#coreFmt Lean.Parser.Command.ctor fun
| #[docComment, barAtom, declModifiers, ident, optDeclSig] =>
  return docComment <> barAtom <> " " <> combine (.<_>.) #[declModifiers, ident, optDeclSig]
| _ => failure

#coreFmt Lean.Parser.Command.optDeriving fun
| #[args] => return combine (.<**>.) args.getArgs
| _ => failure

--- TACTICS ---
-- #coreFmt Lean.Parser.Term.byTactic combine' (PPL.nl)
#coreFmt Lean.Parser.Term.byTactic fun
| #[byAtom, tactic] => do
  let tactic ← formatStx tactic

  let content := byAtom <> (Doc.nest 2 (bridgeHardNl !> tactic) <^> Doc.flatten (bridgeSpace !> tactic))
  return (bridgeNl <! byAtom <> Doc.nest 2 (bridgeNl !> tactic)) <^>
  ((Doc.require (bridgeSpace ||| bridgeNone) <> content <^> Doc.cost 3 content/-allow any bridge, but at a cost-/)) <^>
  (bridgeImmediate <! " " <> (Doc.nest 2 (byAtom <> Doc.nl <> tactic)))
| _ => failure


#coreFmt Lean.Parser.Command.example fun
| #[exampleAtom, typeSignature, content] => do
  let content ← formatStx content
  let typeSignature ← formatStx typeSignature
  return (Doc.nest 4 (combine (.<_>.) #[toDoc exampleAtom, (flattenDoc (toDoc typeSignature))] )) <> " " <> Doc.nest 2 ((bridgeNl !> toDoc content) <^> (bridgeImmediate !> content))
| _ => failure

#coreFmt Lean.Parser.Tactic.simpLemma combine' (.<_>.)
#coreFmt Lean.Parser.Attr.simp combine' (.<_>.)

#coreFmt Lean.Parser.Term.attrInstance combine' (.<_>.)

def addSpaceAfterDelimiter (isDelimiter : String → Bool): Array Syntax → Doc
| args =>
  args.foldl (fun (acc) (p : Syntax) =>
    match p with
    | .atom _ (val : String) =>
      if isDelimiter (val) then
        (acc <> p <> toDoc " ")
      else
        (acc <> p)
    | _ => acc <> p
  ) (toDoc "")

def addSpaceAfterCommas := addSpaceAfterDelimiter (fun s => s == ",")



def formatSimpleProof : Array Syntax → RuleM Doc
| #[] => return toDoc ""
| #[lparen, proofs, rparen] => do
  return lparen <> (addSpaceAfterCommas proofs.getArgs) <> rparen
| _ => failure

-- TODO: missing
#coreFmt Lean.Parser.Tactic.simp fun
| #[simpAtom, config, unknown1, proofOnly, proof, proofLocation] => do
  assumeMissing unknown1
  let proofLocation ← formatStx proofLocation
  let proofOnly ← formatStx proofOnly
  let content := (PrettyFormat.combine (.<_>.) #[toDoc config, toDoc proofOnly, ← formatSimpleProof proof.getArgs, toDoc proofLocation])
  return toDoc simpAtom <> " "<? (content <^> content.flatten)
| _ => failure

#coreFmt Lean.Parser.Term.have fun
| #[haveAtom, haveDecl, unknown1, content] => do
  assumeMissing unknown1
  return haveAtom <_> haveDecl <> (bridgeHardNl !> content)
| _ => failure

#coreFmt Lean.Parser.Term.haveDecl combine' (.<_>.)
#coreFmt Lean.Parser.Term.arrow combine' (.<_>.)

#coreFmt Lean.Parser.Term.show combine' (.<_>.)
#coreFmt Lean.Parser.Term.fromTerm combine' (.<_>.)

#coreFmt Lean.Parser.Term.haveId combine' (.<_>.)
#coreFmt Lean.Parser.Term.prop combine' (.<_>.)

#coreFmt Lean.Parser.Command.open combine' (.<_>.)
#coreFmt Lean.Parser.Command.openSimple fun
| #[args] => return combine (.<_>.) args.getArgs
| _ => failure


-- #coreFmt Tactic.tacticSeq fun
-- | #[tactics] => return toPPL "tacticSeq"
-- | _ => failure


#coreFmt Lean.Parser.Tactic.rwSeq combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.tacticSeq fun
| #[args] => return toDoc args -- TODO: is just a wrawpper for `tacticSeq1`?
| _ => failure


-- #coreFmt Lean.cdot combine' (.<_>.)
#coreFmt Lean.cdot fun
| #[a, b] => return a <> Doc.nest 2 ("" <_> b)
| _ => failure


-- #coreFmt Lean.Parser.Tactic.unfold fun
-- | args => failure



#coreFmt Lean.Parser.Command.private combine' (.<_>.) -- ident

#coreFmt Lean.Parser.Tactic.rwRuleSeq fun
| #[lpar, rwSeq, rpar] => do
  return (toDoc lpar) <> (addSpaceAfterCommas rwSeq.getArgs) <> (toDoc rpar)
| _ => failure

#coreFmt Lean.Parser.Term.anonymousCtor fun
| #[lbracket, rwSeq, rbracket] => do
  return (toDoc lbracket) <> (Doc.provide (bridgeNone)) <> (addSpaceAfterCommas rwSeq.getArgs) <> (toDoc rbracket)
| _ => failure

#coreFmt Lean.Parser.Tactic.simpa combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.location combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.«tactic_<;>_» combine' (.<_>.)

#coreFmt «tacticBy_cases_:_» fun
| #[atom, idents, term] =>
  return combine (.<_>.) #[toDoc atom, combine (.<_>.) idents.getArgs, toDoc term]
| _ => failure

#coreFmt Lean.Parser.Tactic.tacticHave_ combine' (.<_>.)
#coreFmt «term¬_» combine' (.<>.)

#coreFmt Lean.Parser.Term.implicitBinder fun
| #[lpar, vars, types, rpar] =>
  return toDoc lpar <> combine (.<_>.) (vars.getArgs) <> (" " <? (combine (.<_>.) types.getArgs)) <> toDoc rpar
| _ => failure

#coreFmt Lean.Parser.Tactic.subst combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.simpaArgsRest fun
| #[opt, unknown2, unknown3, simpArgs, args] => do
  -- assumeMissing unknown1
  assumeMissing unknown2
  assumeMissing unknown3
  let argsSpaced := args.getArgs.map (fun (s : Lean.Syntax) =>
    if s.getArgs.size > 0 && s.getKind == `null then
      combine (.<_>.) s.getArgs
    else
      toDoc s
  )
  -- assumeMissing unknown4
  return combine (.<_>.) #[toDoc opt, combine (.<_>.) simpArgs.getArgs, combine (.<_>.) argsSpaced]
  -- return toPPL "????"
| _ => failure


#coreFmt termDepIfThenElse fun
| #[ifAtom, binder, colonAtom, statementTerm, thenAtom, positiveTerm, elseAtom, negativeTerm] => do
  let binder ← formatStx binder
  let positiveTerm ← formatStx positiveTerm
  let negativeTerm ← formatStx negativeTerm
  let statementTerm ← formatStx statementTerm

  let multiline := ifAtom <_> binder <_> colonAtom <_> (flattenDoc statementTerm) <_> thenAtom
    <> Doc.nest 2 (bridgeHardNl !> (positiveTerm)) <> " "
  <> bridgeHardNl !> elseAtom
    <> Doc.nest 2 (bridgeHardNl !> (negativeTerm))

  return ifAtom <> " " <> binder <> " " <> colonAtom <> " " <> (flattenDoc statementTerm) <> " " <> thenAtom
    <> (bridgeSpace !> (flattenDoc positiveTerm)) <> " "
  <> elseAtom
    <> (bridgeSpace !> (flattenDoc negativeTerm)) <^>
  ((bridgeNl <! multiline <^> bridgeImmediate <! Doc.nest 2 (Doc.nl <> multiline)))
| _ => failure


#coreFmt Lean.Parser.Tactic.replace combine' (.<_>.)


def combineParenExpression [ToDoc a] [Inhabited a] (sep: Doc → Doc → Doc) (args : Array a): RuleM Doc := do
  if args.size > 1 then

    return (args.get! 0) <> combine sep (args.extract 1 (args.size - 1)) <> (args.get! (args.size - 1))
  else
    return combine sep args

#coreFmt Lean.deprecated fun
| #[deprecatedAtom, previous, unknown1, date] => do
  assumeMissing unknown1
  return combine (.<_>.) #[toDoc deprecatedAtom, toDoc previous, ← (combineParenExpression (.<_>.) date.getArgs)]
| _ => failure


#coreFmt Lean.Parser.Term.match fun
| #[matchAtom, unknown1, unknown2, matchDiscr, withAtom, matchAlts] => do
  assumeMissing unknown1
  assumeMissing unknown2
  return matchAtom <> bridgeSpace !> matchDiscr <> " " <> withAtom <> bridgeNl !> matchAlts
| _ => failure

#coreFmt Lean.Parser.Term.matchAlt fun
| #[barAtom, pattern, arrowAtom, value] => do
  let value ← formatStx value
  let patternSyntax :=
    if pattern.matchesNull 1 && (pattern.getArgs.get! 0|>.getKind) == `null then
      addSpaceAfterCommas (pattern.getArgs.get! 0|>.getArgs)
    else
      toDoc pattern

  return (bridgeNl !> barAtom) <> " " <> (flattenDoc patternSyntax) <> " " <> (Doc.nest 2 (arrowAtom <> (bridgeNl !> value <^> (bridgeSpace !>flattenDoc value))) <^> (arrowAtom <> bridgeImmediate !> value))
| _ => failure

-- def formatMatchAlt (flatten:Bool): Array Syntax → RuleM PPL
-- | #[barAtom, pattern, arrowAtom, v] => do
--   let mut patternSyntax := toPPL pattern
--   if pattern.matchesNull 1 && (pattern.getArgs.get! 0|>.getKind) == `null then
--     patternSyntax ← addSpaceAfterCommas (pattern.getArgs.get! 0|>.getArgs)

--   if flatten then
--     return (spaceNewline !> barAtom) <> [space] !> (flattenPPL patternSyntax) <> [space] !> (arrowAtom <> [space] !> flattenPPL v)
--   else
--     return (spaceNewline !> barAtom) <> [space] !> (flattenPPL patternSyntax) <> [space] !> Doc.nest 2 (arrowAtom <> spaceNewline !> v)
-- | _ => failure

-- TODO: Introduce PPL.expand (Array PPL, Array PPL -> PPL), to align "=>"
#coreFmt Lean.Parser.Term.matchAlts fun
| #[alts] => do
  -- let flatAlts ← alts.getArgs.mapM (fun (f:Syntax)=> formatMatchAlt true f.getArgs)
  -- let spaceAlts ← alts.getArgs.mapM (fun (f:Syntax)=> formatMatchAlt false f.getArgs)
  -- return [bridgeHardNl] !> ((combine (.<$$$>.) flatAlts) <^> ((combine (.<$$$>.) spaceAlts)))
  return bridgeHardNl !> ((combine (.<$$$>.) alts.getArgs))
| _ => failure


-- #coreFmt Lean.Parser.Term.sufficesDecl combine' " "
#coreFmt Lean.Parser.Term.suffices combine' (.<**>.)

#coreFmt Lean.Parser.Term.letPatDecl fun
| #[pattern, unknown1, unknown2, assignAtom, val] => do
  assumeMissing unknown1
  assumeMissing unknown2
  return combine (.<_>.) #[pattern, assignAtom] <> Doc.nest 2 ( bridgeImmediate ||| bridgeSpace ||| bridgeSpaceNl !> val)
| _ => failure



#coreFmt Lean.Parser.Term.sufficesDecl combine' (.<**>.)


#coreFmt Lean.Parser.Term.type combine' (.<_>.)
#coreFmt Lean.Parser.Level.hole combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.exact combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.tacticLet_ combine' (.<_>.)

#coreFmt Lean.Parser.Term.strictImplicitBinder fun
| #[lpar, vars, types, rpar] =>
  return toDoc lpar <> combine (.<_>.) (vars.getArgs) <> (" " <? (combine (.<_>.) types.getArgs)) <> toDoc rpar
| _ => failure
#coreFmt Lean.Parser.Tactic.rintro combine' (.<**>.)
#coreFmt «term[_]» combine' (.<>.)

#coreFmt Lean.Parser.Tactic.refine combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.tacticRwa__ combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.match fun
| #[matchAtom, unknown1, unknown2, pattern, withAtom, matchAlts] => do
-- unknown1 and 2 are most likely `hyp` and `colonAtom`
  assumeMissing unknown1
  assumeMissing unknown2
  return combine (.<_>.) #[matchAtom, pattern, withAtom] <> bridgeHardNl !> matchAlts
| _ => failure




#coreFmt Lean.Parser.Tactic.inductionAltLHS fun
| #[barAtom, value, binding] => do
  return combine (.<_>.) #[toDoc barAtom, toDoc value, combine (.<_>.) binding.getArgs]
| _ => failure


#coreFmt Lean.Parser.Tactic.obtain fun
| #[obtainAtom, cases, unknown1, assign] => do
  return obtainAtom <> bridgeSpace !> cases <> bridgeSpace !> (combine (. <> Doc.provide (bridgeAny ||| bridgeImmediate) <> .) assign.getArgs)
| _ => failure

#coreFmt Lean.Parser.Tactic.rcasesPat.tuple fun
| #[lpar, content, rpar] => do
  return lpar <> (addSpaceAfterCommas content.getArgs) <> rpar
| _ => failure


#coreFmt Lean.Parser.Term.subst combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.inductionAlts fun
| #[withAtom, intros, alts] => do
  -- intros
  return (combine (.<_>.) #[toDoc withAtom, combine (.<_>.) intros.getArgs]) <> bridgeHardNl !> (combine (.<$$$>.) alts.getArgs)
| _ => failure

#coreFmt Lean.Parser.Tactic.inductionAlt fun
| #[group, arrowAtom, proof] => do
  let proof ← formatStx proof
  return group <> " " <> arrowAtom <>
  ((Doc.nest 2 ( bridgeImmediate ||| bridgeNl !> proof))
  <^>
  (bridgeSpace !> flattenDoc (proof))
  )
| _ => failure

-- #coreFmt Lean.Parser.Tactic.intro combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.intro fun
| #[introAtom, symbols] =>
  return introAtom <> " " <? combine (.<_>.) symbols.getArgs
| _ => failure


#coreFmt Lean.Parser.Tactic.tacticSuffices_ fun
| #[sufficesAtom, decl] =>
  return sufficesAtom <> Doc.nest 2 ("" <**> decl)
| _ => failure

#coreFmt Lean.Parser.Tactic.clear fun
| #[clearAtom, variables] =>
  return clearAtom <> ("" <_> "") ?> combine (.<_>.) variables.getArgs
| _ => failure

#coreFmt «term∃_,_» fun
| #[existsAtom, binders, commaAtom, val] =>
  return existsAtom <**> binders <> commaAtom <> bridgeSpace !> val
| _ => failure

#coreFmt Lean.Parser.Tactic.tacDepIfThenElse fun
| #[ifAtom, binder, colonAtom, valTerm, thenAtom, positive, elseAtom, negative] => do
  let binder ← formatStx binder
  let valTerm ← formatStx valTerm
  let positive ← formatStx positive
  let negative ← formatStx negative
  let firstLine := ifAtom <_> flattenDoc (combine (.<_>.) #[binder, toDoc colonAtom, valTerm, toDoc thenAtom])
  return firstLine <> bridgeSpace !> (flattenDoc positive) <> bridgeSpace !> elseAtom <> bridgeSpace !> (flattenDoc negative)
    <^>
    firstLine <> Doc.nest 2 (bridgeHardNl !> positive) <> bridgeHardNl !> elseAtom <> Doc.nest 2 (bridgeHardNl !> negative)
| _ => failure

#coreFmt Lean.Parser.Tactic.tacticTry_ combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.apply fun
| #[applyAtom, content] =>
  return applyAtom <> bridgeAny !> content
| _ => failure

#coreFmt Lean.Parser.Tactic.rwRule combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.specialize fun
| #[specializeAtom, app] =>
  return specializeAtom <> bridgeSpace !> (Doc.nest 2 (toDoc app))
| _ => failure

#coreFmt Lean.«term∀__,_» fun
| #[forAllAtom, binder, binderTerm, commaAtom, proof] =>
  return Doc.nest 2 (forAllAtom <> bridgeSpace !> binder <> bridgeSpace !> binderTerm <> commaAtom <> bridgeSpace !> proof)
| _ => failure

#coreFmt Lean.Parser.Term.syntheticHole combine' (.<>.)
#coreFmt Lean.«binderTerm∈_» combine' (.<_>.)

#coreFmt Lean.Parser.Command.instance fun
| #[kind, instanceAtom, declId, typeSpec, decl, whereStructInst] => do
  let declaration := Doc.nest 4 (combine (.<**>.) #[kind, instanceAtom, declId, typeSpec, decl])
  let struct := (toDoc whereStructInst)
  return declaration <> bridgeAny !> struct
| _ => failure

#coreFmt Lean.Parser.Command.universe fun
| #[universeAtom, variables] =>
  return Doc.nest 2 (combine (.<_>.) #[toDoc universeAtom, combine (.<_>.) variables.getArgs])
| _ => failure

#coreFmt Lean.Parser.Command.variable fun
| #[variableAtom, binders] =>
  return Doc.nest 2 (combine (.<_>.) #[toDoc variableAtom, combine (.<_>.) binders.getArgs])
| _ => failure


#coreFmt Lean.Parser.Command.set_option combine' (.<_>.)

#coreFmt tacticFunext___ fun
| #[funextAtom, idents] =>
  return combine (.<_>.) #[toDoc funextAtom, combine (.<_>.) idents.getArgs]
| _ => failure

#coreFmt Lean.Parser.Tactic.simpArith fun
| #[simpArithAtom, optConfig, unknown1, onlyAtom, proof, unknown2] => do
  assumeMissing unknown1
  assumeMissing unknown2
  return Doc.nest 2 (combine (.<_>.) #[simpArithAtom, optConfig, onlyAtom, proof])
| _ => failure


#coreFmt Lean.Parser.Term.letEqnsDecl fun
| #[goAtom, binder, typeSpec, matchAlts] =>
  return combine (.<_>.) #[toDoc goAtom, combine (.<_>.) binder.getArgs, combine (.<_>.) typeSpec.getArgs] <$$$> matchAlts
| _ => failure

#coreFmt Lean.Parser.Command.inductive fun
| #[inductiveAtom, decl, optDeclSig, whereContainer, terms, unknown1, derive] => do
  assumeMissing unknown1
  return (combine (.<_>.) #[toDoc inductiveAtom, toDoc decl, toDoc optDeclSig, combine (.<>" ??? "<>.) whereContainer.getArgs])
    <> (Doc.nest 2 ("" <$$> combine (.<$$>.) terms.getArgs <> ("" <$$> "" <? derive)))
| _ => failure


#coreFmt Lean.Parser.Command.declValEqns fun
| args =>
  return (combine (.<>.) args)

#coreFmt Lean.Parser.Term.forall fun
| #[forallAtom, binder, typeInfo, commaAtom, arrow] => do
  let spacedTypeInfo := combine (.<_>.) typeInfo.getArgs
  return forallAtom <_> Doc.nest 2 ((combine (.<**>.) #[combine (.<_>.) binder.getArgs, spacedTypeInfo]) <> commaAtom <_> arrow)
| _ => failure


#coreFmt Lean.Parser.Command.instance fun
| #[kind, instanceAtom, declId, typeSpec, decl, whereStructInst] => do
  let declaration := Doc.nest 4 (combine (.<**>.) #[kind, instanceAtom, declId, typeSpec, decl])
  let struct := (toDoc whereStructInst)
  return declaration <> bridgeAny !> struct
| _ => failure

#coreFmt Lean.Parser.Term.matchAltsWhereDecls fun
| #[wheres, suffix, unknown1] => do
  assumeMissing unknown1
  return Doc.nest 2 (toDoc wheres) <> (""<$$$>"" <? suffix)
| _ => failure


#coreFmt Lean.Parser.Termination.terminationBy fun
| #[terminationByAtom, unknown1, argsAndArrow, proof] => do
  assumeMissing unknown1
  match argsAndArrow.getArgs with
  | #[] =>
    return terminationByAtom <_> proof
  | #[args, arrow] =>
    return terminationByAtom <_>  (combine (.<_>.) (args.getArgs)) <_> arrow <**> proof
  | _ => failure
| _ => failure

#coreFmt Lean.Parser.Command.structure fun
| #[structureAtom, declId, explicitBinder, unknown1, unknown2, structFields, optDeriving] => do
  assumeMissing unknown1
  assumeMissing unknown2
  match structFields.getArgs with
  | #[whereAtom, unknown3, structs] =>
    assumeMissing unknown3
    return structureAtom <_> declId <_> (combine (.<**>.) explicitBinder.getArgs) <_> whereAtom <$$$> structs <> ((""<$$$>"") <? optDeriving)
  | _ => failure
| _ => failure

#coreFmt Lean.Parser.Command.structFields fun
| #[structs] => do
  return Doc.nest 2 (combine (.<$$$>.) structs.getArgs)
| _ => failure

#coreFmt «term{_}» fun
| #[lparen, args, rparen] =>
  return lparen <_> addSpaceAfterCommas args.getArgs <_> rparen
| _ => failure

#coreFmt Lean.Parser.Term.tuple fun
| #[lparen, args, rparen] =>
  return lparen <> addSpaceAfterCommas args.getArgs <> rparen
| _ => failure

#coreFmt Lean.Parser.Term.pipeProj fun
| #[left, pipe, func, target] =>
  return left <_> pipe <> func <_> combine (.<**>.) target.getArgs
| _ => failure

#coreFmt Lean.Parser.Tactic.«tacticNext_=>_» fun
| #[nextAtom, binders, arrow, tactic] =>
  return nextAtom <_> (combine (.<_>.) binders.getArgs) <_> arrow <$$> tactic
| _ => failure

#coreFmt Lean.Parser.Tactic.split fun
| #[splitAt, unknown1, location] => do
  assumeMissing unknown1
  return splitAt <**> location
| _ => failure

def tacticSeqIndentSeparators : List Lean.Syntax → Doc
  | [] => toDoc ""
  | x::[] => toDoc x
  | proof::separator::xs =>
    if PrettyFormat.isEmpty separator then
      proof <$$$> (tacticSeqIndentSeparators xs)
    else
      proof <> separator <_> (tacticSeqIndentSeparators xs)

#coreFmt Lean.Parser.Tactic.tacticSeq1Indented fun
| #[args] => do
  return tacticSeqIndentSeparators args.getArgs.toList
| _ => failure

#coreFmt Lean.Parser.Term.haveIdDecl fun
| #[haveId, variables, typeSpec, assignAtom, val] => do
  return haveId <_> combine (.<_>.) variables.getArgs <**> typeSpec <_> assignAtom <**> val
| _ => failure

#coreFmt Lean.Parser.Tactic.renameI fun
| #[rename_iAtom, variables] =>
  return rename_iAtom <_> combine (.<_>.) variables.getArgs
| _ => failure

#coreFmt Lean.Parser.Tactic.unfold fun
| #[atom, idents, location] => do
  return (combine (.<_>.) #[toDoc atom, combine (.<_>.) idents.getArgs, combine (.<_>.) location.getArgs])
| _ => failure

#coreFmt Lean.Parser.Tactic.cases fun
| #[casesAtom, casesTarget, unknown1, proof] => do
  assumeMissing unknown1
  return combine (.<_>.) #[casesAtom, casesTarget, proof]
| _ => failure

#coreFmt Lean.Parser.Tactic.revert fun
| #[revertAtom, variables] =>
  return revertAtom <_> combine (.<_>.) variables.getArgs
| _ => failure


#coreFmt Lean.Parser.Tactic.locationHyp fun
| #[args, unknown1] => do
  assumeMissing unknown1
  return combine (.<_>.) args.getArgs
| _ => failure

#coreFmt Lean.Parser.Term.matchDiscr fun
| #[var, caseIdent] => do
  return (combine (.<_>.) var.getArgs) <**> caseIdent
| _ => failure

#coreFmt Lean.Parser.Term.doSeqIndent fun
| #[args] =>
  -- TODO: force newlines
  return Doc.nest 2 (combine (.<$$$>.) args.getArgs)
| _ => failure


#coreFmt Lean.Parser.Term.doHave combine' (.<**>.)




#coreFmt Lean.Parser.Term.doSeqItem fun
| #[doExpr, unknown1] => do
  assumeMissing unknown1
  return toDoc doExpr
| _ => failure

#coreFmt Lean.Parser.Term.do fun
| #[doAtom, value] => do
  let value ← formatStx value
  return (bridgeImmediate <! " " <> doAtom <$$$>value)
    <^>
    (doAtom <> (""<$$$>value <^> "" <_> flattenDoc (value)))
| _ => failure

#coreFmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, sep, after] =>
  if isEmpty sep then
    return (letSymbol <_> declaration <> bridgeHardNl !> after)
  else
    return (letSymbol <_> declaration <> sep <_> after)

| _ => failure

#coreFmt Lean.Parser.Command.structSimpleBinder fun
| #[declmodifiers, ident, optSig, unknown1] => do
  assumeMissing unknown1
  return declmodifiers <> ident <_> optSig
| _ => failure

#coreFmt «term{_:_//_}» fun
| #[lpar, ident, type, slashAtom, val ,rpar] =>
  return combine (.<_>.) #[toDoc lpar, toDoc ident, combine (.<_>.) type.getArgs, toDoc slashAtom, toDoc val, toDoc rpar]
| _ => failure

#coreFmt Lean.Parser.Term.termReturn fun
| #[returnAtom, val] =>
  return Doc.nest 2 (returnAtom <**> val)
| _ => failure

#coreFmt PrettyFormat.fmtCmd combine' (.<**>.)

#coreFmt PrettyFormat.coreFmtCmd combine' (.<**>.)


#coreFmt Lean.Parser.Term.leading_parser fun
| #[leadingParserAtom, unknown1, unknown2, value] => do
  assumeMissing unknown1
  assumeMissing unknown2
  return leadingParserAtom <$$$> value
| _ => failure



#coreFmt Lean.Parser.Command.quot fun
| #[lpar, decl, rpar] =>
  return lpar <$$> combine (.<$$>.) decl.getArgs <$$> rpar
  -- return lpar <$$$> decl <$$$> rpar <^> lpar <_> flattenPPL decl rpar
| _ => failure

#coreFmt Lean.Parser.Command.axiom fun
| #[axiomAtom, ident, decl] =>
  return axiomAtom <_> ident <**> decl
| _ => failure



#coreFmt Lean.Parser.Term.unsafe fun
| #[unsafeAtom, val] =>
  return unsafeAtom <**> val
| _ => failure

#coreFmt Lean.Parser.Term.binderTactic fun
| #[assignAtom, byAtom, proof] =>
  return Doc.nest 2 (assignAtom <_> byAtom <**> proof)
| _ => failure

#coreFmt Lean.Parser.Term.doPatDecl fun
| #[tuple, arrowAtom, doExpr, unknown1] => do
  assumeMissing unknown1
  return tuple <_> Doc.nest 2 (arrowAtom <**> doExpr)
| _ => failure

#coreFmt Lean.Parser.Term.doLetArrow fun
| #[letAtom, unknown1, val] => do
  assumeMissing unknown1
  return letAtom <_> val
| _ => failure

#coreFmt Lean.Parser.Term.doIdDecl fun
| #[ident, unknown1, arrowAtom, val] => do
  assumeMissing unknown1
  return ident <_> Doc.nest 2 (arrowAtom <**> val)
| _ => failure

#coreFmt Lean.Parser.Command.initialize fun
| #[declModifiers, initializeAtom, typeSpec, value] => do
  return declModifiers <**> initializeAtom <**> typeSpec <**> value
| _ => failure

#coreFmt Lean.Parser.Term.structInstFields fun
| #[args] => do
  return tacticSeqIndentSeparators args.getArgs.toList
| _ => failure

#coreFmt Lean.Parser.Command.in fun
| #[openCmd, inAtom, next] => do
  return openCmd <_> inAtom <$$$> next
| _ => failure

#coreFmt Lean.Parser.Command.elab fun
|#[declModifiers, unknown1, attrKind, elabAtom, unknown2, unknown3, unknown4, macroArgs, elabTail]  => do
  assumeMissing unknown1
  assumeMissing unknown2
  assumeMissing unknown3
  assumeMissing unknown4
  return (declModifiers ?> Doc.provide bridgeNl) <> attrKind <> elabAtom <**> combine (.<**>.) macroArgs.getArgs <**> elabTail
| _ => failure

#coreFmt Lean.Parser.Command.section combine' (.<_>.)


#coreFmt Lean.Parser.Command.attribute fun
| #[attributeAtom, lparen, attrInstance, rparen, content] =>
  return attributeAtom <> lparen <>attrInstance <> rparen <**> PrettyFormat.Doc.nest 2 (toDoc content)
| _ => failure

#coreFmt Lean.Parser.Tactic.tacticShow_ fun
| #[showAtom, proof] =>
  return showAtom <_> proof
| _ => failure

#coreFmt Lean.Parser.Term.structInstFieldDef fun
| #[assignAtom, value] =>
  return assignAtom <_>  bridgeImmediate ||| bridgeSpace ||| bridgeSpaceNl !> value
| _ => failure

#coreFmt Lean.Parser.Term.sort fun
| #[sortAtom, value] =>
  return sortAtom <**> value
| _ => failure

#coreFmt Lean.Parser.Tactic.Conv.conv combine' (. <_> .)

#coreFmt Lean.Parser.Tactic.Conv.unfold combine' (. <_> .)

#coreFmt Lean.Parser.Tactic.Conv.convSeq1Indented fun
| #[args] => do
  return tacticSeqIndentSeparators args.getArgs.toList
| _ => failure

#coreFmt Lean.Parser.Tactic.first fun
| #[firstAtom, proofs] =>
  return firstAtom <_> combine (.<**>.) proofs.getArgs
| _ => failure

#coreFmt group combine' (.<>.)

#coreFmt Lean.Parser.Term.namedArgument fun
| #[lparen, name, assignAtom, value, rparen] =>
  return lparen <> name <_> assignAtom <_> value <> rparen
| _ => failure


#coreFmt Lean.calcTactic fun
| #[calcAtom, tactic] =>
  return calcAtom <_> Doc.nest 2 (toDoc tactic)
| _ => failure

#coreFmt Lean.calcSteps fun
| #[firstStep, restSteps] =>
  return firstStep <$$$> combine (.<$$$>.) restSteps.getArgs
| _ => failure

#coreFmt Lean.calcFirstStep combine' (.<_>.)

#coreFmt Lean.calcStep fun
| #[lhs, assignAtom, rhs] =>
  return (lhs <_> Doc.nest 2 (assignAtom <_> rhs))
| _ => failure

#coreFmt Batteries.Tactic.seq_focus fun
| #[splitAtom, separatorAtom, lparen, proof, rparen] =>

  return splitAtom <_> separatorAtom <**> lparen <> (addSpaceAfterDelimiter (fun s => s == ";") proof.getArgs) <> rparen
| _ => failure

#coreFmt Lean.Parser.Command.abbrev fun
| #[abbrevAtom, decl, optSignature, declSimple] =>
  return abbrevAtom <_> Doc.nest 2 (combine (.<**>.) #[decl, optSignature, declSimple])
| _ => failure

#coreFmt Lean.Parser.Tactic.simpaArgsRest fun
| #[opt, unknown2, only, simpArgs, args] => do
  -- assumeMissing unknown1
  assumeMissing unknown2

  let argsSpaced := args.getArgs.map (fun (s : Lean.Syntax) =>
    if s.getArgs.size > 0 && s.getKind == `null then
      combine (.<_>.) s.getArgs
    else
      toDoc s
  )
  -- assumeMissing unknown4
  return combine (.<_>.) #[toDoc opt, toDoc only, combine (.<_>.) simpArgs.getArgs, combine (.<_>.) argsSpaced]
  -- return toPPL "????"
| _ => failure

#coreFmt Lean.Parser.Tactic.letrec fun
| #[letAtom, recAtom, val] =>
  return letAtom <_> Doc.nest 2 (recAtom <_> val)
| _ => failure

#coreFmt Lean.Parser.Term.structInstField fun
| #[field, value] =>
  return field <_> combine (·<_>·) value.getArgs
| _ => failure

#coreFmt Lean.Parser.Attr.simple combine' (· <_> ·)
#coreFmt Batteries.Tactic.Lint.nolint combine' (· <_> ·)


#coreFmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let condition ← formatStx condition
  let positiveBody ← formatStx positiveBody
  let negativeBody ← formatStx negativeBody

  let content := " " <> condition <> " " <> thenAtom <> Doc.nest 2 ("" <$$> positiveBody) <$$> elseAtom <> Doc.nest 2 ("" <$$> negativeBody)
  return ifAtom <> (content.group)
| _ => failure

#coreFmt group combine' (.<>.)

#coreFmt Lean.Parser.Term.byTactic' fun
| #[byAtom, proof] => do
  let proof ← formatStx proof
  return byAtom <$$> proof.group
| _ => failure

#coreFmt Lean.bracketedExplicitBinders fun
| #[lparen, ident, colonAtom, type, rparen] =>
  return lparen <> ident <_> colonAtom <_> type <> rparen
| _ => failure

#coreFmt Lean.Parser.Termination.decreasingBy fun
| #[decreasingByAtom, proof] =>
  return decreasingByAtom <_> proof
| _ => failure


#coreFmt Lean.Parser.Termination.suffix combine' (· <$$> ·)

#coreFmt Lean.Parser.Term.letIdDecl fun
| #[var, unknown1, typeInfo, assignOperator, content] => do
  assumeMissing unknown1
  -- return (← pf var) <> text " " <> (← pf unknown1) <> (← pf typeInfo) <> (← pf assignOperator) <> (← nest 2 (do (text " " <^> PPL.nl)<>(← pf content)))
  return var <_> unknown1 <> (typeInfo) <> assignOperator <> Doc.nest 2 ("" <_> content)
| _ => do
  failure

-- #coreFmt Lean.Parser.Tactic.simpAll combine' (· <**> ·)
#coreFmt Lean.Parser.Tactic.simpAll fun
| #[simpAll, optConfig, unknown1, onlyAtomContainer, proof] => do
  assumeMissing unknown1
  let formattedProof : Doc := match proof.getArgs with
  | #[lparen, content, rparen] =>
    lparen <> addSpaceAfterCommas content.getArgs <> rparen
  | a => combine (.<**>.) a
  return simpAll <> ("" <**> "" <? Doc.nest 2 (combine (.<**>.) #[toDoc optConfig, toDoc onlyAtomContainer, formattedProof]))
| _ => failure


#coreFmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, sep, after] =>
  if isEmpty sep then
    return (letSymbol <_> declaration <$$$> after )
  else
    return (letSymbol <_> declaration <> sep <_> after)
| _ => failure

#coreFmt Lean.Parser.Term.doLet combine' (.<_>.)
#coreFmt Lean.Parser.Term.doIf fun
| #[ifAtom, condition, thenAtom, positiveBody, unknown1, negativeBody] => do
  assumeMissing unknown1
  match negativeBody.getArgs with
  | #[elseAtom, negativeBody] =>
    let condition ← formatStx condition
    let positiveBody ← formatStx positiveBody
    let negativeBody ← formatStx negativeBody

    let content := " " <> condition <> " " <> thenAtom <> ("" <$$> positiveBody) <$$> elseAtom <> ("" <$$> negativeBody)
    return ifAtom <> (content.group)
  | _ => failure
| _ => failure

-- #coreFmt Lean.Parser.Term.doReturn combine' (.<_>.)
#coreFmt Lean.Parser.Term.doReturn fun
| #[returnAtom, content] =>
  return returnAtom <_> Doc.nest 2 (toDoc content)
| _ => failure

#coreFmt Lean.Parser.Term.structInst fun
| #[lpar, baseStruct, structFields, optEllipsis, unknown2, rpar] => do
  let structFields ← formatStx structFields
  -- assumeMissing unknown1
  assumeMissing unknown2

  return ((Doc.require bridgeImmediate <> " " <^> "") <> lpar <$$> Doc.nest 2 ((combine (.<_>.) baseStruct.getArgs) <$$> structFields <> ((""<$$>"") <? optEllipsis)) <> rpar).group
  -- return toDoc "what"
| _ => failure



#coreFmt Lean.Parser.Term.doLetElse fun
| #[letAtom, unknown1, var, assignAtom, value, barAtom, alternative] => do
  assumeMissing unknown1
  return letAtom <_> (var <_> assignAtom <_> value <_> barAtom <**> alternative)
| _ => failure

#coreFmt Lean.termThrowError__ fun
| #[throwAtom, desc] =>
  return throwAtom <**> desc
| _ => failure


#coreFmt Lean.Parser.Command.definition fun
| #[defAtom, declId, optDeclSig, val, derivings] => do
  let derive := match derivings.getArgs with
  | #[derivingAtom, values] => ""<$$$>derivingAtom <_> addSpaceAfterCommas values.getArgs
  | _ => toDoc ""

  return defAtom <_> Doc.nest 4 (combine (.<**>.) #[declId, optDeclSig]) <**> val <> derive
| _ => failure

#coreFmt Lean.Parser.Term.liftMethod combine' (.<_>.)


#coreFmt Lean.Parser.Term.attributes fun
| #[lparen, content, rparen] =>
  return lparen <> addSpaceAfterCommas content.getArgs <> rparen
| _ => failure

#coreFmt Lean.Parser.Term.depArrow combine' (.<**>.)
#coreFmt Lean.Parser.commandUnseal__ combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.dsimp fun
| #[dsimpAtom, optConfig, unknown1, onlyAtom, proof, location] => do
  assumeMissing unknown1
  let proof := match proof.getArgs with
  | #[lparen, content, rparen] =>
    lparen <> content <> rparen
  | _ => toDoc ""
  return dsimpAtom <_> optConfig <_> onlyAtom <**> proof <**> location
| _ => failure

#coreFmt Lean.Parser.Command.declValSimple fun
| #[assignAtom, value, suffix, whereDecls] => do
  let value ← formatStx value
  return (Doc.nest 2 (assignAtom <> ((("" <_> (flattenDoc value))
  <^> ("" <$$> value))))
  -- we require space here because we let the do notation handle the next indentation, which means that we momentarily have no indentation
  <^> bridgeSpace <! assignAtom <> bridgeImmediate !> value)
  <> (Doc.nl <? suffix)
  <> (Doc.nl <? whereDecls)
| _ => failure

#coreFmt Lean.Parser.Command.theorem fun
| #[theoremAtom, ident, typeSignature, content] =>
  return (theoremAtom <**> Doc.nest 4 (ident <**> (typeSignature ?> (""<_>""))) <> (toDoc content))
| _ => failure

#coreFmt Lean.Parser.Tactic.induction fun
| #[withAtom, symbol, usings, generalizingAtoms, inductionsAlts] => do
  -- generalizingAtoms contains ["generalizing", [variables...]]
  let syntaxes := generalizingAtoms.getArgs.map (fun (s : Lean.Syntax) =>
    if s.getArgs.size > 0 then
      combine (.<_>.) s.getArgs
    else
      toDoc s
  )
  return combine (.<_>.) #[toDoc withAtom, toDoc symbol, combine (.<_>.) usings.getArgs, combine (.<_>.) syntaxes, toDoc inductionsAlts]
  -- return combine (.<_>.) #[toDoc withAtom, toDoc symbol, combine (.<_>.) generalizingAtoms.getArgs, toDoc inductionsAlts]
-- | #[inductionAtom, ident, using, unknown1, inductionAlts, ] => do

| _ => failure

#coreFmt Lean.Parser.Syntax.paren fun
| #[lparen, content, rparen] =>
  return lparen <> combine (.<**>.) content.getArgs <> rparen
| _ => failure
#coreFmt Lean.Parser.Syntax.atom trivialPPL

#coreFmt Lean.Parser.Command.syntaxAbbrev fun
| #[docComment, syntaxAtom, ident, assignAtom, value] =>
  return docComment <$$> syntaxAtom <_> ident <_> assignAtom <**> Doc.nest 2 (combine (· <**> ·) value.getArgs)
| _ => failure
#coreFmt «stx_<|>_» termOperator

#coreFmt Lean.Parser.Command.syntax fun
| #[docComment, unknown1, attrKind, syntaxAtom, unknown2, unknown3, unknown4, value, colon, type] => do
  assumeMissing unknown1
  assumeMissing unknown2
  assumeMissing unknown3
  assumeMissing unknown4
  return docComment <$$> combine (· <**> .) #[attrKind, syntaxAtom] <**> Doc.nest 2 (combine (· <**> ·) #[combine (. <**> .) value.getArgs, toDoc colon, toDoc type])
| _ => failure


#coreFmt Lean.Parser.Command.docComment fun
| #[startAtom, content] =>

  -- TODO: handle whitespace comments after content
  match content with
  | .atom (_ : SourceInfo) (val : String) =>
    let parts := val.split (fun f => f == '\n') |>.map String.trimRight
    -- we don't just trim left, because some doc comments use indentation to convey meaning
    let removeFront:= parts.tail |> linePrefix |>.foldl Nat.min 1000000
    let tail := parts.tail |>.map (fun s => s.drop removeFront)

    let comments := (parts.head! :: tail)
      |>.foldl (fun (acc) (c:String) => acc <> Doc.nl <> c) (toDoc "")

    return ((startAtom <> flattenDoc (comments) <^> (startAtom <> comments)) <> (Doc.provide bridgeHardNl))
  | _ => failure
| _ => failure
