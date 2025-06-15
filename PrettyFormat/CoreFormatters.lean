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

def nullNode : Syntax := Syntax.node (Lean.SourceInfo.none) `null #[]


/-
function declaration
-/

#coreFmt Lean.Parser.Command.declaration fun
| s =>
  -- -- dbg_trace s!"declaration: {s}"
  let v := combine (. <> provideDoc (bridgeAny ||| bridgeImmediate) <> .) s
  -- -- dbg_trace s!"the vals?: {v.toString}"
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


-- TODO: handle do/by notation

#coreFmt Lean.Parser.Term.explicitBinder fun
| #[lparen, var, typeDecl, binder, rparen] => do
  return lparen <> ( combine (.<_>.) #[
        (combine (.<_>.) var.getArgs),
        (combine (.<_>.) typeDecl.getArgs),
        combine (.<_>.) binder.getArgs
      ]
    <> rparen).group
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
  return whereAtom <> nestDoc 2 ("" <$$$> decl)
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
  return (left <**> (operator <**> right).preferFlatten)
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
#coreFmt «term_<*>_» termOperator
#coreFmt «term_<*_» termOperator
#coreFmt «term_*>_» termOperator
#coreFmt «term_>>=_» termOperator


#coreFmt «term{}» combine' (.<>.)

#coreFmt Lean.Parser.Term.hole trivialPPL
#coreFmt Lean.binderIdent trivialPPL
#coreFmt fieldIdx trivialPPL
#coreFmt Lean.explicitBinders trivialPPL
#coreFmt Lean.Parser.Term.ellipsis trivialPPL
#coreFmt Lean.Parser.Tactic.tacticRfl trivialPPL
#coreFmt num trivialPPL

#coreFmt Lean.Parser.Command.protected trivialPPL


-- #coreFmt Lean.Parser.Command.whereStructInst combine' (.<$$>.)
#coreFmt Lean.Parser.Command.whereStructInst fun
| #[whereAtom, structInst, unknown1] => do
  assumeMissing unknown1
  return whereAtom <> (nestDoc 2 ("" <$$> structInst))
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

  let content := "" <_> condition <_> thenAtom <> nestDoc 2 ("" <$$> positiveBody) <$$> elseAtom <> nestDoc 2 ("" <$$> negativeBody)
  return ifAtom <> content.group
| _ => failure

--- Inductive ---
-- #coreFmt Lean.Parser.Command.inductive fun
-- | #[inductiveAtom, decl, optDeclSig, whereContainer, terms, unknown1, derive] => do
--   assumeMissing unknown1
--   return (combine (.<_>.) #[toPPL inductiveAtom, toPPL decl, toPPL optDeclSig, combine (.<_>.) whereContainer.getArgs])
--     <> (nestDoc 2 ("" <$$> combine (.<$$>.) terms.getArgs) <> (PPL.nl <? derive))
-- | _ => failure

#coreFmt Lean.Parser.Command.ctor fun
| #[docComment, barAtom, declModifiers, ident, optDeclSig] =>
  return docComment <> combine (.<_>.) #[barAtom, declModifiers, ident, optDeclSig]
| _ => failure

#coreFmt Lean.Parser.Command.optDeriving fun
| #[args] => return combine (.<**>.) args.getArgs
| _ => failure

--- TACTICS ---


#coreFmt Lean.Parser.Command.example fun
| #[exampleAtom, typeSignature, content] => do
  let content ← formatStx content
  let typeSignature ← formatStx typeSignature
  return (nestDoc 4 (combine (.<_>.) #[toDoc exampleAtom, (flattenDoc (toDoc typeSignature))] ))
  <_> nestDoc 2 ((bridgeNl !> toDoc content) <^> (bridgeImmediate !> content))
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
        (acc <> p <**> "")
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
| #[args] => return toDoc args -- TODO: is just a wrapper for `tacticSeq1`?
| _ => failure


-- #coreFmt Lean.cdot combine' (.<_>.)
#coreFmt Lean.cdot fun
| #[a, b] => return a <> nestDoc 2 ("" <_> b)
| _ => failure


-- #coreFmt Lean.Parser.Tactic.unfold fun
-- | args => failure



#coreFmt Lean.Parser.Command.private combine' (.<_>.) -- ident

#coreFmt Lean.Parser.Tactic.rwRuleSeq fun
| #[lpar, rwSeq, rpar] => do
  return (toDoc lpar) <> (addSpaceAfterCommas rwSeq.getArgs) <> (toDoc rpar)
| _ => failure




#coreFmt Lean.Parser.Tactic.location combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.«tactic_<;>_» combine' (.<_>.)

#coreFmt «tacticBy_cases_:_» fun
| #[atom, idents, term] =>
  return combine (.<_>.) #[toDoc atom, combine (.<_>.) idents.getArgs, toDoc term]
| _ => failure


#coreFmt «term¬_» combine' (.<>.)

#coreFmt Lean.Parser.Term.implicitBinder fun
| #[lpar, vars, types, rpar] =>
  return toDoc lpar <> combine (.<_>.) (vars.getArgs) <> ((""<_>"") <? (combine (.<_>.) types.getArgs)) <> toDoc rpar
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

  return ((ifAtom <_> binder <_> colonAtom <_> statementTerm.group <_> thenAtom
    <$$> ((nestDoc 2 positiveTerm <^> bridgeImmediate !> positiveTerm))
    <$$> elseAtom).group <$$> (nestDoc 2 negativeTerm <^> bridgeImmediate !> negativeTerm)).group-- better?

  -- let multiline := ifAtom <_> binder <_> colonAtom <_> (flattenDoc statementTerm) <_> thenAtom
  --   <> nestDoc 2 (bridgeHardNl !> (positiveTerm)) <> " "
  -- <> bridgeHardNl !> elseAtom
  --   <> nestDoc 2 (bridgeHardNl !> (negativeTerm))

  -- return ifAtom <> " " <> binder <> " " <> colonAtom <> " " <> (flattenDoc statementTerm) <> " " <> thenAtom
  --   <> (bridgeSpace !> (flattenDoc positiveTerm)) <> " "
  -- <> elseAtom
  --   <> (bridgeSpace !> (flattenDoc negativeTerm)) <^>
  -- ((bridgeNl <! multiline <^> bridgeImmediate <! nestDoc 2 (Doc.nl <> multiline)))
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






-- def formatMatchAlt (flatten:Bool): Array Syntax → RuleM PPL
-- | #[barAtom, pattern, arrowAtom, v] => do
--   let mut patternSyntax := toPPL pattern
--   if pattern.matchesNull 1 && (pattern.getArgs.get! 0|>.getKind) == `null then
--     patternSyntax ← addSpaceAfterCommas (pattern.getArgs.get! 0|>.getArgs)

--   if flatten then
--     return (spaceNewline !> barAtom) <> [space] !> (flattenPPL patternSyntax) <> [space] !> (arrowAtom <> [space] !> flattenPPL v)
--   else
--     return (spaceNewline !> barAtom) <> [space] !> (flattenPPL patternSyntax) <> [space] !> nestDoc 2 (arrowAtom <> spaceNewline !> v)
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
  return combine (.<_>.) #[pattern, assignAtom] <> nestDoc 2 ( bridgeImmediate ||| bridgeSpace ||| bridgeSpaceNl !> val)
| _ => failure



#coreFmt Lean.Parser.Term.sufficesDecl combine' (.<**>.)


#coreFmt Lean.Parser.Term.type combine' (.<_>.)
#coreFmt Lean.Parser.Level.hole combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.exact combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.tacticLet_ combine' (.<_>.)

#coreFmt Lean.Parser.Term.strictImplicitBinder fun
| #[lpar, vars, types, rpar] =>
  return toDoc lpar <> combine (.<_>.) (vars.getArgs) <> ((""<_>"") <? (combine (.<_>.) types.getArgs)) <> toDoc rpar
| _ => failure

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
  assumeMissing unknown1
  return obtainAtom <> bridgeSpace !> cases <> bridgeSpace !> (combine (. <> provideDoc (bridgeAny ||| bridgeImmediate) <> .) assign.getArgs)
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
  return group <_> arrowAtom <>
  ((nestDoc 2 ( bridgeImmediate ||| bridgeNl !> proof))
  <^>
  (bridgeSpace !> flattenDoc (proof))
  )
| _ => failure

-- #coreFmt Lean.Parser.Tactic.intro combine' (.<_>.)
#coreFmt Lean.Parser.Tactic.intro fun
| #[introAtom, symbols] =>
  return introAtom <> ("" <_> "") <? combine (.<_>.) symbols.getArgs
| _ => failure


#coreFmt Lean.Parser.Tactic.tacticSuffices_ fun
| #[sufficesAtom, decl] =>
  return sufficesAtom <> nestDoc 2 ("" <**> decl)
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
    firstLine <> nestDoc 2 (bridgeHardNl !> positive) <> bridgeHardNl !> elseAtom <> nestDoc 2 (bridgeHardNl !> negative)
| _ => failure

#coreFmt Lean.Parser.Tactic.tacticTry_ combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.apply fun
| #[applyAtom, content] =>
  return applyAtom <> bridgeAny !> content
| _ => failure

#coreFmt Lean.Parser.Tactic.rwRule combine' (.<_>.)

#coreFmt Lean.Parser.Tactic.specialize fun
| #[specializeAtom, app] =>
  return specializeAtom <> bridgeSpace !> (nestDoc 2 (toDoc app))
| _ => failure

#coreFmt Lean.«term∀__,_» fun
| #[forAllAtom, binder, binderTerm, commaAtom, proof] =>
  return nestDoc 2 (forAllAtom <> bridgeSpace !> binder <> bridgeSpace !> binderTerm <> commaAtom <> bridgeSpace !> proof)
| _ => failure

#coreFmt Lean.Parser.Term.syntheticHole combine' (.<>.)
#coreFmt Lean.«binderTerm∈_» combine' (.<_>.)




#coreFmt Lean.Parser.Command.universe fun
| #[universeAtom, variables] =>
  return nestDoc 2 (combine (.<_>.) #[toDoc universeAtom, combine (.<_>.) variables.getArgs])
| _ => failure

#coreFmt Lean.Parser.Command.variable fun
| #[variableAtom, binders] =>
  return nestDoc 2 (combine (.<_>.) #[toDoc variableAtom, combine (.<_>.) binders.getArgs])
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
  return nestDoc 2 (combine (.<_>.) #[simpArithAtom, optConfig, onlyAtom, proof])
| _ => failure


#coreFmt Lean.Parser.Term.letEqnsDecl fun
| #[goAtom, binder, typeSpec, matchAlts] =>
  return combine (.<_>.) #[toDoc goAtom, combine (.<_>.) binder.getArgs, combine (.<_>.) typeSpec.getArgs] <$$$> matchAlts
| _ => failure

#coreFmt Lean.Parser.Command.inductive fun
| #[inductiveAtom, decl, optDeclSig, whereContainer, terms, unknown1, derive] => do
  assumeMissing unknown1
  return (combine (.<_>.) #[toDoc inductiveAtom, toDoc decl, toDoc optDeclSig, combine (.<>" ??? "<>.) whereContainer.getArgs])
    <> (nestDoc 2 ("" <$$> combine (.<$$>.) terms.getArgs <> ("" <$$> "" <? derive)))
| _ => failure


#coreFmt Lean.Parser.Command.declValEqns fun
| args =>
  return (combine (.<>.) args)




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



#coreFmt Lean.Parser.Command.structFields fun
| #[structs] => do
  return nestDoc 2 (combine (.<$$$>.) structs.getArgs)
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


#coreFmt Lean.Parser.Tactic.renameI fun
| #[rename_iAtom, variables] =>
  return rename_iAtom <_> combine (.<_>.) variables.getArgs
| _ => failure

#coreFmt Lean.Parser.Tactic.unfold fun
| #[atom, idents, location] => do
  return (combine (.<_>.) #[toDoc atom, combine (.<_>.) idents.getArgs, combine (.<_>.) location.getArgs])
| _ => failure


#coreFmt Lean.Parser.Tactic.revert fun
| #[revertAtom, variables] =>
  return revertAtom <_> combine (.<_>.) variables.getArgs
| _ => failure


#coreFmt Lean.Parser.Term.matchDiscr fun
| #[var, caseIdent] => do
  return (combine (.<_>.) var.getArgs) <**> caseIdent
| _ => failure

#coreFmt Lean.Parser.Term.doSeqIndent fun
| #[args] =>
  -- TODO: force newlines
  return nestDoc 2 (combine (.<$$$>.) args.getArgs)
| _ => failure


#coreFmt Lean.Parser.Term.doHave combine' (.<**>.)




#coreFmt Lean.Parser.Term.doSeqItem fun
| #[doExpr, unknown1] => do
  -- TODO: this unknown1 might contain a semicolon
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




#coreFmt «term{_:_//_}» fun
| #[lpar, ident, type, slashAtom, val ,rpar] =>
  return combine (.<_>.) #[toDoc lpar, toDoc ident, combine (.<_>.) type.getArgs, toDoc slashAtom, toDoc val, toDoc rpar]
| _ => failure

#coreFmt Lean.Parser.Term.termReturn fun
| #[returnAtom, val] =>
  return nestDoc 2 (returnAtom <**> val)
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
  return nestDoc 2 (assignAtom <_> byAtom <**> proof)
| _ => failure

#coreFmt Lean.Parser.Term.doPatDecl fun
| #[tuple, arrowAtom, doExpr, unknown1] => do
  assumeMissing unknown1
  return tuple <_> nestDoc 2 (arrowAtom <**> doExpr)
| _ => failure

#coreFmt Lean.Parser.Term.doLetArrow fun
| #[letAtom, unknown1, val] => do
  assumeMissing unknown1
  return letAtom <_> val
| _ => failure

#coreFmt Lean.Parser.Term.doIdDecl fun
| #[ident, unknown1, arrowAtom, val] => do
  assumeMissing unknown1
  return ident <_> nestDoc 2 (arrowAtom <**> val)
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
  return (declModifiers ?> provideDoc bridgeNl) <> attrKind <> elabAtom <**> combine (.<**>.) macroArgs.getArgs <**> elabTail
| _ => failure

#coreFmt Lean.Parser.Command.section combine' (.<_>.)


#coreFmt Lean.Parser.Tactic.tacticShow_ fun
| #[showAtom, proof] =>
  return showAtom <_> proof
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
  return calcAtom <_> nestDoc 2 (toDoc tactic)
| _ => failure

#coreFmt Lean.calcSteps fun
| #[firstStep, restSteps] =>
  return firstStep <$$$> combine (.<$$$>.) restSteps.getArgs
| _ => failure

#coreFmt Lean.calcFirstStep combine' (.<_>.)

#coreFmt Lean.calcStep fun
| #[lhs, assignAtom, rhs] =>
  return (lhs <_> nestDoc 2 (assignAtom <_> rhs))
| _ => failure

#coreFmt Batteries.Tactic.seq_focus fun
| #[splitAtom, separatorAtom, lparen, proof, rparen] =>

  return splitAtom <_> separatorAtom <**> lparen <> (addSpaceAfterDelimiter (fun s => s == ";") proof.getArgs) <> rparen
| _ => failure

#coreFmt Lean.Parser.Command.abbrev fun
| #[abbrevAtom, decl, optSignature, declSimple] =>
  return abbrevAtom <_> nestDoc 2 (combine (.<**>.) #[decl, optSignature, declSimple])
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
  return letAtom <_> nestDoc 2 (recAtom <_> val)
| _ => failure



#coreFmt Lean.Parser.Attr.simple combine' (· <_> ·)
#coreFmt Batteries.Tactic.Lint.nolint combine' (· <_> ·)


#coreFmt termIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let condition ← formatStx condition
  let positiveBody ← formatStx positiveBody
  let negativeBody ← formatStx negativeBody

  let content := ""<_> condition <_> thenAtom <> nestDoc 2 ("" <$$> positiveBody) <$$> elseAtom <> nestDoc 2 ("" <$$> negativeBody)
  return ifAtom <> (content.group)
| _ => failure

#coreFmt group combine' (.<>.)


#coreFmt Lean.bracketedExplicitBinders fun
| #[lparen, ident, colonAtom, type, rparen] =>
  return lparen <> ident <_> colonAtom <_> type <> rparen
| _ => failure

#coreFmt Lean.Parser.Termination.decreasingBy fun
| #[decreasingByAtom, proof] =>
  return decreasingByAtom <_> proof
| _ => failure


#coreFmt Lean.Parser.Termination.suffix combine' (· <$$> ·)

-- #coreFmt Lean.Parser.Tactic.simpAll combine' (· <**> ·)
#coreFmt Lean.Parser.Tactic.simpAll fun
| #[simpAll, optConfig, unknown1, onlyAtomContainer, proof] => do
  assumeMissing unknown1
  let formattedProof : Doc := match proof.getArgs with
  | #[lparen, content, rparen] =>
    lparen <> addSpaceAfterCommas content.getArgs <> rparen
  | a => combine (.<**>.) a
  return simpAll <> ("" <**> "" <? nestDoc 2 (combine (.<**>.) #[toDoc optConfig, toDoc onlyAtomContainer, formattedProof]))
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

    let content := "" <_> condition <_> thenAtom <> ("" <$$> positiveBody) <$$> elseAtom <> ("" <$$> negativeBody)
    return ifAtom <> (content.group)
  | _ => failure
| _ => failure

-- #coreFmt Lean.Parser.Term.doReturn combine' (.<_>.)
#coreFmt Lean.Parser.Term.doReturn fun
| #[returnAtom, content] =>
  return returnAtom <_> nestDoc 2 (toDoc content)
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
  -- -- dbg_trace s!"definition {defAtom} {declId} {optDeclSig} {val} {derivings}"
  let derive := match derivings.getArgs with
  | #[derivingAtom, values] => ""<$$$>derivingAtom <_> addSpaceAfterCommas values.getArgs
  | _ => toDoc ""

  -- return defAtom <_> nestDoc 4 (combine (.<**>.) #[declId, optDeclSig]) <**> val <> derive

  let l:=defAtom <_> nestDoc 4 (combine (.<**>.) #[declId, optDeclSig]) <**> val <> derive
  -- let sss:=toDoc "and"
  -- dbg_trace s!"def {repr l}"
  -- -- dbg_trace s!"def {repr (toDoc defAtom)} and {(← formatStx defAtom).toString} ___ {repr (combine (.<_>.) #[toDoc defAtom, sss])}"
  -- -- dbg_trace s!"definition v: {l.toString} derive? {derive.toString}"
  return l
| _ => failure

#coreFmt Lean.Parser.Term.liftMethod combine' (.<_>.)


#coreFmt Lean.Parser.Term.attributes fun
| #[lparen, content, rparen] =>
  return lparen <> addSpaceAfterCommas content.getArgs <> rparen
| _ => failure

#coreFmt Lean.Parser.Term.depArrow combine' (.<**>.)

#coreFmt Lean.Parser.Tactic.dsimp fun
| #[dsimpAtom, optConfig, unknown1, onlyAtom, proof, location] => do
  assumeMissing unknown1
  let proof := match proof.getArgs with
  | #[lparen, content, rparen] =>
    lparen <> content <> rparen
  | _ => toDoc ""
  return dsimpAtom <_> optConfig <_> onlyAtom <**> proof <**> location
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
  return docComment <$$> syntaxAtom <_> ident <_> assignAtom <**> nestDoc 2 (combine (· <**> ·) value.getArgs)
| _ => failure
#coreFmt «stx_<|>_» termOperator

#coreFmt Lean.Parser.Command.syntax fun
| #[docComment, unknown1, attrKind, syntaxAtom, unknown2, unknown3, unknown4, value, colon, type] => do
  assumeMissing unknown1
  assumeMissing unknown2
  assumeMissing unknown3
  assumeMissing unknown4
  return docComment <$$> combine (· <**> .) #[attrKind, syntaxAtom] <**> nestDoc 2 (combine (· <**> ·) #[combine (. <**> .) value.getArgs, toDoc colon, toDoc type])
| _ => failure



#coreFmt Lean.Parser.Command.declaration fun
| s =>
  -- -- dbg_trace s!"declaration: {s}"
  let v := combine (. <> provideDoc (bridgeAny ||| bridgeImmediate) <> .) s
  -- -- dbg_trace s!"the vals?: {v.toString}"
  return v.group

#coreFmt Lean.Parser.Command.declModifiers fun
| #[docComment, attributes, visibility, noncomputableS, unsafeS, partialS] => do
  let modifiers := combine (.<_>.) #[visibility, noncomputableS, unsafeS, partialS]
  return docComment <> (attributes ?> (""<**>"")) <> modifiers
| _ => failure

#coreFmt Lean.Parser.Command.docComment fun
| #[startAtom, content] =>
  -- dbg_trace s!"@docComment start"

  -- TODO: handle whitespace comments after content
  match content with
  | .atom _ (val : String) =>
    let parts := val.split (fun f => f == '\n') |>.map String.trimRight
    -- we don't just trim left, because some doc comments use indentation to convey meaning
    let removeFront:= parts.tail |> linePrefix |>.foldl Nat.min 1000000
    let tail := parts.tail |>.map (fun s => s.drop removeFront)

    let comments := (parts.head! :: tail)
      |>.foldl (fun (acc) (c:String) => acc <> Doc.nl <> c) (toDoc "")

    let l := ((startAtom <> flattenDoc (comments) <^> (startAtom <> comments)) <> (provideDoc bridgeHardNl))
    -- dbg_trace s!"@docComment {repr l}"
    return l
  | _ => failure
| _ => failure



#coreFmt List.«term_<:+:_» termOperator
#coreFmt List.«term_<:+_» termOperator
#coreFmt List.«term_<+:_» termOperator
#coreFmt Lean.unbracketedExplicitBinders fun
| #[binders, unknown1] => do
  assumeMissing unknown1
  return combine (.<_>.) binders.getArgs
| _ => failure

#coreFmt Lean.Parser.Tactic.case fun
| #[caseAtom, identArgs, arrowAtom, proof] => do
  let proof ← formatStx proof

  return caseAtom <_> addSpaceAfterCommas identArgs.getArgs <_> nestDoc 2 (arrowAtom <$$> proof)
| _ => failure

#coreFmt Lean.Parser.Tactic.simpArgs fun
| #[lparen, proof, rparen] => do
  return lparen <> addSpaceAfterCommas proof.getArgs <> rparen
| _ => failure

#coreFmt Lean.Parser.Term.anonymousCtor fun
| #[lbracket, rwSeq, rbracket] => do
  return ((toDoc lbracket) <> (provideDoc (bridgeNone)) <> (addSpaceAfterCommas rwSeq.getArgs) <> (toDoc rbracket)).preferFlatten
| _ => failure

#coreFmt Lean.Parser.commandUnseal__ fun
| #[unsealAtom, arguments] =>
  return unsealAtom <_> combine (.<_>.) arguments.getArgs
| _ => failure

#coreFmt Lean.Parser.Tactic.rintro fun
| #[rintroAtom, bindings, unknown1] => do
  assumeMissing unknown1
  return rintroAtom <_> combine (.<_>.) bindings.getArgs
| _ => failure







#coreFmt Lean.Parser.Tactic.simpa fun
| #[simpaAtom, unknown1, unknown2, argsRest] => do
  assumeMissing unknown1
  assumeMissing unknown2
  let argsRest ← formatStx argsRest

  return simpaAtom <_> nestDoc 2 (argsRest)
| _ => failure



#coreFmt Lean.Parser.Command.attribute fun
| #[attributeAtom, lparen, attrInstance, rparen, content] =>
  if content.getKind = `null then
    return attributeAtom <> lparen <>attrInstance <> rparen <**> PrettyFormat.nestDoc 2 (combine (.<**>.) content.getArgs)
  else
    return attributeAtom <> lparen <>attrInstance <> rparen <**> PrettyFormat.nestDoc 2 (toDoc content)
| _ => failure

#coreFmt Lean.Parser.Tactic.tacticHave_ combine' (.<_>.)
-- #coreFmt Lean.Parser.Tactic.tacticHave_ fun
-- | l => do
--   return toDoc "tactic_have_"

#coreFmt Lean.Parser.Tactic.cases fun
| #[casesAtom, casesTarget, unknown1, proof] => do
  assumeMissing unknown1
  return combine (.<_>.) #[casesAtom, casesTarget, proof]
| _ => failure



-- #coreFmt Lean.Parser.Command.declValEqns fun
-- | args => do
--   return "" <$$$>"declValEqns"
--   -- return (combine (.<>.) args)



#coreFmt Lean.Parser.Term.matchAltsWhereDecls fun
| #[wheres, suffix, unknown1] => do
  assumeMissing unknown1
  return nestDoc 2 (toDoc wheres) <> (""<$$$>"" <? suffix)
  -- return toDoc "matchAltsWhereDecls"
| _ => failure



#coreFmt Lean.Parser.Tactic.locationHyp fun
| #[args, next] => do
  --next is likely incomplete, it could be the "⊢" symbol
  return combine (.<_>.) args.getArgs <> ((""<_>"") <? next)
| _ => failure

#coreFmt Lean.Parser.Tactic.simp fun
| #[simpAtom, config, unknown1, proofOnly, proof, proofLocation] => do
  assumeMissing unknown1
  let proofLocation ← formatStx proofLocation
  let proofOnly ← formatStx proofOnly
  let content := (PrettyFormat.combine (.<_>.) #[toDoc config, toDoc proofOnly, ← formatSimpleProof proof.getArgs, toDoc proofLocation])
  return toDoc simpAtom <> ("" <_> "")<? nestDoc 2 content.group
| _ => failure



#coreFmt Lean.«term∃__,_» fun
| #[existAtom, binder, binderTerm, commaAtom, app] => do
  return existAtom <_> binder <_> binderTerm <> commaAtom <**> app
| _ => failure






#coreFmt Lean.Parser.Term.forall fun
| #[forallAtom, binder, typeInfo, commaAtom, arrow] => do
  let spacedTypeInfo := combine (.<_>.) typeInfo.getArgs
  return forallAtom <_> ((combine (.<**>.) #[combine (.<_>.) binder.getArgs, spacedTypeInfo]) <> commaAtom <_> arrow)
| _ => failure


#coreFmt Lean.Parser.Command.export fun
| #[exportAtom, name, lparen, value, rparen] =>
  -- return toDoc value
  return exportAtom <_> nestDoc 2 (name <_> lparen <> combine (.<**>.) value.getArgs <>rparen)
| _ => failure

#coreFmt Lean.Parser.Term.typeSpec fun
| #[colonAtom, type] =>
  return colonAtom <**> (toDoc type).preferFlatten
| _ => failure







#coreFmt Lean.Parser.Tactic.rcases fun
| #[rcasesAtom, target, withAtom] =>
  return rcasesAtom <_> addSpaceAfterCommas target.getArgs <_> combine (.<_>.) withAtom.getArgs
| _ => failure

#coreFmt Tactic.rcasesPatMed combine' (.<_>.)

#coreFmt Lean.Parser.Command.instance fun
| #[kind, instanceAtom, declId, typeSpec, decl, whereStructInst] => do

  let declaration := combine (.<_>.) #[kind, instanceAtom] <_> nestDoc 4 (combine (.<**>.) #[declId, typeSpec, decl])
  let struct := (toDoc whereStructInst)
  -- dbg_trace "should have given instance_str"
  -- dbg_trace s!"instance_str: {(declaration <> bridgeAny !> struct).toString}"
  return declaration <> bridgeAny !> struct
| _ => failure


#coreFmt Lean.Parser.Command.theorem fun
| #[theoremAtom, ident, typeSignature, content] => do
  -- must allow newline after typeSignature, because it could be followed by

  let val := (requireDoc bridgeSpace <> bridgeImmediate !> content) <^> (("" <$$> content).group <> costDoc 3)

  return ((theoremAtom <**> nestDoc 4 (ident <**> ((typeSignature) ?> (""<**>"")))).group <> val.group).group
| _ => failure

#coreFmt Lean.Parser.Term.byTactic fun
| #[byAtom, tactic] => do
  let tactic ← formatStx tactic

  let content := byAtom <> (nestDoc 2 (bridgeHardNl !> tactic) <^> flattenDoc (bridgeSpace !> tactic))
  return (((((bridgeImmediate <! " ") <> (nestDoc 2 (byAtom <$$> tactic).group)))))
    <^> (bridgeNl <! byAtom <> costDoc 1 <> nestDoc 2 (bridgeNl !> tactic)) /-discourage newline, compared to bridge Immediate-/
    <^> (((bridgeSpace ||| bridgeNone) <! content))
| _ => failure

#coreFmt Lean.Parser.Command.declValSimple fun
| #[assignAtom, value, suffix, whereDecls] => do
  -- declValSimple breaks the rule "bridges should accept any"
  let value ← formatStx value
  return (nestDoc 2 ((bridgeImmediate|||bridgeSpace) <! assignAtom <> ((
  ("" <$$> value)<^> ("" <_> (flattenDoc value)))))
  -- we require space here because we let the do notation handle the next indentation, which means that we momentarily have no indentation
  <^> bridgeImmediate <! assignAtom <> bridgeImmediate !> value
  )
  <> (Doc.nl <? suffix)
  <> (Doc.nl <? whereDecls)
| _ => failure

#coreFmt «term_∨_» combine' (.<_>.)

#coreFmt Lean.Parser.Term.nomatch combine' (.<_>.)
#coreFmt Lean.Parser.Command.extends combine' (.<_>.)

#coreFmt Lean.Parser.Term.basicFun fun
| #[args, typeDecl, arrowAtom, content] => do
  let content ← formatStx content
  let typeDecl ← formatStx typeDecl

  let argsFormatted := combine (· <_> ·) args.getArgs
  return (bridgeImmediate <! " " <> nestDoc 2 (combine (. <_> .) #[argsFormatted, flattenDoc (toDoc typeDecl), toDoc arrowAtom] <> (Doc.nl <> content)))
   <^> (
    combine (· <_> ·) #[argsFormatted, flattenDoc (toDoc typeDecl), toDoc arrowAtom] <> ((nestDoc 2 (Doc.nl <> content)) <^> ("" <_> (flattenDoc (toDoc content))))
   )
| _ => failure


#coreFmt Lean.Parser.Term.match fun
| #[matchAtom, unknown1, unknown2, matchDiscr, withAtom, matchAlts] => do
  assumeMissing unknown1
  assumeMissing unknown2
  -- we might want to allow a variation of bridgeImmediate, because we might want to allow match being assigned to a value,
  -- (bridgeImmediate <! " "<> matchAtom <_> nestDoc 2 (matchDiscr <_> withAtom <> bridgeNl !> matchAlts)) <^>
  return (matchAtom <_> matchDiscr <_> withAtom <> bridgeNl !> matchAlts)
| _ => failure

#coreFmt Lean.Parser.Term.instBinder fun
| #[lparen, inst, app, rparen] =>
  return lparen <> combine (.<_>.) #[combine (.<_>.) inst.getArgs, toDoc app] <> rparen
| _ => failure



#coreFmt Lean.Parser.Term.structInst fun
| #[lpar, baseStruct, structFields, optEllipsis, unknown2, rpar] => do
  let structFields ← formatStx structFields
  -- assumeMissing unknown1
  assumeMissing unknown2

  let value := lpar <$$> nestDoc 2 ((combine (.<_>.) baseStruct.getArgs) <$$> structFields <> ((""<$$>"") <? optEllipsis)) <> rpar
  return (Doc.require bridgeImmediate <_> nestDoc 2 value <^> value).group
  -- return toDoc "what"
| _ => failure

#coreFmt boolIfThenElse fun
| #[ifAtom, condition, thenAtom, positiveBody, elseAtom, negativeBody] => do
  let condition ← formatStx condition
  let positiveBody ← formatStx positiveBody
  let negativeBody ← formatStx negativeBody

  let content := "" <_> condition <_> thenAtom <> nestDoc 2 ("" <$$> positiveBody) <$$> elseAtom <> nestDoc 2 ("" <$$> negativeBody)
  return ifAtom <> content.group
| _ => failure

#coreFmt «term_::_» combine' (.<_>.)


#coreFmt «term_%_» termOperator

#coreFmt Lean.Parser.Term.matchAlt fun
| #[barAtom, pattern, arrowAtom, value] => do
  let value ← formatStx value
  let patternSyntax :=
    if pattern.getKind == `null then
      combine (.<_>.) (pattern.getArgs.map (fun a =>
        if a.getKind == `null then
          addSpaceAfterCommas a.getArgs
        else
          toDoc a
      ))
      -- addSpaceAfterCommas (.get! 0|>.getArgs)
    else
      toDoc pattern

  return (bridgeNl !> barAtom) <_> (flattenDoc patternSyntax) <_> ((nestDoc 2 (arrowAtom <> (bridgeNl !> value <^> (bridgeSpace !>flattenDoc value)))) <^> (arrowAtom <> bridgeImmediate !> value))
| _ => failure


#coreFmt Lean.Parser.Term.pipeProj fun
| #[left, pipe, func, target] =>
  return left <_> pipe <> func <> ((""<_>"") <? (combine (.<**>.) target.getArgs))
| _ => failure

#coreFmt Lean.Parser.Term.letrec fun
| #[letRecGroup, defintition, unknown1, after] => do
  assumeMissing unknown1;
  return combine (.<_>.) letRecGroup.getArgs <**> defintition <$$$> after
| _ => failure


#coreFmt Lean.Parser.Command.mixfix combine' (.<_>.) -- TODO: There is probably more to this. It is used to define scoped infixl



#coreFmt Lean.Parser.Command.structSimpleBinder fun
-- | #[declmodifiers, ident, optSig, unknown1] => do
--   assumeMissing unknown1
--   return declmodifiers <> ident <_> optSig

| #[declmodifiers, ident, optSig, binder] => do
  -- assumeMissing unknown1
  return declmodifiers <> ident <_> optSig <> ((""<_>"") <? binder)
-- | #[a,b,c,d,e] => return toDoc "5 ahahah"
| _ => failure

#coreFmt Lean.Parser.Command.structure fun
| #[structureAtom, declId, explicitBinder, extend, typeDecl, structFields, optDeriving] => do

  match structFields.getArgs with
  | #[whereAtom, renamer, structs] =>
    -- assumeMissing unknown2
    -- return toDoc unknown2
    if (PrettyFormat.isEmpty renamer) then
      return structureAtom <_> declId <_> (combine (.<**>.) explicitBinder.getArgs) <> (""<_>""<?extend) <> ((""<_>"")<?(combine (.<**>.) typeDecl.getArgs)) <_> whereAtom <$$$> structs <> ((""<$$$>"") <? optDeriving)
    else
      return structureAtom <_> declId <_> (combine (.<**>.) explicitBinder.getArgs) <> (""<_>""<?extend) <> ((""<_>"")<?(combine (.<**>.) typeDecl.getArgs)) <_> whereAtom <$$$> nestDoc 2 renamer <$$$> structs <> ((""<$$$>"") <? optDeriving)
  | #[] =>
    return structureAtom <_> declId <_> (combine (.<**>.) explicitBinder.getArgs) <> (""<_>""<?extend) <> ((""<_>"")<?(combine (.<**>.) typeDecl.getArgs))  <> ((""<$$$>"") <? optDeriving)
  | _ => failure
| _ => failure

#coreFmt «term_&&_» termOperator


#coreFmt Lean.Parser.Term.byTactic' fun
| #[byAtom, proof] => do
  let proof ← formatStx proof
  return ((bridgeImmediate <! " " <> byAtom <$$> nestDoc 2 proof) <^> byAtom <$$> proof <> costDoc 1).group
| _ => failure

#coreFmt Lean.Parser.Term.haveIdDecl fun
| #[haveId, variables, typeSpec, assignAtom, val] => do
  return haveId <_> nestDoc 2 (combine (.<_>.) variables.getArgs <**> typeSpec <_> assignAtom <**> val)
| _ => failure

#coreFmt Lean.Parser.Term.structInstFieldDef fun
| #[assignAtom, value] =>
  return assignAtom <**> nestDoc 2 (value)
    <^> (assignAtom <> bridgeImmediate !> value)
| _ => failure




#coreFmt Lean.Parser.Term.let fun
| #[letSymbol, declaration, sep, after] =>
  if PrettyFormat.isEmpty sep then
    return (bridgeHardNl<!letSymbol <_> declaration <> bridgeHardNl !> after)
  else
    return (bridgeHardNl<!letSymbol <_> declaration <> sep <**> after)
| _ => failure


#coreFmt Lean.Parser.Term.structInstField fun
| #[field, value] => do
  match value.getArgs with
  | #[t, sep, val] =>
    -- assumeMissing unknown1
    return field <_> combine (·<_>·) #[combine (.<_>.) t.getArgs, toDoc sep, toDoc val]
  | _ =>
    return field <> ((""<_>"") <? addSpaceAfterCommas value.getArgs)
| _ => failure
