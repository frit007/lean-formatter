import BaseFormatter

import Lean.Parser.Term
import Lean.Elab.Attributes
import Lean.Parser
import Lean
import Lean.Parser.Tactic

namespace Lean.Elab.Command

-- syntax "| " term " => " term :FmtMatch

-- syntax (name:=fmtCmd) "#fmt " FmtMatch+ : command

-- infixl

-- initialize registerCoreFormatter

declare_syntax_cat FmtMatch
syntax term " => " term : FmtMatch
syntax term " => " term "| " FmtMatch : FmtMatch

syntax (name:=fmtCmd) "#fmt" ident "|" FmtMatch : command

partial def alternativesToMatchAlts (stx : Syntax): Array Syntax:=
  match stx with
  | `($m:term "=>" $val:term) =>
    let newNode := mkNode `Lean.Parser.Term.matchAlt #[mkAtom "|", m, mkAtom "=>", val]
    #[newNode]
  | `($m:term "=>" $val:term "|" $more:term) =>
    let newNode := mkNode `Lean.Parser.Term.matchAlt #[mkAtom "|", m, mkAtom "=>", val]
    alternativesToMatchAlts more |>.push newNode
  | _ =>
    #[]

-- initialize registerCoreFormatter `Term fun (stx : Syntax) => do
--   match stx with
--   | `(command|#fmt $id:ident | $matchAlternatives:FmtMatch) => return PrettyFormat.PPL.text "correct"
--   | stx => PrettyFormat.PPL.text "wrong"

macro_rules
| `(command|#fmt $id:ident | $matchAlternatives:FmtMatch) => do
  let matchAlternatives := mkNode `Lean.Parser.Term.matchAlts #[mkNullNode (alternativesToMatchAlts matchAlternatives)]
  `( )
  -- logInfo s!"Registered core formatter {keyIdent}"

-- @[command_elab fmtCmd]
-- def elabFmtFunction : CommandElab
-- | `(command|#fmt $id:ident | $keyIdent:FmtMatch) => do
--   logInfo s!"Registered core formatter {keyIdent}"
-- | stx => logError m!"Syntax tree?: {stx}"


#fmt fmtCmd
| `(#fmt $id:ident | $a:FmtMatch) => text "#fmt" <> PPL.nl <> text "content"
| _ => text "unknown"

-- #fmt fmtCmd
-- | `(#fmt $id:ident | $a:FmtMatch) => text "#fmt" <> PPL.nl <> text "content"
-- | `(#check $b) => text "#check" <> PPL.nl <> text "content"
-- | _ => text "unknown"

-- @[inline]
-- def withFn (f : ParserFn → ParserFn) (p : Parser) : Parser := { p with fn := f p.fn }

-- def many1NoAntiquot : Parser → Parser := withFn many1Fn

-- def adaptCacheableContextFn (f : CacheableParserContext → CacheableParserContext) (p : ParserFn) : ParserFn := fun c s =>
--   p { c with toCacheableParserContext := f c.toCacheableParserContext } s


-- def withPosition : Parser → Parser := withFn fun f c s =>
--     adaptCacheableContextFn ({ · with savedPos? := s.pos }) f c s

-- @[run_builtin_parser_attribute_hooks] def many1 (p : Parser) : Parser :=
--   many1NoAntiquot (withAntiquotSpliceAndSuffix `many p (symbol "*"))

-- @[run_builtin_parser_attribute_hooks, inline] def many1Indent (p : Parser) : Parser :=
--   withPosition $ many1 (checkColGe "irrelevant" >> p)

-- def matchAlts (rhsParser : Parser := termParser) : Parser :=
--   leading_parser withPosition $ many1Indent (ppLine >> matchAlt rhsParser)

-- syntax (name:=fmtCmd2) "#fmt2" "|" Lean.Parser.Term.matchAlts : command


def hi (x : Nat) : Nat :=
  match x with
  | 1 => 2
  | _ => 1

-- #fmt
-- |


-- @[command_parser] def «macro_rules» := leading_parser
--   optional docComment >> optional Term.«attributes» >> Term.attrKind >>
--   "macro_rules" >> optKind >> Term.matchAlts
