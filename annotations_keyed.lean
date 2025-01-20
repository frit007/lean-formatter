import Lean.Elab.Term
import Lean.PrettyPrinter.Delaborator.Options
import Lean.PrettyPrinter.Delaborator.SubExpr
import Lean.PrettyPrinter.Delaborator.TopDownAnalyze
import Lean.KeyedDeclsAttribute
open Lean
open Lean.Meta


open Lean.Meta Lean.SubExpr
open Lean.Elab (Info TermInfo Info.ofTermInfo)


structure FormatContext where
  optionsPerPos  : OptionsPerPos
  currNamespace  : Name
  inPattern      : Bool := false -- true when delaborating `match` patterns
  subExpr        : SubExpr
  /-- Current recursion depth during delaboration. Used by the `pp.deepTerms false` option. -/
  depth          : Nat := 0

structure MyState where
  mctx             : MetavarContext := {}
  cache            : Cache := {}
  deriving Inhabited


abbrev formatPPLM := ReaderT FormatContext (StateRefT MyState MetaM)
abbrev formatPPL := formatPPLM Nat

unsafe def mkPFormatAttr : IO (KeyedDeclsAttribute formatPPL) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtin_pFormat,
    name := `pFormat,
    descr    := "Register a delaborator.

  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`
  constructor `k`. Multiple delaborators for a single constructor are tried in turn until
  the first success. If the term to be delaborated is an application of a constant `c`,
  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")
  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
  is tried first.",
    valueTypeName := `formatPPL
    evalKey := fun _ stx => do
      let stx ← Attribute.Builtin.getIdent stx
      let kind := stx.getId
      if (← Elab.getInfoState).enabled && kind.getRoot == `app then
        let c := kind.replacePrefix `app .anonymous
        if (← getEnv).contains c then
          Elab.addConstInfo stx c none
      pure kind
  } `pFormat
@[init mkPFormatAttr] opaque pFormatAttr : KeyedDeclsAttribute formatPPL




-- initialize myAttr : KeyedDeclsAttribute String ←
--   KeyedDeclsAttribute.init {
--     name := `myAttr,  -- The name of the attribute
--     descr := "An example attribute with a string key.",  -- Description
--     getParam := fun stx =>
--       match stx with
--       -- Parse the key from the syntax. For example, expecting `(myAttr "some_key")`.
--       | `(attr| myAttr &key:str) => return key.getString!
--       | _ => throwError "Invalid syntax for myAttr. Expected: (myAttr \"key\")"
--   }

macro "app_pFormat" id:ident : attr => do
  match ← Macro.resolveGlobalName id.getId with
  | [] => Macro.throwErrorAt id s!"unknown declaration '{id.getId}'"
  | [(c, [])] => `(attr| pFormat $(mkIdentFrom (canonical := true) id (`app ++ c)))
  | _ => Macro.throwErrorAt id s!"ambiguous declaration '{id.getId}'"

-- initialize myFunctionAttr : KeyedDeclsAttribute String ←
--   KeyedDeclsAttribute.init {
--     name := `myFunctionAttr,
--     descr := "An attribute to associate functions with string keys",
--     getKeys := fun val =>
--       match val with
--       | Expr.lit (Literal.strVal key) _ => [key]
--       | _ => []
--   }
