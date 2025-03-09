import PrettyFormat
import CoreFormatters

open Lean Meta

syntax (name := formatCmd)
  "#format" ppLine command : command

open Lean Elab Parser Command

@[command_elab formatCmd]
unsafe def elabFormatCmd : CommandElab
  | `(command|#format $cmd) => liftTermElabM do
    let env ← getEnv
    logInfo s!"\n{cmd.raw.prettyPrint}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"


/--
info:
def x := do 10 + 12
-/
#guard_msgs in
#format
  def x := do 10 + 12 -- hi?



/-- info: "done" -/
#guard_msgs in
#eval "done"




def withPushMacroExpansionStack (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

def withMacroExpansion (beforeStx afterStx : Syntax) (x : TermElabM α) : TermElabM α :=
  Lean.Elab.Term.ContainsPendingMVar.elabTerm
  withMacroExpansionInfo beforeStx afterStx do
    withPushMacroExpansionStack beforeStx afterStx x



def adaptExpander (exp : Syntax → TermElabM Syntax) : TermElab := fun stx expectedType? => do
  let stx' ← exp stx
  withMacroExpansion stx stx' <| elabTerm stx' expectedType?

@[command_elab «macro_rules»] def elabMacroRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk $alts:matchAlt*) =>
    -- exclude command prefix from synthetic position used for e.g. jumping to the macro definition
    withRef (mkNullNode #[tk, mkNullNode alts]) do
      expandNoKindMacroRulesAux alts "macro_rules" fun kind? alts =>
        `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules $[(kind := $(mkIdent <$> kind?))]? $alts:matchAlt*)
  -- | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk (kind := $kind) | $x:ident => $rhs) =>
  --   withRef (mkNullNode #[tk, rhs]) do
  --     let attr ← `(attrInstance| $attrKind:attrKind macro $kind)
  --     let attrs := match attrs? with
  --       | some attrs => attrs.getElems.push attr
  --       | none => #[attr]
  --     `($[$doc?:docComment]? @[$attrs,*]
  --       Lean.Elab.Command.aux_def $(mkIdentFrom tk kind.getId (canonical := true)) $kind : Macro := fun $x:ident => $rhs)
  -- | `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind macro_rules%$tk (kind := $kind) $alts:matchAlt*) =>
  --   withRef (mkNullNode #[tk, mkNullNode alts]) do
  --     elabMacroRulesAux doc? attrs? attrKind tk (← resolveSyntaxKind kind.getId) alts
  | _  => throwUnsupportedSyntax


open TSyntax.Compat

def convertToTerm (s : Syntax) : Option (TSyntax `term) :=
  if s.isOfKind `term then
    some s  -- Lean automatically coerces Syntax to TSyntax `term
  else
    none

def convertToFmt (s : Syntax) : Option (TSyntax `fmtCmd) :=
  if s.isOfKind `term then
    some s  -- Lean automatically coerces Syntax to TSyntax `term
  else
    none

def example3 (s : Syntax) : IO Unit:=
  -- if s.isOfKind `term then
  --   some s  -- Lean automatically coerces Syntax to TSyntax `term
  -- else
  --   none

  match convertToFmt stx with
  | `(#fmt $typeExpr $fnExpr) =>
    IO.println ""
  | _ =>
    IO.println "aa"
