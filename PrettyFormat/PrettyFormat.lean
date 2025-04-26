import Std.Data.HashMap
import Lean
import PFMT
import Lean.Exception

open Lean
open Data
open Std

open Lean
open Lean.Meta
open Lean.Elab.Command


namespace PrettyFormat

partial def prettyPrint  (ppl : Doc) : String :=
  prettyPrint' 0 ppl
where
  prettyPrint' (indent:Nat): (ppl : Doc) → String
  | .fail s _ => "\n" ++ s ++ " "
  | .text s _ => s
  | .newline _ _ => "\n".pushn ' ' indent
  | .choice left right _ => prettyPrint' indent left ++ " | " ++ prettyPrint' indent right
  | .flatten inner _ => prettyPrint' indent inner
  | .align inner _ => prettyPrint' indent inner
  | .nest n inner _ => prettyPrint' (indent + n) inner
  | .concat left right _ => prettyPrint' indent left ++ prettyPrint' indent right
  | .stx stx _ => s!"stx {stx}"
  | .bubbleComment s _ => s!"bubbleComment {s}"
  | .reset s _ => s!"reset {prettyPrint' 0 s}"
  | .rule name s _ => s!"rule {name} {prettyPrint' indent s}"
  | .provide s _ => s!"provide {s}"
  | .require s _ => s!"require {s}"
  | .cost s _ => s!"cost {s}"

  def escapeQuotes (s : String) : String :=
    s.replace "\"" "\\\""

  inductive FormatError where
  | NotHandled (name : Name) (stx : List Syntax)
  | NoFormatter (stx : Syntax)
  | Unknown
  deriving Inhabited, Repr

  instance : ToString FormatError where
    toString b :=
      match b with
      | .NotHandled name stx =>
        let parentChain := stx.map (fun s => s.getKind) |>.filter (fun s => s != `missing && s != `ident) |>.map toString |>.reverse |> String.intercalate " → "

        s!"Not handled {name} {stx.length} chain: {parentChain}"
      | .NoFormatter stx => s!"NoFormatter {stx.getKind}"
      | .Unknown => "unknown"

  instance : Repr FormatError where
    reprPrec b n :=
      match b with
      | .NotHandled name stx => s!"Not handled {name} {repr stx}"
      | .NoFormatter stx => s!"NoFormatter {repr stx}"
      | .Unknown => "unknown"

  structure FormattingDiagnostic where
    failures : List (FormatError × List Syntax) := []
    -- to make it faster to debug write down the first instance the the formatter is missing
    missingFormatters : Std.HashMap Name Syntax := Std.HashMap.empty
  deriving Inhabited

  instance : Repr (IO.Ref FormattingDiagnostic) where
    reprPrec a n :=
      "ref Formatting diagnostic" --we cannot

  instance : Repr FormattingDiagnostic where
    reprPrec a n :=
      let failuresRepr := a.failures.foldl (fun acc (err, num) => s!"{acc}{repr err}:{num}\n") ""
      let missingFormattersRepr := a.missingFormatters.fold (fun acc name stx => s!"{acc}{name}:{stx}\n") ""
      s!"failures:\n{failuresRepr}\nmissingFormatters:\n{missingFormattersRepr}"
    -- match a with
    --   | (FormattingDiagnostic.failures lst) => lst.fold (fun acc name stx => s!"{acc}{name}:{stx}\n") ""
    --   | (FormattingDiagnostic.missingFormatters map) => map.fold (fun acc name stx => s!"{acc}{name}:{stx}\n") ""
  -- reprPrec n _ :=
  --   n.failures
  --   -- let failureCount :String := n..fold (fun acc x => s!"{acc}___:____\n") ""
  --   let missingFormattersRepr := n.missingFormatters.fold (fun acc name stx => s!"{acc}{name}:{stx}\n") ""
  --   s!"failures:\n{failureCount}\n missingFormatters:\n{missingFormattersRepr}"


  structure FormatReport where
    missingFormatters : Std.HashMap Name Nat := Std.HashMap.empty
    totalCommands: Nat := 0
    formattedCommands: Nat := 0
    timePF : Nat := 0
    timeDoc : Nat := 0
    timeReadAndParse : Nat := 0
    timeReparse : Nat := 0

  def FormatReport.combineReports (a : FormatReport) (b : FormatReport) : FormatReport :=
    { missingFormatters := a.missingFormatters.fold (fun acc name p => acc.insert name (acc.getD name 0 + p)) b.missingFormatters,
      totalCommands := a.totalCommands + b.totalCommands,
      formattedCommands := a.formattedCommands + b.formattedCommands
      timePF := a.timePF + b.timePF
      timeDoc := a.timeDoc + b.timeDoc
      timeReadAndParse := a.timeReadAndParse + b.timeReadAndParse
      timeReparse := a.timeReparse + b.timeReparse
    }

  structure FormatState where
    options: Options := {}
    nextId : Nat := 0 -- used to generate ids
    diagnostic: FormattingDiagnostic := {}
    stx : List Syntax := [] -- note that syntax is in reverse order for performance reasons
    formattingFunction : (Syntax → Nat → FormattingDiagnostic → List Syntax → (Doc × Nat × FormattingDiagnostic ))
  -- deriving Repr

  def FormatState.toReport (s : FormatState) : FormatReport :=
    { missingFormatters := s.diagnostic.missingFormatters.fold (fun acc name _ => acc.insert name (acc.getD name 0 + 1)) Std.HashMap.empty,
      totalCommands := 1,
      formattedCommands := 0
    }

  abbrev FormatM a := (StateM FormatState) a
  abbrev RuleM a := ExceptT FormatError FormatM a
  abbrev RuleRec := (Syntax → FormatM Doc)
  -- abbrev Rule := RuleRec → Array Syntax → (RuleM PPL)

  -- abbrev RuleCtx := ReaderT RuleRec RuleM PPL
  abbrev Rule := Array Syntax → RuleM Doc

  abbrev Formatter := (Name → Option Rule)
  abbrev Formatters := List (Formatter)

  def RuleRec.placeHolder : RuleRec := fun _ => do
    return toDoc "stx"

  def formatStx (stx : Syntax) : FormatM Doc := do
    let s ← get
    let (doc, nextId, diagnostics) := s.formattingFunction stx s.nextId s.diagnostic s.stx
    -- We do this to avoid cyclic dependencies in the definition of FormatState
    -- however this means that this code is fragile, because we need to make sure that all necessary fields are copied at this point
    set { s with nextId := nextId, diagnostic := diagnostics }
    return doc

  unsafe def mkPFormatAttr : IO (KeyedDeclsAttribute Rule) :=
    KeyedDeclsAttribute.init {
      builtinName := `builtin_pFormat,
      name := `pFormat,
      descr    := "Register a formatter.

      [pFormat k]"
      valueTypeName := `PrettyFormat.Rule
      evalKey := fun _ stx => do
        let stx ← Attribute.Builtin.getIdent stx
        let kind := stx.getId
        pure kind
    } `pFormat
  @[init mkPFormatAttr] opaque pFormatAttr : KeyedDeclsAttribute Rule

instance : MonadBacktrack FormatState RuleM where
  saveState      := get
  restoreState s := set s

@[inline] protected def orElse (x : RuleM α) (y : Unit → RuleM α) : RuleM α := do
  let s ← saveState
  try x catch _ => do set s; y ()

instance : OrElse (RuleM α) := ⟨PrettyFormat.orElse⟩

instance : Alternative RuleM where
  failure := fun {_} => do

    throw (FormatError.NotHandled (← get).stx.head!.getKind (← get).stx)
  orElse  := PrettyFormat.orElse



register_option pf.lineLength : Nat := {
  defValue := 100
  group    := "pf"
  descr    := "(pretty format) Maximum number of characters in a line"
}

register_option pf.debugSyntax : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, before being formatted"
}
register_option pf.debugSyntaxAfter : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, after being formatted"
}
register_option pf.debugErrors : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the errors"
}
register_option pf.debugMissingFormatters : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output a list of missing formatters above the function"
}
register_option pf.debugPPL : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the generated PPL above the function"
}
register_option pf.debugPPLGroups : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) Add grouping around every PPL formatter"
}
register_option pf.debugDoc : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) debug the generated Doc"
}
register_option pf.warnCSTmismatch : Bool := {
    defValue := true
    group    := "pf"
    descr    := "(pretty format) When the formatted syntax does not match the original syntax, output a warning"
}
register_option pf.debugTime : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) Debug how time is used"
}
register_option pf.debugLog : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) Debug logging"
}

def getPFLineLength (o : Options) : Nat := o.get pf.lineLength.name pf.lineLength.defValue

def getDebugSyntax (o : Options) : Bool := (o.get pf.debugSyntax.name pf.debugSyntax.defValue)
def getDebugSyntaxAfter (o : Options) : Bool := (o.get pf.debugSyntaxAfter.name pf.debugSyntaxAfter.defValue)
def getDebugErrors (o : Options) : Bool := (o.get pf.debugErrors.name pf.debugErrors.defValue)
def getDebugMissingFormatters (o : Options) : Bool := (o.get pf.debugMissingFormatters.name pf.debugMissingFormatters.defValue)
def getDebugPPL (o : Options) : Bool := (o.get pf.debugPPL.name pf.debugPPL.defValue)
def getDebugDoc (o : Options) : Bool := (o.get pf.debugDoc.name pf.debugDoc.defValue)
def getWarnCSTmismatch (o : Options) : Bool := (o.get pf.warnCSTmismatch.name pf.warnCSTmismatch.defValue)
def getDebugTime (o : Options) : Bool := (o.get pf.debugTime.name pf.debugTime.defValue)
def getDebugLog (o : Options) : Bool := (o.get pf.debugLog.name pf.debugLog.defValue)

initialize coreFormatters : IO.Ref (Std.HashMap Name (Rule)) ← IO.mkRef {}

def RuleM.genId : RuleM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId

def FormatM.genId : FormatM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId


end PrettyFormat
