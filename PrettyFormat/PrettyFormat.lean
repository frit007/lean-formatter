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
    reprPrec b _ :=
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
    reprPrec _ _ :=
      "ref Formatting diagnostic"

  instance : Repr FormattingDiagnostic where
    reprPrec a _ :=
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

  def FormatReport.serialize (r : FormatReport) : String :=
    let formatters := r.missingFormatters.fold (fun acc key val =>
      if acc != "" then
        s!"{acc};:;:;{val};{key}"
      else
        s!"{val};{key}"
    ) ""
    s!"{r.totalCommands},{r.formattedCommands},{r.timePF},{r.timeDoc},{r.timeReadAndParse},{r.timeReparse},{formatters}"



  def FormatReport.deserialize (s : String) : FormatReport :=
    match s.split (fun c => c == ',') with
    | totalCommands :: formattedCommands :: timePF :: timeDoc :: timeReadAndParse :: timeReparse :: rest =>
      let formatters := rest.intersperse "," |> String.join |>.splitOn ";:;:;"
      -- IO.println s!"{keys.length}"
      let missingFormatters : Std.HashMap Name Nat := formatters.foldl (fun acc x =>
        let count := x.takeWhile (fun c => c != ';')
        let formatter := x.dropWhile (fun c => c != ';') |>.drop 1
        match count.toNat? with
        | some c =>
          acc.insert formatter.toName c
        | _ =>
          acc.insert formatter.toName 1
      ) {}
      match (totalCommands.toNat?, formattedCommands.toNat?, timePF.toNat?, timeDoc.toNat?, timeReadAndParse.toNat?, timeReparse.toNat?) with
      | (some totalCommands, some formattedCommands, some timePF, some timeDoc, some timeReadAndParse, some timeReparse) =>
        {
          totalCommands := totalCommands
          formattedCommands := formattedCommands
          timePF := timePF
          timeDoc := timeDoc
          timeReadAndParse := timeReadAndParse
          timeReparse := timeReparse
          missingFormatters := missingFormatters
        }
      | _ => {}
    | _ => {}

  def skipFormatting : Syntax → Nat → FormattingDiagnostic → List Syntax → (Doc × Nat × FormattingDiagnostic)
  | _, n, d, _ => (toDoc "skip", n, d)

  structure FormatState where
    options: Options := {}
    nextId : Nat := 1 -- used to generate ids
    diagnostic: FormattingDiagnostic := {}
    cacheDistance : Nat := 3
    -- avoid calculating the syntax multiple times
    stxCache : Std.HashMap Nat Doc := {}
    stx : List Syntax := [] -- note that syntax is in reverse order for performance reasons
    formattingFunction : (Syntax → Nat → FormattingDiagnostic → List Syntax → (Doc × Nat × FormattingDiagnostic )) := skipFormatting
  -- deriving Repr



  def FormatState.toReport (s : FormatState) : FormatReport :=
    { missingFormatters := s.diagnostic.missingFormatters.fold (fun acc name _ => acc.insert name (acc.getD name 0 + 1)) Std.HashMap.empty,
      totalCommands := 1,
      formattedCommands := 0
    }

  abbrev FormatM a := (StateM FormatState) a
  abbrev RuleM a := ExceptT FormatError FormatM a
  abbrev RuleRec := (Syntax → FormatM Doc)

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

  def formatStxs (stx : Array Syntax) : FormatM (Array Doc) := do
    let mut formatted := #[]
    for s in stx do
      let doc ← formatStx s
      formatted := formatted.push doc
    return formatted

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



register_option pf.pageWidth : Nat := {
  defValue := 100
  group    := "pf"
  descr    := "(pretty format) Maximum number of characters in a line"
}

register_option pf.computationWidth : Nat := {
  defValue := 120
  group    := "pf"
  descr    := "(pretty format) Maximum number of characters before the formatter will pick any solution"
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
  descr    := "(pretty format) Get information about failed formatting rules, this is usually caused by a formatting rule not handling all of its cases"
}
register_option pf.debugMissingFormatters : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) List syntax that do not have an associated formatting rule"
}
register_option pf.debugAsHtml : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) generates HTML view of the document, this is useful for debugging"
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

register_option pf.cacheDistance : Nat := {
    defValue := 2
    group    := "pf"
    descr    := "(pretty format) To reduce memory usage we do not have cache every element. A larger cache distance means fewer elements get cached"
}

register_option pf.debugMode : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) debug enables the use of #fmt to define local formatting rules, which can be used while testing the correctness of a node. However this comes at the cost of performance"
}

def getPageWidth (o : Options) : Nat := o.get pf.pageWidth.name pf.pageWidth.defValue
def getComputationWidth (o : Options) : Nat := o.get pf.computationWidth.name pf.computationWidth.defValue
def getCacheDistance (o : Options) : Nat := (o.get pf.cacheDistance.name pf.cacheDistance.defValue)

def getDebugSyntax (o : Options) : Bool := (o.get pf.debugSyntax.name pf.debugSyntax.defValue)
def getDebugSyntaxAfter (o : Options) : Bool := (o.get pf.debugSyntaxAfter.name pf.debugSyntaxAfter.defValue)
def getDebugErrors (o : Options) : Bool := (o.get pf.debugErrors.name pf.debugErrors.defValue)
def getDebugMissingFormatters (o : Options) : Bool := (o.get pf.debugMissingFormatters.name pf.debugMissingFormatters.defValue)
def getDebugAsHtml (o : Options) : Bool := (o.get pf.debugAsHtml.name pf.debugAsHtml.defValue)
def getDebugDoc (o : Options) : Bool := (o.get pf.debugDoc.name pf.debugDoc.defValue)
def getWarnCSTmismatch (o : Options) : Bool := (o.get pf.warnCSTmismatch.name pf.warnCSTmismatch.defValue)
def getDebugTime (o : Options) : Bool := (o.get pf.debugTime.name pf.debugTime.defValue)
def getDebugMode (o : Options) : Bool := (o.get pf.debugMode.name pf.debugMode.defValue)


initialize coreFormatters : IO.Ref (Std.HashMap Name (Rule)) ← IO.mkRef {}

def RuleM.genId : RuleM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId

def FormatM.genId : FormatM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId






namespace Transport

abbrev NodeId := Nat

structure EncState where
  nextId : NodeId := 0
  -- store all strings in a long list string, they can later be restored
  symbols : String := ""
  defs   : Std.HashMap NodeId String := {}

abbrev EncM := StateM EncState

structure DecState where
  -- store all strings in a long list string, they can later be restored
  symbols : String := ""
abbrev DecM := StateM DecState

-- TODO: maybe optimize by reusing string that have already occured
partial def storeString (s:String): EncM String := do
  let state ← get
  let start := state.symbols.utf8ByteSize

  let stop := state.symbols.utf8ByteSize + s.utf8ByteSize
  modify (fun state => {state with symbols := state.symbols ++ s})
  return s!"{start}&{stop}"

partial def getString (s:String): DecM String := do
  let state ← get
  let parts := s.splitOn "&"
  match parts with
  | start::stop::[] =>
    match (start.toNat?, stop.toNat?) with
    | (some start,some stop) =>
      return state.symbols.extract ⟨start⟩ ⟨stop⟩
    | _ => panic! s!"could not getString with '{s}' as input"
  | _ => panic! "invalidPattern"

-- note we skip positions
def encodeSourceInfo : SourceInfo → EncM String
  | .original (leading : Substring) _ (trailing : Substring) _ => do
    return s!"o_{← storeString leading.toString}_{← storeString trailing.toString}"
  | .synthetic _ _ _ =>
    return s!"s"
  | .none =>
    return "n"


partial def encodeName : Name → EncM String
  | Name.anonymous => return "anon"
  | Name.str p s   => return s!"str_{← storeString s}_{← encodeName p}"
  | Name.num p n   => return s!"num_{toString n}_{← encodeName p}"

partial def decodeName : List String → DecM Name
 | "anon"::_ => return Name.anonymous
 | "str"::val::xs => do return Name.str (← decodeName xs) (← getString val)
 | "num"::n::xs => do return Name.num (← decodeName xs) (n.toNat!)
 | _ => panic "invalid name"

partial def encodeSyntaxDAG (stx : Syntax) : EncM NodeId := do
  let s ← get
  let id := s.nextId
  modify fun s => { s with nextId := s.nextId + 1 }
  match stx with
  | .missing =>
    modify fun s => {s with defs := s.defs.insert id "m"}
    return id
  | .atom info val =>
    let node := s!"a,{← encodeSourceInfo info},{← storeString val}"
    modify fun s => {s with defs := s.defs.insert id node}
    return id
  | .ident info raw name _ =>
    let node := s!"i,{← encodeSourceInfo info},{← storeString raw.toString},{← storeString name.toString}"
    modify fun s => {s with defs := s.defs.insert id node}
    return id
  | .node _ kind args =>
    let kindStr ← encodeName kind
    let argIds ← args.toList.mapM encodeSyntaxDAG
    let argString := ((argIds.map toString).intersperse ";") |> String.join

    let node := s!"n,{kindStr}," ++ argString

    modify fun s => {s with defs := s.defs.insert id node}
    return id



/-- Decode a source info string like:
    o,<leading>,<trailing> | s | n
-/
def decodeSourceInfo (parts : List String) : DecM (SourceInfo) := do
  match parts with
  | ["o", leading, trailing] =>
    let lead := (← getString leading).toSubstring
    let trail := (← getString trailing).toSubstring
    return (SourceInfo.original lead ⟨0⟩ trail ⟨0⟩)
  | ["s"] => return (SourceInfo.synthetic ⟨0⟩ ⟨0⟩ true)
  | ["n"] => return (SourceInfo.none)
  | _ => panic! s!"Invalid source info encoding: {parts}"

/-- Parse a single encoded node into `Syntax`, using the recursive node map. -/
partial def decodeNode (strMap : Std.HashMap NodeId String) (id : NodeId) : DecM Syntax := do
  let str := strMap[id]!
  let parts := str.splitOn ","
  let (stx : Syntax) ← match parts with
    | ["m"] => return .missing

    | ["a", sourceInfo, val] =>
      let info ← decodeSourceInfo (sourceInfo.splitOn "_")
      let val ← getString val
      return .atom info val

    | ["i", sourceInfo, raw, name] =>
      let info ← decodeSourceInfo (sourceInfo.splitOn "_")
      let raw ← getString raw
      let val ← getString name
      return .ident info raw.toSubstring (Name.mkSimple val) []

    | ["n", kind, argIdsStr] =>
      let kind ← decodeName (kind.splitOn "_")
      let argIds := if argIdsStr.isEmpty then [] else argIdsStr.splitOn ";"
      let argIdsNat := argIds.map String.toNat!
      let args ← argIdsNat.mapM (decodeNode strMap)
      return .node .none kind args.toArray

    | _ => panic! s!"Invalid node encoding: {str}"
  return stx


partial def encodeSyntax (stxs: List Syntax) : String := Id.run do
  let mut symbols := ""
  let mut fmtStxs := #[]
  for stx in stxs do
    let (_,state) := encodeSyntaxDAG stx |>.run {nextId:= 0, defs := {}, symbols := symbols}
    symbols := state.symbols
    fmtStxs := fmtStxs.push (state.defs.map (fun id str => s!"{id}:{str}") |>.toList |>.map Prod.snd |>.intersperse "|" |> String.join)

  let formatted := fmtStxs.toList |>.intersperse "$" |> String.join
  return s!"{formatted}~{symbols}"

/-- Top-level decode function. Takes the full encoded string and returns a `Syntax`. -/
def decodeSyntax (s : String) : ((List Syntax)× String) := Id.run do
  let mut found := #[]
  -- the document is split into 2 parts based on "~"
  let splitPos := s.find (fun c => c == '~')
  let symbols := s.extract (splitPos + ⟨1⟩) ⟨s.utf8ByteSize⟩
  let s := s.extract ⟨0⟩ splitPos
  let syntaxes := s.splitOn "$"

  for synt in syntaxes do
    let lines := synt.splitOn "|"
    let idStrs := lines.filterMap fun line =>
      let parts := line.splitOn ":"
      match parts with
      | [idStr, rest] =>
        match String.toNat? idStr with
        | some id => some (id, rest)
        | none => none
      | _ => none
    let strMap : Std.HashMap NodeId String := idStrs.foldl (fun acc (id, str) => acc.insert id str) {}
    let rootId := 0 -- Always the first ID assigned during encoding
    let (stx, _) := (decodeNode strMap rootId |>.run {symbols := symbols})
    found := found.push stx

  return (found.toList, symbols)


end Transport


end PrettyFormat
