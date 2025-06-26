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






namespace Base64

def base64Table : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

-- def reverseTable : Std.HashMap Char UInt8 :=
--   base64Table.foldl (init := {}) (fun (acc : Std.HashMap Char UInt8) c => acc.insert c (c.toUInt8))
def reverseTable : Std.HashMap Char UInt8 :=
  base64Table.mapIdx (fun i c => (i, c)) |>.foldl (init := {}) (fun acc (i,c) => acc.insert c (i.toUInt8))

def encodeChunk (chunk : List UInt8) : String :=
  let bytes := chunk ++ List.replicate (3 - chunk.length) 0
  let b := bytes.map (·.toUInt32)
  let n := (b[0]! <<< 16) ||| (b[1]! <<< 8) ||| b[2]!
  let c1 := base64Table.get! ((n >>> 18) &&& 0x3F).toNat
  let c2 := base64Table.get! ((n >>> 12) &&& 0x3F).toNat
  let c3 := if chunk.length > 1 then base64Table.get! ((n >>> 6) &&& 0x3F).toNat else '='
  let c4 := if chunk.length > 2 then base64Table.get! (n &&& 0x3F).toNat else '='
  s!"{c1}{c2}{c3}{c4}"

partial def encode (bytes : ByteArray) : String :=
  let rec go (i : Nat) (acc : String) :=
    if i ≥ bytes.size then acc
    else
      let chunk := (List.range 3).filterMap fun j =>
        if i + j < bytes.size then some (bytes.get! (i + j)) else none
      go (i + 3) (acc ++ encodeChunk chunk)
  go 0 ""

def decodeChar (c : Char) : Option UInt8 :=
  if c == '=' then none else reverseTable[c]?

def decodeBlock (block : List Char) : Option (List UInt8) := do
  if block.length ≠ 4 then
    panic! "not equal to 4"
  else
    let vals? := block.map decodeChar
    -- Bail if invalid char (not padding or base64 char)
    -- if vals?.any (·.isNone) ∧ block.any (fun c => c ≠ '=') then
    --   -- none
    --   panic! s!"bad char {repr block} {vals?.any (·.isNone)} ??? {block.any (fun c => c ≠ '=')}"
    -- else
    let vals := vals?.map (Option.getD · 0)
    let n := (vals[0]!.toUInt32 <<< 18) ||| (vals[1]!.toUInt32 <<< 12) |||
              (vals[2]!.toUInt32 <<< 6) ||| vals[3]!.toUInt32
    let padCount := block.count '='
    let out :=
      match padCount with
      | 0 => [((n >>> 16) &&& 0xFF).toUInt8,
              ((n >>> 8) &&& 0xFF).toUInt8,
              (n &&& 0xFF).toUInt8]
      | 1 => [((n >>> 16) &&& 0xFF).toUInt8,
              ((n >>> 8) &&& 0xFF).toUInt8]
      | 2 => [((n >>> 16) &&& 0xFF).toUInt8]
      | _ => []  -- shouldn't happen with valid base64
    some out

partial def chunk (n : Nat) (xs : List α) : List (List α) :=
  let rec go (acc : List (List α)) (xs : List α) :=
    match xs with
    | [] => acc.reverse
    | _ =>
      let (first, rest) := xs.splitAt n
      go (first :: acc) rest
  go [] xs

def decode (str : String) : Option ByteArray :=
  let clean := str.data.filter (fun c => c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ ' ')
  let blocks := chunk 4 clean
  let rec go (acc : List UInt8) (blocks : List (List Char)) :=
    match blocks with
    | [] => some (ByteArray.mk acc.toArray)
    | b :: bs =>
      match decodeBlock b with
      | some decoded => go (acc ++ decoded) bs
      | none => none
  go [] blocks

def testRoundtrip (s : String) : IO Unit := do
  let encoded := Base64.encode (ByteArray.mk s.toUTF8.data)
  match Base64.decode encoded with
  | some decoded =>
    match String.fromUTF8? decoded with
    | some decodedStr =>
      if decodedStr == s then
        IO.println s!"ok: roundtrip passed"
      else
        IO.println s!"fail: roundtrip mismatch: {decodedStr} ≠ {s}"
    | none => IO.println "fail: invalid UTF-8"
  | none => IO.println "fail: decode failed"

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip ""

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "f"

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "fo"

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "foo1"

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "foo"


/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "hello!"

/-- info: ok: roundtrip passed -/
#guard_msgs in
#eval testRoundtrip "Lean `"

/--
error: invalid field 'repeat', the environment does not contain 'String.repeat'
  "a"
has type
  String
-/
#guard_msgs in
#eval testRoundtrip ("a".repeat 1000)

def encode64Str (str:String): String :=
  Base64.encode (ByteArray.mk str.toUTF8.data)

def decode64Str! (encoded:String): String :=
  match Base64.decode encoded with
  | some decoded =>
    match String.fromUTF8? decoded with
    | some decodedStr =>
      decodedStr
    | none => panic! "fail: invalid UTF-8"
  | none => panic! "fail: decode failed"


def generateBigString : String :=
  String.mk (List.replicate 100000 'a')  -- 10,000 'a's

-- note we skip positions
def encodeSourceInfo : SourceInfo → String
  | .original (leading : Substring) _ (trailing : Substring) _ =>
    s!"o_{encode64Str leading.toString}_{encode64Str trailing.toString}"
  | .synthetic _ _ _ =>
    s!"s"
  | .none =>
    "n"

abbrev NodeId := Nat

structure EncState where
  nextId : NodeId := 0
  defs   : Std.HashMap NodeId String := {}

abbrev EncM := StateM EncState

partial def encodeName : Name → String
  | Name.anonymous => "anon"
  | Name.str p s   => s!"str_{encode64Str s}_{encodeName p}"
  | Name.num p n   => s!"num_{toString n}_{encodeName p}"

partial def decodeName : List String → Name
 | "anon"::_ => Name.anonymous
 | "str"::val::xs => Name.str (decodeName xs) (decode64Str! val)
 | "num"::n::xs => Name.num (decodeName xs) (n.toNat!)
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
    let node := s!"a,{encodeSourceInfo info},{encode64Str val}"
    modify fun s => {s with defs := s.defs.insert id node}
    return id
  | .ident info raw name _ =>
    let node := s!"i,{encodeSourceInfo info},{encode64Str raw.toString},{encode64Str name.toString}"
    modify fun s => {s with defs := s.defs.insert id node}
    return id
  | .node _ kind args =>
    let kindStr := encodeName kind
    let argIds ← args.toList.mapM encodeSyntaxDAG
    let argString := ((argIds.map toString).intersperse ";") |> String.join

    let node := s!"n,{kindStr}," ++ argString

    modify fun s => {s with defs := s.defs.insert id node}
    return id

partial def encodeSyntax (stx:Syntax) : String :=
  let (_,state) := encodeSyntaxDAG stx |>.run {nextId:= 0, defs := {}}
  state.defs.map (fun id str => s!"{id}:{str}") |>.toList |>.map Prod.snd |>.intersperse "|" |> String.join


/-- Decode a source info string like:
    o,<leading>,<trailing> | s | n
-/
def decodeSourceInfo (parts : List String) : (SourceInfo) :=
  match parts with
  | ["o", leading, trailing] =>
    let lead := (decode64Str! leading).toSubstring
    let trail := (decode64Str! trailing).toSubstring
    (SourceInfo.original lead ⟨0⟩ trail ⟨0⟩)
  | ["s"] => (SourceInfo.synthetic ⟨0⟩ ⟨0⟩ true)
  | ["n"] => (SourceInfo.none)
  | _ => panic! s!"Invalid source info encoding: {parts}"

/-- Parse a single encoded node into `Syntax`, using the recursive node map. -/
partial def decodeNode (strMap : Std.HashMap NodeId String) (id : NodeId) : Syntax := Id.run do
  let str := strMap[id]!
  let parts := str.splitOn ","
  let (stx : Syntax) ← match parts with
    | ["m"] => return .missing

    | ["a", sourceInfo, val] =>
      let info := decodeSourceInfo (sourceInfo.splitOn "_")
      let val := decode64Str! val
      return .atom info val

    | ["i", sourceInfo, raw, name] =>
      let info := decodeSourceInfo (sourceInfo.splitOn "_")
      let raw := decode64Str! raw
      let val := decode64Str! name
      return .ident info raw.toSubstring (Name.mkSimple val) []

    | ["n", kind, argIdsStr] =>
      let kind := decodeName (kind.splitOn "_")
      let argIds := if argIdsStr.isEmpty then [] else argIdsStr.splitOn ";"
      let argIdsNat := argIds.map String.toNat!
      let args ← argIdsNat.mapM (decodeNode strMap)
      return .node .none kind args.toArray

    | _ => panic! s!"Invalid node encoding: {str}"
  return stx

/-- Top-level decode function. Takes the full encoded string and returns a `Syntax`. -/
def decodeSyntax (s : String) : Syntax :=
  let lines := s.splitOn "|"
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
  decodeNode strMap rootId


end Base64


end PrettyFormat
