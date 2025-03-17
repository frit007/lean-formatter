import CoreFormatters
import PFMT

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System



-- #guard_msgs in
-- #eval false

-- def add (a b:Nat) : Nat := a + b

-- def a : List Nat := Id.run do
--   let mut aa := []
--   for i in [:10] do
--     aa := (10-1-i)::aa
--   return aa

-- #eval a

-- partial def removeTheLastComment (stx:Syntax) : (Syntax) :=
--   let (_, stx') := removeTheLastComment' stx
--   stx'
-- where
-- removeTheLastComment' (stx:Syntax) : (Bool × Syntax) := Id.run do
--   match stx with
--   | .missing =>
--     return (false, stx)
--   | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
--     for i in [:args.size] do
--       let idx := args.size - i - 1
--       let (found, stx') := removeTheLastComment' args[idx]!
--       if found then
--         let updated := args.set! idx stx'
--         return (true, mkNode kind updated)
--     return (false, stx)
--   | .atom (info : SourceInfo) (val : String) =>
--     -- return (true, mkAtom (removeTrailing info) val)
--     return (true, mkAtom info "myvalue!!s")
--   | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
--     return (true, mkAtom info "myvalue2!!s")
--     -- return (true, .ident (removeTrailing info) rawVal val preresolved)
-- removeTrailing (info : SourceInfo) : SourceInfo :=
--     match info with
--     | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
--       .original "".toSubstring pos "".toSubstring endPos
--     | .synthetic (pos : String.Pos) (endPos : String.Pos) (canonical) =>
--       .synthetic pos endPos canonical
--     | .none => .none

syntax (name := formatCmd)
  "#format" ppLine command : command

@[command_elab formatCmd]
unsafe def elabFormatCmd : CommandElab
  | `(command|#format $cmd) => liftTermElabM do
    let env ← getEnv
    let opts ← getOptions
    let stx := cmd.raw

    let formatters ← getFormatters env
    let result ← pfTopLevelWithDebug stx env formatters opts (← getFileName)

    logInfo s!"\n{result.formattedPPL}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"

syntax (name := formatDebugCmd)
  "#formatDebug" ppLine command : command

@[command_elab formatDebugCmd]
unsafe def elabFormatDebugCmd : CommandElab
  | `(command|#formatDebug $cmd) => liftTermElabM do
    let env ← getEnv
    let opts ← getOptions
    let stx := cmd.raw

    let formatters ← getFormatters env
    let result ← pfTopLevelWithDebug stx env formatters opts (← getFileName)

    logInfo s!"\n{result.reportAsComment ++ result.formattedPPL}"
  | stx => logError m!"Syntax tree?: {stx.getKind}"

def findLineEnd (source:String) (pos:String.Pos) : String.Pos:= Id.run do
  let mut currentPos := pos
  while (source.get? currentPos).isSome do
    if (source.get! currentPos) == '\n' then
      return currentPos
    currentPos := source.next currentPos
  return currentPos

def extractLine (source:String) (pos:String.Pos) : String:= Id.run do
  let startOfLine := source.findLineStart pos
  let mut endOfLine := findLineEnd source pos
  let line := source.extract startOfLine endOfLine
  return line

partial def findStartOfDebugComment (source:String) (pos:String.Pos) : Option (String.Pos):= do
  let endPos ← findEndOfComment source (pos |> source.prev |> source.prev)
  let startPos ← findStartOfComment source (endPos |> source.prev)
  -- endPos
  -- match (← findStrPosRev source pos "DEBUG" (fun _ => true)) with
  -- | some c => some pos
  -- | _ => none
  -- findStrPosRev source pos "DEBUG" (fun _ => true)
  match strMatch source startPos "/-FORMAT DEBUG:" with
  | true => some startPos
  | _ => none
  -- startPos
where
  strMatch (source:String) (pos:String.Pos) (str:String) : Bool := Id.run do
    let mut currPos := pos
    let mut strPos := String.Pos.mk 0
    for _ in [0:str.length] do
      match source.get? (currPos) with
      | none => return false
      | some c => if c != str.get! strPos then return false
      currPos := source.next currPos
      strPos := str.next strPos
    return true

  findStrPosRev (source:String) (pos:String.Pos) (pattern:String) (allowed : Char → Bool) : Option (String.Pos) := do
    let p ← source.get? pos
    if allowed p then
      if strMatch source pos pattern then
        return pos
      else
        findStrPosRev source (source.prev pos) pattern allowed
    else
      none

  findEndOfComment (s:String) (pos:String.Pos) :Option (String.Pos):= do
    findStrPosRev s pos "-/" (fun c => c == '\n' || c == '\r' || c == ' ' || c == '-' || c == '/')

  findStartOfComment (s:String) (pos:String.Pos) :Option (String.Pos):= do
    findStrPosRev s pos "/-" (fun _ => true)

open CodeAction Server RequestM in
-- @[command_code_action]
-- @[command_code_action Lean.Parser.Command.declaration]
@[command_code_action]
def formatCmdCodeAction : CommandCodeAction := fun p _ info node => do
  let .node i ts := node | return #[]


  let top := ts.findSome? fun
    | .node (.ofCustomInfo { stx, .. }) _ => return stx
    | _ => none

  let name := match top with
  | .some a => a.getId
  | .none => `unknown

  let name := `definition

  -- let fileName ← getFileName
  -- p.textDocument.uri



  let opts := info.options
  let stx :Syntax := i.stx
  let doc ← readDoc
  let eager :Lsp.CodeAction := {
    title := s!"Format {name}"
    kind? := "refactor.rewrite"
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let r :String.Range := stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!

      let source := info.fileMap.source
      let start := match findStartOfDebugComment source r.start with
        | some pos => pos
        | none => r.start
      let tail := r.stop


      let formatters ← getFormatters info.env

      let result ← pfTopLevelWithDebug (stx) info.env formatters opts p.textDocument.uri

      let newText := result.reportAsComment ++ result.formattedPPL



      -- let newText := toDoc ppl |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)
      -- let newText := "newText"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]



set_option pf.debugErrors 1

-- /--
-- info: def test (n : Nat):=
--   add 2 3
-- -/
-- #guard_msgs in
-- #format
-- def test (n:Nat) :=
--   add 2 3

-- set_option pf.debugSyntax 1
set_option pf.debugMissingFormatters 1
set_option pf.debugErrors 1
-- set_option pf.debugSyntaxAfter 1
set_option pf.debugPPL 1
-- #format

-- #fmt Lean.Parser.Term.app fun
-- | #[functionName, arguments]  => do
--   return (← pf functionName) <> text " " <> (← pfCombineWithSeparator (text " ") arguments.getArgs)
-- | _ => failure
-- @[pFormat Lean.Parser.Term.app]
-- def formatApp : Rule
-- | #[functionName, arguments]  => do
--   return (← pf functionName) <> text " " <> (← pfCombineWithSeparator (text " ") arguments.getArgs)
-- | _ => failure


def add (x y:Nat): Nat:=
  x + -- some important comment, which is stored(and lost) in the ⟪+⟫ atom
    y


def test2 : Nat :=
  add 2 3
where
  add (x y:Nat):Nat:=
    x + y


/-FORMAT DEBUG:
---- Could not parse syntax again ----
Could not parse syntax again: Expected 2 commands to be generated, your top level command and end of file
 But generated 1 commands Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Command.eoi
  #[Lean.Syntax.atom (Lean.SourceInfo.original "".toSubstring { byteIdx := 0 } "".toSubstring { byteIdx := 0 }) ""]

-/

/-
Lean.Syntax.node
              (Lean.SourceInfo.none)
              `«term_+_»
              #[Lean.Syntax.ident
                  (Lean.SourceInfo.original "".toSubstring { byteIdx := 5638 } " ".toSubstring { byteIdx := 5639 })
                  "x".toSubstring
                  `x
                  [],
                Lean.Syntax.atom
                  (Lean.SourceInfo.original "".toSubstring { byteIdx := 5640 } " ".toSubstring { byteIdx := 5641 })
                  "+",
                Lean.Syntax.ident
                  (Lean.SourceInfo.original "".toSubstring { byteIdx := 5642 } "\n\n\n".toSubstring { byteIdx := 5643 })
                  "y".toSubstring
                  `y
                  []]
-/
def testSyntax : IO Bool := do
  let a := mkNode `plus #[mkIdent `x, mkAtom "+", mkIdent `y]

  let _ ← IO.println s!"{repr (a)}"

  return isEmpty (toPPL a)

#eval testSyntax
