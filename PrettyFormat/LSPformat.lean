import CoreFormatters
import PFMT

open Lean Elab PrettyPrinter PrettyFormat
open Lean Elab Parser Command
open Lean.Elab.Command

open Lean.Meta
open System



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

    logInfo s!"\n{(← result.reportAsComment) ++ result.formattedPPL}"
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

@[command_code_action]
def formatCmdCodeAction : CommandCodeAction := fun p _ info node => do
  let .node i _ := node | return #[]

  let opts := info.options
  let stx :Syntax := i.stx
  let doc ← readDoc
  let eager :Lsp.CodeAction := {
    title := s!"Format {stx.getKind}"
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
      let mut result : Option FormatResult :=none
      if getDebugMode opts then do
        result := (← pfTopLevelWithDebug (stx) info.env formatters opts p.textDocument.uri)
      else do
        match (← pfTopLevelWithDebugDelegate [(stx,info.env, opts)] p.textDocument.uri ) with
        | x::_ => result := x
        | _ => result := none

      match result with
      | some res =>
        let newText := (← res.reportAsComment) ++ res.formattedPPL

        pure { eager with
          edit? := some <|.ofTextEdit doc.versionedIdentifier {
            range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
            newText
          }
        }
      | _ =>
        pure { eager with
          edit? := some <|.ofTextEdit doc.versionedIdentifier {
            range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
            newText := "fail"
          }
        }
  }]


syntax (name := formatDocCmd)
  "#formatDoc" : command


@[command_elab formatDocCmd]
unsafe def elabFormatDocCmd : CommandElab
  | _ => liftTermElabM do
    logInfo s!"\nUse quick action to reformat the document"


open CodeAction Server RequestM in
@[command_code_action formatDocCmd]
def formatDocCmdCodeAction : CommandCodeAction := fun p _ info _ => do
  let doc ← readDoc
  let eager :Lsp.CodeAction := {
    title := s!"Reformat document"
    kind? := "refactor.rewrite"
    isPreferred? := true
  }

  let t := doc.cmdSnaps.getAll


  pure #[{
    eager
    lazy? := some do

      let snapShots: List Snapshots.Snapshot := t.fst
      let states := snapShots.map (fun s => (s.stx, s.cmdState.env, info.options)) -- TODO: get options at the specific command

      let (results, time) ← measureTime (fun _ => pfTopLevelWithDebugDelegate states p.textDocument.uri)
      let timeDoc := results.foldl (fun _ a => a.timeDoc) 0
      let timePf := results.foldl (fun _ a => a.timePF) 0
      let timeReparse := results.foldl (fun acc a => acc + a.timeReparse) 0
      dbg_trace s!"wallTime {(Float.ofNat time)/1000000000} doc: {(Float.ofNat timeDoc)/1000000000} pf: {(Float.ofNat timePf)/1000000000} reparse:{(Float.ofNat timeReparse)/1000000000}"

      let newText := results.foldl (fun (acc:String) a => acc ++ "\n\n" ++ a.formattedPPL) ""
      let tail :String.Pos := states.foldl ( fun (_:String.Pos) (stx,_,_) => stx.getRange?.orElse (fun () => String.Range.mk ⟨0⟩  ⟨0⟩ )|>.get!.stop ) ⟨0⟩


      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨0, tail⟩
          newText := newText
        }
      }
  }]
