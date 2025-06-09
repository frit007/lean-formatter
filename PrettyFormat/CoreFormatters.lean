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

