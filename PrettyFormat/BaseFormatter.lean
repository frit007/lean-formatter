import PrettyFormat
import Lean
import PFMT



open Lean
open Data
open Std

open Lean
open Lean.Meta
open Lean.Elab.Command
open Lean Elab PrettyPrinter PrettyFormat
open Lean.Meta


open Lean.Meta
open System

namespace PrettyFormat
  partial def nest (n:Nat) (s: RuleM PPL): RuleM PPL :=
    do
    let state ← get
    set {state with nesting := state.nesting + n}
    let result ← s
    let o:PPL := PPL.nest n (result)
    let state' ← get
    set {state' with nesting := state.nesting}
    return o

  partial def nl : RuleM PPL := do
    modify fun s => {s with startOfLine := true}
    return PPL.nl

  partial def findPatternStartAux (s pattern : String) : Option String :=
    if s.length < pattern.length then none
    else if s.take pattern.length == pattern then some (s.drop pattern.length)
    else findPatternStartAux (s.drop 1) pattern

  def findPatternStart (s pattern : String) : Option String :=
    findPatternStartAux s pattern

  def stringCommentsStr (s:String) : List String :=
  s.split (fun c => c == '\n')
  |>.filterMap (fun s => findPatternStart s "--")
  |>.filter (fun (s:String) => s.trim.length > 0)
  |>.map (fun (s:String) => "-- " ++ s.trim)

  def findFirstMatch (envs : List Environment) (kind: SyntaxNodeKind) (args : Array Syntax) :FormatM (List FormatError ⊕ PPL):= do
    let mut errors : List FormatError := []
    for env in envs do
      let options := pFormatAttr.getValues env kind
      for opt in options do
        match ← opt args with
        | .ok ppl => return Sum.inr ppl
        | .error e => errors := e::errors

    return Sum.inl errors

  def updateSyntaxTrail (stx : Syntax) (f:FormatM PPL) : FormatM PPL := do
    let _ ← modify (fun s => {s with stx := stx::s.stx})
    let v ← f
    let _ ← modify (fun s => {s with stx := s.stx.tail})
    return v

  mutual
    partial def pf (stx: Syntax): FormatM PPL := updateSyntaxTrail stx do
      -- can we assume that the other environment has all of the attributes? for now we do not
      let context ← read
      let state ← get

      match stx with
      | .missing => pure (text "")
      | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
        match kind with
        | `null => -- null nodes are combined without whitespaces
          pfCombine args
        | _ =>
          let formatted ← findFirstMatch (← read).envs kind args

          match formatted with
          | Sum.inr ppl => return PPL.group (toString kind) ppl
          | Sum.inl errs =>
            let s ← get
            let d := s.diagnostic
            if errs.length == 0 then
              let v := d.missingFormatters.insertIfNew kind stx
              let _ ←  set {s with diagnostic := {d with missingFormatters:= v}}

            else
              let mut v := d.failures
              for e in errs do
                v := (e, (← get).stx)::v

            return PPL.group (toString kind) (← pfCombine args)
      | .atom (info : SourceInfo) (val : String) =>
        -- return text val
        if state.unknown then
          return (unknownSurroundWithComments info (text "")) (fun p => p <> text val)
        else
          return (surroundWithComments info (text "")) (fun p => p <> text val)

      | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
        -- return text rawVal.toString
          -- return (unknownSurroundWithComments info (text "")) (fun p => p <> text rawVal.toString)
        if state.unknown then
          return (unknownSurroundWithComments info (text "")) (fun p => p <> text rawVal.toString)
        else
          return (surroundWithComments info (text "")) (fun p => p <> text rawVal.toString)


    partial def unknownStringCommentsStr (s:String) : List String :=
    if s.contains '\n' then
      s.split (fun c => c == '\n')
      |>.filterMap (fun s => findPatternStart s "--")
      |>.filter (fun (s:String) => s.trim.length > 0)
      |>.map (fun (s:String) => "-- " ++ s.trim)
    else
      if s.length > 0 then
        []
      else
        []


    partial def knownStringToPPL (s:String) (p: PPL) : PPL :=
      stringCommentsStr s |>.foldl (fun p' c => p' <> commentText c <> PPL.nl) p

    partial def surroundWithComments (info : SourceInfo) (p:PPL) (f : PPL → PPL): PPL:=
      match info with
      | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
        knownStringToPPL leading.toString p
        |> f
        |> knownStringToPPL trailing.toString
      | _ => f p

    partial def unknownStringToPPL (s:String) (p: PPL) : PPL :=
      unknownStringCommentsStr s |>.foldl (fun p' c => p' <> commentText c <> PPL.nl) p

    -- if the value is unknown then we will try to keep the value the same as it was
    partial def unknownSurroundWithComments (info : SourceInfo) (p:PPL) (f : PPL → PPL): PPL:=
      match info with
      | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
        unknownStringToPPL leading.toString p
        |> f
        |> unknownStringToPPL trailing.toString
      | _ => f p

    -- combine the formatters without separators
    partial def pfCombine (stxArr : Array Syntax) : FormatM PPL := do
      let mut res := text ""
      for p in stxArr do
        res := res <> (← pf p)
      return res

    partial def pfCombineWithSeparator (sep: PPL) (stxArr : Array Syntax) : FormatM PPL := do
      let mut combined := text ""
      for p in stxArr do
        let p' ← pf p
        if isEmpty [] p' then
          combined := combined -- no change
        else if isEmpty [] combined then
          combined := p' --
        else
          combined := combined <> sep <> p'
      return combined

  end

  structure CommandSyntax where
    env : Environment
    options: Options
    currNamespace : Name := Name.anonymous
    openDecls : List OpenDecl := []
    stx : Syntax

  instance : Repr CommandSyntax where
    reprPrec s _ := repr s.stx

  def extractTopLevelCommands (s : Frontend.State) : IO (Array CommandSyntax):= do
    let mut topLevelCmds : Array CommandSyntax := #[]
    for infoTree in s.commandState.infoState.trees.toArray do
      match infoTree with
      | InfoTree.context i (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
        match i with
        | .commandCtx { env, currNamespace, openDecls, options,.. } =>
          topLevelCmds := topLevelCmds.push {env, options, currNamespace, openDecls, stx}
        | _ => pure ()
      | _ => pure ()
    return topLevelCmds

  -- remove leading spaces based on the indentation level.
  -- for this to work we would need the indentation level that the formatter wants to use
  -- but we would also need the indentation level that the previous formatter used, to know whether we should increase the indentation level
  -- def removeLeading SpacesBasedOnNesting (leading : String) FormatPPLM PPL:= do
  --   leading.splitOn "\n"
  --   |>.map.

  private def whitespaceToPPL (str:String):PPL:=
    let parts := str.split (fun c => c == '\n') |>.map (fun c => text c)
    match parts with
    | x::xs => xs.foldl (fun acc x => acc <> x <> PPL.nl) x
    | _ => text ""

  private def getLeading (info:SourceInfo) : String :=
    match info with
    | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
      leading.toString
    | _ => ""

  private def getTrailing (info:SourceInfo) : String :=
    match info with
    | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
      trailing.toString
    | _ => ""

  -- keep the syntax exactly the same
  -- TODO: remove Id.run
  partial def topLevelUnformatedSyntaxToPPL (stx:Syntax): PPL := Id.run do
    match stx with
    | .missing => return text ""
    | .node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
      let combined ← args.foldlM (fun acc c => do return acc <> (← topLevelUnformatedSyntaxToPPL c) ) (text "")
      return combined
      -- info.
    | .atom   (info : SourceInfo) (val : String) => return (getLeading info |> whitespaceToPPL) <> text val <> (getTrailing info |> whitespaceToPPL)
    | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
      return (getLeading info |> whitespaceToPPL) <> text rawVal.toString <> (getTrailing info |> whitespaceToPPL)



-- @[inline] def formatMeta (stx: Syntax) (ctx:FormatContext) (s:MyState) : MetaM PPL :=
--   pf stx |>.run ctx |>.run' s
  structure CSTCompareError where
    before : String
    after : String
    trace : List String

  partial def compareCst (before after: Syntax) : Option (CSTCompareError):=
    match compareCst' before after [] with
      -- The trace is reversed to make it easier to read, but the list is built in reverse order for performance reasons
    | some e => some {e with trace := e.trace.reverse}
    | none => none
  where
    compareCst' (before after: Syntax) (trace : List String) : Option (CSTCompareError):=
      match (before, after) with
      | (Syntax.missing, Syntax.missing) => none
      | (Syntax.node _ lkind largs, Syntax.node _ rkind rargs) =>
        if (lkind != rkind) then
          some {before := toString lkind, after := toString rkind, trace}
        else
          compareCstArr largs rargs ((toString lkind)::trace)
      | (Syntax.atom _ (lval : String), Syntax.atom _ (rval : String)) =>
        if lval == rval then
          none
        else
          some {before := lval, after := rval, trace}
      | (Syntax.ident  _ (lrawVal : Substring) (lval : Name) _, Syntax.ident  _ (rrawVal : Substring) (rval : Name) _) =>
        if lrawVal == rrawVal then
          none
        else
          some {before := toString lrawVal, after := toString rrawVal, trace}
      | _ => some {before := toString before.getKind, after := toString after.getKind, trace}
    compareCstArr (left right : Array Syntax) (trace : List String): Option (CSTCompareError) := Id.run do
      for i in [0: (max left.size right.size)] do
        match (left[i]?, right[i]?)  with
        | (some l, some r) =>
          match compareCst' l r (trace ++ [toString i]) with
          | some e => return some e
          | none => ()
        | (some l, none) => return some {before := toString l.getKind, after := "missing" , trace := (toString i)::trace}
        | (none, some r) => return some {before := "missing", after := toString r.getKind , trace := (toString i)::trace}
        | _ => return none
      return none
      -- left.size == right.size
      -- && ((left.zip right) |>.foldl (fun acc x => acc && ) true)

  def stringToPPL (s:String) : PPL:=
    s.split (fun c => c == '\n') |>.map (fun s => text s) |>.foldl (fun acc p => acc <> p <> PPL.nl) (text "")


  structure FormatResult where
    stx : Syntax
    ppl : PPL
    opts : Options
    formattedPPL : String
    generatedSyntax : Except String Syntax
    state : FormatState
    cstDifferenceError : Option CSTCompareError

  def FormatResult.preservesCst (res : FormatResult) : Bool :=
    match res.cstDifferenceError with
      | .none => true
      | .some _ => false



  def debugReportAsPPL (res : FormatResult): PPL := Id.run do
    let stx := res.stx
    let opts := res.opts
    let generatedSyntax := res.generatedSyntax
    let ppl := res.ppl
    let state := res.state

    let mut errString := ""


    match generatedSyntax with
    | Except.error e => errString := errString ++ "---- Could not parse syntax again ----\n" ++ e
    | Except.ok generatedStx =>
      if PrettyFormat.getWarnCSTmismatch opts && !res.preservesCst then
        errString := errString ++ "---- CST mismatch! ----\n"

      if PrettyFormat.getDebugSyntaxAfter opts then
        errString := errString ++ "\n---- Syntax after format ----\n" ++ toString (repr generatedStx)

    if PrettyFormat.getDebugSyntax opts then
      errString := errString ++ "\n---- Syntax before format ----\n" ++ toString (repr stx)

    if (PrettyFormat.getDebugMissingFormatters opts) && state.diagnostic.missingFormatters.size > 0 then
      errString := errString ++ "\n---- Missing formatters ----\n"
      for (kind,stx) in state.diagnostic.missingFormatters do
        errString := errString ++ s!"{kind}: {stx}\n"
    if (PrettyFormat.getDebugPPL opts) then
      errString := errString ++ "\n---- Generated PPL ----\n" ++ (output ppl)

    if errString.length > 0 then
      return text "/-FORMAT DEBUG:" <> PPL.nl <> stringToPPL errString <> PPL.nl <> text "-/\n"
    else
      return text ""

  -- Enable dot notation with an extension function
  def FormatResult.reportAsComment (res : FormatResult) : String :=
    let debugReport := debugReportAsPPL res
    let formattedReport := toDoc debugReport |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength res.opts)
    formattedReport

  def pfTopLevel (stx : Syntax) (environments : List Environment) (options : Options) : (PPL × FormatState) :=
    let introduceContext := ((pf stx).run { envs:= environments, options:= options})
    let introduceState := introduceContext.run {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
    introduceState.run

  -- Also fallback to standard syntax if formatting fails
  partial def pfTopLevelWithDebug (stx : Syntax) (environments : List Environment) (opts : Options) (fileName:String): IO FormatResult := do
    let (ppl, state) := pfTopLevel stx environments opts
    let formattedPPL := toDoc ppl |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts)

    -- parse the syntax
    let generatedSyntax ← reparseSyntax formattedPPL fileName environments opts
    let cstDifferenceError := match generatedSyntax with
      | Except.error _ => compareCst stx Syntax.missing
      | Except.ok generatedStx => compareCst stx generatedStx

    return {stx, ppl, opts, formattedPPL, generatedSyntax, state, cstDifferenceError}
  where
    reparseSyntax (formattedPPL fileName: String) (envs : List Environment) (opts : Options): IO (Except String Syntax) :=
      let inputCtx := Parser.mkInputContext formattedPPL fileName
      -- assume that the user environment is the first one in the list
      -- because the this allows the user to override formatting options that are set by the formatter
      match envs.get? 0 with
      | none => .error "Could not parse syntax again: no environment"
      | some env => do
        let s ← IO.processCommands inputCtx {}
          { Command.mkState env {} opts with infoState := { enabled := true } }
          let topLevelCmds ← extractTopLevelCommands s
          if topLevelCmds.size == 2 then
            match topLevelCmds.get? 0 with
            | some command => return .ok command.stx
            | none => return .error "Could not parse syntax again: no command"
          else
            let combinedCommands := topLevelCmds.map (fun c => toString (repr c)) |>.toList |> "\n".intercalate

            return .error s!"Could not parse syntax again: Expected 2 commands to be generated, your top level command and end of file\n But generated {topLevelCmds.size} commands {combinedCommands}"


  def assumeMissing (stx : Syntax): RuleM Unit := do
    if stx.getKind == `null && stx.getArgs.size == 0 then
      return ()
    else
      failure


end PrettyFormat



initialize formattedCode : IO.Ref String ← IO.mkRef "initialString"



initialize coreFormatters : IO.Ref (Std.HashMap Name (Rule)) ← IO.mkRef {}

--- CORE FORMATTER ---
-- Core formatters are used to format
def registerCoreFormatter (name : Name) (f: Rule) : IO Unit := do
  let fmts ← coreFormatters.get
  let fmts := fmts.insert name f
  coreFormatters.set fmts
  return ()

def getCoreFormatter (name : Name) : IO (Option Rule) := do
  let fmts ← coreFormatters.get
  return fmts[name]?

-- -- only used for internally, use
-- syntax (name:=coreFmtCmd) "#coreFmt " ident term : command
-- syntax (name:=fmtCmd) "#fmt " ident term : command

-- -- def typeToExpr : Type → MetaM Expr
-- -- | Type 0 => return mkSort Level.zero  -- `Type 0` as `Sort 0`
-- -- | Type 1 => return mkSort Level.succ (Level.zero)  -- `Type 1` as `Sort (0+1)`
-- -- | _ => throwError "Unsupported Type"

-- @[command_elab coreFmtCmd]
-- def elabCoreFmtFunction : CommandElab
-- | `(command|#coreFmt $keyIdent $fnExpr) => do
--   -- -- trying to register the core formatter during elaboration is a crash
--   -- registerCoreFormatter `Lean.Parser.Term.app fun
--   -- | #[a] => do
--   --   return text "app?"
--   -- | _ => failure

--   -- This does not work :)
--   let cmd ← `(initialize
--     let _ : IO Unit := registerCoreFormatter $(quote keyIdent.getId) $fnExpr)
--   elabCommand cmd
--   logInfo s!"Registered core formatter {keyIdent.getId}"
-- | stx => logError m!"Syntax tree?: {stx.getKind}"



-- @[command_elab fmtCmd]
-- def elabFmtCmdFunction : CommandElab
-- | `(command|#fmt $keyIdent $fnExpr) => do

--   let cmd ← `(@[pFormat Lean.Parser.Termination.suffix]
--     def format$(quote keyIdent.getId) (args: Array Syntax) : Rule := $fnExpr)
--     )
--     -- let _ : IO Unit := registerCoreFormatter $(quote keyIdent.getId) $fnExpr
--   elabCommand cmd
-- | stx => logError m!"Syntax tree?: {stx.getKind}"
-- syntax (name:=coreFmtCmd) "register " ident " => " term : command

-- @[command_elab coreFmtCmd]
-- unsafe def elabFormatCmd : CommandElab
--   | `(command|#coreFmt $cmd => t) => liftTermElabM do
--     let env ← getEnv
--     let opts ← getOptions
--     let stx := cmd.raw
--     let leadingUpdated := stx|>.getArgs
--     let introduceContext := ((pfCombineWithSeparator PPL.nl leadingUpdated).run { envs:= [env], options := ← getOptions})
--     let introduceState := introduceContext.run' {nextId := 0}
--     let ppl := introduceState.run

--     let doc := toDoc ppl
--     let result := doc.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := 100)

--     logInfo s!"{result}"
--   | stx => logError m!"Syntax tree?: {stx.getKind}"

-- #coreFmt Lean.Parser.Term.app __ (fun stx => return text "app")

-- you cannot use it for initialize :)
-- initialize registerCoreFormatter `Lean.Parser.Term.app fun
--   | #[a] => do
--     return text "app?"
--   | _ => failure

-- initialize registerCoreFormatter `Lean.Parser.Term.letIdDecl fun
--   | #[a] => do
--     return text "app?"
--   | _ => failure

-- #coreFmt Lean.Parser.Term.app fun
--   | #[a] => do return text "app?"
--   | _ => failure


syntax (name:=coreFmtCmd) "#coreFmt " ident term : command
macro_rules
  | `(#coreFmt $typeExpr $fnExpr) =>
      -- Generate the `initialize` code by using the syntax trees
      -- let a := typeExpr.getId
      `(initialize registerCoreFormatter $(quote typeExpr.getId) $fnExpr)

syntax (name:=fmtCmd) "#fmt " ident term : command
macro_rules
  | `(#fmt $typeExpr $fnExpr) =>
      -- Generate the `initialize` code by using the syntax trees
      -- let a := typeExpr.getId
      let funName := typeExpr.getId.toString.replace "." "_"
      let idSyntax := mkIdent (Name.mkSimple funName)
      `(@[pFormat $(typeExpr)]
      def $(idSyntax) : Rule := $fnExpr)

-- #coreFmt2 Lean.Parser.Term.app fun
--   | #[a] => do return text "app?"
--   | _ => failure

-- initialize registerCoreFormatter `Lean.Parser.Term.app fun
--   | #[a] => do return text "app?"
--   | _ => failure
-- #coreFmt Lean.Parser.Term.app => 2

-- #coreFmt `app : do
--   let name ← evalExpr Name `($2)
--   let f ← evalExpr Rule `($3)
--   registerCoreFormatter name f
--   return ()
