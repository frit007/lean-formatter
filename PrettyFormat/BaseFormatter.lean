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
open System


namespace PrettyFormat
  -- partial def nest (n:Nat) (s: RuleM PPL): RuleM PPL :=
  --   do
  --   let state ← get
  --   set {state with nesting := state.nesting + n}
  --   let result ← s
  --   let o:PPL := PPL.nest n (result)
  --   let state' ← get
  --   set {state' with nesting := state.nesting}
  --   return o

  partial def findPatternStartAux (s pattern : String) : Option String :=
    if s.length < pattern.length then none
    else if s.take pattern.length == pattern then some (s.drop pattern.length)
    else findPatternStartAux (s.drop 1) pattern

  def findPatternStart (s pattern : String) : Option String :=
    findPatternStartAux s pattern



  def findFirstMatch (fmts : List (Name → Option Rule)) (kind : SyntaxNodeKind) (r : RuleRec) (stx : Syntax) :FormatM (List FormatError ⊕ PPL):= do
    let mut errors : List FormatError := []
    for fmt in fmts do
      -- let options := pFormatAttr.getValues env kind
      let opt := fmt kind
      match opt with
      | none =>
        errors := errors
      | some f =>
        match ← f stx.getArgs with
        | .ok ppl =>
          let res ← expandSyntax r ppl
          -- if stx.getKind == `Lean.Parser.Tactic.tacticSeq then
          --   let diag := (← get).diagnostic
          --   return Sum.inr (PPL.text s!"found! {repr diag.missingFormatters}")
          return Sum.inr res
        | .error e => errors := e::errors

    return Sum.inl errors
  where
    -- since the result might contain Syntax we expand it now
    expandSyntax (r : RuleRec) : PPL → FormatM PPL
      | .error s => return .error s
      | .text s => return .text s
      | .nl => return .nl
      | .choice left right => return .choice (← expandSyntax r left) (← expandSyntax r right)
      | .flatten inner => return .flatten (← expandSyntax r inner)
      | .align inner => return .align (← expandSyntax r inner)
      | .nest n inner => return .nest n (← expandSyntax r inner)
      | .unallignedConcat left right => return .unallignedConcat (← expandSyntax r left) (← expandSyntax r right)
      -- for performance reasons stop when seing another group, to avoid re-evaluating the entire tree
      -- this is safe because another group has already been
      | .rule name ppl => return .rule name ppl
      | .bubbleComment s => return .bubbleComment s
      | .endOfLineComment s => return .endOfLineComment s
      | .stx stx => return ← r stx
      | .reset s => return .reset (← expandSyntax r s)
      | .provide s => return .provide s
      | .expect s => return .expect s

  def updateSyntaxTrail (stx : Syntax) (f:FormatM PPL) : FormatM PPL := do
    let _ ← modify (fun s => {s with stx := stx::s.stx})
    let v ← f
    let _ ← modify (fun s => {s with stx := s.stx.tail})
    return v


  def stringCommentsStr (s:String) : List String :=
  -- s.split (fun c => c == '\n')
  -- |>.filterMap (fun s => findPatternStart s "--")
  -- |>.filter (fun (s:String) => s.trim.length > 0)
  -- |>.map (fun (s:String) => "-- " ++ s.trim)
    s.split (fun c => c == '\n')
    |>.map (fun s => s.trim)
    |>.filter (fun s => s.length > 0)

  partial def unknownStringCommentsStr (s:String) : List String :=
  if s.contains '\n' then
    s.split (fun c => c == '\n')
    |>.filterMap (fun s => findPatternStart s "--")
    -- |>.filter (fun (s:String) => s.trim.length > 0)
    |>.map (fun (s:String) => "-- " ++ s.trim)
  else
    if s.length > 0 then
      []
    else
      []

  partial def knownStringToPPL (s:String) (p: PPL) : PPL :=
    -- stringCommentsStr s |>.foldl (fun p' c => p' <> ((PPL.endOfLineComment (" " ++ c)) <^> PPL.bubbleComment c)) p
    stringCommentsStr s |>.foldl (fun p' c => p' <> ((" " ++ c <> (PPL.provide [spaceHardNl])) <^> PPL.bubbleComment c)) p

  partial def surroundWithComments (info : SourceInfo) (p:PPL) (f : PPL → PPL): PPL:=
    match info with
    | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
      knownStringToPPL leading.toString p
      |> f
      |> knownStringToPPL trailing.toString
    | _ => f p

  def hasNewlineBeforeNonWhitespace (s : String) : Bool :=
  let chars := s.toList
  let rec check : List Char → Bool
    | [] => false
    | '\n' :: cs => true -- Mark that we've seen a newline
    | c :: cs => if c.isWhitespace then check cs else false
  check chars

  partial def unknownStringToPPL (s:String) (leading : Bool): PPL :=
    let comments := unknownStringCommentsStr s
    let bubbled := comments.foldl (fun p' c =>
        p' <> PPL.bubbleComment (c)
    ) (.text "")
    let endOfLine := comments.foldl (fun p' c => p' <> (((c) <> (PPL.provide [spaceHardNl])) <^> PPL.bubbleComment c)) (.text "")
    if comments.length == 0 then
      .text ""
    else
      if leading || hasNewlineBeforeNonWhitespace s then
        bubbled <^> [spaceHardNl] !> endOfLine
      else
        bubbled <^> [space] !> endOfLine

  -- if the value is unknown then we will try to keep the value the same as it was
  partial def unknownSurroundWithComments (info : SourceInfo) (p:PPL): PPL:=
    match info with
    | .original (leading : Substring) _ (trailing : Substring) _ =>
      unknownStringToPPL leading.toString true
      <> p <> unknownStringToPPL trailing.toString false
    | _ => p

  partial def pfCombine (r: RuleRec) (stxArr : Array Syntax) : FormatM PPL := do
    let mut res := text ""
    for p in stxArr do
      res := res <> (← r p)
    return res

  partial def pf (formatters : Formatters) (stx: Syntax): FormatM PPL := updateSyntaxTrail stx do
    -- can we assume that the other environment has all of the attributes? for now we do not
    -- let context ← read
    let r : RuleRec := fun (stx) => pf formatters stx
    -- let rr : RuleCtx :=

    match stx with
    | .missing => pure (text "")
    | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
      match kind with
      | `null => -- null nodes are combined without whitespaces
        pfCombine r args
      | _ =>
        let formatted ← findFirstMatch formatters kind r stx

        match formatted with
        | Sum.inr ppl =>
          -- if stx.getKind == `Lean.Parser.Tactic.tacticSeq then
          --   return text "capture good"
          return PPL.rule (toString kind) ppl
        | Sum.inl errs =>
          -- if stx.getKind == `Lean.Parser.Tactic.tacticSeq then
          --   return text "capture err"
          let s ← get
          let d := s.diagnostic
          if errs.length == 0 then
            let v := d.missingFormatters.insertIfNew kind stx
            set {s with diagnostic := {d with missingFormatters:= v}}

          else
            let mut v := d.failures
            for e in errs do
              v := (e, (← get).stx)::v
            set {s with diagnostic := {d with failures := v}}

          return PPL.rule (toString kind) (← pfCombine r args)
    | .atom (info : SourceInfo) (val : String) =>
      return (unknownSurroundWithComments info (text val))
      -- return text val
      -- if state.unknown then
      --   return
      -- else
      --   return (surroundWithComments info (text "")) (fun p => p <> text val)

    | .ident  (info : SourceInfo) (rawVal : Substring) _ _ =>
      return (unknownSurroundWithComments info (text rawVal.toString))
      -- return text rawVal.toString
        -- return (unknownSurroundWithComments info (text "")) (fun p => p <> text rawVal.toString)
      -- if state.unknown then
      --   return (unknownSurroundWithComments info (text "")) (fun p => p <> text rawVal.toString)
      -- else
      --   return (surroundWithComments info (text "")) (fun p => p <> text rawVal.toString)


  -- def combine [ToPPL a] [ToPPL b] (sep: a) (stxArr : Array b) : PPL := Id.run do
  --   let mut combined := text ""
  --   for p in stxArr do
  --     let p' ← toPPL p
  --     if isEmpty p' then
  --       combined := combined -- no change
  --     else if isEmpty combined then
  --       combined := p' --
  --     else
  --       combined := combined <> sep <> p'
  --   return combined

  def combine [ToPPL a] (sep: PPL → PPL → PPL) (stxArr : Array a) : PPL := Id.run do
    let mut combined : PPL := text ""
    for p in stxArr do
      let p' ← toPPL p
      if isEmpty p' then
        combined := combined -- no change
      else if isEmpty combined then
        combined := p' --
      else
        combined := sep combined p'
    return combined

  -- continue combining children if they are null arrays
  partial def nestedCombine (sep: PPL → PPL → PPL) (stxArr : Array Syntax) : PPL := Id.run do
    let mut combined := text ""
    for p in stxArr do
      let p' ← toPPL p
      let formatted :=
        if p.getKind == `null then
            sep combined (nestedCombine (fun a b => "n(" <> sep a b <> ")n") p.getArgs)
          else
            sep combined p'
      if isEmpty p' then
        combined := combined -- no change
      else if isEmpty combined then
        combined := formatted
      else
        combined := sep combined formatted
    return combined

  def combine' [ToPPL a] (sep : PPL → PPL → PPL) (stx : Array a) : RuleM PPL :=
    return combine sep stx
  -- def combineArgs' [ToPPL a] (sep : a) (stx : Syntax) : RuleM PPL :=
  --   return combine sep stx.getArgs


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
          if lkind == `Lean.Parser.Command.docComment then
            none -- TODO: compare string content
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

  def stringToPPL (s:String) : PPL:=
    s.split (fun c => c == '\n') |>.map (fun s => text s) |>.foldl (fun acc p => acc <> p <> PPL.nl) (text "")

  structure FormatResult where
    stx : Syntax
    ppl : PPL
    opts : Options
    doc : Pfmt.Doc
    formattedPPL : String
    generatedSyntax : Except String Syntax
    state : FormatState
    cstDifferenceError : Option CSTCompareError
    timePF : Nat
    timeDoc : Nat
    timeReparse : Nat

  def FormatResult.toReport (res: FormatResult) : FormatReport :=
    {
      res.state.toReport
      with
      timePF:=res.timePF
      timeDoc:=res.timeDoc
      timeReparse:=res.timeReparse
    }

  def FormatResult.preservesCst (res : FormatResult) : Bool :=
    match res.cstDifferenceError with
      | .none => true
      | .some _ => false

  -- def findSpacingFailure (path:List String) (spacing: Option (Std.HashSet String)) (flattened : Bool): PPL -> Option (List (List String))
  -- | .nl =>
  --   if flattened then
  --     match spacing with
  --     | none => none
  --     | some s => if s.contains spaceNl || s.contains spaceHardNl then none else return [path]
  --   else
  --     match spacing with
  --     | none => none
  --     | some s => if s.contains spaceNl || s.contains spaceHardNl then none else return [path]
  -- | .text t =>
  --   match spacing with
  --   | none => return none
  --   | some e =>
  --     if t.startsWith " " && ! e.contains space then [path]
  --     else
  --       if e.contains space || e.contains spaceHardNl || e.contains spaceNl || e.contains nospace then none else [path]
  -- | .error => [path]
  -- | .choice l r =>
  --   match (findSpacingFailure path spacing flattened l, findSpacingFailure path spacing flattened r) with
  --   | (some ls, some rs) => return [ls @ rs]
  --   | _ => none
  -- | .unallignedConcat l r:

  -- | .flatten : PPL → PPL
  -- | .align : PPL → PPL
  -- | .nest : Nat → PPL → PPL
  -- | .rule : String → PPL → PPL
  -- | .reset : (PPL → PPL)
  -- | .bubbleComment (comment : String)
  -- | .endOfLineComment (comment : String)
  -- | .provide (options : List String)
  -- | .expect (options : List String)

  def nanosecondsToSeconds (ns : Nat) : Float :=
    ns.toFloat / 1_000_000_000.0
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

    if PrettyFormat.getDebugDoc opts then
      errString := errString ++ "\n---- Generated Doc ----\n" ++ toString (repr res.doc)

    if PrettyFormat.getDebugSyntax opts then
      errString := errString ++ "\n---- Syntax before format ----\n" ++ toString (repr stx)

    if (PrettyFormat.getDebugMissingFormatters opts) && state.diagnostic.missingFormatters.size > 0 then
      errString := errString ++ "\n---- Missing formatters ----\n"
      for (kind,stx) in state.diagnostic.missingFormatters do
        errString := errString ++ s!"{kind}:({stx.getArgs.size}) {stx}\n"

    if (PrettyFormat.getDebugErrors opts) && state.diagnostic.failures.length > 0 then
      errString := errString ++ "\n---- Formatter errors ----\n"
      for (kind,stx) in state.diagnostic.failures do
        errString := errString ++ s!"{kind}:({stx.length}) \n"

    if (PrettyFormat.getDebugPPL opts) then
      errString := errString ++ "\n---- Generated PPL ----\n" ++ (output ppl)

    if (PrettyFormat.getDebugTime opts) then
      errString := errString ++ s!"\n---- timingPPL ----\ntimePF{nanosecondsToSeconds res.timePF}s\ntimeDoc{nanosecondsToSeconds res.timeDoc}s\ntimeReparse{nanosecondsToSeconds res.timeReparse}s"

    if errString.length > 0 then
      return text "/-FORMAT DEBUG:" <> PPL.nl <> stringToPPL errString <> PPL.nl <> text "-/\n"
    else
      return text ""

  -- Enable dot notation with an extension function
  def FormatResult.reportAsComment (res : FormatResult) : String :=
    let debugReport := debugReportAsPPL res
    let formattedReport := toDoc debugReport |>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength res.opts)
    formattedReport

  def pfTopLevel (stx : Syntax) (formatters : List (Name → Option Rule)) (options : Options) : (PPL × FormatState) :=
    let introduceContext := pf formatters stx
    let introduceState := introduceContext.run {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
    introduceState.run



partial def someComputation (sum:Nat) (n : Nat):IO Nat :=
  if n == 0 then
    return sum
  else
    someComputation (sum * 3) (n-1)
  partial def measureTime (f : Unit → IO α) : IO (α × Nat):= do
    let before ← IO.monoNanosNow
    let res ← f ()
    let after ← IO.monoNanosNow
    return (res, after - before)
  -- Also fallback to standard syntax if formatting fails
  partial def pfTopLevelWithDebug (stx : Syntax) (env : Environment) (formatters : List (Name → Option Rule)) (opts : Options) (fileName:String): IO FormatResult := do
    let ((ppl, state), timePF) ← measureTime (fun _ => do
      return pfTopLevel stx formatters opts)

    let ((doc, formattedPPL), timeDoc) ← measureTime (fun _ => do
      let d := toDoc ppl
      return (d, d|>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts))
    )


    let (generatedSyntax, timeReparse) ← measureTime ( fun _ => do
      try
        return ← reparseSyntax formattedPPL fileName env opts
      catch e =>
        return Except.error e.toString
    )
    -- let (_, timeReparse) ← measureTime do
    --     someComputation 2 (1100000)
    -- let slowFunction : Nat → Nat
    --   let d := toDoc ppl
    --   let _ := (d, d|>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts))

    -- timeit "does this work now" (fun _ => slowFunction 199)

    let mut cstDifferenceError := match generatedSyntax with
      | Except.error _ => compareCst stx Syntax.missing
      | Except.ok generatedStx => compareCst stx generatedStx

    if stx.getKind == `Lean.Parser.Module.header then
      cstDifferenceError := none

    return {stx, ppl, opts, doc, formattedPPL, generatedSyntax, state, cstDifferenceError, timePF, timeReparse, timeDoc}
    -- return {stx, ppl, opts, doc := Pfmt.Doc.text "skip", formattedPPL := "formatted", generatedSyntax := .error "nope", state, cstDifferenceError := none, timePF, timeReparse, timeDoc := 0}
  where
    reparseSyntax (formattedPPL fileName: String) (env : Environment) (opts : Options): IO (Except String Syntax) := do
      let inputCtx := Parser.mkInputContext formattedPPL fileName
      -- assume that the user environment is the first one in the list
      -- because the this allows the user to override formatting options that are set by the formatter
      -- match envs.get? 0 with
      -- | none => .error "Could not parse syntax again: no environment"
      -- | some env => do
      --   return .error s!"the ppl:={formattedPPL}"

      let s ← IO.processCommands inputCtx {}
        { Command.mkState env {} opts with infoState := { enabled := true } }
      let topLevelCmds ← extractTopLevelCommands s
      if topLevelCmds.size == 2 || topLevelCmds.size == 1 then
        match topLevelCmds.get? 0 with
        | some command => return .ok command.stx
        | none => return .error "Could not parse syntax again: no command"
      else
        let combinedCommands := topLevelCmds.map (fun c => toString (repr c)) |>.toList |> "\n".intercalate

        return .error s!"Could not parse syntax again: Expected 2 commands to be generated, your top level command and end of file\n But generated {topLevelCmds.size} commands {combinedCommands}"

  def formatterFromEnvironment (env : Environment) (name : Name) : Option Rule := do
    let fmts := pFormatAttr.getValues env name

    for fmt in fmts do
      return fmt

    none

  def getCoreFormatters : IO (Formatter) := do
    let fmts ← coreFormatters.get

    return fun name => do
      match fmts[name]? with
      | some f => return f
      | none => none

  def getFormatters (env : Environment): IO Formatters := do
    let coreFormatters : Name → (Option Rule) ← getCoreFormatters
    let envFormatters := formatterFromEnvironment env
    return [envFormatters, coreFormatters]


  def assumeMissing (stx : Syntax): RuleM Unit := do
    if stx.getKind == `null && stx.getArgs.size == 0 then
      return ()
    else
      failure


initialize formattedCode : IO.Ref String ← IO.mkRef "initialString"


-- def format (stx : Syntax) : (RuleCtx) := do
--   (← read) stx

-- def formatThen (sep : PPL) (stx : Syntax) : (RuleCtx) := do
--     let formatted := (← read) stx
--     let ppl ← formatted
--     if isEmpty ppl then
--       return text ""
--     else
--       return ppl <> sep

def formatThen [ToPPL a] [ToPPL b] (sep : a) (ppl : b) : PPL :=
  let p := toPPL ppl
  if isEmpty p then
    text ""
  else
    p <> sep

def formatBefore [ToPPL a] [ToPPL b] (sep : a) (ppl : b) : PPL :=
  let p := toPPL ppl
  if isEmpty p then
    text ""
  else
    sep <> p

infixr:45 " ?> " => fun l r => formatThen r l
infixr:45 " <? " => fun l r => formatBefore l r


instance : Alternative RuleM where
  failure := fun {_} => do

    throw (FormatError.NotHandled (← get).stx.head!.getKind (← get).stx)
  orElse  := PrettyFormat.orElse

--- CORE FORMATTER ---
-- Core formatters are used to format

def  registerCoreFormatter  (name : Name) (f: Rule) : IO Unit := do
  let fmts ← coreFormatters.get
  let fmts := fmts.insert name f
  coreFormatters.set fmts


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

partial def getCommands (cmds : Syntax) : StateT (Array Syntax) Id Unit := do
  if cmds.getKind == nullKind || cmds.getKind == ``Parser.Module.header then
    for cmd in cmds.getArgs do
      getCommands cmd
  else
    modify (·.push cmds)

partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ _ args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.line.joinSep args

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

def printCommands (cmds : Syntax) : CoreM Unit := do
  for cmd in getCommands cmds |>.run #[] |>.2 do
    try
      IO.println (← ppCommand ⟨cmd⟩).pretty
    catch e =>
      IO.println f!"/-\ncannot print: {← e.toMessageData.format}\n{reprint cmd}\n-/"

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode



def prettyPrintSourceInfo : SourceInfo → String
  | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) => s!"leading:{leading} pos: {pos} trailing: {trailing} endPos: {endPos}"
  | .synthetic (pos : String.Pos) (endPos : String.Pos) (canonical) => s!"synthetic: pos:{pos} endPos: {endPos}: cannonical: {canonical}"
  | .none => "nosource"


partial def prettyPrintSyntax : Syntax → String
  | .missing => "missing"
  | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    (args.map prettyPrintSyntax |>.toList |> " ".intercalate)
  | .atom (info : SourceInfo) (val : String) => s!"{val}"
  | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) => s!"{val}"



-- source reformat.lean
unsafe def parseModule (input : String) (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
    IO <| (Array CommandSyntax × Environment) := do
  let mainModuleName := Name.anonymous -- FIXME
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  let _ ← Lean.enableInitializersExecution

  -- IO.println s!"{prettyPrintSyntax header}"
  -- printall error messages and exit
  if messages.hasErrors then
    for msg in messages.toList do
      IO.println s!"{← msg.toString}"
    failWith "error in header"
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  -- We return this version of env because it has executed initializers.
  let env := env.setMainModule mainModuleName

  if messages.hasErrors then
    for msg in messages.toList do
      IO.println s!"{← msg.toString}"
    failWith s!"error in process header{fileName}"
  -- let env0 := env
  let s ← IO.processCommands inputCtx parserState -- TODO: learn about this line
    { Command.mkState env messages opts with infoState := { enabled := true } }

  let topLevelCmds : Array CommandSyntax ← extractTopLevelCommands s

  return (#[{ env := s.commandState.env, options:= opts, stx := header : CommandSyntax }] ++ topLevelCmds, env)

unsafe def parseModule' (fileName : String) (opts : Options) : IO (Array CommandSyntax × Environment):= do
  let input ← IO.FS.readFile fileName
  parseModule input fileName opts


end PrettyFormat
