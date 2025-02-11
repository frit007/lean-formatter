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
  partial def nest (n:Nat) (s: FormatPPLM PPL): FormatPPLM PPL :=
    do
    let state ← get
    set {state with nesting := state.nesting + n}
    let result ← s
    let o:PPL := PPL.nest n (result)
    let state' ← get
    set {state' with nesting := state.nesting}
    return o
  partial def nl : FormatPPLM PPL := do
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

  mutual
    partial def pf (stx: Syntax): FormatPPLM PPL := withReader (fun s => {s  with stx:= stx::s.stx}) do
      -- can we assume that the other environment has all of the attributes? for now we do not
      let context ← read
      let state ← get

      match stx with
      | .missing => pure (text "")
      | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
        match kind with
        | `null => -- null nodes are treated as padding
          pfCombine args
        | _ =>
          -- try to use the other environments attributes
          -- We prefer the other environment
          let formatted :(Option PPL) ← context.envs.foldlM (fun (envP: Option PPL) env => do
            -- get the first formatter that does not fail
            match envP with
            | (some s) => return envP
            | none =>
              let options := pFormatAttr.getValues env kind
              let res ← options.foldlM (fun (p:Option PPL) f => do
                match p with
                | none =>
                  try
                    return some (← f args)
                  catch _ =>
                    return none
                | some p => return some p
                ) none

              match res with
              | none => return none
              | some p => return some p

          ) none

          match formatted with
          | some p => return p
          | none =>
            -- IO.println s!"could not find something for {kind}" -- we could not find a formatter
            -- missing formatter
            let s ← get
            let d := s.diagnostic
            let v := d.missingFormatters.insertIfNew kind stx
            let _ ←  set {s with diagnostic := {d with missingFormatters:= v}}


            pfCombine args
            --return text s!"could not find something for {kind}" -- we could not find a formatter
            -- | none => failure -- we could not find a formatter
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
    partial def pfCombine :FormatPPL
    | a => do
      a.foldlM (fun p s => do
        let p' ← pf s
        return p <> p') (text "")

    partial def pfCombineWithSeparator (sep: PPL) :FormatPPL
    | a => do
      a.foldlM (fun p s => do
        let p' ← pf s
        if isEmpty [] p' then
          return p
        else if isEmpty [] p then
          return p'
        else
          return p <> sep <> p'
        ) (text "")
  end

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
  -- TODO: remove IO
  partial def topLevelUnformatedSyntaxToPPL (stx:Syntax): IO PPL := do
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


  def stringToPPL (s:String) : PPL:=
    s.split (fun c => c == '\n') |>.map (fun s => text s) |>.foldl (fun acc p => acc <> p <> PPL.nl) (text "")

  def debugReportAsPPL (stx:Syntax) (options : Options) (input : Except FormattingError (PPL × FormatState)): IO PPL := do

    let mut errString := ""
    if PrettyFormat.getDebugSyntax options then
      errString := errString ++ "\nSyntax: \n" ++ toString (repr stx)

    -- if (PrettyFormat.get)

    match input with
    | .ok (ppl, state) =>
      if (PrettyFormat.getDebugMissingFormatters options) && state.diagnostic.missingFormatters.size > 0 then
        errString := errString ++ "\nMissing formatters: \n"
        for (kind,stx) in state.diagnostic.missingFormatters do
          errString := errString ++ s!"{kind}: {stx}\n"
      if (PrettyFormat.getDebugPPL options) then
        errString := errString ++ "\n Generated PPL: \n" ++ (output ppl)
    | .error e =>
      if (PrettyFormat.getDebugErrors options) then
        errString := errString ++ "\nFailed to format with error: \n" ++ (toString e) ++ "\n"


    if errString.length > 0 then
      return text "/-FORMAT DEBUG:" <> PPL.nl <> stringToPPL errString <> PPL.nl <> text "-/\n"
    else
      return text ""

    -- let currentEnv := (← getEnv)

    -- let _ ← modify fun s => {s with nextId := 0, MyState.otherEnv}
  def pfTopLevel (stx : Syntax) (environments : List Environment) (options : Options) : IO (Except FormattingError (PPL × FormatState)) :=
    let introduceContext := ((pf stx).run { envs:= environments, options:= options, stx:=[]})
    let introduceState := introduceContext.run {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}}
    introduceState.run

  -- Also fallback to standard syntax if formatting fails
  partial def pfTopLevelWithDebug (stx : Syntax) (environments : List Environment) (options : Options) : IO PPL := do
    let s ← pfTopLevel stx environments options
    let debugReport ← debugReportAsPPL stx options s
    -- TODO: figure out do notation weirdness here
    let ppl ← match s with
    | .ok (ppl, _) => pure ppl  -- Use `pure` instead of `do return`
    | .error _ => topLevelUnformatedSyntaxToPPL stx  -- No `do` needed

    return debugReport <> ppl


end PrettyFormat



initialize formattedCode : IO.Ref String ← IO.mkRef "initialString"
