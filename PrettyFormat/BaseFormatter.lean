import PrettyFormat

open Lean
open Data
open Std

open Lean
open Lean.Meta
open Lean.Elab.Command

namespace PrettyFormat
  partial def nest (n:Nat) (s: formatPPLM PPL): formatPPLM PPL :=
    do
    let state ← get
    set {state with nesting := state.nesting + n}
    let result ← s
    let o:PPL := PPL.nest n (result)
    let state' ← get
    set {state' with nesting := state.nesting}
    return o
  partial def nl : formatPPLM PPL := do
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
    partial def pf (stx: Syntax): formatPPLM PPL := do
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
            IO.println s!"could not find something for {kind}" -- we could not find a formatter
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
    partial def pfCombine :formatPPL
    | a => do
      a.foldlM (fun p s => do
        let p' ← pf s
        return p <> p') (text "")

    partial def pfCombineWithSeparator (sep: PPL) :formatPPL
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
end PrettyFormat
