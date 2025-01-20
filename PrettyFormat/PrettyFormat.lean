
-- inductive Value where
--   | newline : Value
--   | text : String → Value
--   | choice : List Value → Value
--   deriving Repr
import Std.Data.HashMap
import Lean

open Lean
open Data
open Std

open Lean
open Lean.Meta
open Lean.Elab.Command


namespace PrettyFormat

inductive PPL where
  | nl : PPL
  | text : String → PPL
  -- This will be turned into text, but is used to detect
  -- whether we accidentally flatten code to be part of a comment
  | commentText : String → PPL
  -- If we get into a scenario where we cannot parse the
  | error : String → PPL

  | choice : PPL → PPL → PPL
  | unallignedConcat : PPL → PPL → PPL
  | flatten : PPL → PPL
  | align : PPL → PPL
  | nest : Nat → PPL → PPL
  | var : String → PPL
  | letExpr : String → PPL → PPL → PPL
  deriving Repr

infixl:60 " <^> " => fun l r => PPL.choice l r
infixl:60 " <> " => fun l r => PPL.unallignedConcat l r
macro "let " x:ident " = " s:term " in " body:term : term =>
  `(PPL.letExpr $(Lean.quote x.getId.toString) $s $body)

infixl:60 " <$> " => fun l r => l <> PPL.nl <> r
infixl:60 " <+> " => fun l r => l <> PPL.align r

-- abstractions
-- a choice between flattening or not
-- macro group -- M(𝛼1) = 𝛼1 <|> flatten 𝛼1
-- vertical concatenation
-- macro <$> -- M(𝛼1, 𝛼2) = 𝛼1 <> nl <> 𝛼2.
-- alligned concatenation
-- macro <+> -- M(𝛼1, 𝛼2) = 𝛼1 <> align 𝛼2.


def text (s: String): PPL:=
  PPL.text s

def commentText (s: String): PPL:=
  PPL.commentText s

def flatten (s: PPL): PPL:=
  PPL.flatten s

def align (s: PPL): PPL:=
  PPL.align s


def group (s: PPL): PPL:=
  s <^> flatten s

def nl : PPL:=
  PPL.nl

def empty := -- used when starting a new node
  text ""

def v (s: String): PPL:=
  PPL.var s



#eval let x = text "s" in flatten (text "hello" <^> text "b")

def genTest: PPL :=
  let o := (text "function␣append(first,second,third){"
          <> PPL.nest 4 (
          let f = text "first +" in
          let s = text "second +" in
          let t = text "third" in
          nl <> text "return " <>
          group (PPL.nest 4 ((v "f") <> nl <> (v "s") <> nl <> (v "t")))
          ) <> nl <> text "}")
  o
-- def genTest2: PPL :=
--   let o := (text "function␣append(first,second,third){" <$> ( let f = text "first␣+" in
--         let s = text "second␣+" in
--         let t = text "third" in
--         let sp = text "␣" in
--         let ret = text "return␣" in
--         text "␣␣␣␣" <+>
--         (((ret <+> text "(") <$>
--         (text <+> (f <$> s <$> t)) <$>
--         text ")") <|>
--         (ret <+> f <+> sp <+> s <+> sp <+> t)))
--         <$> text "}")
--   o

def repeatString (s : String) (n : Nat) : String :=
  let rec loop (acc : String) : Nat → String
    | 0 => acc
    | n + 1 => loop (acc ++ s) (n)
  loop "" n



partial def prettyPrintWithVars (vars : List (String × PPL)) (indent:Nat): (ppl : PPL) → String
  | PPL.var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => prettyPrintWithVars vars indent value
    | none => v
  | PPL.commentText s => s
  | PPL.error s => "\n" ++ s ++ " "
  | PPL.text s => s
  | PPL.nl => "\n" ++ repeatString " " indent
  | PPL.choice left right => prettyPrintWithVars vars indent left ++ " | " ++ prettyPrintWithVars vars indent right
  | PPL.flatten inner => prettyPrintWithVars vars indent inner
  | PPL.align inner => prettyPrintWithVars vars indent inner
  | PPL.nest n inner => prettyPrintWithVars vars (indent + n) inner
  | PPL.unallignedConcat left right => prettyPrintWithVars vars indent left ++ prettyPrintWithVars vars indent right
  | PPL.letExpr var expr body =>
    let vars := (var, expr) :: vars
    prettyPrintWithVars vars indent body

partial def output : PPL → String
  | PPL.var v => v
  | PPL.commentText s => s!"text \"{s}\"\n"
  | PPL.error s => s!"error {s}"
  | PPL.text s => s!"text \"{s}\""
  | PPL.nl => "nl\n"
  | PPL.choice left right => s!"({output left})<|>({output right})\n"
  | PPL.flatten inner => s!"flatten ({output inner})"
  | PPL.align inner => s!"align ({output inner})"
  | PPL.nest n inner => s!"nest {n} ({output inner})"
  | PPL.unallignedConcat left right => s!"({output left}) <> ({output right})"
  | PPL.letExpr var expr body => s!"let {var} = ({output expr}) in ({output body})"

partial def toOcaml : PPL → String
  | PPL.var v => "exit_"++v
  | PPL.commentText s => s!"text \"{s}\"\n"
  | PPL.error s => s!"error {s}\n"
  | PPL.text s => s!"text \"{s}\""
  | PPL.nl => "nl\n"
  | PPL.choice left right => s!"({toOcaml left})\n<|>({toOcaml right})"
  | PPL.flatten inner => s!"flatten ({toOcaml inner})\n"
  | PPL.align inner => s!"align ({toOcaml inner})"
  | PPL.nest n inner => s!"nest {n} ({toOcaml inner})"
  | PPL.unallignedConcat left right => s!"({toOcaml left}) ^^ ({toOcaml right})"
  | PPL.letExpr var expr body => s!"let exit_{var} = ({toOcaml expr}) in ({toOcaml body})\n"

partial def isEmpty (vars : List (String × PPL)): (ppl : PPL) → Bool
  | PPL.var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => isEmpty vars value
    | none => true
  | PPL.commentText s => s.trim.length == 0
  | PPL.error s => true
  | PPL.text s => s.trim.length == 0
  | PPL.nl => false
  | PPL.choice left right => isEmpty vars left && isEmpty vars right
  | PPL.flatten inner => isEmpty vars inner
  | PPL.align inner => isEmpty vars inner
  | PPL.nest n inner => isEmpty vars inner
  | PPL.unallignedConcat left right => isEmpty vars left && isEmpty vars right
  | PPL.letExpr var expr body =>
    let vars := (var, expr) :: vars
    isEmpty vars body

#eval output genTest
#eval prettyPrintWithVars [] 0 genTest
#eval genTest

structure CommentFix where
  flatten : Bool
  startedComment : Bool
  vars: Std.HashMap String PPL


instance : Inhabited PPL where
  default := PPL.error "default error"

instance : Inhabited CommentFix where
  default := { flatten := false, startedComment := false, vars := {} }

instance : Inhabited (PPL × CommentFix) where
  default := (default, default)

-- propagate errors up the tree
-- detect whether comments accidentally
partial def eliminateErrors (state: CommentFix) : PPL → (PPL × CommentFix)
  | PPL.var v =>
    if state.flatten then
      match state.vars[v]? with
    | some (value) =>
      match eliminateErrors state value with
      | (PPL.error e, s') => (PPL.error e, s')
      | _ => (PPL.var v, state)
    | none => (PPL.error s!"Using undefined variable {v}", state)
   else (PPL.var v, state)
  | PPL.commentText s => (PPL.commentText s, {state with startedComment := true })
  | PPL.error s => (PPL.error s, state)
  | PPL.text s =>
    if state.flatten && state.startedComment && s.trim.length > 0 then
      (PPL.error "cannot write text after an inline comment", state)
    else
      (PPL.text s, state)
  | PPL.nl =>
    if state.flatten then
      (text " ", state)
    else
      (PPL.nl, {state with startedComment := false})
  | PPL.choice left right => --s!"({output left})<|>({output right})"
    match (eliminateErrors state left, eliminateErrors state right) with
    | ((PPL.error l, _), (PPL.error r, _)) => (PPL.error s!"{l}<|>{r}", state)
    | ((PPL.error l, _), (v, s)) => (v,s)
    | ((v,s), (PPL.error r, _)) => (v,s)
    | ((vl,sl), (vr,sr)) => (vl<^>vr, {sl with startedComment:= sl.startedComment && sr.startedComment})
  | PPL.flatten inner =>
    let (inner', state') := (eliminateErrors {state with flatten:=true} inner)
    match inner' with
    | PPL.error x => (PPL.error x, {state with startedComment:= state'.startedComment})
    | _ => (PPL.flatten inner', {state with startedComment:= state'.startedComment})
  | PPL.align inner =>
    let (inner', state') := (eliminateErrors state inner)
    match inner' with
    | PPL.error x => (PPL.error x, {state with startedComment:= state'.startedComment})
    | _ => (PPL.align inner', {state with startedComment:= state'.startedComment})
  | PPL.nest n inner =>
    let (inner', state') := (eliminateErrors state inner)
    match inner' with
    | PPL.error x => (PPL.error x, state)
    | _ =>
      if state.flatten then
        (PPL.nest n inner', state)
      else
        (PPL.nest n inner', {state with startedComment:= state'.startedComment})
  | PPL.unallignedConcat left right => (left, state) -- TODO
  | PPL.letExpr var expr body => (body, state) -- TODO


  structure FormatContext where
    tmp : Nat := 0

  structure MyState where
    nextId : Nat -- used to generate ids
    otherEnv: Environment -- The env from the formatted file
    nesting: Nat := 0 -- how many times we have nested


  abbrev formatPPLM := ReaderT FormatContext (StateRefT MyState MetaM)
  abbrev formatPPL := Array Syntax → formatPPLM PrettyFormat.PPL
  -- abbrev formatPPLArg := Array Syntax → formatPPLM PrettyFormat.PPL

  unsafe def mkPFormatAttr : IO (KeyedDeclsAttribute formatPPL) :=
    KeyedDeclsAttribute.init {
      builtinName := `builtin_pFormat,
      name := `pFormat,
      descr    := "Register a delaborator.

    [pFormat k]",
      valueTypeName := `PrettyFormat.formatPPL
      evalKey := fun _ stx => do
        let stx ← Attribute.Builtin.getIdent stx
        let kind := stx.getId
        if (← Elab.getInfoState).enabled && kind.getRoot == `app then
          let c := kind.replacePrefix `app .anonymous
          if (← getEnv).contains c then
            Elab.addConstInfo stx c none
        pure kind
    } `pFormat
  @[init mkPFormatAttr] opaque pFormatAttr : KeyedDeclsAttribute formatPPL


  partial def nest (n:Nat) (s: formatPPLM PPL): formatPPLM PPL :=
    do
    let state ← get
    set {state with nesting := state.nesting + n}
    let result ← s
    let o:PPL := PPL.nest n (result)
    let state' ← get
    set {state' with nesting := state.nesting}
    return o


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
      let state ← get
      match stx with
      | .missing => pure (text "")
      | .node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
        -- try to use the other environments attributes
        -- We prefer the other environment
        let options := pFormatAttr.getValues state.otherEnv kind
          -- get the first formatter that does not fail
        let res ← options.foldlM (fun p f => do
            match p with
            | none =>
              try
                return some (← f args)
              catch _ =>
                return none
            | some p => return some p
            )
          none
        match res with
        | some p => return p
        | none =>
          let env ← getEnv
          -- try to use the current environment attributes
          let options := pFormatAttr.getValues env kind
          -- get the first formatter that does not fail
          let res ← options.foldlM (fun p f => do
              match p with
              | none =>
                try
                  return some (← f args)
                catch _ =>
                  return none
              | some p => return some p
              )
            none
          match res with
          | some p => return p
          | none => return text s!"could not find something for {kind}" -- we could not find a formatter
          -- | none => failure -- we could not find a formatter
      | .atom (info : SourceInfo) (val : String) => return (unknownSurroundWithComments info (text "")) (fun p => p <> text val)
      | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
          match val with
          | _ => return (unknownSurroundWithComments info (text "")) (fun p => p <> text rawVal.toString)


    partial def unknownStringCommentsStr (s:String) : List String :=
    if s.contains '\n' then
      s.split (fun c => c == '\n')
      |>.filterMap (fun s => findPatternStart s "--")
      |>.filter (fun (s:String) => s.trim.length > 0)
      |>.map (fun (s:String) => "-- " ++ s.trim)
    else
      if s.length > 0 then
        [" "]
      else
        []

    partial def unknownStringToPPL (s:String) (p: PPL) : PPL :=
      stringCommentsStr s |>.foldl (fun p' c => p' <> commentText c <> nl) p

    -- if the value is unknown then we will try to keep the value the same as it was
    partial def unknownSurroundWithComments (info : SourceInfo) (p:PPL) (f : PPL → PPL): PPL:=
      match info with
      | .original (leading : Substring) (pos : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
        unknownStringToPPL leading.toString p
        |> f
        |> unknownStringToPPL trailing.toString
      | _ => f p

  end

  -- combine the formatters without separators
  partial def pfCombine :formatPPL
  | a => do
    a.foldlM (fun p s => do
      let p' ← pf s
      return p <> p') (text "")

  partial def pfCombineWithSeparator (sep: PPL) :formatPPL
  | a => do
    IO.println "first time through?"
    a.foldlM (fun p s => do
      let p' ← pf s
      return p <> sep <> p') (text "")

end PrettyFormat



-- initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

-- -- so initialize
-- initialize formatAttr : ParametricAttribute Name ← do
--   registerParametricAttribute {
--     name := `format
--     descr := "Custom format attribute"
--     getParam := fun _ stx => do
--       match stx with
--       | `(attr| format $id:ident) => pure id.getId
--       | _ => throwError "invalid [format] attribute usage"
--   }


-- initialize registerBuiltinAttribute {
--   name := `trace_add
--   descr := "Simply traces when added, to debug double-application bugs"
--   add   := fun decl _stx _kind => do
--     logInfo m!"trace_add attribute added to {decl}"
--   -- applicationTime := .afterCompilation
-- }

-- namespace PPL
-- end PPL

-- syntax text
-- syntax nl
-- -- arbitrary choice
-- syntax <_> -- should be <|>
-- syntax <>
-- syntax nest n
-- syntax flatten
-- syntax align

-- let $a = $v in
