
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

inductive PPLSpacing where
  | space : PPLSpacing
  | newline : PPLSpacing
  | either : PPLSpacing
  deriving Repr, BEq

inductive PPL where
  | nl : PPL
  | text : String → PPL
  -- This will be turned into text, but is used to detect
  -- whether we accidentally flatten code to be part of a comment
  | commentText : String → PPL
  -- If we get into a scenario where we cannot parse the
  | error : String → PPL
  -- optional space, that will be reduced to a single space or a newline
  | optionalSpace : PPLSpacing → PPL
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

def empty := -- used when starting a new node
  text ""

def v (s: String): PPL:=
  PPL.var s


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
  | PPL.optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => " "
    | PPLSpacing.newline => "\n"
    | PPLSpacing.either => "\n"
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
  | PPL.optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => s!"text \" \"\n"
    | PPLSpacing.newline => "nl\n"
    | PPLSpacing.either => s!"text \" \"\n"
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

def escapeQuotes (s : String) : String :=
  s.replace "\"" "\\\""

partial def toOcaml : PPL → String
  | PPL.var v => "exit_"++v
  | PPL.commentText s => s!"text \"{escapeQuotes s}\"\n"
  | PPL.optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => s!"text \" \"\n"
    | PPLSpacing.newline => "nl\n"
    | PPLSpacing.either => s!"text \" \"\n"
  | PPL.error s => s!"error {escapeQuotes s}\n"
  | PPL.text s => s!"text \"{escapeQuotes s}\""
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
  | PPL.optionalSpace _ =>
    true
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
  | PPL.optionalSpace spacing =>
    if state.flatten && spacing == PPLSpacing.newline then
      (PPL.optionalSpace spacing, state)
    else
      (PPL.optionalSpace spacing, {state with startedComment := state.startedComment && spacing != PPLSpacing.newline})
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


  inductive newlineState where
    | none
    | space
    | newline

  -- partial def removeDuplicateSpaces : PPL → (PPL × newlineState)
  -- | PPL.var v => (PPL.var v, newlineState.space)
  -- | PPL.unallignedConcat left right =>
  --   let (l, s):= removeDuplicateSpaces left

  structure FormatContext where
    -- prefer the first environment
    envs: List Environment
    options: Options
    -- myEnv: Environment -- The env from the file
    -- otherEnv: Environment -- The env from the formatted file

  structure MyState where
    nextId : Nat := 0-- used to generate ids
    nesting: Nat := 0 -- how many times we have nested
    startOfLine: Bool := true -- whether we are at the start of a line
    unknown: Bool := false -- whether we are in an unknown state (If we are in an unkown state we will try to keep the value the same as it was)


  abbrev formatPPLM := ReaderT FormatContext (StateRefT MyState MetaM)
  abbrev formatPPL := Array Syntax → formatPPLM PrettyFormat.PPL

  unsafe def mkPFormatAttr : IO (KeyedDeclsAttribute formatPPL) :=
    KeyedDeclsAttribute.init {
      builtinName := `builtin_pFormat,
      name := `pFormat,
      descr    := "Register a formatter.

    [pFormat k]"
      valueTypeName := `PrettyFormat.formatPPL
      evalKey := fun _ stx => do
        let stx ← Attribute.Builtin.getIdent stx
        let kind := stx.getId
        pure kind
    } `pFormat
  @[init mkPFormatAttr] opaque pFormatAttr : KeyedDeclsAttribute formatPPL



register_option pf.lineLength : Nat := {
  defValue := 100
  group    := "pf"
  descr    := "(pretty format) Maximum number of characters in a line"
}

def getPFLineLength (o : Options) : Nat := o.get pf.lineLength.name pf.lineLength.defValue


end PrettyFormat
