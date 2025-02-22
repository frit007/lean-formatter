
-- inductive Value where
--   | newline : Value
--   | text : String → Value
--   | choice : List Value → Value
--   deriving Repr
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
  | group : String → PPL → PPL
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



partial def prettyPrintWithVars  (ppl : PPL) : String :=
  prettyPrintWithVars' [] 0 ppl
where
  prettyPrintWithVars' (vars : List (String × PPL)) (indent:Nat): (ppl : PPL) → String
  | PPL.var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => prettyPrintWithVars' vars indent value
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
  | PPL.choice left right => prettyPrintWithVars' vars indent left ++ " | " ++ prettyPrintWithVars' vars indent right
  | PPL.flatten inner => prettyPrintWithVars' vars indent inner
  | PPL.align inner => prettyPrintWithVars' vars indent inner
  | PPL.nest n inner => prettyPrintWithVars' vars (indent + n) inner
  | PPL.unallignedConcat left right => prettyPrintWithVars' vars indent left ++ prettyPrintWithVars' vars indent right
  | PPL.letExpr var expr body =>
    let vars := (var, expr) :: vars
    prettyPrintWithVars' vars indent body
  | PPL.group _ ppl => prettyPrintWithVars' vars indent ppl


partial def output (ppl:PPL) : String :=
  output' 0 ppl
where
  output' (indent : Nat) : PPL → String
  | PPL.var v => v
  | PPL.optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => s!"text \" \""
    | PPLSpacing.newline => "nl"
    | PPLSpacing.either => s!"text \" \""
  | PPL.commentText s => s!"text \"{s}\""
  | PPL.error s => s!"error {s}"
  | PPL.text s => s!"text \"{s}\""
  | PPL.nl => "nl"
  | PPL.choice left right => s!"({output' indent left})<|>({output' indent right})\n"
  | PPL.flatten inner => s!"flatten ({output' indent inner})"
  | PPL.align inner => s!"align ({output' indent inner})"
  | PPL.nest n inner => s!"nest {n} ({output' indent inner})"
  | PPL.unallignedConcat left right => s!"({output' indent left}) <> ({output' indent right})"
  | PPL.letExpr var expr body => s!"let {var} = ({output' indent expr}) in ({output' indent body})"
  | PPL.group s inner => s!"\n {repeatString " " indent} ({s}: {output' (indent + 2) inner})"

def escapeQuotes (s : String) : String :=
  s.replace "\"" "\\\""

open Pfmt

partial def toDoc (ppl:PPL): Doc :=
  toDoc' [] ppl
where
 toDoc' (vars : List (String × Doc)) : PPL → Doc
  | PPL.var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => value
    | none => Doc.text s!"missing variable {v}"
  | PPL.commentText s => Doc.text s
  | PPL.optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => Doc.text s!" "
    | PPLSpacing.newline => Doc.newline ""
    | PPLSpacing.either => Doc.text s!" " <|||> Doc.newline ""
  | PPL.error s => Doc.text s
  | PPL.text s => Doc.text s
  | PPL.nl => Doc.newline ""
  | PPL.choice l r => (toDoc' vars l) <|||> (toDoc' vars r)
  | PPL.flatten inner => toDoc' vars inner -- for now nothing
  | PPL.align inner => Doc.align (toDoc' vars inner)
  | PPL.nest n inner => Doc.nest n (toDoc' vars inner)
  | PPL.unallignedConcat l r => Doc.concat (toDoc' vars l) (toDoc' vars r)
  | PPL.letExpr var expr body => toDoc' ((var, toDoc' vars expr)::vars) body
  | .group _ inner => toDoc' vars inner



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
  | PPL.group _ inner => toOcaml inner

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
  | PPL.group _ inner => isEmpty vars inner

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
-- detect whether comments accidentally are flattened, and if they are eliminate choices where that happens
-- this will probably be moved to creation of the object
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
  | .group _ inner => (inner, state)


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

  inductive FormatError where
  | FlattenedComment
  | NotHandled (name : Name) (stx : List Syntax)
  | NoFormatter (stx : Syntax)
  | Unknown
  deriving Inhabited, Repr

  instance : ToString FormatError where
    toString b :=
      match b with
      | .FlattenedComment => "FlattenedComment"
      | .NotHandled name stx =>
        let parentChain := stx.map (fun s => s.getKind) |>.filter (fun s => s != `missing && s != `ident) |>.map toString |>.reverse |> String.intercalate " → "

        s!"Not handled {name} {stx.length} chain: {parentChain}"
      | .NoFormatter stx => s!"NoFormatter {stx.getKind}"
      | .Unknown => "unknown"

  instance : Repr FormatError where
    reprPrec b n :=
      match b with
      | .FlattenedComment => "FlattenedComment"
      | .NotHandled name stx => s!"Not handled {name} {repr stx}"
      | .NoFormatter stx => s!"NoFormatter {repr stx}"
      | .Unknown => "unknown"

  structure FormattingDiagnostic where
    failures : List (FormatError × List Syntax) := []
    -- to make it faster to debug write down the first instance the the formatter is missing
    missingFormatters : Std.HashMap Name Syntax := Std.HashMap.empty
  deriving Inhabited

  instance : Repr (IO.Ref FormattingDiagnostic) where
    reprPrec a n :=
      "ref Formatting diagnostic" --we cannot

  instance : Repr FormattingDiagnostic where
    reprPrec a n :=
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


  structure FormatState where
    nextId : Nat := 0 -- used to generate ids
    nesting: Nat := 0 -- how many times we have nested
    startOfLine: Bool := true -- whether we are at the start of a line
    unknown: Bool := false -- whether we are in an unknown state (If we are in an unkown state we will try to keep the value the same as it was)
    diagnostic: FormattingDiagnostic := {}
    stx : List Syntax := [] -- note that syntax is in reverse order for performance reasons
  deriving Repr


  abbrev FormatM a := ReaderT FormatContext (StateM FormatState) a
  abbrev RuleM a := ExceptT FormatError FormatM a
  abbrev Rule := Array Syntax → (RuleM PPL)

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



-- @[always_inline]
-- instance : Monad FormatPPLM := let i := inferInstanceAs (Monad FormatPPLM); { pure := i.pure, bind := i.bind }

-- instance : Inhabited (FormatPPLM α) where
--   default := fun _ _ => default

instance : MonadBacktrack FormatState RuleM where
  saveState      := get
  restoreState s := set s


@[inline] protected def orElse (x : RuleM α) (y : Unit → RuleM α) : RuleM α := do
  let s ← saveState
  try x catch _ => do set s; y ()

instance : OrElse (RuleM α) := ⟨PrettyFormat.orElse⟩

-- instance : MonadRef FormatPPLM where
--   getRef := return (← read).stx.get! 0
--   withRef ref x := withReader (fun ctx => { ctx with stx := [ref] }) x


set_option diagnostics true

-- instance : MonadExcept FormatPPLM where
--   throw {α : Type v} : ε → m α
--   tryCatch {α : Type v} : m α → (ε → m α) → m α

instance : Alternative RuleM where
  failure := fun {_} => do

    throw (FormatError.NotHandled (← get).stx.head!.getKind (← get).stx)
  orElse  := PrettyFormat.orElse



register_option pf.lineLength : Nat := {
  defValue := 100
  group    := "pf"
  descr    := "(pretty format) Maximum number of characters in a line"
}

register_option pf.debugSyntax : Nat := {
  defValue := 0
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, before being formatted"
}
register_option pf.debugSyntaxAfter : Nat := {
  defValue := 0
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, after being formatted"
}
register_option pf.debugErrors : Nat := {
  defValue := 0
  group    := "pf"
  descr    := "(pretty format) Output the errors"
}
register_option pf.debugMissingFormatters : Nat := {
  defValue := 0
  group    := "pf"
  descr    := "(pretty format) Output a list of missing formatters above the function"
}
register_option pf.debugPPL : Nat := {
  defValue := 0
  group    := "pf"
  descr    := "(pretty format) Output the generated PPL above the function"
}
register_option pf.debugPPLGroups : Nat := {
    defValue := 0
    group    := "pf"
    descr    := "(pretty format) Add grouping around every PPL formatter"
}
register_option pf.warnCSTmismatch : Nat := {
    defValue := 1
    group    := "pf"
    descr    := "(pretty format) When the formatted syntax does not match the original syntax, output a warning"
}

def getPFLineLength (o : Options) : Nat := o.get pf.lineLength.name pf.lineLength.defValue

def getDebugSyntax (o : Options) : Bool := (o.get pf.debugSyntax.name pf.debugSyntax.defValue) != 0
def getDebugSyntaxAfter (o : Options) : Bool := (o.get pf.debugSyntaxAfter.name pf.debugSyntaxAfter.defValue) != 0
def getDebugErrors (o : Options) : Bool := (o.get pf.debugErrors.name pf.debugErrors.defValue) != 0
def getDebugMissingFormatters (o : Options) : Bool := (o.get pf.debugMissingFormatters.name pf.debugMissingFormatters.defValue) != 0
def getDebugPPL (o : Options) : Bool := (o.get pf.debugPPL.name pf.debugPPL.defValue) != 0
def getWarnCSTmismatch (o : Options) : Bool := (o.get pf.warnCSTmismatch.name pf.warnCSTmismatch.defValue) != 0


end PrettyFormat
