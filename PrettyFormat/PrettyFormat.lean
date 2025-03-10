
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
  -- group is only intended to be used internally by the library
  -- group must satisfy the invariant: group cannot contain PPL.stx. Because the formatting rules will never be applied
  -- group does not affect the way the code is formatted
  -- group helps us debug the output by keeping track of which formatting rule produced the output
  | group : String → PPL → PPL
  | stx : (Syntax → PPL)
  deriving Repr


class ToPPL (α : Type u) where
  toPPL : α → PPL

export ToPPL (toPPL)

instance : ToPPL PPL where
  toPPL ppl:= ppl
instance : ToPPL Syntax where
  toPPL stx:= PPL.stx stx
instance : ToPPL String where
  toPPL text:= PPL.text text
instance : ToPPL (TSyntax a) where
  toPPL tstx:= PPL.stx tstx.raw

infixl:40 " <^> " => fun l r => PPL.choice (toPPL l) (toPPL r)
infixl:40 " <> " => fun l r => PPL.unallignedConcat (toPPL l) (toPPL r)
macro "let " x:ident " = " s:term " in " body:term : term =>
  `(PPL.letExpr $(Lean.quote x.getId.toString) $s (toPPL $body))

infixl:40 " <$> " => fun l r => l <> PPL.nl <> (toPPL r)
infixl:40 " <+> " => fun l r => l <> PPL.align (toPPL r)


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
  | .var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => prettyPrintWithVars' vars indent value
    | none => v
  | .optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => " "
    | PPLSpacing.newline => "\n"
    | PPLSpacing.either => "\n"
  | .commentText s => s
  | .error s => "\n" ++ s ++ " "
  | .text s => s
  | .nl => "\n" ++ repeatString " " indent
  | .choice left right => prettyPrintWithVars' vars indent left ++ " | " ++ prettyPrintWithVars' vars indent right
  | .flatten inner => prettyPrintWithVars' vars indent inner
  | .align inner => prettyPrintWithVars' vars indent inner
  | .nest n inner => prettyPrintWithVars' vars (indent + n) inner
  | .unallignedConcat left right => prettyPrintWithVars' vars indent left ++ prettyPrintWithVars' vars indent right
  | .letExpr var expr body =>
    let vars := (var, expr) :: vars
    prettyPrintWithVars' vars indent body
  | .group _ ppl => prettyPrintWithVars' vars indent ppl
  | .stx stx => s!"stx {stx}"


partial def output (ppl:PPL) : String :=
  output' 0 ppl
where
  output' (indent : Nat) : PPL → String
  | .var v => v
  | .optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => s!"text \" \""
    | PPLSpacing.newline => "nl"
    | PPLSpacing.either => s!"text \" \""
  | .commentText s => s!"text \"{s}\""
  | .error s => s!"error {s}"
  | .text s => s!"text \"{s}\""
  | .nl => "nl"
  | .choice left right => s!"({output' indent left})<|>({output' indent right})\n"
  | .flatten inner => s!"flatten ({output' indent inner})"
  | .align inner => s!"align ({output' indent inner})"
  | .nest n inner => s!"nest {n} ({output' indent inner})"
  | .unallignedConcat left right => s!"({output' indent left}) <> ({output' indent right})"
  | .letExpr var expr body => s!"let {var} = ({output' indent expr}) in ({output' indent body})"
  | .group s inner => s!"\n {repeatString " " indent} ({s}: {output' (indent + 2) inner})"
  | .stx stx => "stx\n"

def escapeQuotes (s : String) : String :=
  s.replace "\"" "\\\""

open Pfmt

partial def toDoc (ppl:PPL): Doc :=
  toDoc' [] ppl
where
 toDoc' (vars : List (String × Doc)) : PPL → Doc
  | .var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => value
    | none => Doc.text s!"missing variable {v}"
  | .commentText s => Doc.text s
  | .optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => Doc.text s!" "
    | PPLSpacing.newline => Doc.newline ""
    | PPLSpacing.either => Doc.text s!" " <|||> Doc.newline ""
  | .error s => Doc.text s
  | .text s => Doc.text s
  | .nl => Doc.newline ""
  | .choice l r => (toDoc' vars l) <|||> (toDoc' vars r)
  | .flatten inner => toDoc' vars inner -- for now nothing
  | .align inner => Doc.align (toDoc' vars inner)
  | .nest n inner => Doc.nest n (toDoc' vars inner)
  | .unallignedConcat l r => Doc.concat (toDoc' vars l) (toDoc' vars r)
  | .letExpr var expr body => toDoc' ((var, toDoc' vars expr)::vars) body
  | .group _ inner => toDoc' vars inner
  | .stx _ => Doc.text "unformated syntax"



partial def toOcaml : PPL → String
  | .var v => "exit_"++v
  | .commentText s => s!"text \"{escapeQuotes s}\"\n"
  | .optionalSpace spacing =>
    match spacing with
    | PPLSpacing.space => s!"text \" \"\n"
    | PPLSpacing.newline => "nl\n"
    | PPLSpacing.either => s!"text \" \"\n"
  | .error s => s!"error {escapeQuotes s}\n"
  | .text s => s!"text \"{escapeQuotes s}\""
  | .nl => "nl\n"
  | .choice left right => s!"({toOcaml left})\n<|>({toOcaml right})"
  | .flatten inner => s!"flatten ({toOcaml inner})\n"
  | .align inner => s!"align ({toOcaml inner})"
  | .nest n inner => s!"nest {n} ({toOcaml inner})"
  | .unallignedConcat left right => s!"({toOcaml left}) ^^ ({toOcaml right})"
  | .letExpr var expr body => s!"let exit_{var} = ({toOcaml expr}) in ({toOcaml body})\n"
  | .group _ inner => toOcaml inner
  | .stx _ => "text \"\""

partial def isSyntaxEmpty (stx : Syntax) : Bool :=
  match stx with
  | .missing => false
  | .node _ _ args =>
    args.all (fun s => isSyntaxEmpty s)
  | .atom (info : SourceInfo) (val : String) =>
    val.trim.length == 0 -- TODO: there might be a comment attached to this node
  | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
    (toString rawVal).trim.length == 0


partial def isEmpty [ToPPL a] (ppl : a) : Bool :=
  isEmpty' [] (toPPL ppl)
where
  isEmpty' (vars : List (String × PPL)) : (ppl : PPL) → Bool
  | PPL.var v =>
    match vars.find? (fun (name, _) => name = v) with
    | some (_, value) => isEmpty' vars value
    | none => true
  | PPL.commentText s => s.trim.length == 0
  | PPL.optionalSpace _ =>
    true
  | PPL.error s => true
  | PPL.text s => s.trim.length == 0
  | PPL.nl => false
  | PPL.choice left right => isEmpty' vars left && isEmpty' vars right
  | PPL.flatten inner => isEmpty' vars inner
  | PPL.align inner => isEmpty' vars inner
  | PPL.nest n inner => isEmpty' vars inner
  | PPL.unallignedConcat left right => isEmpty' vars left && isEmpty' vars right
  | PPL.letExpr var expr body =>
    let vars := (var, expr) :: vars
    isEmpty' vars body
  | PPL.group _ inner => isEmpty' vars inner
  | .stx s => isSyntaxEmpty s



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
  | .var v =>
    if state.flatten then
      match state.vars[v]? with
    | some (value) =>
      match eliminateErrors state value with
      | (PPL.error e, s') => (PPL.error e, s')
      | _ => (PPL.var v, state)
    | none => (PPL.error s!"Using undefined variable {v}", state)
   else (PPL.var v, state)
  | .commentText s => (PPL.commentText s, {state with startedComment := true })
  | .optionalSpace spacing =>
    if state.flatten && spacing == PPLSpacing.newline then
      (PPL.optionalSpace spacing, state)
    else
      (PPL.optionalSpace spacing, {state with startedComment := state.startedComment && spacing != PPLSpacing.newline})
  | .error s => (PPL.error s, state)
  | .text s =>
    if state.flatten && state.startedComment && s.trim.length > 0 then
      (PPL.error "cannot write text after an inline comment", state)
    else
      (PPL.text s, state)
  | .nl =>
    if state.flatten then
      (text " ", state)
    else
      (PPL.nl, {state with startedComment := false})
  | .choice left right => --s!"({output left})<|>({output right})"
    match (eliminateErrors state left, eliminateErrors state right) with
    | ((PPL.error l, _), (PPL.error r, _)) => (PPL.error s!"{l}<|>{r}", state)
    | ((PPL.error l, _), (v, s)) => (v,s)
    | ((v,s), (PPL.error r, _)) => (v,s)
    | ((vl,sl), (vr,sr)) => (vl<^>vr, {sl with startedComment:= sl.startedComment && sr.startedComment})
  | .flatten inner =>
    let (inner', state') := (eliminateErrors {state with flatten:=true} inner)
    match inner' with
    | .error x => (PPL.error x, {state with startedComment:= state'.startedComment})
    | _ => (PPL.flatten inner', {state with startedComment:= state'.startedComment})
  | .align inner =>
    let (inner', state') := (eliminateErrors state inner)
    match inner' with
    | .error x => (PPL.error x, {state with startedComment:= state'.startedComment})
    | _ => (PPL.align inner', {state with startedComment:= state'.startedComment})
  | .nest n inner =>
    let (inner', state') := (eliminateErrors state inner)
    match inner' with
    | .error x => (PPL.error x, state)
    | _ =>
      if state.flatten then
        (PPL.nest n inner', state)
      else
        (PPL.nest n inner', {state with startedComment:= state'.startedComment})
  | .unallignedConcat left right => (left, state) -- TODO
  | .letExpr var expr body => (body, state) -- TODO
  | .group _ inner => (inner, state)
  | .stx stx => (PPL.stx stx, state)


  inductive newlineState where
    | none
    | space
    | newline


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


  structure FormatReport where
    missingFormatters : Std.HashMap Name Nat := Std.HashMap.empty
    totalCommands: Nat := 0
    formattedCommands: Nat := 0
    timePF : Nat := 0
    timeDoc : Nat := 0
    timeReadAndParse : Nat := 0
    timeReparse : Nat := 0

  def FormatReport.combineReports (a : FormatReport) (b : FormatReport) : FormatReport :=
    { missingFormatters := a.missingFormatters.fold (fun acc name p => acc.insert name (acc.getD name 0 + p)) b.missingFormatters,
      totalCommands := a.totalCommands + b.totalCommands,
      formattedCommands := a.formattedCommands + b.formattedCommands
      timePF := a.timePF + b.timePF
      timeDoc := a.timeDoc + b.timeDoc
      timeReadAndParse := a.timeReadAndParse + b.timeReadAndParse
      timeReparse := a.timeReparse + b.timeReparse
    }

  structure FormatState where
    options: Options := {}
    nextId : Nat := 0 -- used to generate ids
    nesting: Nat := 0 -- how many times we have nested
    startOfLine: Bool := true -- whether we are at the start of a line
    unknown: Bool := false -- whether we are in an unknown state (If we are in an unkown state we will try to keep the value the same as it was)
    diagnostic: FormattingDiagnostic := {}
    stx : List Syntax := [] -- note that syntax is in reverse order for performance reasons
  -- deriving Repr

  def FormatState.toReport (s : FormatState) : FormatReport :=
    { missingFormatters := s.diagnostic.missingFormatters.fold (fun acc name _ => acc.insert name (acc.getD name 0 + 1)) Std.HashMap.empty,
      totalCommands := 1,
      formattedCommands := 0
    }

  abbrev FormatM a := (StateM FormatState) a
  abbrev RuleM a := ExceptT FormatError FormatM a
  abbrev RuleRec := (Syntax → FormatM PPL)
  -- abbrev Rule := RuleRec → Array Syntax → (RuleM PPL)

  -- abbrev RuleCtx := ReaderT RuleRec RuleM PPL
  abbrev Rule := Syntax → RuleM PPL

  abbrev Formatter := (Name → Option Rule)
  abbrev Formatters := List (Formatter)

  -- structure FormatContext where
  --   -- prefer the first environment
  --   -- envs: List Environment
  --   formatters := List ((Name → Option Rule))
  --   -- envs : List Environment
  --   -- options: Options
  --   -- myEnv: Environment -- The env from the file
  --   -- otherEnv: Environment -- The env from the formatted file

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

initialize coreFormatters : IO.Ref (Std.HashMap Name (Rule)) ← IO.mkRef {}

end PrettyFormat
