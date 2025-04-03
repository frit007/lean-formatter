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

-- structure PPLSpacing where
--   space : Bool := true
--   -- will be flattened to a space
--   newline : Bool := true
--   -- will not be flattened to a space, and instead fails (if there are no alternative spacing options)
--   hardNewline : Bool := true
--   none : Bool := true
--   /--
--   used to counter the following scenario:
--   flatten (text "-- comment" <> optionalSpace hardNewline) <> optionalSpace hardNewline
--   -/
--   flattened := false
--   deriving Repr, BEq

inductive PPL where
  | nl : PPL
  | text : String → PPL
  -- -- This will be turned into text, but is used to detect
  -- -- whether we accidentally flatten code to be part of a comment
  -- | commentText : String → PPL
  -- If we get into a scenario where we cannot parse the
  | error : String → PPL
  -- optional space, that will be reduced to a single space or a newline
  /--
  Spacing is intended to fix a few issues.
  We want to place a newline or a space between two elements.
  But we also want to tell child rules which choice we made.
  The motivation for this is do-notation, because it

  -/
  -- | spacing : PPLSpacing → PPL
  | choice : PPL → PPL → PPL
  | unallignedConcat : PPL → PPL → PPL
  -- Part of the hierarchy because we delay the evaluation
  | flatten : PPL → PPL
  | align : PPL → PPL
  | nest : Nat → PPL → PPL
  -- rule is only intended to be used internally by the library
  -- rule must satisfy the invariant: rule cannot contain PPL.stx. Because the formatting rules will never be applied
  -- rule does not affect the way the code is formatted
  -- rule helps us debug the output by keeping track of which formatting rule produced the output
  | rule : String → PPL → PPL
  /--
  To make the syntax generation cleaner we delay
  -/
  | stx : (Syntax → PPL)
  -- Used for potentially handling multiline strings
  | reset : (PPL → PPL)
  /--
  bubbleComment will be placed before the current line with the same indentation
  -/
  | bubbleComment (comment : String)
  /--
  These comments have been placed at the end of the line
  This is enforced by failing any document, where the next character is not a newLine

  Technically we know that these comments are legal syntax, because we were able to parse the document
  But to follow the style of the library author we will only allow the comment if a newline is possible
  The main reason for this is to respect the decision made by flatten. The intended use is to combine both comments (bubbleUpComment c <^> endOfLineComment c)
  -/
  | endOfLineComment (comment : String)
  | provide (options : List String)
  | expect (options : List String)
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
  isEmpty' (toPPL ppl)
where
  isEmpty' : (ppl : PPL) → Bool
  | .error s => false
  | .text s => s.length == 0
  | .nl => false
  | .choice left right => isEmpty' left && isEmpty' right
  | .flatten inner => isEmpty' inner
  | .align inner => isEmpty' inner
  | .nest n inner => isEmpty' inner
  | .unallignedConcat left right => isEmpty' left && isEmpty' right
  | .stx s => isSyntaxEmpty s
  | .bubbleComment s => s.length == 0
  | .endOfLineComment s => false
  | .reset inner => isEmpty' inner
  | .rule _ inner => isEmpty' inner
  | .provide _ => false
  | .expect _ => false

infixl:34 " <^> " => fun l r => PPL.choice (toPPL l) (toPPL r)
-- infixl:40 " <> " => fun l r =>
--   match (isEmpty l, isEmpty r) with
--   | (true, _) => (toPPL r)
--   | (_, true) => (toPPL l)
--   | _ => PPL.unallignedConcat (toPPL l) (toPPL r)

def concat [ToPPL a] [ToPPL b] (l : a) (r : b) : PPL :=
  if isEmpty l then toPPL r
  else if isEmpty r then toPPL l
  else PPL.unallignedConcat (toPPL l) (toPPL r)

def space := Pfmt.space
def spaceNl := Pfmt.spaceNl
def spaceHardNl := Pfmt.spaceHardNl
def spaceNewline := [spaceNl, spaceHardNl]
def nospace := Pfmt.nospace
def immediateValue := "immediateValue"
def anySpace := [space, spaceNl, spaceHardNl]

infixl:40 " <> " => fun l r => concat l r

infixl:39 " <$$> " => fun l r => (toPPL l) <> PPL.provide [spaceNl, spaceHardNl] <> (toPPL r)
infixl:38 " <$$$> " => fun l r => (toPPL l) <> PPL.provide [spaceHardNl] <> (toPPL r)
infixl:37 " <**> " => fun l r => (toPPL l) <> PPL.provide anySpace <> (toPPL r)
infixl:36 " <_> " => fun l r => (toPPL l) <> PPL.provide [space] <> (toPPL r)


infixl:40 " <+> " => fun l r => (toPPL l) <> PPL.align (toPPL r)
infixl:45 " !> " => fun l r => (PPL.provide l) <> (toPPL r)
infixl:45 " <! " => fun l r => (PPL.expect l) <> (toPPL r)


-- def anySeparator := [space, spaceNl, spaceHardNl, nospace]

-- abstractions
-- a choice between flattening or not
-- macro group -- M(𝛼1) = 𝛼1 <|> flatten 𝛼1
-- vertical concatenation
-- macro <$> -- M(𝛼1, 𝛼2) = 𝛼1 <> nl <> 𝛼2.
-- alligned concatenation
-- macro <+> -- M(𝛼1, 𝛼2) = 𝛼1 <> align 𝛼2.


def text (s: String): PPL:=
  PPL.text s

def nl : PPL:=
  PPL.nl

def flattenPPL [ToPPL a] (s: a): PPL:=
  PPL.flatten (toPPL s)

def align (s: PPL): PPL:=
  PPL.align s

def group (s: PPL): PPL:=
  s <^> flattenPPL s

def empty := -- used when starting a new node
  text ""




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



partial def prettyPrint  (ppl : PPL) : String :=
  prettyPrint' 0 ppl
where
  prettyPrint' (indent:Nat): (ppl : PPL) → String
  -- | spacing spacing =>
  --   match spacing with
  --   | PPLSpacing.space => " "
  --   | PPLSpacing.newline => "\n"
  --   | PPLSpacing.either => "\n"
  | .error s => "\n" ++ s ++ " "
  | .text s => s
  | .nl => "\n" ++ repeatString " " indent
  | .choice left right => prettyPrint' indent left ++ " | " ++ prettyPrint' indent right
  | .flatten inner => prettyPrint' indent inner
  | .align inner => prettyPrint' indent inner
  | .nest n inner => prettyPrint' (indent + n) inner
  | .unallignedConcat left right => prettyPrint' indent left ++ prettyPrint' indent right
  | .stx stx => s!"stx {stx}"
  | .bubbleComment s => s!"bubbleComment {s}"
  | .endOfLineComment s => s!"endOfLineComment {s}"
  | .reset s => s!"reset {prettyPrint' 0 s}"
  | .rule name s => s!"rule {name} {prettyPrint' indent s}"
  | .provide s => s!"provide {s}"
  | .expect s => s!"expect {s}"


partial def output (ppl:PPL) : String :=
  output' 0 ppl
where
  output' (indent : Nat) : PPL → String
  -- | .optionalSpace spacing =>
  --   match spacing with
  --   | PPLSpacing.space => s!"text \" \""
  --   | PPLSpacing.newline => "nl"
  --   | PPLSpacing.either => s!"text \" \""
  | .error s => s!"error {s}"
  | .text s => s!"text \"{s}\""
  | .nl => "nl"
  | .choice left right => s!"({output' indent left})<|>({output' indent right}){newline indent}"
  | .flatten inner => s!"flatten ({output' indent inner})"
  | .align inner => s!"align ({output' indent inner})"
  | .nest n inner => s!"nest {n} ({output' indent inner})"
  | .unallignedConcat left right => s!"({output' indent left}) <> ({output' indent right})"
  | .stx stx => "stx\n"
  | .bubbleComment s => s!"bubbleComment \"{s}\""
  | .endOfLineComment s => s!"endOfLine \"{s}\""
  | .rule name s => s!"rule {name} {newline indent} ({output' (indent + 2) s}) {newline indent}"
  | .reset s => s!"reset ({output' indent s})"
  | .provide s => s!"provide {s}"
  | .expect s => s!"expect {s}"
  newline indent := "\n" ++ repeatString " " indent

def escapeQuotes (s : String) : String :=
  s.replace "\"" "\\\""

open Pfmt

partial def toDoc : PPL → Doc
  -- | spacing spacing =>
  --   match spacing with
  --   | PPLSpacing.space => Doc.text s!" "
  --   | PPLSpacing.newline => Doc.newline ""
  --   | PPLSpacing.either => Doc.text s!" " <|||> Doc.newline ""
  | .error s => Doc.fail s
  | .text s => Doc.text s
  | .nl => Doc.newline " "
  | .choice l r => (toDoc l) <|||> (toDoc r)
  | .flatten inner => Doc.flatten (toDoc inner)
  | .align inner => Doc.align (toDoc inner)
  | .nest n inner => Doc.nest n (toDoc inner)
  | .unallignedConcat l r => Doc.concat (toDoc l) (toDoc r)
  | .stx _ => Doc.text "unformated syntax"
  | .bubbleComment s => Doc.bubbleComment (s)
  | .endOfLineComment s => Doc.endOfLineComment s
  | .reset s => Doc.reset (toDoc s)
  /- rule does not affect the way the code is formatted
  -/
  | .rule name s => Doc.rule name (toDoc s)
  | .provide s => Doc.provide (Std.HashSet.ofList s)
  | .expect s => Doc.expect (Std.HashSet.ofList s)


structure CommentFix where
  flatten : Bool
  startedComment : Bool
  vars: Std.HashMap String PPL


instance : Inhabited PPL where
  default := PPL.error "default error"

-- instance : Inhabited CommentFix where
--   default := { flatten := false, startedComment := false, vars := {} }

-- instance : Inhabited (PPL × CommentFix) where
--   default := (default, default)

-- -- propagate errors up the tree
-- -- detect whether comments accidentally are flattened, and if they are eliminate choices where that happens
-- -- this will probably be moved to creation of the object
-- partial def eliminateErrors (state: CommentFix) : PPL → (PPL × CommentFix)
--   | .var v =>
--     if state.flatten then
--       match state.vars[v]? with
--     | some (value) =>
--       match eliminateErrors state value with
--       | (PPL.error e, s') => (PPL.error e, s')
--       | _ => (PPL.var v, state)
--     | none => (PPL.error s!"Using undefined variable {v}", state)
--    else (PPL.var v, state)
--   | .commentText s => (PPL.commentText s, {state with startedComment := true })
--   | .optionalSpace spacing =>
--     if state.flatten && spacing == PPLSpacing.newline then
--       (PPL.optionalSpace spacing, state)
--     else
--       (PPL.optionalSpace spacing, {state with startedComment := state.startedComment && spacing != PPLSpacing.newline})
--   | .error s => (PPL.error s, state)
--   | .text s =>
--     if state.flatten && state.startedComment && s.trim.length > 0 then
--       (PPL.error "cannot write text after an inline comment", state)
--     else
--       (PPL.text s, state)
--   | .nl =>
--     if state.flatten then
--       (text " ", state)
--     else
--       (PPL.nl, {state with startedComment := false})
--   | .choice left right => --s!"({output left})<|>({output right})"
--     match (eliminateErrors state left, eliminateErrors state right) with
--     | ((PPL.error l, _), (PPL.error r, _)) => (PPL.error s!"{l}<|>{r}", state)
--     | ((PPL.error l, _), (v, s)) => (v,s)
--     | ((v,s), (PPL.error r, _)) => (v,s)
--     | ((vl,sl), (vr,sr)) => (vl<^>vr, {sl with startedComment:= sl.startedComment && sr.startedComment})
--   | .flatten inner =>
--     let (inner', state') := (eliminateErrors {state with flatten:=true} inner)
--     match inner' with
--     | .error x => (PPL.error x, {state with startedComment:= state'.startedComment})
--     | _ => (PPL.flatten inner', {state with startedComment:= state'.startedComment})
--   | .align inner =>
--     let (inner', state') := (eliminateErrors state inner)
--     match inner' with
--     | .error x => (PPL.error x, {state with startedComment:= state'.startedComment})
--     | _ => (PPL.align inner', {state with startedComment:= state'.startedComment})
--   | .nest n inner =>
--     let (inner', state') := (eliminateErrors state inner)
--     match inner' with
--     | .error x => (PPL.error x, state)
--     | _ =>
--       if state.flatten then
--         (PPL.nest n inner', state)
--       else
--         (PPL.nest n inner', {state with startedComment:= state'.startedComment})
--   | .unallignedConcat left right => (left, state) -- TODO
--   | .letExpr var expr body => (body, state) -- TODO
--   | .group _ inner => (inner, state)
--   | .stx stx => (PPL.stx stx, state)

  -- before this step we must flatten and
  -- the problem with bubbling comments is that if we have bunch of unknown newlines in a row (" " <^> PPL.nl), then we must make a choice for the 2 scenarios.
  -- This means we need 2^n space to store the tree, where n is the number of optional newlines(" " <^> PPL.nl)
  -- can we use variables to improve this?
  -- I think it would at least cut down on the space requirement
  -- let us take the (" " <^> PPL.nl) <> longStatement ==> let v1 = longStatement in ((" " <> v1) <^> (PPL.nl <> v1))
  -- this is preferable to
  -- let v1 = longStatement in ((" " <> v1) <^> (PPL.nl <> v1))

  -- The problem is: if I want to modify an existing variable (this is also the flatten problem)

  inductive newlineState where
    | none
    | space
    | newline


  inductive FormatError where
  | NotHandled (name : Name) (stx : List Syntax)
  | NoFormatter (stx : Syntax)
  | Unknown
  deriving Inhabited, Repr

  instance : ToString FormatError where
    toString b :=
      match b with
      | .NotHandled name stx =>
        let parentChain := stx.map (fun s => s.getKind) |>.filter (fun s => s != `missing && s != `ident) |>.map toString |>.reverse |> String.intercalate " → "

        s!"Not handled {name} {stx.length} chain: {parentChain}"
      | .NoFormatter stx => s!"NoFormatter {stx.getKind}"
      | .Unknown => "unknown"

  instance : Repr FormatError where
    reprPrec b n :=
      match b with
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
    -- startOfLine: Bool := true -- whether we are at the start of a line
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
  abbrev Rule := Array Syntax → RuleM PPL

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

register_option pf.debugSyntax : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, before being formatted"
}
register_option pf.debugSyntaxAfter : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the syntax in a comment above each top level command, after being formatted"
}
register_option pf.debugErrors : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the errors"
}
register_option pf.debugMissingFormatters : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output a list of missing formatters above the function"
}
register_option pf.debugPPL : Bool := {
  defValue := false
  group    := "pf"
  descr    := "(pretty format) Output the generated PPL above the function"
}
register_option pf.debugPPLGroups : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) Add grouping around every PPL formatter"
}
register_option pf.debugDoc : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) debug the generated Doc"
}
register_option pf.warnCSTmismatch : Bool := {
    defValue := true
    group    := "pf"
    descr    := "(pretty format) When the formatted syntax does not match the original syntax, output a warning"
}
register_option pf.debugTime : Bool := {
    defValue := false
    group    := "pf"
    descr    := "(pretty format) Debug how time is used"
}

def getPFLineLength (o : Options) : Nat := o.get pf.lineLength.name pf.lineLength.defValue

def getDebugSyntax (o : Options) : Bool := (o.get pf.debugSyntax.name pf.debugSyntax.defValue)
def getDebugSyntaxAfter (o : Options) : Bool := (o.get pf.debugSyntaxAfter.name pf.debugSyntaxAfter.defValue)
def getDebugErrors (o : Options) : Bool := (o.get pf.debugErrors.name pf.debugErrors.defValue)
def getDebugMissingFormatters (o : Options) : Bool := (o.get pf.debugMissingFormatters.name pf.debugMissingFormatters.defValue)
def getDebugPPL (o : Options) : Bool := (o.get pf.debugPPL.name pf.debugPPL.defValue)
def getDebugDoc (o : Options) : Bool := (o.get pf.debugDoc.name pf.debugDoc.defValue)
def getWarnCSTmismatch (o : Options) : Bool := (o.get pf.warnCSTmismatch.name pf.warnCSTmismatch.defValue)
def getDebugTime (o : Options) : Bool := (o.get pf.debugTime.name pf.debugTime.defValue)

initialize coreFormatters : IO.Ref (Std.HashMap Name (Rule)) ← IO.mkRef {}

end PrettyFormat
