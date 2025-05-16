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


partial def findPatternStartAux (s pattern : String) : Option String :=
  if s.length < pattern.length then none
  else if s.take pattern.length == pattern then some (s.drop pattern.length)
  else findPatternStartAux (s.drop 1) pattern

partial def findPatternStart (s pattern : String) : Option String :=
  findPatternStartAux s pattern



/-
Funny sideNote: if we change provide bridgeNl to always be attached to a document it would be nicer to work with from the formatters point of view

but the alternative is easier to write Syntax transformers for
-/
/--
We choose to preprocess flatten to simplify formatting later

Flatten converts all newlines to spaces

The interaction between flatten and bridges is less obvious but the rule is:
"flatten only flattens the bridges inside the flattened section"
This was chosen to allow comments at the end of a flattened section
example:
"a" <**> flatten ("b" <**> "c" <> Provide bridgeNl) <**> "d"
Is flattened to
"a" <**> ("b" <_> "c" <> Provide bridgeNl) <**> "d"

-/
partial def flattenPreprocessor (flattenLeft flattenRight: Bool) (d :Doc) : FlattenStateM Doc := do
  let meta := d.meta
  if meta.shouldBeCached then
    let state ← get
    let existing := match state.cached.get? meta.id with
    | some e => e.find? (fun (c:FlattenCache) => c.flattenLeft == flattenLeft && c.flattenRight == flattenRight)
    | _ => none

    match existing with
    | some e => return e.d
    | _ => flattenPreprocessor' flattenLeft flattenRight d
  else
    flattenPreprocessor' flattenLeft flattenRight d
  -- TODO: update meta
where
  flattenPreprocessor' (flattenLeft flattenRight: Bool) : Doc → FlattenStateM (Doc × Bridge)
    | .fail s m => return (.fail s m, m.leftBridge)
    | .text s m => return (.text s m, m.leftBridge)
    | .newline a m =>
      match a with
      | some s => return (.text s m, m.leftBridge)
      | _ => return (.fail "cannot flatten" m, m.leftBridge)
    | .choice left right _=> do
      let l ← flattenPreprocessor flattenLeft flattenRight left
      let r ← flattenPreprocessor flattenLeft flattenRight right
      return (.choice l r, l.meta.leftBridge)
    | .flatten inner _=> do
      let i ← flattenPreprocessor flattenLeft flattenRight inner
      return (i, i.meta.leftBridge)
    | .align inner m => do
      let i ← flattenPreprocessor flattenLeft flattenRight inner
      return (.align i m, i.meta.leftBridge)
    | .nest i inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenRight inner
      return (.nest i inner m, inner.meta.leftBridge)
    | .concat left right m =>
      -- we could ask: contains text
      -- not good enough because: uncertain if right side contains choice (and for that matter it is uncertain whether left side contains text)
      -- leads to the expansion problem again...
      -- the problem is require and provide?
      -- Can I restructure provide and require to make it simpler
      -- otherwise I must do rewrites
      -- My problem is that I do not know whether I want provide right or left
      -- I could split it into left provide and right provide
      -- require is always left
      -- I don't like that <_> <**> <$$> operators must check before applying to a side
      -- however that is possible
      -- I could keep the nodes and just move them to wrap the next non empty node (This is ruined by choice)

      isEmpty' left && isEmpty' right
    | .stx s _=> panic! "can't flatten syntax"
    | .reset inner _=> isEmpty' inner
    | .rule _ inner _=> isEmpty' inner
    | .provide _ _=> false
    | .require _ _=> false
    | .bubbleComment _ d _=> isEmpty' d
    | .cost _ d _=> isEmpty' d

-- since the result might contain Syntax we expand it now
-- At this point we also tag the syntax with Ids, bug only if they should be cached
-- At this point we want to add bridgeInformation
-- At this point we could also remove failures (we wait until now to because otherwise failure can not be cascade across syntax)
partial def expandSyntax (r : RuleRec) (ppl : Doc) : FormatM Doc := do
  if ppl.meta.hasBeenExpanded then
    return ppl
  match ppl with
  | .fail s _ => return (.fail s)
  | .text s _ => return (.text s)
  | .newline s _ => return (.newline s)
  | .choice left right _ => do
    let left ← expandSyntax r left
    let right ← expandSyntax r right
    match left, right with
    | .fail _, _ =>
      return right
    | _, .fail _ =>
      return left
    | _, _ =>
      cachePPL (.choice left right) (max left.meta.cacheWeight right.meta.cacheWeight) (left.meta.leftBridge ||| right.meta.leftBridge)
  | .flatten inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.flatten inner) (inner.meta.cacheWeight) (inner.meta.leftBridge.flatten)
  | .align inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.align inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
  | .nest n inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.nest n inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
  | .concat left right _ =>
    let left ← expandSyntax r left
    let right ← expandSyntax r right
    match left, right with
    | .fail s, _ =>
      return Doc.fail s
    | _, .fail s =>
      return Doc.fail s
    | _, _ =>
      -- Note that in case of unknown we over estimate the bridges required
      cachePPL (.concat left right) (max left.meta.cacheWeight right.meta.cacheWeight) (left.meta.leftBridge)
  | .rule name inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.rule name inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
  | .bubbleComment s inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.bubbleComment s inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
  | .stx stx _ => return ← r stx
  | .reset inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.reset inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
  | .provide s _ => cachePPL (.provide s) 0 s
  | .require s _ => cachePPL (.require s) 0 s
  | .cost c inner _ =>
    let inner ← expandSyntax r inner
    cachePPL (.cost c inner) (inner.meta.cacheWeight) (inner.meta.leftBridge)
    -- cachePPL (.cost c) 0 bridgeFlex
where

  cachePPL (doc:Doc) (childCacheWeight:Nat) (leftBridge:Bridge := bridgeFlex): FormatM Doc := do
    if childCacheWeight >= (← get).cacheDistance then
      -- return doc leftBridge (← FormatM.genId) 0 true
      return doc.setMeta {
        cacheWeight := 0,
        leftBridge := leftBridge,
        id := ← FormatM.genId
      }
    else
      return doc.setMeta {
        cacheWeight := childCacheWeight + 1,
        leftBridge := leftBridge,
        id := 0
      }


partial def findFirstMatch (fmts : List (Name → Option Rule)) (kind : SyntaxNodeKind) (r : RuleRec) (stx : Syntax) :FormatM (List FormatError ⊕ Doc):= do
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



def updateSyntaxTrail (stx : Syntax) (f:FormatM PPL) : FormatM PPL := do
  let _ ← modify (fun s => {s with stx := stx::s.stx})
  let v ← f
  let _ ← modify (fun s => {s with stx := s.stx.tail})
  return v

private structure CommentInfo where
  isBlockComment : Bool
  -- note that block comments still contain newlines
  comment : String
deriving Repr

def linePrefix : List String → List Nat
  | s :: xs =>
    (s.length - s.trimLeft.length) :: linePrefix xs
  | [] => []

def commentInfoToStrings (c : CommentInfo): List String :=
  if c.isBlockComment then
    let parts := c.comment.split (fun c => c == '\n')
    let removeFront:= parts.tail |> linePrefix |>.foldl Nat.min 1000000
    let tail := parts.tail |>.map (fun s => s.drop removeFront)


      -- |>.foldl (fun (acc) (c:String) => acc <> Doc.nl <> c) (toDoc "")

    (parts.head! :: tail)
  else
    ["-- " ++ c.comment.trim]

def commentInfoToEndOfLine (c : CommentInfo) : Doc :=
  let comments := commentInfoToStrings c
    |>.foldl (fun (acc:Doc) (c:String) =>
      if isEmpty acc then
        toDoc c
      else
        acc <> Doc.nl <> c
    ) (toDoc "")
  comments

def CommentInfoToBubbleComment (c : CommentInfo) (p:Doc) : Doc :=
  let comments := commentInfoToStrings c
    |>.foldl (fun (acc) (c:String) => Doc.cost 3 (Doc.bubbleComment c acc)) (p)
  comments

-- def CommentInfo.toDocs (c : CommentInfo) : Doc :=


partial def parseComments (comments:List CommentInfo): List Char → (List CommentInfo)
| '-'::'-'::xs =>
  let (comment, xs) := parseEndOfLineComment [] xs
  parseComments ({isBlockComment := false, comment:=String.mk comment} :: comments) xs
| '/'::'-'::xs =>
  let (comment, xs) := parseMultilineComment ['-','/'] 0 xs
  parseComments ({isBlockComment := true, comment:=String.mk comment} :: comments) xs
| _::xs => parseComments comments xs
| _ => comments
where
  parseEndOfLineComment (acc : List Char): List Char → (List Char × List Char)
    | [] => (acc.reverse, [])
    | '\n'::xs => (acc.reverse, xs)
    | x::xs => parseEndOfLineComment (x::acc) xs
  parseMultilineComment (acc : List Char): Nat → List Char → (List Char × List Char)
    | n, '/'::'-'::xs => parseMultilineComment ('-'::'/'::acc) (n + 1) xs
    | 0, '-'::'/'::xs => (('/'::'-'::acc).reverse, xs)
    | _, [] => (acc.reverse, [])
    | n, '-'::'/'::xs => parseMultilineComment ('/'::'-'::acc) (n - 1) xs
    | n, x::xs => parseMultilineComment (x::acc) (n) xs

/-- info: [{ isBlockComment := true, comment := "/-a comment-/" }] -/
#guard_msgs in
#eval parseComments [] "/-a comment-/".toList
/--
info: [{ isBlockComment := true, comment := "/-once-/" },
 { isBlockComment := false, comment := "hello" },
 { isBlockComment := false, comment := " one" }]
-/
#guard_msgs in
#eval parseComments [] "-- one\n--hello\n/-once-/".toList
/-- info: [{ isBlockComment := true, comment := "/-on\nce-/" }] -/
#guard_msgs in
#eval parseComments [] "/-on\nce-/".toList
/-- info: [{ isBlockComment := true, comment := "/-on/- nested-/ ce-/" }] -/
#guard_msgs in
#eval parseComments [] "/-on/- nested-/ ce-/".toList


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


def hasNewlineBeforeNonWhitespace (s : String) : Bool :=
  let chars := s.toList
  let rec check : List Char → Bool
    | [] => false
    | '\n' :: cs => true -- Mark that we've seen a newline
    | c :: cs => if c.isWhitespace then check cs else false
  check chars

/--
We are considering the options
newline followed by comments
inline comment: /--/
 - inline comments are allowed to
multiline comment: /--/
end of line comment: --
-/
partial def commentStringToPPL (s:String) (leading : Bool) (d : Doc): Doc :=
  if s.length == 0 then
    d
  else
    let comments := parseComments [] s.toList |>.reverse

    if hasNewlineBeforeNonWhitespace s then
      /-
      example:
        def fun (a:Nat ) :=
          -- a comment before our content
          /- or a block comment -/
          a
      -/
      let hardline := if leading then
        "" <$$$> (combineEndOfLineComments comments) <$$$> d
      else
        d <$$$> ((combineEndOfLineComments comments)) <$$$> ""
      hardline <^> comments.foldl (fun acc c => CommentInfoToBubbleComment c acc) d
    else
      let isInlineComment := comments.length == 1 && comments.all (fun c => c.isBlockComment)
      if isInlineComment then
        -- a single short comment can be placed any where
        /-
        example:

        def fun (a:Nat /-An inline comment-/) := a
        -/
        let comment := comments.foldl (fun _ c => commentInfoToEndOfLine c) (toDoc "")
        if leading then
          comment <_> d
        else
          d <_> comment
      else
        let hardline := if leading then
          (combineEndOfLineComments comments) <$$$> d <$$$> ""
        else
          d <_> (combineEndOfLineComments comments) <$$$> ""
        hardline <^> comments.foldl (fun acc c => CommentInfoToBubbleComment c acc) d
where
combineEndOfLineComments (comments : List CommentInfo) : Doc :=
  comments.foldl (fun acc c =>
    if isEmpty acc then
      commentInfoToEndOfLine c
    else
      acc <$$$> commentInfoToEndOfLine c
  ) (toDoc "")

-- if the value is unknown then we will try to keep the value the same as it was
partial def surroundWithComments (info : SourceInfo) (p:Doc): Doc :=
  match info with
  | .original (leading : Substring) _ (trailing : Substring) _ =>
    commentStringToPPL leading.toString true p |> commentStringToPPL trailing.toString false
    -- commentStringToPPL leading.toString true
    -- <> p <> commentStringToPPL trailing.toString false
  | _ => p

partial def pfCombine (r: RuleRec) (stxArr : Array Syntax) : FormatM Doc := do
  let mut res := toDoc ""
  for p in stxArr do
    res := res <> (← r p)
  return res

partial def pf (formatters : Formatters) (stx: Syntax): FormatM Doc := updateSyntaxTrail stx do
  -- can we assume that the other environment has all of the attributes? for now we do not
  let formattingRule : RuleRec := fun (stx) => pf formatters stx

  let curr ← get
  let updated := {curr with formattingFunction := fun stx nextId diagnostics path =>
    let (doc,state) := (pf formatters stx).run {curr with options := curr.options, nextId := nextId, diagnostic := diagnostics, stx := path} |>.run
    (doc, state.nextId, state.diagnostic)
  }
  set updated

  match stx with
  | .missing => pure (toDoc "")
  | .node (_ : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    match kind with
    | `null => -- null nodes are combined without whitespaces
      pfCombine formattingRule args
    | _ =>
      let formatted ← findFirstMatch formatters kind formattingRule stx

      match formatted with
      | Sum.inr ppl =>
        -- if stx.getKind == `Lean.Parser.Tactic.tacticSeq then
        --   return text "capture good"
        return Doc.rule (toString kind) ppl
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

        return Doc.rule (toString kind) (← pfCombine formattingRule args)
  | .atom (info : SourceInfo) (val : String) =>
    return (surroundWithComments info (toDoc val))


  | .ident  (info : SourceInfo) (rawVal : Substring) _ _ =>
    return (surroundWithComments info (toDoc rawVal.toString))


def combine [ToDoc a] (sep: Doc → Doc → Doc) (stxArr : Array a) : Doc := Id.run do
  let mut combined : Doc := toDoc ""
  for p in stxArr do
    let p' ← toDoc p
    if isEmpty p' then
      combined := combined -- no change
    else if isEmpty combined then
      combined := p' --
    else
      combined := sep combined p'
  return combined


def sep [ToDoc a] (stxs : Array a) : Doc :=
  (combine (.<_>.) stxs) <^> (combine (.<$$>.) stxs)

-- continue combining children if they are null arrays
partial def nestedCombine (sep: Doc → Doc → Doc) (stxArr : Array Syntax) : Doc := Id.run do
  let mut combined := toDoc ""
  for p in stxArr do
    let p' ← toDoc p
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

def combine' [ToDoc a] (sep : Doc → Doc → Doc) (stx : Array a) : RuleM Doc :=
  return combine sep stx



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

private def whitespaceToPPL (str:String):Doc:=
  let parts := str.split (fun c => c == '\n') |>.map (fun c => toDoc c)
  match parts with
  | x::xs => xs.foldl (fun acc x => acc <> x <> Doc.newline " ") x
  | _ => toDoc ""

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
partial def topLevelUnformatedSyntaxToPPL (stx:Syntax): Doc := Id.run do
  match stx with
  | .missing => return toDoc ""
  | .node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    let combined ← args.foldlM (fun acc c => do return acc <> (← topLevelUnformatedSyntaxToPPL c) ) (toDoc "")
    return combined
    -- info.
  | .atom   (info : SourceInfo) (val : String) => return (getLeading info |> whitespaceToPPL) <> toDoc val <> (getTrailing info |> whitespaceToPPL)
  | .ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List Syntax.Preresolved) =>
    return (getLeading info |> whitespaceToPPL) <> toDoc rawVal.toString <> (getTrailing info |> whitespaceToPPL)



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

def stringToPPL (s:String) : Doc:=
  s.split (fun c => c == '\n') |>.foldl (fun acc p => acc <> p <> Doc.newline " ") (toDoc "")

structure FormatResult where
  stx : Syntax
  ppl : Doc
  opts : Options
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
  def FormatResult.reportAsComment (res : FormatResult): String := Id.run do
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
        errString := errString ++ s!"{kind}:({stx.getArgs.size}) {stx}\n"

    if (PrettyFormat.getDebugErrors opts) && state.diagnostic.failures.length > 0 then
      errString := errString ++ "\n---- Formatter errors ----\n"
      for (kind,stx) in state.diagnostic.failures do
        errString := errString ++ s!"{kind}:({stx.length}) \n"

    if (PrettyFormat.getDebugPPL opts) then
      errString := errString ++ "\n---- Generated PPL ----\n" ++ (ppl.toString)

    if (PrettyFormat.getDebugTime opts) then
      errString := errString ++ s!"\n---- timingPPL ----\ntimePF{nanosecondsToSeconds res.timePF}s\ntimeDoc{nanosecondsToSeconds res.timeDoc}s\ntimeReparse{nanosecondsToSeconds res.timeReparse}s"

    if errString.length > 0 then
      return "/-FORMAT DEBUG: \n" ++ errString ++"\n-/\n"
    else
      return ""

  def pfTopLevel (stx : Syntax) (formatters : List (Name → Option Rule)) (options : Options) : (Doc × FormatState) :=
    let introduceContext := pf formatters stx
    let introduceState := introduceContext.run {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}, formattingFunction := (fun _ _ _ _ => (Doc.fail "Formatting function must be replaced", 0, {}))}
    introduceState.run



partial def someComputation (sum:Nat) (n : Nat) : IO Nat :=
  if n == 0 then
    return sum
  else
    someComputation (sum * 3) (n-1)


-- Also fallback to standard syntax if formatting fails
partial def pfTopLevelWithDebug (stx : Syntax) (env : Environment) (formatters : List (Name → Option Rule)) (opts : Options) (fileName:String): IO FormatResult := do
  let ((ppl, state), timePF) ← measureTime (fun _ => do
    return pfTopLevel stx formatters opts)

  let (formattedPPL, timeDoc) ← measureTime (fun _ => do
    if getDebugLog opts then
      ppl.prettyPrintLog DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts)
    else
      -- return ppl.prettyPrint DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts)
      ppl.prettyPrint DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts)
  )

  let (generatedSyntax, timeReparse) ← measureTime ( fun _ => do
    try
      return ← reparseSyntax formattedPPL fileName env opts
    catch e =>
      return Except.error e.toString
  )

  let mut cstDifferenceError := match generatedSyntax with
    | Except.error _ => compareCst stx Syntax.missing
    | Except.ok generatedStx => compareCst stx generatedStx

  if stx.getKind == `Lean.Parser.Module.header then
    cstDifferenceError := none

  return {stx, ppl, opts, formattedPPL, generatedSyntax, state, cstDifferenceError, timePF, timeReparse, timeDoc}
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

def formatThen [ToDoc a] [ToDoc b] (sep : a) (ppl : b) : Doc :=
  let p := toDoc ppl
  if isEmpty p then
    toDoc ""
  else
    p <> sep

def formatBefore [ToDoc a] [ToDoc b] (sep : a) (ppl : b) : Doc :=
  let p := toDoc ppl
  if isEmpty p then
    toDoc ""
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

  Lean.enableInitializersExecution

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
