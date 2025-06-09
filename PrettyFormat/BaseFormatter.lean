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

/--
Assign an id to every syntax element, reuse the position to store the id
-/
partial def uniqueSyntaxIds (nextId : Nat) (stx:Syntax): (Nat × Syntax) :=
  -- dbg_trace s!"working on ids {nextId}"
  match stx with
  | .missing => (nextId, stx)
  | .node (si : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) =>
    let (nextId, newSi) := setSourceInfoId nextId si
    let (nextId, newArgs) := args.foldl (fun (nextId, arr) (stx) =>
      let (nextId, stx) := uniqueSyntaxIds nextId stx
      (nextId, arr.push stx)
    ) (nextId, #[])
    -- dbg_trace s!"updated node {getId newSi}"

    (nextId, Syntax.node newSi kind newArgs)
  | .atom (si : SourceInfo) (val : String) =>
    let (nextId, si) := setSourceInfoId nextId si
    (nextId, .atom si val)
  | .ident  (si : SourceInfo) (rawVal : Substring) name preresolved =>
    let (nextId, si) := setSourceInfoId nextId si
    (nextId, .ident si rawVal name preresolved)
where
  setSourceInfoId (nextId : Nat) (si : SourceInfo): (Nat × SourceInfo) :=
  match si with
  | .original (leading : Substring) (_ : String.Pos) (trailing : Substring) (endPos : String.Pos) =>
    (nextId + 1, SourceInfo.original leading {byteIdx := nextId} trailing endPos)
  | .synthetic (_ : String.Pos) (endPos : String.Pos) (canonical : Bool) =>
    (nextId + 1, SourceInfo.synthetic {byteIdx := nextId} endPos canonical)
  | _ =>
    (nextId + 1, SourceInfo.synthetic {byteIdx := nextId} {byteIdx := nextId} false)

  getId (si : SourceInfo): (Option Nat) :=
  match si with
  | .original _ (p : String.Pos) _ _ =>
    return p.byteIdx
  | .synthetic (p : String.Pos) _ _ =>
    return p.byteIdx
  | _ => none


partial def printAllIds (stx:Syntax): Nat :=
  -- dbg_trace s!"working on ids {nextId}"
  match stx with
  | .missing =>
    dbg_trace "missing"
    1
  | .node (si : SourceInfo) (_ : SyntaxNodeKind) (args : Array Syntax) =>
    dbg_trace s!"node id {getId si}"
    args.foldl (fun _ stx => printAllIds stx +1) 0
  | .atom (si : SourceInfo) (_ : String) =>
    dbg_trace s!"atom id {getId si}"
    1
  | .ident  (si : SourceInfo) (_ : Substring) _ _ =>
    dbg_trace s!"ident id {getId si}"
    1
where
  getId (si : SourceInfo): (Option Nat) :=
  match si with
  | .original _ (p : String.Pos) _ _ =>
    return p.byteIdx
  | .synthetic (p : String.Pos) _ _ =>
    return p.byteIdx
  | _ => none
-- since the result might contain Syntax we expand it now
-- At this point we also tag the syntax with Ids, bug only if they should be cached
-- At this point we want to add bridgeInformation
-- At this point we could also remove failures
partial def expandSyntax (r : RuleRec) (doc : Doc) : FormatM Doc := do
  -- -- dbg_trace s!"expanding: {repr ppl}"
  if doc.meta.hasBeenExpanded then
    return doc

  match doc with
  | .text s m =>
    cachePPL (.text s m) 0
  | .newline s m =>
    if s.isSome then
      -- dbg_trace s!"newline
      cachePPL (.newline s {m with
        nlCount := 1
      }) 0
    else
      cachePPL (.newline s {m with
        nlCount := 1
      }) 0
  | .choice originalLeft originalRight m => do
    let left ← expandSyntax r originalLeft
    let right ← expandSyntax r originalRight
    cachePPL (.choice left right {m with
      nlCount := max left.meta.nlCount right.meta.nlCount
    }) (max left.meta.cacheWeight right.meta.cacheWeight)
  | .flatten inner m =>
    let inner ← expandSyntax r inner
    -- if inner.isDead then
      -- dbg_trace s!"should not be dead {inner.toString} repr inner: {repr inner}"
    -- TOD: fix paths
    cachePPL (.flatten inner {m with
      nlCount := 0
    }) (inner.meta.cacheWeight)
  | .align inner m =>
    let inner ← expandSyntax r inner
    -- if inner.isDead then
      -- dbg_trace s!"should not be dead {inner.toString} repr inner: {repr inner}"
    cachePPL (.align inner {m with
      nlCount := inner.meta.nlCount
      }) (inner.meta.cacheWeight)
  | .nest n inner m =>
    let inner ← expandSyntax r inner
    -- if inner.isDead then
      -- dbg_trace s!"should not be dead {inner.toString} repr inner: {repr inner}"
    cachePPL (.nest n inner {m with
      nlCount := inner.meta.nlCount,
    }) (inner.meta.cacheWeight)
  | .concat left right m =>
    let left ← expandSyntax r left
    let right ← expandSyntax r right

    -- dbg_trace s!"bridges: {(left.meta.collapses, right.meta.collapses)} , left: {left.toString} right: {right.toString}"
    cachePPL (.concat left right { m with
      nlCount := left.meta.nlCount + right.meta.nlCount,
      }) (max left.meta.cacheWeight right.meta.cacheWeight)

  | .rule name inner m =>
    let inner ← expandSyntax r inner
    -- if inner.isDead then
      -- dbg_trace s!"should not be dead {inner.toString} repr inner: {repr inner}"
    cachePPL (.rule name inner {m with
      nlCount := inner.meta.nlCount,
    }) (inner.meta.cacheWeight)
  | .bubbleComment s m =>
    cachePPL (.bubbleComment s {m with
      nlCount := 1
      }) 0
  | .stx stx _ =>
    match getSyntaxId stx with
    | .some syntaxId =>
      let s ← get
      match s.stxCache.get? syntaxId with
      | some cachedDoc =>
        return cachedDoc
      | _ =>
        let value ← (expandSyntax r (← r stx))
        modify (fun s => {s with stxCache := s.stxCache.insert syntaxId value})
        return value
    | _ =>
      expandSyntax r (← r stx)
  | .reset inner m =>
    let inner ← expandSyntax r inner
    -- if inner.isDead then
      -- dbg_trace s!"should not be dead {inner.toString} repr inner: {repr inner}"
    cachePPL (.reset inner { m with
      nlCount := inner.meta.nlCount,
    }) (inner.meta.cacheWeight)
  | .cost c m =>
    cachePPL (.cost c {m with
      nlCount := c,
    }) 0
where
  cachePPL (doc:Doc) (childCacheWeight:Nat) : FormatM Doc := do
    -- let newMeta := doc.calcMeta
    -- -- dbg_trace s!"cachePPL {repr doc} {repr newMeta}"
    -- if newMeta.shouldBeExpanded then
    --   return doc
    -- else
    if childCacheWeight >= (← get).cacheDistance then
    -- if childCacheWeight >= 1 then
      -- return doc leftBridge (← FormatM.genId) 0 true
      -- dbg_trace s!"cachePPL we generate a new id"
      let newId ← FormatM.genId
      -- dbg_trace s!"gedId: {newId}"
      return doc.setMeta {
        doc.meta with
        cacheWeight := 0,
        id := newId
      }
    else
      -- dbg_trace s!"cachePPL we skip new id"
      return doc.setMeta {
        doc.meta with
        cacheWeight := childCacheWeight + 1,
        id := 0
      }
  getSyntaxId : Syntax → Option Nat
  | .missing => none
  | .node (si : SourceInfo) _ _ =>
    getSourceId si
  | .atom (si : SourceInfo) _ =>
    getSourceId si
  | .ident  (si : SourceInfo) _ _ _ =>
    getSourceId si

  getSourceId : SourceInfo → Option Nat
    | .original _ (pos : String.Pos) _ _ =>
      some pos.byteIdx
    | .synthetic (pos : String.Pos) _ _ =>
      some pos.byteIdx
    | _ =>
      none

-- this functions assumes that there are no Syntax objects in the doc
def simpleFormattingContext (doc:FormatM Doc) (cacheDistance : Nat := 2) : (Doc × FormatState) :=
  let (doc, cache) := (finallyExpand doc).run {stxCache := {}, cacheDistance ,formattingFunction := fun _ _ _ _ =>
    (toDoc "_", 0, {})}
  (doc, cache)
where
  finallyExpand (doc:FormatM Doc) : FormatM Doc := do
    let d ← doc
    expandSyntax RuleRec.placeHolder d

def fmt (doc : Doc) : FormatM Doc :=
  expandSyntax RuleRec.placeHolder doc


partial def findFirstMatch (fmts : List (Name → Option Rule)) (kind : SyntaxNodeKind) (r : RuleRec) (stx : Syntax) :FormatM (List FormatError ⊕ Doc):= do
  -- -- dbg_trace s!"findFirstMatch {stx.getKind}"
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
    |>.foldl (fun (acc:Doc) (c:String) => costDoc 3 <> (bubbleCommentDoc c) <> acc) (p)
  comments

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



def hasNewlineBeforeNonWhitespace (s : String) : Bool :=
  let chars := s.toList
  let rec check : List Char → Bool
    | [] => false
    | '\n' :: _ => true -- Mark that we've seen a newline
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
partial def commentStringToPPL (s:String) (leading : Bool) (atom : Doc): Doc :=
  if s.length == 0 then
    atom
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
        "" <$$$> (combineEndOfLineComments comments) <$$$> atom
      else
        atom <$$$> ((combineEndOfLineComments comments)) <$$$> ""
      hardline <^> comments.foldl (fun acc c => CommentInfoToBubbleComment c acc) atom
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
          comment <_> atom
        else
          atom <_> comment
      else
        let hardline := if leading then
          (combineEndOfLineComments comments) <$$$> atom <$$$> ""
        else
          atom <_> (combineEndOfLineComments comments) <$$$> ""
        hardline <^> comments.foldl (fun acc c => CommentInfoToBubbleComment c acc) atom
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
    let (doc, state) := (pf formatters stx).run {curr with nextId := nextId, diagnostic := diagnostics, stx := path} |>.run
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
        expandSyntax formattingRule (Doc.rule (toString kind) ppl)
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

        let inner ← pfCombine formattingRule args

        expandSyntax formattingRule ((Doc.rule (toString kind) inner))
  | .atom (info : SourceInfo) (val : String) =>
    expandSyntax formattingRule (surroundWithComments info (toDoc val))


  | .ident  (info : SourceInfo) (rawVal : Substring) _ _ =>
    expandSyntax formattingRule (surroundWithComments info (toDoc rawVal.toString))


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
  | .original (leading : Substring) _ _ _ =>
    leading.toString
  | _ => ""

private def getTrailing (info:SourceInfo) : String :=
  match info with
  | .original _ _ (trailing : Substring) _ =>
    trailing.toString
  | _ => ""

-- keep the syntax exactly the same
-- TODO: remove Id.run
partial def topLevelUnformatedSyntaxToPPL (stx:Syntax): Doc := Id.run do
  match stx with
  | .missing => return toDoc ""
  | .node   _ _ (args : Array Syntax) =>
    let combined ← args.foldlM (fun acc c => do return acc <> (← topLevelUnformatedSyntaxToPPL c) ) (toDoc "")
    return combined
    -- info.
  | .atom   (info : SourceInfo) (val : String) => return (getLeading info |> whitespaceToPPL) <> toDoc val <> (getTrailing info |> whitespaceToPPL)
  | .ident  (info : SourceInfo) (rawVal : Substring) _ _ =>
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
    | (Syntax.ident  _ (lrawVal : Substring) _ _, Syntax.ident  _ (rrawVal : Substring) _ _) =>
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
  doc : Doc
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
  def nanosecondsToSeconds (ns : Nat) : Float :=
    ns.toFloat / 1_000_000_000.0
  def FormatResult.reportAsComment (res : FormatResult): String := Id.run do
    let stx := res.stx
    let opts := res.opts
    let generatedSyntax := res.generatedSyntax
    let doc := res.doc
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

    if (PrettyFormat.getDebugDoc opts) then
      errString := errString ++ "\n---- Generated PPL ----\n" ++ (doc.toString)

    if (PrettyFormat.getDebugNoSolution opts) then
      -- errString := errString ++ "\n---- Path  ----\n" ++ (ppl.printDependencies)
      errString := errString ++ "\n---- Path  ----\n" ++ (doc.toJSON)

    if (PrettyFormat.getDebugTime opts) then
      errString := errString ++ s!"\n---- timingPPL ----\ntimePF{nanosecondsToSeconds res.timePF}s\ntimeDoc{nanosecondsToSeconds res.timeDoc}s\ntimeReparse{nanosecondsToSeconds res.timeReparse}s"

    if errString.length > 0 then
      return "/-FORMAT DEBUG: \n" ++ errString ++"\n-/\n"
    else
      return ""

  def pfTopLevel (stx : Syntax) (formatters : List (Name → Option Rule)) : (Doc × FormatState) :=
    -- stx
    let (_, stx) := uniqueSyntaxIds 1 stx
    let introduceContext := pf formatters stx
    let introduceState := introduceContext.run {nextId := 0, diagnostic:= {failures := [], missingFormatters := Std.HashMap.empty}, formattingFunction := (fun _ _ _ _ => (Doc.text "Missing syntax transformer", 0, {})), stxCache := {}}
    introduceState.run




partial def someComputation (sum:Nat) (n : Nat) : IO Nat :=
  if n == 0 then
    return sum
  else
    someComputation (sum * 3) (n-1)


-- Also fallback to standard syntax if formatting fails
partial def pfTopLevelWithDebug (stx : Syntax) (env : Environment) (formatters : List (Name → Option Rule)) (opts : Options) (fileName:String): IO FormatResult := do
  let ((doc, state), timePF) ← measureTime (fun _ => do
    return pfTopLevel stx formatters)
  -- printAllIds
  let (formattedPPL, timeDoc) ← measureTime (fun _ => do
    if getDebugLog opts then
      doc.prettyPrintLog DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts) (computationWidth := PrettyFormat.getPFLineLength opts)
    else
      -- return ppl.prettyPrint DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts)
      doc.prettyPrint DefaultCost state.nextId (col := 0) (widthLimit := PrettyFormat.getPFLineLength opts) (computationWidth := PrettyFormat.getPFLineLength opts)
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

  return {stx, doc, opts, formattedPPL, generatedSyntax, state, cstDifferenceError, timePF, timeReparse, timeDoc}
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
