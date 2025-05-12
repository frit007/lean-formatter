import Std.Data.HashSet
open Std

namespace PrettyFormat

abbrev Bridge := UInt32



def bridgeNull :Bridge := 0
def bridgeFlex :Bridge := 1
def bridgeSpaceNl :Bridge := 2 -- flattens to a space
def bridgeHardNl :Bridge := 4 -- flattens to fail
-- If you allow a newline, you should also be compatible with HardNl
def bridgeNl :Bridge := bridgeSpaceNl ||| bridgeHardNl
def bridgeSpace :Bridge := 8
def bridgeNone :Bridge := 16
def bridgeImmediate :Bridge := 32
def bridgeAny := bridgeSpace ||| bridgeNl ||| bridgeHardNl

def Bridge.subsetOf (l r: Bridge) : Bool :=
  (l &&& r) == r

def Bridge.contains (l r: Bridge) : Bool :=
  if l == r then
    true
  else if l == bridgeNull then
    false
  else
    (l &&& r) == l

def Bridge.overlapsWith (l r: Bridge) : Bool :=
  l &&& r != 0

def Bridge.lessThan (lhs rhs: Bridge) :=
  lhs.subsetOf rhs

def Bridge.erase (lhs rhs: Bridge) :=
  lhs &&& (~~~ rhs)

def Bridge.intersection (lhs rhs: Bridge) : Bridge :=
  lhs &&& rhs

def Bridge.union (lhs rhs: Bridge) : Bridge :=
  lhs ||| rhs

def Bridge.add (lhs rhs: Bridge) : Bridge :=
  lhs ||| rhs

def Bridge.isEmpty (b : Bridge) : Bool :=
  b == 0

def Bridge.smallerThan (lhs rhs: Bridge) : Bool :=
  lhs < rhs

-- The idea is that bridge flex will
def Bridge.canHandle (lhs rhs: Bridge) : Bool :=
  -- if we give the right side bridge flex it
  let provided := if lhs.contains bridgeFlex then
    lhs.add bridgeAny
  else lhs

  let canHandleFlex := !rhs.contains bridgeFlex || (provided.overlapsWith bridgeAny)

  let required := rhs.erase bridgeFlex

  provided.subsetOf required && canHandleFlex

def Bridge.replaceIfExists (bridge old new : Bridge) :Bridge :=
  if bridge.contains old then
    (bridge.erase old) ||| new
  else
    bridge

def Bridge.flatten (bridge : Bridge) : Bridge :=
  bridge.replaceIfExists bridgeFlex (bridgeSpace ||| bridgeNone ||| bridgeSpaceNl)
    |>.erase bridgeHardNl

/-- info: true -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeHardNl)
/-- info: true -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeSpace)
/-- info: true -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeFlex)
/-- info: true -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeFlex)
/-- info: false -/
#guard_msgs in
#eval bridgeImmediate.canHandle (bridgeFlex)
/-- info: true -/
#guard_msgs in
#eval (bridgeImmediate|||bridgeSpace).canHandle (bridgeFlex)
/-- info: false -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeImmediate)
/-- info: false -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeImmediate|||bridgeSpace)
/-- info: false -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeAny)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeAny)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeSpace)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeNl)

#eval bridgeNull.subsetOf bridgeSpace
/--
like LE but for `Bool`, due to my lack of knowledge regarding proofs
-/
class LEB (α : Type) where
  leq : α → α → Bool


/--
This typeclass allows us to calculate the cost of a `Doc`. We use it to find
the prettier document in `Doc.choice`. A valid `Cost` instance must satisfy
the laws defined in `LawfulCost`.
-/
class Cost (χ : Type) extends LEB χ, Add χ, Repr χ, Inhabited χ where
  /--
  Compute the cost of a `String` of length `length`, rendered at `col` with a certain
  `widhLimit`.
  -/
  text : (widthLimit : Nat) → (col : Nat) → (length : Nat) → χ
  /--
  Compute the cost of a new line.
  -/
  nl : (indent : Nat) → χ


structure DefaultCost where
  widthCost : Nat
  lineCost : Nat
  deriving Inhabited, Repr

def DefaultCost.add (lhs rhs : DefaultCost) : DefaultCost :=
  { widthCost := lhs.widthCost + rhs.widthCost, lineCost := lhs.lineCost + rhs.lineCost }

instance : Add DefaultCost where
  add := DefaultCost.add

-- def DefaultCost.le (lhs rhs : DefaultCost) : Bool :=
--   if lhs.widthCost == rhs.widthCost then lhs.lineCost ≤ rhs.lineCost else lhs.widthCost < rhs.widthCost

def DefaultCost.le (lhs rhs : DefaultCost) : Bool :=
  if lhs.widthCost == rhs.widthCost then lhs.lineCost ≤ rhs.lineCost else lhs.widthCost < rhs.widthCost

instance : LEB DefaultCost where
  leq lhs rhs := DefaultCost.le lhs rhs

-- instance : DecidableRel (LE.le (α := DefaultCost)) := fun _ _ => Bool.decEq _ _

def DefaultCost.text (widthLimit : Nat) (col : Nat) (length : Nat) : DefaultCost :=
  if col + length > widthLimit then
    let a := max widthLimit col - widthLimit
    let b := col + length - max widthLimit col
    { widthCost := b * (2 * a + b), lineCost := 0 }
  else
    { widthCost := 0, lineCost := 0 }

def DefaultCost.nl (_indent : Nat) : DefaultCost :=
  { widthCost := 0, lineCost := 1 }

instance : Cost DefaultCost where
  text := DefaultCost.text
  nl := DefaultCost.nl


structure DocMeta where
  leftBridge : Bridge := bridgeFlex
  id : Nat := 0
  cacheWeight : Nat := 0
deriving Inhabited, Repr

def DocMeta.hasBeenExpanded (meta : DocMeta) : Bool :=
  meta.id != 0 || meta.cacheWeight != 0
def DocMeta.shouldBeCached (meta : DocMeta) : Bool :=
  meta.id != 0
/--
A decision tree for rendering a document. If a `Doc` does not contain a `Doc.choice`
constructor we call it "choice free". Usually we view a `Doc` in a rendering
context that consists of:
1. A width limit `W` which we attempt to respect when rendering a `Doc`.
2. A current column position `c`.
3. An indentation level `i`.
-/
inductive Doc where
/--
Render a `String` that does not contain newlines.
-/
| text (s : String) (meta : DocMeta := {})
/--
Render a newline. Also contains an alternative rendering for the newline for `Doc.flatten`.
If s is `none` then it will fail
-/
| newline (s : Option String) (meta : DocMeta := {})
/--
Concatenate two documents unaligned. If `l` is the chars that we get from `lhs`
and `r` from `rhs` they will render as:
```
llllllllll
lllllrrrrrrrr
rrrr
```
-/
| concat (lhs rhs : Doc) (meta : DocMeta := {})
/--
Render `doc` width the indentation level increased by `nesting`.
-/
| nest (nesting : Nat) (doc : Doc) (meta : DocMeta := {})
/--
Render `doc` with the indentation level set to the column position.
-/
| align (doc : Doc) (meta : DocMeta := {})
/--
Make a choice between rendering either `lhs` or `rhs` by picking the prettier variant.
If one of the sides `fail`, then other side is chosen. If both sides `fail`, then the result is also `fail`
-/
| choice (lhs rhs : Doc) (meta : DocMeta := {})

/--
Reset the indentation level to 0.
-/
| reset (doc : Doc) (meta : DocMeta := {})
/--
Fail will never be rendered.
This error will propagate until the next choice, where branches containing errors are eliminated.
-/
| fail (err : String) (meta : DocMeta := {})
/--
The special spacing options are
- `space` which is a single space
- `nl` which is a newline, which is converted to a `space` in `flatten`
- `hardNl` which is a newline, which is removed when flattened `flatten`
- `nospace` which is nothing and leaves the formatting choice up to the child, and is used when we want parenthesis.
`nospace` will be automatically applied even if the parent does not provide any spacing information
We can create variations of `nospace`,
for example this can be used to detect if we are directly after a new function declaration
do/by notation use `assignValue` to handle this scenario so they can place their keyword on the same line and then indent

provide can be chained to narrow the options to overlap between the two sets
-/
| provide (spacing : Bridge) (meta : DocMeta := {})
/--
`require` must be preceded by a `provide` and will fail if the provided spacing does not contain the expected spacing
-/
| require (spacing : Bridge) (meta : DocMeta := {})
-- TODO: Think about adding the cost constructor. It does however make type inference much harder
| rule (r : String) (doc : Doc) (meta : DocMeta := {})
| stx (s : Lean.Syntax) (meta : DocMeta := {})
| flatten (inner : Doc) (meta : DocMeta := {})
/--
Add cost equivalent to `nl` newlines
-/
| cost (nl:Nat) (inner : Doc) (meta : DocMeta := {})
/--
The comment will be placed after the last newline before this line
-/
| bubbleComment (comment : String) (inner : Doc)  (meta : DocMeta := {})
deriving Inhabited, Repr

def Doc.meta : Doc → DocMeta
  | .text _ meta => meta
  | .newline _ meta => meta
  | .concat _ _ meta => meta
  | .nest _ _ meta => meta
  | .align _ meta => meta
  | .choice _ _ meta => meta
  | .reset _ meta => meta
  | .fail _ meta => meta
  | .provide _ meta => meta
  | require _ meta => meta
  | .rule _ _ meta => meta
  | .stx _ meta => meta
  | .flatten _ docMeta => docMeta
  | .cost _ _ meta => meta
  | .bubbleComment _ _ meta => meta

def Doc.setMeta (doc : Doc) (meta : DocMeta) : Doc :=
  match doc with
  | .text s _ => .text s meta
  | .newline s _ => .newline s meta
  | .concat l r _ => .concat l r meta
  | .nest n d _ => .nest n d meta
  | .align d _ => .align d meta
  | .choice l r _ => .choice l r meta
  | .reset d _ => .reset d meta
  | .fail err _ => .fail err meta
  | .provide s _ => .provide s meta
  | require s _ => require s meta
  | .rule r d _ => .rule r d meta
  | .stx s _ => .stx s meta
  | .flatten inner _ => .flatten inner meta
  | .cost c d _ => .cost c d meta
  | .bubbleComment c d _ => .bubbleComment c d meta

/--
A `Measure` contains a `Doc` along with meta information from the rendering process.
We use it in `MeasureSet`s to find the prettiest document.
-/
structure Measure (χ : Type) where
  /--
  The last column position if we choose to use `layout`.
  -/
  last : Nat
  /--
  The cost of using `layout`.
  -/
  cost : χ
  /--
  The choice less document that we are contemplating to use.
  -/
  -- TODO: Maybe Array?
  layout : List String → List String
  -- spacingL : Option (HashSet String) := none
  spacingR : Bridge := bridgeFlex
  -- /--
  -- Force the next character to be newline. If it is not then fail
  -- -/
  -- forcedNewLine : Bool
  -- /--

  -- -/
  -- startsWithNewLine : Bool
  -- /--
  -- -/
  fail: Option (List (List String)) := none
deriving Inhabited

def groupBySpacingR [BEq χ] [Hashable χ] (measures : List (Measure χ)) : Std.HashMap (Bridge) (List (Measure χ)) :=
  measures.foldl
    (fun acc m =>
      let key := m.spacingR
      acc.insert key (m :: (acc.getD key []))
    )
    HashMap.empty

instance [Cost χ] : LEB (Measure χ) where
  leq lhs rhs :=
    (lhs.fail.isSome && rhs.fail.isNone) || (lhs.last ≤ rhs.last && LEB.leq lhs.cost rhs.cost)

def Measure.mkFail [Cost χ] (cost : χ ) (err : (List (List String))) : Measure χ := {last := 0, cost:=cost, layout := fun _ => panic! "We never want to print fail", fail := some err}

def bridgeIntersection (set1 set2 : Bridge): Bridge :=
  set1 &&& set2

/--
Lifting `Doc.concat` to `Measure`.
-/
def Measure.concat [Cost χ] (lhs rhs : Measure χ) :Measure χ :=
  match (lhs.fail, rhs.fail) with
  | (some l, none) => Measure.mkFail lhs.cost l
  | (none, some r) => Measure.mkFail rhs.cost r
  | (some l, some r) => Measure.mkFail lhs.cost (l ++ r)
  | _ => { last := rhs.last, cost := lhs.cost + rhs.cost, layout := fun ss => rhs.layout (lhs.layout ss), spacingR := rhs.spacingR, fail := none }

def Measure.addCost [Cost χ] (m : Measure χ) (c : χ) : Measure χ :=
  { m with cost := m.cost + c}

def Measure.prependLayout [Cost χ] (m : Measure χ) (layoutFn : List String → List String) : Measure χ :=
  { m with layout := fun ss => m.layout (layoutFn ss)}

structure TaintedState where
  trace : List String
  col : Nat
  indent : Nat
  widthLimit : Nat
  flatten : Bool
  leftBridge : Bridge
  expectBridge : Bridge

structure MeasureSet (χ : Type) where
  /--
  A measureSet is grouped by the right bridge, because measures with non overlapping or partially overlapping bridges are not
  -/
  rightBridge : Bridge
  /--
  A list of `Measure`s that form a Pareto front for our rendering problem.
  This list is ordered by the last line length in strict ascending order.
  -/
  set : List (Measure χ)
  -- tainted : List (TaintedTrunk χ)


inductive TaintedTrunk (χ : Type) where
| leftTainted (left: List (TaintedTrunk χ)) (doc: Doc) (state : TaintedState) (id: Nat)
| rightTainted (left : Measure χ) (right:List (TaintedTrunk χ)) (state : TaintedState) (id: Nat)
| center (doc : Doc) (state : TaintedState)
| cost (cost : Nat) (trunk : List (TaintedTrunk χ))
| bubbleComment (bubleComment : String) (trunk : List (TaintedTrunk χ))
-- | partialTainted (left right : List (MeasureSet χ))
-- try lhs, if it satisfied all wanted bridges, then stop
-- | merge (lhs rhs: TaintedTrunk χ) (state : TaintedState)

def TaintedTrunk.cacheInfo (trunk : TaintedTrunk χ) : Option (TaintedState × Nat) :=
  match trunk with
  | .leftTainted _ _ s id => some (s, id)
  | .rightTainted _ _ s id => some (s, id)
  | _ => none


abbrev MeasureGroups (χ : Type) := (List (MeasureSet χ) × List (TaintedTrunk χ))


structure Cache (χ : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  flatten: Bool --
  column: Nat --
  -- if the result is tainted, do not allow using it in a non tainted context
  -- The idea is that we can momentarily be in a tainted context (and accept any ugly solution),
  -- but when we reach the next line we should try to find the pretties solution again. However to avoid recalculations
  isTainted: Bool

  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  -- maxWidth : Nat
  -- if there are no results it is considered a failure
  -- results : List (MeasureSet χ)
  results : MeasureGroups χ

-- def Cache.toString (cache : Cache χ) : String :=
--   s!"{cache.leftBridge} {cache.indent} {cache.flatten} {cache.column} {cache.results.toString}"

structure CacheStore (χ : Type) where
  log : Option (List (String))
  giveUp : Nat -- give up if we reach zero
  lastMeasurement : Nat -- the last time we took a measurement
  size:Nat
  content : Array (List (Cache χ))

abbrev MeasureResult χ := StateT (CacheStore χ) IO



def cacheLog (message : Unit → String): (MeasureResult χ) Unit := do
  modify (fun s =>
    match s.log with
    | none => s
    | some log => { s with log := some (log ++ [message ()]) })

-- initialize cacheCount : IO.Ref (Nat × Array (List (Cache χ))) ← IO.mkRef (0, #[])
-- We can't reference a generic class from IO ref



initialize cache : IO.Ref (Nat × Array (List (Cache DefaultCost))) ← IO.mkRef (0, #[])

class ToDoc (α : Type u) where
  toDoc : α → Doc

instance : ToDoc Doc where
  toDoc ppl:= ppl

instance : ToDoc Lean.Syntax where
  -- note that syntax is placed as a placeholder and will be expanded later
  toDoc stx:= Doc.stx stx
instance : ToDoc (Lean.TSyntax a) where
  toDoc tstx:= Doc.stx tstx.raw
instance : ToDoc String where
  toDoc text:= Doc.text text

instance : ToDoc Bridge where
  toDoc b := Doc.provide b

export ToDoc (toDoc)

partial def isSyntaxEmpty (stx : Lean.Syntax) : Bool :=
  match stx with
  | .missing => false
  | .node _ _ args =>
    args.all (fun s => isSyntaxEmpty s)
  | .atom _ (val : String) =>
    val.trim.length == 0 -- TODO: there might be a comment attached to this node
  | .ident  _ (rawVal : Substring) _ _ =>
    (toString rawVal).trim.length == 0

partial def isEmpty [ToDoc α] (ppl : α) : Bool :=
  isEmpty' (toDoc ppl)
where
  isEmpty' : Doc → Bool
  | .fail _ _=> false
  | .text s _=> s.length == 0
  | .newline _ _=> false
  | .choice left right _=> isEmpty' left && isEmpty' right
  | .flatten inner _=> isEmpty' inner
  | .align inner _=> isEmpty' inner
  | .nest _ inner _=> isEmpty' inner
  | .concat left right _=> isEmpty' left && isEmpty' right
  | .stx s _=> isSyntaxEmpty s
  | .reset inner _=> isEmpty' inner
  | .rule _ inner _=> isEmpty' inner
  -- directional
  -- | .provideL _ _ => isEmpty' inner
  -- | .provideR _ _ => isEmpty' inner
  -- | .requireL _ _ => isEmpty' inner
  -- | .requireR _ _ => isEmpty' inner
  | .provide _ _=> false
  | .require _ _=> false
  /-
  Note that this means that cost and bubble comments will be discarded if they are not attached to a relevant object
  -/
  | .bubbleComment _ d _=> isEmpty' d
  | .cost _ d _=> isEmpty' d

-- partial def moveRight (d:Doc): Doc → Doc
-- -- when we reach a leaf return
-- | .fail _ _ => d
-- | .text _ _ => d
-- | .newline _ _ => d

def concat [ToDoc a] [ToDoc b] (l : a) (r : b) : Doc :=
  let l := toDoc l
  let r := toDoc r
  if isEmpty l then r
  else if isEmpty r then l
  else
    Doc.concat l r

infixl:40 " <> " => fun l r => concat l r



infixl:39 " <$$> " => fun l r => (toDoc l) <> Doc.provide (bridgeNl) <> (toDoc r)
infixl:38 " <$$$> " => fun l r => (toDoc l) <> Doc.provide bridgeHardNl <> (toDoc r)
infixl:37 " <**> " => fun l r => (toDoc l) <> Doc.provide bridgeAny <> (toDoc r)
infixl:36 " <_> " => fun l r => (toDoc l) <> Doc.provide bridgeSpace <> (toDoc r)


infixl:40 " <+> " => fun l r => (toDoc l) <> Doc.align (toDoc r)
infixl:45 " !> " => fun l r => (Doc.provide l) <> (toDoc r)
infixl:45 " <! " => fun l r => (Doc.require l) <> (toDoc r)

infixl:34 " <^> " => fun l r => Doc.choice (toDoc l) (toDoc r)



def Doc.group (doc : Doc) : Doc :=
  toDoc (doc <^> (Doc.flatten doc))

def spacing (s : Bridge) : Doc := (Doc.provide s)
def expect (s : Bridge) : Doc := (Doc.require s)

def align [ToDoc α] (s: α): Doc:=
  (Doc.align (toDoc s))

def Doc.nl : Doc := (Doc.newline (some " "))
def Doc.hardNl : Doc := (Doc.newline none)

def flattenDoc [ToDoc α] (s: α): Doc:=
  (Doc.flatten (toDoc s))
-- tainted result is sorted by the bridge
abbrev TaintedResult (χ : Type) := List (Bridge × Measure χ)

/--
Aligned concatenation, joins two sub-layouts horizontally, aligning the whole right sub-layout at the
column where it is to be placed in. Aka the `<+>` operator.
-/
def Doc.alignedConcat [ToDoc α] [ToDoc β] (lhs : α) (rhs : β) : Doc := (toDoc lhs) <> Doc.align (toDoc rhs)
-- /--
-- TODO: Better name
-- -/
def Doc.flattenedAlignedConcat [ToDoc α] [ToDoc β] (lhs : α) (rhs : β) : Doc := Doc.alignedConcat (Doc.flatten (toDoc lhs)) rhs


def Bridge.str (b : Bridge) : String := Id.run do
  let mut str := []
  let mut bridge : Bridge := b
  if bridgeNull == bridge then
    return "bridgeNull"
  if bridge.subsetOf bridgeAny then
    str := str ++ ["bridgeAny"]
    bridge := bridge.erase bridgeAny
  if bridge.subsetOf bridgeNl then
    str := str ++ ["bridgeNl"]
    bridge := bridge.erase bridgeNl
  if bridge.subsetOf bridgeHardNl then
    str := str ++ ["bridgeHardNl"]
    bridge := bridge.erase bridgeHardNl
  if bridge.subsetOf bridgeSpaceNl then
    str := str ++ ["bridgeSpaceNl"]
    bridge := bridge.erase bridgeSpaceNl
  if bridge.subsetOf bridgeSpace then
    str := str ++ ["bridgeSpace"]
    bridge := bridge.erase bridgeSpace
  if bridge.subsetOf bridgeImmediate then
    str := str ++ ["bridgeImmediate"]
    bridge := bridge.erase bridgeImmediate
  if bridge.subsetOf bridgeNone then
    str := str ++ ["bridgeNone"]
    bridge := bridge.erase bridgeNone
  if bridge.subsetOf bridgeFlex then
    str := str ++ ["bridgeFlex"]
    bridge := bridge.erase bridgeFlex
  if bridge != 0 then
    str := str ++ [toString bridge]
    bridge := bridge.erase bridgeNone
  if str.length == 1 then
    return String.join (str.intersperse "|||")
  else
    return s!"({String.join (str.intersperse "|||")})"

def Doc.toString (ppl:Doc) : String :=
  output' 0 ppl
where
  output' (indent : Nat) (d:Doc): String :=
  let inner := match d with
  | .fail s _ => s!"Doc.fail {s}"
  | .text s _ => s!"Doc.text \"{s}\""
  | .newline s _ => s!"Doc.newline {newlineString s}"
  | .choice left right _ => s!"({output' indent left})<^>({output' indent right}){newline indent}"
  | .flatten inner _ => s!"Doc.flatten ({output' indent inner})"
  | .align inner _ => s!"Doc.align ({output' indent inner})"
  | .nest n inner _ => s!"Doc.nest {n} ({output' indent inner})"
  | .concat left right _ => s!"({output' indent left}) <> ({output' indent right})"
  | .stx _ _ => "stx\n"
  | .rule name s _ => s!"Doc.rule \"{name}\" {newline indent} ({output' (indent + 2) s}) {newline indent}"
  | .reset s _ => s!"Doc.reset ({output' indent s})"
  | .provide b _ => s!"Doc.provide {b.str}"
  | .require b _ => s!"Doc.require {b.str}"
  | .cost n d _ => s!"Doc.cost {n} ({output' indent d})"
  | .bubbleComment s d _ => s!"bubbleComment \"{s}\" ({output' indent d})"
  if d.meta.id != 0 then
    s!"/-{d.meta.id}-/ {inner}"
  else
    inner
  newline indent := "\n".pushn ' ' indent
  newlineString : Option String -> String
  | none => "none"
  | some s => s!"(some \"{s}\")"

def Doc.kind : Doc → String
  | .fail _ _ => "fail"
  | .text s _ => s!"text {s}"
  | .newline s _ => s!"Doc.newline {s}"
  | .choice _ _ _ => s!"choice"
  | .flatten _ _ => s!"flatten"
  | .align _ _ => s!"align"
  | .nest _ _ _ => s!"nest"
  | .concat _ _ _ => s!"concat"
  | .stx _ _ => "stx\n"
  | .rule _ _ _ => s!"rule"
  | .reset _ _ => s!"reset"
  | .provide _ _ => s!"provide"
  | .require _ _ => s!"expect"
  | .bubbleComment s _ _ => s!"bubbleComment \"{s}\""
  | .cost _ _ _ => s!"cost"

def measureTime (f : Unit → IO α) : IO (α × Nat):= do
  let before ← IO.monoNanosNow
  let res ← f ()
  let after ← IO.monoNanosNow
  return (res, after - before)

def measureDiff (str:String): MeasureResult χ Unit := do
  return () -- TODO: remove
  -- let now ← IO.monoNanosNow
  -- let s ← get
  -- set {s with lastMeasurement := now}
  -- IO.println s!"{str}::PERF {(now - s.lastMeasurement).toFloat / 1000000000.0} ({now})"

end PrettyFormat
