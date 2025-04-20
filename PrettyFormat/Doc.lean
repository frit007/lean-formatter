import Std.Data.HashSet
open Std

namespace PrettyFormat

abbrev Bridge := UInt32

def bridgeEmpty :Bridge := 0
def bridgeFlex :Bridge := 1
def bridgeSpaceNl :Bridge := 2 -- flattens to a space
def bridgeHardNl :Bridge := 4 -- flattens to fail
-- If you allow a newline, you should also be compatible with HardNl
def bridgeNl :Bridge := bridgeSpaceNl ||| bridgeHardNl
def bridgeSpace :Bridge := 8
def bridgeImmediate :Bridge := 16
def bridgeNone :Bridge := 32
def bridgeAny := bridgeSpace ||| bridgeNl ||| bridgeHardNl

def Bridge.subset (l r: Bridge) : Bool :=
  l &&& r == r

def Bridge.contains (l r: Bridge) : Bool :=
  l &&& r == l

def Bridge.overlapsWith (l r: Bridge) : Bool :=
  l &&& r != 0

def Bridge.lessThan (lhs rhs: Bridge) :=
  lhs.subset rhs

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

instance : DecidableRel (LE.le : Bridge → Bridge → Prop) :=
  inferInstanceAs (DecidableRel (LE.le : UInt32 → UInt32 → Prop))


/--
This typeclass allows us to calculate the cost of a `Doc`. We use it to find
the prettier document in `Doc.choice`. A valid `Cost` instance must satisfy
the laws defined in `LawfulCost`.
-/
class Cost (χ : Type) extends LE χ, Add χ where
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

instance foo : LE DefaultCost where
  le lhs rhs := DefaultCost.le lhs rhs

instance : DecidableRel (LE.le (α := DefaultCost)) := fun _ _ => Bool.decEq _ _

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

def cacheLimit := 6

structure DocMeta where
  leftBridge : Bridge := bridgeFlex
  id : Nat := 0
  cacheWeight : Nat := 0
  shouldCache : Bool := false
deriving Inhabited, Repr

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
-/
| newline (s : String) (meta : DocMeta := {})
/--
Concatenate two documents unaligned. If `l` is the chars that we get from `lhs`
and `r` from `rhs` they will render as:
```
llllllllll
lllllrrrrrrrr
rrrrrr
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
The comment will be placed after the last newline before this line
-/
| bubbleComment (comment : String) (meta : DocMeta := {})
/--
These comments have been placed at the end of the line
This is enforced by failing any document, where the next character is not a newLine

Technically we know that these comments are legal syntax, because we were able to parse the document
But to follow the style of the library author we will only allow the comment if a newline is possible
The main reason for this is to respect the decision made by flatten. The intended use is to combine both comments (bubbleComment c <^> endOfLineComment c)
-/
| endOfLineComment (comment : String) (meta : DocMeta := {})
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
expect must be preceded by a `provide` and will fail if the provided spacing does not contain the expected spacing
-/
| expect (spacing : Bridge) (meta : DocMeta := {})
-- TODO: Think about adding the cost constructor. It does however make type inference much harder
| rule (r : String) (doc : Doc) (meta : DocMeta := {})
| stx (s : Lean.Syntax) (meta : DocMeta := {})
| flatten (inner : Doc) (meta : DocMeta := {})
deriving Inhabited, Repr

-- inductive PPL where
-- | mk (d : Doc) (leftBridge : Bridge := bridgeFlex) (id : Nat := 0) (cacheWeight : Nat := 0) (shouldCache : Bool := false)
-- structure PPL where
--   d : Doc PPL
--   leftBridge : Bridge := bridgeFlex
--   /--
--   If id is 0, then it will be assigned an id later
--   The Id is important to avoid formatting code twice
--   -/
--   id : Nat := 0
--   /--
--   To avoid too much memory usage we don't want to cache every element in the tree
--   therefore cache every 6th element in the tree.
--    - When the weight exceeds `cacheLimit` and reset the weight
--   -/
--   cacheWeight : Nat := 0
--   shouldCache : Bool := false

def Doc.meta : Doc → DocMeta
  | .text _ meta => meta
  | .newline _ meta => meta
  | .concat _ _ meta => meta
  | .nest _ _ meta => meta
  | .align _ meta => meta
  | .choice _ _ meta => meta
  | .reset _ meta => meta
  | .bubbleComment _ meta => meta
  | .endOfLineComment _ meta => meta
  | .fail _ meta => meta
  | .provide _ meta => meta
  | .expect _ meta => meta
  | .rule _ _ meta => meta
  | .stx _ meta => meta
  | .flatten _ docMeta => docMeta

def Doc.setMeta (doc : Doc) (meta : DocMeta) : Doc :=
  match doc with
  | .text s _ => .text s meta
  | .newline s _ => .newline s meta
  | .concat l r _ => .concat l r meta
  | .nest n d _ => .nest n d meta
  | .align d _ => .align d meta
  | .choice l r _ => .choice l r meta
  | .reset d _ => .reset d meta
  | .bubbleComment c _ => .bubbleComment c meta
  | .endOfLineComment c _ => .endOfLineComment c meta
  | .fail err _ => .fail err meta
  | .provide s _ => .provide s meta
  | .expect s _ => .expect s meta
  | .rule r d _ => .rule r d meta
  | .stx s _ => .stx s meta
  | .flatten inner _ => .flatten inner meta

-- def PPL.leftBridge : Doc → Bridge
--   | ⟨_, leftBridge, _, _, _⟩ => leftBridge
-- def PPL.id : Doc → Nat
--   | ⟨_, _, id, _, _⟩ => id
-- def PPL.cacheWeight : Doc → Nat
--   | ⟨_, _, _, cacheWeight, _⟩ => cacheWeight
-- def PPL.shouldCache : Doc → Bool
--   | ⟨_, _, _, _, shouldCache⟩ => shouldCache


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

instance [Cost χ] : LE (Measure χ) where
  le lhs rhs := lhs.last ≤ rhs.last ∧ lhs.cost ≤ rhs.cost
-- #check inferInstanceAs (Decidable ((some (HashSet.ofList ["1"])) ≤ some (HashSet.ofList ["2"])))

-- instance [Cost χ] : LE (Option (HashSet String)) where
--   le lhs rhs := lhs.last ≤ rhs.last ∧ lhs.cost ≤ rhs.cost

instance [Cost χ] [DecidableRel (LE.le (α := χ))] (lhs rhs : Measure χ) : Decidable (lhs ≤ rhs) :=
  inferInstanceAs (Decidable (lhs.last ≤ rhs.last ∧ lhs.cost ≤ rhs.cost))








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

  -- _ (none, _) => { last := rhs.last, cost := lhs.cost + rhs.cost, layout := fun ss => rhs.layout (lhs.layout ss), forcedNewLine := rhs.forcedNewLine, startsWithNewLine := lhs.startsWithNewLine, fail := false }
  -- Do I want to just call mergeList?


-- inductive MeasureSet where
-- | w : Nat → MeasureSet

-- Can I return a list of doc
inductive MeasureX where
| aa : Something → MeasureXThunk → Other → MeasureX

structure MeasureXThunk where
  run : MeasureX → Bool


structure CacheX (t : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  flatten: Bool --
  column: Nat --
  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  -- maxWidth : Nat
  -- if there are no results it is considered a failure
  results : List (t)
  taintedResults : List (Measure n)

-- inductive MeasureX (χ : Type) where
--   | set (b:Bridge) (m: List (Measure χ))
--   | tainted (b:Bridge) (t : Unit → Nat)
--   | aa : CacheX (MeasureX χ) → MeasureX χ → MeasureX χ


-- inductive MeasureX (χ : Type) where
--   | set (b:Bridge) (m: List (Measure χ))
--   | tainted (b:Bridge) (t : CacheX (MeasureX χ) → (State, CacheX (MeasureX χ)))

class MeasureS (m : Type) where
  res : m → List Nat
  getBridge : m → Bridge
  isTainted : Bool

structure CacheM (χ : Type) (p: Type) (n: Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  flatten: Bool --
  column: Nat --
  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  -- maxWidth : Nat
  -- if there are no results it is considered a failure
  results : List (MeasureS p)
  taintedResults : List (Measure n)

structure MeasureRes where
  bridge : Bridge
  res : List Nat

structure MeasureTainted (χ p n: Type) where
  cache : Array (CacheM χ p n)
  bridge : Bridge
  res : Array (CacheM χ p n) → List Nat


class MyLength (a : Type) where
  len : a → Nat



-- structure MeasureTainted where
--   bridge : Bridge
--   bridge : Bridge
--   res : List Nat

instance : MeasureS MeasureRes where
  res m := m.res
  getBridge m := m.bridge
  isTainted := false




structure TaintedState where
  trace : List String
  col : Nat
  indent : Nat
  widthLimit : Nat
  flatten : Bool
  leftBridge : Bridge
  -- /--
  -- Can I say what I expect? (I might as well return and cache it at this point, since we have reached a result)
  -- Why would I care?
  --  - the argument for is that a merge operation can look at the left side and determine whether it has found enough results
  --  - for now let us add it later
  -- -/
  -- expectSpacing : Bridge


-- instance [Cost χ] : Append ((Measure χ)) where
--   append := Measure.concat

-- -- The point of tainted is to stop early right?
-- -- However when the width limit is reached we essentially play the lottery (would lottery actually work?)
-- /--
-- A set of `Measure`s out of which we will pick an optimal `Doc` in the end.
-- -/
-- inductive MeasureSet (χ : Type) where
-- /--
-- If a branch of the rendering process would end up producing only invalid documents
-- it produces a `MeasureSet.tainted`. It consists of a thunk that we can evaluate
-- to a `Measure` if we end up finding no way to produce a valid document.

-- To avoid cycles we can't take the cache as a an argument when expanding the trunk
-- Therefore capture all possible expansions as
-- -/
-- -- tainted cannot be prioritized, because they might contain important information
-- -- We could Instead create a series of functions that will
-- | tainted (bridge: Bridge) (trunk: TaintedTrunk χ)
-- /--
-- A list of `Measure`s that form a Pareto front for our rendering problem.
-- This list is ordered by the last line length in strict ascending order.
-- -/
-- | set (bridge: Bridge) (ms : List (Measure χ))
-- -- | set (bridge : Bridge) ()
-- -- deriving Inhabited

structure MeasureSet (χ : Type) where
  bridge : Bridge
  /--
  A list of `Measure`s that form a Pareto front for our rendering problem.
  This list is ordered by the last line length in strict ascending order.
  -/
  set : List (Measure χ)
  -- tainted : List (TaintedTrunk χ)


inductive TaintedTrunk (χ : Type) where
| leftTainted (left: List (TaintedTrunk χ)) (doc: Doc) (state : TaintedState)
| rightTainted (left : Measure χ) (right:List (TaintedTrunk χ)) (state : TaintedState)
| center (doc : Doc) (state : TaintedState)
-- try lhs, if it satisfied all wanted bridges, then stop
-- | merge (lhs rhs: TaintedTrunk χ) (state : TaintedState)



abbrev MeasureGroups (χ : Type) := (List (MeasureSet χ) × List (TaintedTrunk χ))


structure Cache (χ : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  flatten: Bool --
  column: Nat --
  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  -- maxWidth : Nat
  -- if there are no results it is considered a failure
  -- results : List (MeasureSet χ)
  results : MeasureGroups χ

structure CacheStore (χ : Type) where
  size:Nat
  content : Array (List (Cache χ))

abbrev MeasureResult χ := StateT (CacheStore χ) Id

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
  | .bubbleComment s _=> s.length == 0
  | .endOfLineComment _ _=> false
  | .reset inner _=> isEmpty' inner
  | .rule _ inner _=> isEmpty' inner
  | .provide _ _=> false
  | .expect _ _=> false

def concat [ToDoc a] [ToDoc b] (l : a) (r : b) : Doc :=
  if isEmpty l then toDoc r
  else if isEmpty r then toDoc l
  else
    let ld := toDoc l
    let rd := toDoc r
    Doc.concat ld rd

infixl:40 " <> " => fun l r => concat l r



infixl:39 " <$$> " => fun l r => (toDoc l) <> Doc.provide (bridgeNl ||| bridgeHardNl) <> (toDoc r)
infixl:38 " <$$$> " => fun l r => (toDoc l) <> Doc.provide bridgeHardNl <> (toDoc r)
infixl:37 " <**> " => fun l r => (toDoc l) <> Doc.provide bridgeAny <> (toDoc r)
infixl:36 " <_> " => fun l r => (toDoc l) <> Doc.provide bridgeSpace <> (toDoc r)


infixl:40 " <+> " => fun l r => (toDoc l) <> Doc.align (toDoc r)
infixl:45 " !> " => fun l r => (Doc.provide l) <> (toDoc r)
infixl:45 " <! " => fun l r => (Doc.expect l) <> (toDoc r)

infixl:34 " <^> " => fun l r => toDoc (Doc.choice (toDoc l) (toDoc r))

def group [ToDoc α] (doc : α) : Doc :=
  toDoc (doc <^> (Doc.flatten (toDoc doc)))

def nl : Doc := (Doc.newline "")

def spacing (s : Bridge) : Doc := (Doc.provide s)
def expect (s : Bridge) : Doc := (Doc.expect s)

def align [ToDoc α] (s: α): Doc:=
  (Doc.align (toDoc s))


def PPL.flatten (s: Doc): Doc:=
  (Doc.flatten (toDoc s))

def Doc.nl : Doc := (Doc.newline "")

def flattenPPL [ToDoc α] (s: α): Doc:=
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


end PrettyFormat
