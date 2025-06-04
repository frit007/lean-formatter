import Std.Data.HashSet
open Std

namespace PrettyFormat


/--
Why do we need so many flattens?
The issue is that flatten should be delayed until the outer bridges have found a value
-/
inductive Flatten where
| notFlattened
| flattenLeft
| flattenRight
| flattenEventually
| flattened
deriving DecidableEq, Repr

-- flattening has started, but not yet completed
def Flatten.shouldFlattenNl (f : Flatten) : Bool :=
  f != Flatten.notFlattened

def Flatten.isFlat (f : Flatten) : Bool :=
  f == flattened

def Flatten.startFlatten : Flatten → Flatten
| notFlattened => flattenEventually
| f => f


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
def bridgeEnding := bridgeAny ||| bridgeFlex

def Bridge.subsetOf (l r: Bridge) : Bool :=
  (l &&& r) == r

def Bridge.contains (l r: Bridge) : Bool :=
  if l == r then
    true
  else if l == bridgeNull then
    false
  else
    (l &&& r) == r

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

partial def Bridge.parts : Bridge → List Bridge
| 0 => []
| x =>
  let one := (x &&& (~~~ (x - 1)))
  one :: Bridge.parts (x &&& (~~~ one))

#eval bridgeFlex.parts

-- The idea is that bridge flex will accept any bridge
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
  bridge.replaceIfExists bridgeSpaceNl (bridgeSpace)
    |>.erase bridgeHardNl

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


def Bridge.provideIntersection (l r : Bridge) :=
  if l == bridgeFlex then
    r
  else if r == bridgeFlex then
    l
  else
    l.intersection r



def Bridge.requireIntersection (l r : Bridge) :=
  if l == bridgeFlex && r.subsetOf (bridgeAny ||| bridgeNone) then
    r
  else if r == bridgeFlex && l.subsetOf (bridgeAny ||| bridgeNone) then
    l
  else
    l.intersection r

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
  nl : χ



structure DefaultCost where
  widthCost : Nat
  lineCost : Nat
  deriving Inhabited, Repr

def DefaultCost.add (lhs rhs : DefaultCost) : DefaultCost :=
  { widthCost := lhs.widthCost + rhs.widthCost, lineCost := lhs.lineCost + rhs.lineCost }

instance : Add DefaultCost where
  add := DefaultCost.add

def DefaultCost.le (lhs rhs : DefaultCost) : Bool :=
  if lhs.widthCost == rhs.widthCost then lhs.lineCost ≤ rhs.lineCost else lhs.widthCost < rhs.widthCost

instance : LEB DefaultCost where
  leq lhs rhs := DefaultCost.le lhs rhs

def DefaultCost.text (widthLimit : Nat) (col : Nat) (length : Nat) : DefaultCost :=
  if col + length > widthLimit then
    let a := max widthLimit col - widthLimit
    let b := col + length - max widthLimit col
    { widthCost := b * (2 * a + b), lineCost := 0 }
  else
    { widthCost := 0, lineCost := 0 }

def DefaultCost.nl : DefaultCost :=
  { widthCost := 0, lineCost := 1 }

instance : Cost DefaultCost where
  text := DefaultCost.text
  nl := DefaultCost.nl

inductive Ternary
| yes
| no
| maybe
deriving Inhabited, Repr

def Ternary.and : Ternary → Ternary → Ternary
| .yes, .yes => .yes
| .no, .no => .no
| _, _ => .maybe

def Ternary.or : Ternary → Ternary → Ternary
| .yes, _ => .yes
| _, .yes => .yes
| .no, .no => .no
| _, _ => .maybe

def Ternary.eq : Ternary → Ternary → Bool
| .yes, .yes => true
| .no, .no => true
| .maybe, .maybe => true
| _, _ => false

def Ternary.toString : Ternary → String
| .yes => "yes"
| .no => "no"
| .maybe => "maybe"

def Ternary.neq (lhs rhs :Ternary) : Bool :=
  !lhs.eq rhs

abbrev Path := Array (Bridge × Bridge)

structure DocMeta where
  id : Nat := 0
  cacheWeight : Nat := 0

  /--
   This is used for for flatten
  The issue is that flatten wants to ignore the first bridge on either side of a flatten operation. For example
  "def main := " <$$> flatten ("return 1" <> "-- end of line comment" <$$$>)
  wants to allow to allow the newline before the flatten operation (remember that the bridge is evaluated when we reach the "return 1" text)
  -/
  collapsesBridges : Ternary := Ternary.yes

  path : Path := #[]
  flattenPath : Path := #[]
  eventuallyFlattenPath : Path := #[]
  flattenLPath : Path := #[]
  flattenRPath : Path := #[]
deriving Inhabited, Repr


def DocMeta.collapses (meta : DocMeta) : Bool :=
  meta.collapsesBridges.neq Ternary.no

def DocMeta.findPath (meta : DocMeta) (flatten : Flatten) : Path :=
  match flatten with
  | Flatten.flattenLeft =>
    meta.flattenLPath
  | Flatten.flattenRight =>
   meta.flattenRPath
  | Flatten.flattened =>
    meta.flattenPath
  | Flatten.flattenEventually =>
    meta.eventuallyFlattenPath
  | Flatten.notFlattened =>
    meta.path

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
| text (s : String) (meta : DocMeta := {collapsesBridges := if s.length > 0 then Ternary.yes else Ternary.no})
/--
Render a newline. Also contains an alternative rendering for the newline for `Doc.flatten`.
If s is `none` then it will fail
-/
| newline (s : Option String) (meta : DocMeta := {collapsesBridges := Ternary.yes})
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
The special spacing options are
- `space` which is a single space
- `nl` which is a newline, which is converted to a `space` in `flatten`
- `hardNl` which is a newline, which is removed when flattened `flatten`
- `nospace` which is nothing and leaves the formatting choice up to the child, and is used when we want parenthesis.
`nospace` will be automatically applied even if the parent does not provide any spacing information
We can create variations of `nospace`,
for example this can be used to detect if we are directly after a new function declaration
do/by notation use `immediateValue` to handle this scenario so they can place their keyword on the same line and then indent

provide can be chained to narrow the options to overlap between the two sets
-/
| provide (bridge : Bridge) (meta : DocMeta := {})
/--
`require` must be preceded by a `provide` and will fail if the provided bridge does not contain the expected spacing
-/
| require (bridge : Bridge) (meta : DocMeta := {collapsesBridges := Ternary.yes})
| rule (r : String) (doc : Doc) (meta : DocMeta := {})
| stx (s : Lean.Syntax) (meta : DocMeta := {})
| flatten (inner : Doc) (meta : DocMeta := {})
/--
Add cost equivalent to `nl` newlines
-/
| cost (nl:Nat) (meta : DocMeta := {})
/--
The comment will be placed after the last newline before this line
-/
| bubbleComment (comment : String) (meta : DocMeta := {})
deriving Inhabited, Repr

def Doc.meta : Doc → DocMeta
  | .text _ meta => meta
  | .newline _ meta => meta
  | .concat _ _ meta => meta
  | .nest _ _ meta => meta
  | .align _ meta => meta
  | .choice _ _ meta => meta
  | .reset _ meta => meta
  | .provide _ meta => meta
  | .require _ meta => meta
  | .rule _ _ meta => meta
  | .stx _ meta => meta
  | .flatten _ docMeta => docMeta
  | .cost _ meta => meta
  | .bubbleComment _ meta => meta

def Doc.setMeta (doc : Doc) (meta : DocMeta) : Doc :=
  match doc with
  | .text s _ => .text s meta
  | .newline s _ => .newline s meta
  | .concat l r _ => .concat l r meta
  | .nest n d _ => .nest n d meta
  | .align d _ => .align d meta
  | .choice l r _ => .choice l r meta
  | .reset d _ => .reset d meta
  | .provide s _ => .provide s meta
  | .require s _ => require s meta
  | .rule r d _ => .rule r d meta
  | .stx s _ => .stx s meta
  | .flatten inner _ => .flatten inner meta
  | .cost c _ => .cost c meta
  | .bubbleComment c _ => .bubbleComment c meta

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

  bridgeR : Bridge

  fail: Bool := false
deriving Inhabited

-- def groupBySpacingR [BEq χ] [Hashable χ] (measures : List (Measure χ)) : Std.HashMap (Bridge) (List (Measure χ)) :=
--   measures.foldl
--     (fun acc m =>
--       acc.insert key (m :: (acc.getD key []))
--     )
--     HashMap.empty

instance [Cost χ] : LEB (Measure χ) where
  leq lhs rhs :=
    (lhs.fail && !rhs.fail) || (lhs.last ≤ rhs.last && LEB.leq lhs.cost rhs.cost)


def bridgeIntersection (set1 set2 : Bridge): Bridge :=
  set1 &&& set2

/--
Lifting `Doc.concat` to `Measure`.
-/
def Measure.concat [Cost χ] (lhs rhs : Measure χ) :Measure χ :=
  match (lhs.fail, rhs.fail) with
  | (true, _) => lhs
  | (false, true) => rhs
  | _ =>
    -- dbg_trace s!"concat {lhs.bridgeR} :: {rhs.bridgeR}"
    { last := rhs.last, cost := lhs.cost + rhs.cost, layout := fun ss => rhs.layout (lhs.layout ss), bridgeR := rhs.bridgeR }

def Measure.addCost [Cost χ] (m : Measure χ) (c : χ) : Measure χ :=
  { m with cost := m.cost + c}

def Measure.prependLayout [Cost χ] (m : Measure χ) (layoutFn : List String → List String) : Measure χ :=
  { m with layout := fun ss => m.layout (layoutFn ss)}

structure TaintedState where
  col : Nat
  indent : Nat
  widthLimit : Nat
  leftBridge : Bridge
  rightBridge : Bridge
  flatten : Flatten



inductive TaintedTrunk (χ : Type) where
| leftTainted (left: TaintedTrunk χ) (doc: Doc) (state : TaintedState) (id: Nat)
| rightTainted (left : Measure χ) (right: TaintedTrunk χ) (state : TaintedState) (id: Nat)
-- | center (doc : Doc) (state : TaintedState) (id: Nat)
| value (m : Measure χ)
-- | cost (cost : Nat) (trunk : (TaintedTrunk χ)) (id: Nat)
-- | bubbleComment (bubleComment : String) (trunk : (TaintedTrunk χ)) (id: Nat)

inductive MeasureSet (χ : Type)
  /-
  A list of `Measure`s that form a Pareto front for our rendering problem.
  This list is ordered by the last line length in strict ascending order.
  -/
  | set (s : List (Measure χ))
  | tainted (tainted: TaintedTrunk χ) (fail:Bool)

def impossibleMeasure [Cost χ] (err:String) : Measure χ := {
      last := 0,
      cost := Cost.text 0 0 0,
      layout := fun ss => s!"(no possible formatter::{err})" :: ss
      fail := true
      bridgeR := bridgeFlex
    }
def impossibleMeasureSet [Cost χ] (err:String): MeasureSet χ :=
  .set [impossibleMeasure err]

instance [Cost χ]: Inhabited (MeasureSet χ) where
  -- default := MeasureSet.set []
  default := MeasureSet.tainted (TaintedTrunk.value (impossibleMeasure "default")) true

instance : Repr (MeasureSet χ) where
  reprPrec
    | MeasureSet.set s, _ =>
      let children := s.foldl (fun (a : List String) x => s!"(rightBridge {x.bridgeR}, last:{x.last})" :: a) []
      s!"MeasureSet.set {s.length} {children}"
    | MeasureSet.tainted t f, _ =>
      "MeasureSet.tainted "

def TaintedTrunk.cacheInfo (trunk : TaintedTrunk χ) : Option (TaintedState × Nat) :=
  match trunk with
  | .leftTainted _ _ s id => some (s, id)
  | .rightTainted _ _ s id => some (s, id)
  | _ => none
  -- | .cost _ _ id => some ({trace := [], col := 0, indent := 0, widthLimit := 0, leftBridge := bridgeFlex}, id)
  -- | _ => none



structure Cache (χ : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  rightBridge : Bridge
  indent : Nat
  column: Nat --
  flatten: Flatten --

  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  results : MeasureSet χ

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


def Doc.toString (ppl:Doc) : String :=
  output' 0 ppl
where
  output' (indent : Nat) (d:Doc): String :=
  let inner := match d with
  | .text s _ => s!"\"{s}\""
  | .newline s _ => s!"Doc.newline {newlineString s}"
  | .choice left right _ => s!"({output' indent left})<^>({output' indent right}){newline indent}"
  | .flatten inner _ => s!"flattenDoc ({output' indent inner})"
  | .align inner _ => s!"alignDoc ({output' indent inner})"
  | .nest n inner _ => s!"nestDoc {n} ({output' indent inner})"
  | .concat left right _ => s!"({output' indent left}) <> ({output' indent right})"
  | .stx _ _ => "stx\n"
  | .rule name s _ => s!"ruleDoc \"{name}\" {newline indent} ({output' (indent + 2) s}) {newline indent}"
  | .reset s _ => s!"Doc.reset ({output' indent s})"
  | .provide b _ => s!"provideDoc {b.str}"
  | .require b _ => s!"requireDoc {b.str}"
  | .cost n _ => s!"costDoc {n}"
  | .bubbleComment s _ => s!"bubbleComment \"{s}\""
  if d.meta.id != 0 then
    s!"/-{d.meta.id}-/ {inner}"
  else
    inner
  newline indent := "\n".pushn ' ' indent
  newlineString : Option String -> String
  | none => "none"
  | some s => s!"(some \"{s}\")"

def Doc.kind : Doc → String
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
  | .require _ _ => s!"require"
  | .bubbleComment s _ => s!"bubbleComment \"{s}\""
  | .cost _ _ => s!"cost"

initialize cache : IO.Ref (Nat × Array (List (Cache DefaultCost))) ← IO.mkRef (0, #[])

class ToDoc (α : Type u) where
  toDoc : α → Doc

instance : ToDoc Doc where
  toDoc ppl:= ppl


partial def isSyntaxEmpty (stx : Lean.Syntax) : Bool :=
  match stx with
  | .missing => false
  | .node _ _ args =>
    args.all (fun s => isSyntaxEmpty s)
  | .atom _ (val : String) =>
    val.trim.length == 0 -- TODO: there might be a comment attached to this node
  | .ident  _ (rawVal : Substring) _ _ =>
    (toString rawVal).trim.length == 0


instance : ToDoc Lean.Syntax where
  -- note that syntax is placed as a placeholder and will be expanded later
  toDoc stx:= Doc.stx stx {collapsesBridges := if isSyntaxEmpty stx then Ternary.no else Ternary.yes}

instance : ToDoc (Lean.TSyntax a) where
  toDoc tstx:= Doc.stx tstx.raw {collapsesBridges := if isSyntaxEmpty tstx.raw then Ternary.no else Ternary.yes}

instance : ToDoc String where
  toDoc text:= Doc.text text

export ToDoc (toDoc)

partial def isEmpty [ToDoc α] (ppl : α) : Bool :=
  isEmpty' (toDoc ppl)
where
  isEmpty' : Doc → Bool
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
  | .provide _ _=> false
  | .require _ _=> false
  /-
  Note that this means that cost and bubble comments will be discarded if they are not attached to a relevant object
  -/
  | .bubbleComment _ _=> false
  | .cost _ _=> false

def choiceDoc [ToDoc a] [ToDoc b] (l : a) (r : b) :=
  let l := toDoc l
  let r := toDoc r

  Doc.choice l r {collapsesBridges := l.meta.collapsesBridges.and r.meta.collapsesBridges}

def provideDoc (b : Bridge) : Doc :=
  -- Should expand did not work, because even if it may contain whitespace, it may still
  Doc.provide b {collapsesBridges:= Ternary.no}


/--
concat guarantees the following properties:
 - There are only the final leaf nodes that contain whitespace
 - provides are moved to the right or to the final final leaf node
-/
partial def concatDoc [ToDoc α] [ToDoc β] (l : α) (r : β) : Doc :=
  let l := toDoc l
  let r := toDoc r

  if empty l then
    r
  else if empty r then
    l
  else
    Doc.concat l r {collapsesBridges := l.meta.collapsesBridges.or r.meta.collapsesBridges}
where
  empty :Doc → Bool
  | .stx s _ => isSyntaxEmpty s
  | .text t _ => t.length == 0
  | _ => false


infixl:40 " <> " => fun l r => concatDoc l r


def requireDoc (b : Bridge) : Doc :=
  Doc.require b

def bridgeConcat [ToDoc α] [ToDoc β] (bridge:Bridge) (l : α) (r : β) : Doc :=
  concatDoc (concatDoc l (provideDoc bridge)) r

infixl:39 " <$$> " => fun l r => bridgeConcat bridgeNl l r
infixl:38 " <$$$> " => fun l r => bridgeConcat bridgeHardNl l r
infixl:37 " <**> " => fun l r => bridgeConcat bridgeAny l r
infixl:36 " <_> " => fun l r => bridgeConcat bridgeSpace l r


infixl:30 " <+> " => fun l r => concatDoc (toDoc l) (Doc.align (toDoc r))

infixl:45 " !> " => fun l r => concatDoc (provideDoc l) r
infixl:45 " <! " => fun l r => concatDoc (requireDoc l) (toDoc r)

#eval "a" <+> "b"

-- #eval expandDoc ("hello" <> "world")

infixl:34 " <^> " => fun l r => choiceDoc l r


def flattenDoc [ToDoc α] (s: α): Doc:=
  let s := (toDoc s)
  (Doc.flatten s {collapsesBridges := s.meta.collapsesBridges})

def nestDoc [ToDoc α] (n : Nat) (s: α) : Doc:=
  let s := (toDoc s)
  (Doc.nest n s {collapsesBridges := s.meta.collapsesBridges})

def Doc.group (doc : Doc) : Doc :=
  (doc <^> (flattenDoc doc))

def costDoc (cost:Nat) : Doc :=
  Doc.cost cost {collapsesBridges := Ternary.no}

def Doc.preferFlatten (doc : Doc) : Doc :=
  -- TODO: at the moment the penalty is equivalent to a full newline.
  ((doc <> costDoc 1) <^> (flattenDoc doc))

-- def spacing (s : Bridge) (d:Doc) : Doc := (Doc.provideL s d {containsWhiteSpace:=d.meta.containsWhiteSpace})

def alignDoc [ToDoc α] (s: α): Doc:=
  let s := (toDoc s)
  (Doc.align s {collapsesBridges := s.meta.collapsesBridges})

def Doc.nl : Doc := (Doc.newline (some " ") {collapsesBridges := Ternary.yes})
def Doc.hardNl : Doc := (Doc.newline none {collapsesBridges := Ternary.yes})

/--
Aligned concatenation, joins two sub-layouts horizontally, aligning the whole right sub-layout at the
column where it is to be placed in. Aka the `<+>` operator.
-/
def Doc.alignedConcat [ToDoc α] [ToDoc β] (lhs : α) (rhs : β) : Doc := concatDoc lhs (alignDoc rhs)
-- /--
-- TODO: Better name
-- -/
def Doc.flattenedAlignedConcat [ToDoc α] [ToDoc β] (lhs : α) (rhs : β) : Doc := Doc.alignedConcat (flattenDoc (toDoc lhs)) rhs


def bubbleCommentDoc (s:String) : Doc :=
  Doc.bubbleComment s {collapsesBridges := Ternary.no}

def ruleDoc [ToDoc α] (s:String) (d:α) : Doc :=
  let d := toDoc d
  Doc.rule s d {collapsesBridges := d.meta.collapsesBridges}

def measureTime (f : Unit → IO α) : IO (α × Nat):= do
  let before ← IO.monoNanosNow
  let res ← f ()
  let after ← IO.monoNanosNow
  return (res, after - before)

def measureDiff (str:String): MeasureResult χ Unit := do
  -- return () -- TODO: remove
  let now ← IO.monoNanosNow
  let s ← get
  set {s with lastMeasurement := now}
  IO.println s!"{str}::PERF {(now - s.lastMeasurement).toFloat / 1000000000.0} ({now})"

def formatThen [ToDoc α] [ToDoc β] (sep : α) (ppl : β) : Doc :=
  let p := toDoc ppl
  if PrettyFormat.isEmpty p then
    toDoc ""
  else
    p <> sep

def formatBefore [ToDoc a] [ToDoc b] (sep : a) (doc : b) : Doc :=
  let d := toDoc doc
  let sep := toDoc sep
  if PrettyFormat.isEmpty d then
    toDoc ""
  else
    sep <> d

infixr:45 " ?> " => fun l r => formatThen r l
infixr:45 " <? " => fun l r => formatBefore l r

#eval ("def:= " <_> nestDoc 4 ("funcName" <**> "helps") <**> "val").toString

/--
To visualize the call graph we want to avoid drawing the shared nodes multiple times.
-/
def findSharedNodes (map:Std.HashMap Nat Nat) (d : Doc): (Std.HashMap Nat Nat) := Id.run do
  let mut map := map
  if d.meta.id != 0 then
    map := map.alter d.meta.id (fun (o : Option (Nat)) =>
      match o with
      | none => some (1)
      | some l => some (1 + l)
    )
    if map.get! d.meta.id > 1 then
      -- if this is the first time we see this node, then we can add it to the map
      return map
  match d with
  | .text _ _=> return map
  | .newline _ _=> return map
  | .choice left right _=>
    map := findSharedNodes map left
    return findSharedNodes map right
  | .flatten inner _=> return findSharedNodes map inner
  | .align inner _=> return findSharedNodes map inner
  | .nest _ inner _=> return findSharedNodes map inner
  | .concat left right _=>
    map := findSharedNodes map left
    return findSharedNodes map right
  | .stx _ _=> return map
  | .reset inner _=> return findSharedNodes map inner
  | .rule _ inner _=> return findSharedNodes map inner
  | .provide _ _=> return map
  | .require _ _=> return map
  | .bubbleComment _ _=> return map
  | .cost _ _=> return map

def printNodes (d : Doc) (indentation : Nat) (sharedNodes : Std.HashMap Nat Nat) (results : Std.HashMap Nat String): (String × Std.HashMap Nat String) := Id.run do
  if d.meta.id != 0 then
    match results.get? d.meta.id with
    | some _ => return (s!"/-{d.meta.id}-/", results)
    | none =>
      let isShared := sharedNodes.get! d.meta.id > 1
        -- if  then
      if isShared then
        -- dbg_trace s!"printing node {d.meta.id} with sharedNodes: is shared"
        let (v, results) := printNode 0 d
        (s!"/-{d.meta.id}-/", results.insert d.meta.id v)
      else
        -- dbg_trace s!"printing node {d.meta.id} with sharedNodes: not shared"
        let (v, results) := printNode indentation d
        return (s!"{v}", results)
  else
    return printNode indentation d
where
  printNl : Nat → String
  | indent => "\n".pushn ' ' indent
  printMeta (indentation:Nat): DocMeta → String
  | m => s!"meta: \{ id := {m.id},{printNl indentation}cacheWeight := {m.cacheWeight},{printNl indentation}collapsesBridges := {repr m.collapsesBridges},{printNl indentation}flattenPath := {m.flattenPath},{printNl indentation}flattenRPath := {m.flattenRPath},{printNl indentation}flattenLPath := {m.flattenLPath},{printNl indentation}eventuallyFlattenPath := {m.eventuallyFlattenPath},{printNl indentation}path := {m.path} }"
  printNode (indentation:Nat): Doc → (String × Std.HashMap Nat String)
  | .text s m => (s!"(Doc.text \"{s}\" {printNl indentation}{printMeta indentation m})", results)
  | .newline s m => (s!"(Doc.newline {s} {printNl indentation}{printMeta indentation m})", results)
  | .choice left right m =>
    let (l, results) := printNodes left (indentation + 2) sharedNodes results
    let (r, results) := printNodes right (indentation + 2) sharedNodes results
    (s!"(Doc.choice {printNl indentation}{printMeta indentation m}{printNl indentation}l: {l}{printNl indentation}r: {r})", results)
  | .flatten inner m =>
    let (i, results) := printNodes inner (indentation + 2) sharedNodes results
    (s!"(Doc.flatten {i} {printNl indentation}{printMeta indentation m} {printNl indentation}inner: {i})", results)
  | .align inner m =>
    let (i, results) := printNodes inner (indentation + 2) sharedNodes results
    (s!"(Doc.align {printNl indentation}{printMeta indentation m} {printNl indentation}inner: {i})", results)
  | .nest n inner m =>
    let (i, results) := printNodes inner (indentation + 2) sharedNodes results
    (s!"(Doc.nest {n} {printNl indentation}{printMeta indentation m} {printNl indentation}inner: {i})", results)
  | .concat left right m =>
    let (l, results) := printNodes left (indentation + 2) sharedNodes results
    let (r, results) := printNodes right (indentation + 2) sharedNodes results
    (s!"(Doc.concat {printNl indentation}{printMeta indentation m}{printNl indentation}l: {l}{printNl indentation}r: {r})", results)
  | .stx _ _ => ("stx", results)
  | .reset inner m =>
    let (i, results) := printNodes inner (indentation + 2) sharedNodes results
    (s!"(Doc.reset {printNl indentation}{printMeta indentation m}{printNl indentation}inner: {i})", results)
  | .rule name inner m =>
    let (i, results) := printNodes inner (indentation + 2) sharedNodes results
    (s!"(Doc.rule {name} {printNl indentation}{printMeta indentation m}{printNl indentation}inner: {i})", results)
  | .provide b m =>
    (s!"(Doc.provide {b} {printNl indentation}{printMeta indentation m}{printNl indentation})", results)
  | .require b m =>
    (s!"(Doc.require {b} {printNl indentation}{printMeta indentation m}{printNl indentation})", results)
  | .bubbleComment s m =>
    (s!"(Doc.bubbleComment \"{s}\" {printNl indentation}{printMeta indentation m}{printNl indentation})", results)
  | .cost n m =>
    (s!"(Doc.cost \"{n}\" {printNl indentation}{printMeta indentation m}{printNl indentation})", results)

def Doc.printDependencies (d : Doc) : String := Id.run do
  let sharedNodes := findSharedNodes {} d
  let (s, n) := printNodes d 0 sharedNodes {}
  let mut res := s!"{s}\n\n"
  for (k, v) in n.toArray do
    if v.length > 1 then
      res := res ++ s!"{k} -> {v}\n"
  res


def verifyChoiceInvariant (path:String): Doc → List String
  | .text s _=> []
  | .newline _ _=> []
  | .choice left right m =>
    let l := verifyChoiceInvariant (s!"{path}/choice") left
    let r := verifyChoiceInvariant (s!"{path}/choice") right
    let a := l.append r
    if m.collapsesBridges.eq Ternary.maybe then
      (s! "{path} left {left.toString} {right.toString}")::a
    else
      a
  | .flatten inner _=> verifyChoiceInvariant (s!"{path}/flatten") inner
  | .align inner _=> verifyChoiceInvariant (s!"{path}/align") inner
  | .nest _ inner _=> verifyChoiceInvariant (s!"{path}/nest") inner
  | .concat left right _=>
    let l := verifyChoiceInvariant (s!"{path}/concat") left
    let r := verifyChoiceInvariant (s!"{path}/concat") right
    l.append r
  | .stx s _=> []
  | .reset inner _=> verifyChoiceInvariant (s!"{path}/reset") inner
  | .rule _ inner _=> verifyChoiceInvariant (s!"{path}/rule") inner
  | .provide _ _=> []
  | .require _ _=> []
  /-
  Note that this means that cost and bubble comments will be discarded if they are not attached to a relevant object
  -/
  | .bubbleComment _ _=> []
  | .cost _ _=> []

-- hack because \{ breaks highlight in vscode
def lparen := "{"
-- convert to JSON, but try to compress it by reducing repetitions
partial def Doc.toJSON (d : Doc) : String :=
  let (main, results) := jsonInternal d 2 {}
  let maps := results.fold (fun acc k v => s!"{acc},\n  \"{k}\" : {v}") ""
  -- results
  s!"{lparen}\n  \"start\":{main}{maps}\n}"
where
  jsonInternal (d : Doc) (indentation : Nat) (results : Std.HashMap Nat String): (String × Std.HashMap Nat String) := Id.run do
    if d.meta.id != 0 then
      match results.get? d.meta.id with
      | some _ => return (s!"{lparen}\"$ref\": {d.meta.id}}", results)
      | none =>
        let (v, results) := printNode 4 results d
        return (s!"{lparen}\"$ref\": {d.meta.id}}", results.insert d.meta.id v)
    else
      return printNode indentation results d
  printNl : Nat → String
  | indent => "\n".pushn ' ' indent

  approximation (path:Path): String :=
    let x := path.foldl (fun acc v =>
      if acc.length > 0 then
        acc  ++ s!", [{v.fst}, {v.snd}]"
      else
        s!"[{v.fst}, {v.snd}]"
      ) ""
    s!"[{x}]"
  printMeta (indentation : Nat) (m:DocMeta): String :=
    let nl := printNl (indentation + 2)
    s!"\"meta\": {lparen}" ++
    s!"{nl}\"id\": {m.id}," ++
    s!"{nl}\"cacheWeight\": {m.cacheWeight}," ++
    s!"{nl}\"collapsesBridges\": \"{m.collapsesBridges.toString}\"," ++
    s!"{nl}\"flattenPath\": {approximation m.flattenPath}," ++
    s!"{nl}\"flattenRPath\": {approximation m.flattenRPath}," ++
    s!"{nl}\"flattenLPath\": {approximation m.flattenLPath}," ++
    s!"{nl}\"eventuallyFlattenPath\": {approximation m.eventuallyFlattenPath}," ++
    s!"{nl}\"path\": {approximation m.path}" ++
    s!"{nl}}"
  printNode (indentation:Nat) (results : Std.HashMap Nat String): Doc → (String × Std.HashMap Nat String)
  | .text s m =>
    (s!"{lparen}\"type\": \"text\", \"s\": \"{s.replace "\"" "\\\""}\",{printNl indentation}{printMeta indentation m}}", results)

  | .newline s m =>
    (s!"{lparen}\"type\": \"newline\", \"flattened\": \"{s}\",{printNl indentation}{printMeta indentation m}}", results)

  | .choice left right m =>
    let (l, results) := jsonInternal left (indentation + 2) results
    let (r, results) := jsonInternal right (indentation + 2) results
    (
      s!"{lparen}\"type\": \"choice\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"lhs\": {l},{printNl indentation}\"rhs\": {r}}",
      results
    )
  | .flatten inner m =>
    let (i, results) := jsonInternal inner (indentation + 2) results
    (
      s!"{lparen}\"type\": \"flatten\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"inner\": {i}}",
      results
    )

  | .align inner m =>
    let (i, results) := jsonInternal inner (indentation + 2) results
    (
      s!"{lparen}\"type\": \"align\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"inner\": {i}}",
      results
    )

  | .nest n inner m =>
    let (i, results) := jsonInternal inner (indentation + 2) results
    (
      s!"{lparen}\"type\": \"nest\", \"indent\": {n},{printNl indentation}{printMeta indentation m},{printNl indentation}\"inner\": {i}}",
      results
    )
  | .concat left right m =>
    let (l, results) := jsonInternal left (indentation + 2) results
    let (r, results) := jsonInternal right (indentation + 2) results
    (
      s!"{lparen}\"type\": \"concat\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"lhs\": {l},{printNl indentation}\"rhs\": {r}}",
      results
    )
  | .stx _ m =>
    (s!"{lparen}\"type\": \"stx\",{printNl indentation}{printMeta indentation m}}", results)
  | .reset inner m =>
    let (i, results) := jsonInternal inner (indentation + 2) results
    (
      s!"{lparen}\"type\": \"reset\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"inner\": {i}}",
      results
    )
  | .rule name inner m =>
    let (i, results) := jsonInternal inner (indentation + 2) results
    (
      s!"{lparen}\"type\": \"rule\", \"name\": \"{name}\",{printNl indentation}{printMeta indentation m},{printNl indentation}\"inner\": {i}}",
      results
    )
  | .provide b m =>
    (
      s!"{lparen}\"type\": \"provide\", \"value\": {b},{printNl indentation}{printMeta indentation m}}",
      results
    )
  | .require b m =>
    (
      s!"{lparen}\"type\": \"require\", \"value\": {b},{printNl indentation}{printMeta indentation m}}",
      results
    )
  | .bubbleComment s m =>
    (
      s!"{lparen}\"type\": \"bubbleComment\", \"comment\": \"{s}\",{printNl indentation}{printMeta indentation m}}",
      results
    )
  | .cost n m =>
    (
      s!"{lparen}\"type\": \"cost\", \"value\": {n},{printNl indentation}{printMeta indentation m}}",
      results
    )


end PrettyFormat
