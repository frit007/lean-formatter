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
  bridge.replaceIfExists bridgeFlex (bridgeSpace ||| bridgeNone)
    |>.replaceIfExists bridgeSpaceNl (bridgeSpace)
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

-- /-- info: "bridgeSpace" -/
-- #guard_msgs in
-- #eval bridgeAny.flatten.str

-- /-- info: "(bridgeSpace|||bridgeNone)" -/
-- #guard_msgs in
-- #eval bridgeFlex.flatten.str

-- /-- info: "bridgeImmediate" -/
-- #guard_msgs in
-- #eval bridgeImmediate.flatten.str

-- /-- info: "bridgeNull" -/
-- #guard_msgs in
-- #eval bridgeHardNl.flatten.str

-- /-- info: "bridgeSpace" -/
-- #guard_msgs in
-- #eval (bridgeSpaceNl.flatten).str

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

-- What I want to ask is?
-- containsWhiteSpace
-- What am I trying to ask?
-- I am trying to figure out if there is a choice operator on the left side, that may or
-- choice operators are not that bad the problem is if one of the choice operators returns
-- contains choice
-- maybe it just does not make sense to ask concat whether or not it collapses...
-- walk the left side of the tree

-- def Ternary.or : Ternary → Ternary → Ternary
-- | .yes, _ => .yes
-- | _, .yes => .yes
-- | .maybe, _ => .maybe
-- | _, .maybe => .maybe
-- | .no, .no => .no

def Ternary.and : Ternary → Ternary → Ternary
| .yes, .yes => .yes
| .no, .no => .no
| _, _ => .maybe

def Ternary.eq : Ternary → Ternary → Bool
| .yes, .yes => true
| .no, .no => true
| .maybe, .maybe => true
| _, _ => false


-- inductive D where
-- | cached (cache: Array (Bridge × Bridge))
-- | passThrough
-- | acceptFlex
-- | provide (b : Bridge)
-- | require (b : Bridge)
-- deriving Inhabited, Repr

structure DocMeta where
  -- leftBridge : Bridge := bridgeFlex
  id : Nat := 0
  cacheWeight : Nat := 0
  -- no default value: to force the user to implement it, or better: use our functions :)
  -- containsWhiteSpace : Bool
  -- shouldBeExpanded : Bool := containsWhiteSpace
  --

  /--
   This is used for for flatten
  The issue is that flatten wants to ignore the first bridge on either side of a flatten operation. For example
  "def main := " <$$> flatten ("return 1" <> "-- end of line comment" <$$$>)
  wants to allow to allow the newline before the flatten operation (remember that the bridge is evaluated when we reach the "return 1" text)
  -/
  collapsesBridges : Ternary
  -- we delay this calculation until flatten, because otherwise we might have to recalculate
  -- paths guarantee that if you provide a bridge on the left then you can reach the right bridge
  paths : Array (Bridge × Bridge) := #[]

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
| concat (lhs rhs : Doc) (meta : DocMeta)
/--
Render `doc` width the indentation level increased by `nesting`.
-/
| nest (nesting : Nat) (doc : Doc) (meta : DocMeta)
/--
Render `doc` with the indentation level set to the column position.
-/
| align (doc : Doc) (meta : DocMeta)
/--
Make a choice between rendering either `lhs` or `rhs` by picking the prettier variant.
If one of the sides `fail`, then other side is chosen. If both sides `fail`, then the result is also `fail`
-/
| choice (lhs rhs : Doc) (meta : DocMeta)

/--
Reset the indentation level to 0.
-/
| reset (doc : Doc) (meta : DocMeta)
/--
Fail will never be rendered.
This error will propagate until the next choice, where branches containing errors are eliminated.
-/
| fail (err : String) (meta : DocMeta := {collapsesBridges := Ternary.yes})
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
| provide (bridge : Bridge) (meta : DocMeta)
/--
`require` must be preceded by a `provide` and will fail if the provided bridge does not contain the expected spacing
-/
| require (bridge : Bridge) (meta : DocMeta := {collapsesBridges := Ternary.yes})
| rule (r : String) (doc : Doc) (meta : DocMeta)
| stx (s : Lean.Syntax) (meta : DocMeta)
| flatten (inner : Doc) (meta : DocMeta)
/--
Add cost equivalent to `nl` newlines
-/
| cost (nl:Nat) (meta : DocMeta)
/--
The comment will be placed after the last newline before this line
-/
| bubbleComment (comment : String) (meta : DocMeta)
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
  | .fail err _ => .fail err meta
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
  -- spacingL : Option (HashSet String) := none
  -- spacingR : Bridge := bridgeFlex
  bridgeR : Bridge
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

-- def groupBySpacingR [BEq χ] [Hashable χ] (measures : List (Measure χ)) : Std.HashMap (Bridge) (List (Measure χ)) :=
--   measures.foldl
--     (fun acc m =>
--       acc.insert key (m :: (acc.getD key []))
--     )
--     HashMap.empty

instance [Cost χ] : LEB (Measure χ) where
  leq lhs rhs :=
    (lhs.fail.isSome && rhs.fail.isNone) || (lhs.last ≤ rhs.last && LEB.leq lhs.cost rhs.cost)

def Measure.mkFail [Cost χ] (cost : χ ) (err : (List (List String))) : Measure χ := {last := 0, cost:=cost, layout := fun _ => panic! "We never want to print fail", fail := some err, bridgeR := bridgeFlex}

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
  | _ => { last := rhs.last, cost := lhs.cost + rhs.cost, layout := fun ss => rhs.layout (lhs.layout ss), fail := none, bridgeR := rhs.bridgeR }

def Measure.addCost [Cost χ] (m : Measure χ) (c : χ) : Measure χ :=
  { m with cost := m.cost + c}

def Measure.prependLayout [Cost χ] (m : Measure χ) (layoutFn : List String → List String) : Measure χ :=
  { m with layout := fun ss => m.layout (layoutFn ss)}

structure TaintedState where
  trace : List String
  col : Nat
  indent : Nat
  widthLimit : Nat
  leftBridge : Bridge
  rightBridge : Bridge



inductive TaintedTrunk (χ : Type) where
| leftTainted (left: TaintedTrunk χ) (doc: Doc) (state : TaintedState) (id: Nat)
| rightTainted (left : Measure χ) (right: TaintedTrunk χ) (state : TaintedState) (id: Nat)
| center (doc : Doc) (state : TaintedState) (id: Nat)
-- | cost (cost : Nat) (trunk : (TaintedTrunk χ)) (id: Nat)
-- | bubbleComment (bubleComment : String) (trunk : (TaintedTrunk χ)) (id: Nat)

inductive MeasureSet (χ : Type)
  /-
  A list of `Measure`s that form a Pareto front for our rendering problem.
  This list is ordered by the last line length in strict ascending order.
  -/
  | set (s : List (Measure χ))
  | tainted (tainted: TaintedTrunk χ) (fail:Bool)

def impossibleMeasure [Cost χ] (trace: List String): Measure χ := {
      last := 0,
      cost := Cost.text 0 0 0,
      layout := fun ss => "(no possible formatter)" :: (String.join (trace.intersperse "::")):: "\n" :: ss
      fail := ["impossible"::trace]
      bridgeR := bridgeFlex
    }
def impossibleMeasureSet [Cost χ] (trace: List String): MeasureSet χ :=
  .set [impossibleMeasure trace]

instance : Inhabited (MeasureSet χ) where
  -- default := MeasureSet.set []
  default := MeasureSet.tainted (TaintedTrunk.center (Doc.text "" {collapsesBridges := Ternary.yes}) {trace := [], col := 0, indent := 0, widthLimit := 0, leftBridge := bridgeFlex, rightBridge := bridgeFlex} 0) true

def TaintedTrunk.cacheInfo (trunk : TaintedTrunk χ) : Option (TaintedState × Nat) :=
  match trunk with
  | .leftTainted _ _ s id => some (s, id)
  | .rightTainted _ _ s id => some (s, id)
  | .center _ s id => some (s, id)
  -- | .cost _ _ id => some ({trace := [], col := 0, indent := 0, widthLimit := 0, leftBridge := bridgeFlex}, id)
  -- | _ => none



structure Cache (χ : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  column: Nat --
  -- if the result is tainted, do not allow using it in a non tainted context
  -- The idea is that we can momentarily be in a tainted context (and accept any ugly solution),
  -- but when we reach the next line we should try to find the pretties solution again. However to avoid recalculations
  isTainted: Bool

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
  | .fail s _ => s!"Doc.fail {s}"
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
  | .require _ _ => s!"require"
  | .bubbleComment s _ => s!"bubbleComment \"{s}\""
  | .cost _ _ => s!"cost"

def Doc.calcMeta : Doc → DocMeta
  | .fail _ m => {m with collapsesBridges := Ternary.yes}
  | .text s m => {m with collapsesBridges := if s.length == 0 then Ternary.no else Ternary.yes}
  | .newline _ m => {m with collapsesBridges:= Ternary.yes}
  | .choice l r m => {m with
      collapsesBridges := l.meta.collapsesBridges.and r.meta.collapsesBridges,
    }
  | .flatten i m => {m with collapsesBridges := i.meta.collapsesBridges}
  | .align i m => {m with collapsesBridges := i.meta.collapsesBridges}
  | .nest _ i m => {m with collapsesBridges := i.meta.collapsesBridges}
  | .concat l r m => {m with
    collapsesBridges := l.meta.collapsesBridges.and r.meta.collapsesBridges,
    }
  | .stx _ m => m
  | .rule _ i m => {m with collapsesBridges := i.meta.collapsesBridges}
  | .reset i m => {m with collapsesBridges := i.meta.collapsesBridges}
  | .provide _ m => {m with collapsesBridges := Ternary.no}
  | .require _ m => {m with collapsesBridges := Ternary.no}
  | .bubbleComment _ m => {m with collapsesBridges := Ternary.no}
  | .cost _ m => {m with collapsesBridges := Ternary.no}
where
  -- use the first delayedProvide, because one of these is going to be the source of a delayedProvide and we do not want to delete the source
  firstDelayed : Option (List Bridge) → Option (List Bridge) → Option (List Bridge)
  | none, none => none
  | some l, _ => some l
  | none, some r => some r

def Doc.updateMeta : Doc -> Doc
  | d => d |> Doc.calcMeta |> Doc.setMeta d


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

-- instance : ToDoc Bridge where
--   toDoc b := Doc.provide b (Doc.text "" {containsWhiteSpace := true, delayedProvide := some [b]}) {containsWhiteSpace := true, delayedProvide := some [b]}

export ToDoc (toDoc)

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
  | .provide _ _=> false
  | .require _ _=> false
  /-
  Note that this means that cost and bubble comments will be discarded if they are not attached to a relevant object
  -/
  | .bubbleComment _ _=> false
  | .cost _ _=> false


partial def moveRight (d:Doc): Doc → Doc
  | .choice _ _ _ => panic "should not move choice (right)"
  | .flatten inner _ => moveRight d inner
  | .align inner _ => moveRight d inner
  | .nest _ inner _ => moveRight d inner
  | .reset inner _ => moveRight d inner
  | .rule r inner m => Doc.rule r (moveRight d inner) (m) |>.updateMeta
  | .concat l r m => Doc.concat l (moveRight d r) m |>.updateMeta
  /-
  Note that this means that cost and bubble comments will be discarded if they are not attached to a relevant object
  -/
  -- when we reach a leaf return
  | _ => d


/--
Expand choice operator until it must no longer be expanded. While moving over modifiers
-/
def expandDoc (d : Doc) (isLeft : Bool): (List Doc) :=
  if d.meta.collapsesBridges.eq Ternary.yes then
    [d]
  else
    expandDoc' d
    -- [.text "are we heer?" {containsWhiteSpace:=false}]
where
  expandDoc' : Doc → (List Doc)
  | .choice l r _ => expandDoc l isLeft|>.append (expandDoc r isLeft)
  | .rule n inner m => expandDoc inner isLeft |> .map (fun d => Doc.rule n d {m with collapsesBridges := d.meta.collapsesBridges} |>.updateMeta )
  | .reset inner m => expandDoc inner isLeft |> .map (fun d => Doc.reset d {m with collapsesBridges := d.meta.collapsesBridges} |>.updateMeta)
  | .flatten inner m => expandDoc inner isLeft |> .map (fun d => Doc.flatten d {m with collapsesBridges := d.meta.collapsesBridges} |>.updateMeta)
  | .align inner m => expandDoc inner isLeft |> .map (fun d => Doc.align d {m with collapsesBridges := d.meta.collapsesBridges} |>.updateMeta)
  | .nest i inner m => expandDoc inner isLeft |> .map (fun d => Doc.nest i d {m with collapsesBridges := d.meta.collapsesBridges} |>.updateMeta)
  | .concat l r m =>
    --  dbg_trace s!"expand concatDoc: l: {repr l} r: {repr r}"
    if isLeft then
      if l.meta.collapsesBridges.eq Ternary.yes then
        [.concat l r m]
      else if r.meta.collapsesBridges.eq Ternary.yes then
        expandDoc l isLeft |>.foldl (fun acc (dl) => Doc.concat dl r {collapsesBridges := dl.meta.collapsesBridges.and r.meta.collapsesBridges} :: acc) []
      else
        let rr := expandDoc r isLeft
        expandDoc l isLeft |>.foldl (fun acc dl =>
          rr.foldl (fun acc dr =>
            Doc.concat dl dr {collapsesBridges := dl.meta.collapsesBridges.and dr.meta.collapsesBridges} :: acc
          ) acc
        ) []

    else
      if r.meta.collapsesBridges.eq Ternary.yes then
        [.concat l r m]
      else if l.meta.collapsesBridges.eq Ternary.yes then
        expandDoc r isLeft |>.foldl (fun acc (dr) => Doc.concat l dr {collapsesBridges := l.meta.collapsesBridges.and dr.meta.collapsesBridges} :: acc) []
      else
        let rr := expandDoc r isLeft
        expandDoc l isLeft |>.foldl (fun acc dl =>
          rr.foldl (fun acc dr =>
            Doc.concat dl dr {collapsesBridges := dl.meta.collapsesBridges.and dr.meta.collapsesBridges} :: acc
          ) acc
        ) []
  | d => [d]

def choiceDoc [ToDoc a] [ToDoc b] (l : a) (r : b) :=
  let l := toDoc l
  let r := toDoc r

  -- let combinedProvide := match l.meta.delayedProvide, r.meta.delayedProvide with
  -- | none, none => none
  -- | some b, none => some b
  -- | none, some b => some b
  -- | some b1, some b2 => some (b1 ++ b2)
  Doc.choice l r {collapsesBridges := l.meta.collapsesBridges.and r.meta.collapsesBridges} |>.updateMeta

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

  Doc.concat l r {collapsesBridges := l.meta.collapsesBridges.and r.meta.collapsesBridges}
where
  listToChoices : List Doc → Doc
  | a::[] => a
  | a::b::[] => (choiceDoc a b)
  | a::b::rest => (choiceDoc a ((listToChoices (b::rest))))
  | [] => toDoc ""


infixl:40 " <> " => fun l r => concatDoc l r


def requireDoc (b : Bridge) : Doc :=
  Doc.require b

def bridgeConcat [ToDoc α] [ToDoc β] (bridge:Bridge) (l : α) (r : β) : Doc :=
  concatDoc (concatDoc l (provideDoc bridge)) r

infixl:39 " <$$> " => fun l r => bridgeConcat bridgeNl l r
infixl:38 " <$$$> " => fun l r => bridgeConcat bridgeHardNl l r
infixl:37 " <**> " => fun l r => bridgeConcat bridgeAny l r
infixl:36 " <_> " => fun l r => bridgeConcat bridgeSpace l r


infixl:40 " <+> " => fun l r => concatDoc (toDoc l) Doc.align (toDoc r)

infixl:45 " !> " => fun l r => concatDoc (provideDoc l) r
infixl:45 " <! " => fun l r => concatDoc (requireDoc l) (toDoc r)



-- #eval expandDoc ("hello" <> "world")

infixl:34 " <^> " => fun l r => choiceDoc l r


def flattenDoc [ToDoc α] (s: α): Doc:=
  let s := (toDoc s)
  (Doc.flatten s {collapsesBridges := s.meta.collapsesBridges}) |>.updateMeta

def nestDoc [ToDoc α] (n : Nat) (s: α) : Doc:=
  let s := (toDoc s)
  (Doc.nest n s {collapsesBridges := s.meta.collapsesBridges}) |>.updateMeta

def Doc.group (doc : Doc) : Doc :=
  (doc <^> (flattenDoc doc))

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

def costDoc (cost:Nat) : Doc :=
  Doc.cost cost {collapsesBridges := Ternary.no} |>.updateMeta

def bubbleCommentDoc (s:String) : Doc :=
  Doc.bubbleComment s {collapsesBridges := Ternary.no} |>.updateMeta

def ruleDoc [ToDoc α] (s:String) (d:α) : Doc :=
  let d := toDoc d
  Doc.rule s d {collapsesBridges := d.meta.collapsesBridges} |>.updateMeta

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

/--
info: [PrettyFormat.Doc.concat
   (PrettyFormat.Doc.concat
     (PrettyFormat.Doc.text
       "Hello"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     (PrettyFormat.Doc.text
       "world"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
   (PrettyFormat.Doc.provide 6 { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
   { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] },
 PrettyFormat.Doc.concat
   (PrettyFormat.Doc.concat
     (PrettyFormat.Doc.text
       "Hello"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     (PrettyFormat.Doc.text
       "world"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
   (PrettyFormat.Doc.text "!" { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
   { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] },
 PrettyFormat.Doc.concat
   (PrettyFormat.Doc.concat
     (PrettyFormat.Doc.provide
       14
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
     (PrettyFormat.Doc.text
       "world"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
   (PrettyFormat.Doc.provide 6 { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
   { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] },
 PrettyFormat.Doc.concat
   (PrettyFormat.Doc.concat
     (PrettyFormat.Doc.provide
       14
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
     (PrettyFormat.Doc.text
       "world"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
   (PrettyFormat.Doc.text "!" { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
   { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] }]
-/
#guard_msgs in
#eval (expandDoc (("Hello"<^> provideDoc bridgeAny) <> "world" <> ("!"<^> provideDoc bridgeNl)) true )
/--
info: PrettyFormat.Doc.concat
  (PrettyFormat.Doc.concat
    (PrettyFormat.Doc.choice
      (PrettyFormat.Doc.text
        "Hello"
        { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
      (PrettyFormat.Doc.provide
        14
        { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
      { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
    (PrettyFormat.Doc.text
      "world"
      { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
    { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
  (PrettyFormat.Doc.choice
    (PrettyFormat.Doc.text
      "!"
      { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
    (PrettyFormat.Doc.provide
      6
      { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
    { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
  { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] }
-/
#guard_msgs in
#eval ((("Hello"<^> provideDoc bridgeAny) <> "world" <> ("!"<^> provideDoc bridgeNl)) )

/--
info: [PrettyFormat.Doc.concat
   (PrettyFormat.Doc.concat
     (PrettyFormat.Doc.text
       "nothing"
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
     (PrettyFormat.Doc.choice
       (PrettyFormat.Doc.provide
         14
         { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
       (PrettyFormat.Doc.provide
         8
         { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
       { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.no, paths := #[] })
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] })
   (PrettyFormat.Doc.text
     "to do"
     { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.yes, paths := #[] })
   { id := 0, cacheWeight := 0, collapsesBridges := PrettyFormat.Ternary.maybe, paths := #[] }]
-/
#guard_msgs in
#eval (expandDoc ("nothing" <> (provideDoc bridgeAny <^> provideDoc bridgeSpace)<> "to do") false )


/--
info: "((\"hey\") <> (provideDoc bridgeSpace)) <> (((((((\"l\") <> (provideDoc bridgeSpace)) <> (\"\"))<^>(((\"r\") <> (provideDoc bridgeNl)) <> (\"\"))\n) <> ((((\"a\") <> (provideDoc bridgeSpace)) <> (\"\"))<^>(((\"b\") <> (provideDoc bridgeNl)) <> (\"\"))\n)) <> (\"reset\")) <> ((\"no more\")<^>(\"branches\")\n))"
-/
#guard_msgs in
#eval ("hey" <_> (("l"<_>""<^> "r"<$$>"")) <> (("a"<_>""<^> "b"<$$>"")) <> "reset" <> ("no more"<^> "branches")).toString


/-- info: "((((\"l\") <> (provideDoc bridgeSpace)) <> (\"\")) <> (\"reset\")) <> (\"warning\")" -/
#guard_msgs in
#eval ((("l"<_>"")) <> "reset" <> "warning").toString

/--
info: "(((\"hey\") <> (provideDoc bridgeSpace)) <> (((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\"))) <> (\"final\")"
-/
#guard_msgs in
#eval (("hey" <_> (("hasValue"<$$>""))) <> "final").toString

/--
info: "((\"hey\") <> (provideDoc bridgeSpace)) <> ((((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\")) <> (\"final\"))"
-/
#guard_msgs in
#eval ("hey" <_> (("hasValue"<$$>"")) <> "final").toString




/--
info: "((\"hey\") <> (provideDoc bridgeSpace)) <> ((((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\"))<^>(((\"hasValue\") <> (provideDoc bridgeSpace)) <> (\"\"))\n)"
-/
#guard_msgs in
#eval ("hey" <_> (("hasValue"<$$>"") <^> ("hasValue" <_> ""))).toString


/--
info: "((\"hey\") <> (provideDoc bridgeSpace)) <> (((((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\"))<^>(((\"hasValue\") <> (provideDoc bridgeSpace)) <> (\"\"))\n) <> (\"later\"))"
-/
#guard_msgs in
#eval ("hey" <_> (("hasValue"<$$>"") <^> ("hasValue" <_> "")) <> "later").toString

/-- info: "(\"hello\") <> ((\"world\") <> (\"\"))" -/
#guard_msgs in
#eval ("hello" <> ("world" <> "")).toString

/--
info: "((\"hey\") <> (provideDoc bridgeSpace)) <> (((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\"))"
-/
#guard_msgs in
#eval ("hey" <_> (("hasValue"<$$>""))).toString

/--
info: "((((\"hey\") <> (provideDoc bridgeSpace)) <> (\"\")) <> (provideDoc bridgeSpace)) <> (((\"hasValue\") <> (provideDoc bridgeNl)) <> (\"\"))"
-/
#guard_msgs in
#eval ("hey" <_>"" <_> (("hasValue"<$$>""))).toString

/-- info: "((\"hey\") <> (provideDoc bridgeSpace)) <> (\"\")" -/
#guard_msgs in
#eval ("hey" <_> "").toString

/-- info: "((\"aaa\") <> (provideDoc bridgeImmediate)) <> (\"hello\")" -/
#guard_msgs in
#eval ("aaa" <> provideDoc bridgeImmediate <> "hello").toString

/--
info: "(ruleDoc \"hey\" \n (((flattenDoc (\"hey\"))<^>(\"b\")\n  ) <> (provideDoc bridgeHardNl)) \n) <> (\"hello\")"
-/
#guard_msgs in
#eval ((ruleDoc "hey" ((flattenDoc "hey" <^> "b") <> provideDoc bridgeHardNl)) <> "hello").toString

/--
info: "((ruleDoc \"a\" \n ((((\"1\") <> (provideDoc bridgeSpace)) <> (\"\"))<^>(((\"1b\") <> (provideDoc bridgeNl)) <> (\"\"))\n  ) \n) <> (ruleDoc \"b\" \n ((((\"2\") <> (provideDoc bridgeSpace)) <> (\"\"))<^>(((\"2b\") <> (provideDoc bridgeNl)) <> (\"\"))\n  ) \n)) <> (\"later\")"
-/
#guard_msgs in
#eval ((ruleDoc "a" ("1" <_> "" <^> "1b" <$$> "")) <> (ruleDoc "b" ("2" <_> "" <^> "2b" <$$> "")) <> "later").toString


-- def estimateBridge (b : List Bridge): Doc → List Bridge
--   | .fail _ m => []
--   | .text s m => b.map (fun b => bridgeAny)
--   | .newline _ m => b.map (fun b => bridgeAny)
--   | .choice l r m => {m with
--       leftBridge := l.meta.leftBridge ||| r.meta.leftBridge,
--       containsWhiteSpace := l.meta.containsWhiteSpace || r.meta.containsWhiteSpace,
--       shouldBeExpanded := l.meta.shouldBeExpanded || r.meta.shouldBeExpanded || l.meta.delayedProvide.isSome || r.meta.delayedProvide.isSome
--     }
--   | .flatten i m => {m with leftBridge := i.meta.leftBridge.flatten, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .align i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .nest _ i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .concat l r m => {m with
--     -- if the right side cannot be expanded then neither can the left side
--     leftBridge := if r.meta.leftBridge == bridgeNull then bridgeNull else l.meta.leftBridge,
--     shouldBeExpanded := r.meta.delayedProvide.isSome,
--     containsWhiteSpace := false, -- invariant: concat is never whitespace, it should have been combined to a single doc
--     delayedProvide := r.meta.delayedProvide
--     }
--   | .stx _ m => m
--   | .rule _ i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .reset i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .provide b i m => {m with leftBridge := i.meta.leftBridge.provideIntersection b, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded}
--   | .require b m => {m with leftBridge := b, containsWhiteSpace := false, shouldBeExpanded := m.delayedProvide.isSome, delayedProvide := m.delayedProvide}
--   | .bubbleComment _ i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
--   | .cost _ i m => {m with leftBridge := i.meta.leftBridge, containsWhiteSpace := i.meta.containsWhiteSpace, shouldBeExpanded := i.meta.shouldBeExpanded, delayedProvide := firstDelayed i.meta.delayedProvide m.delayedProvide}
-- where
--   flatten


#eval ("def:= " <_> nestDoc 4 ("funcName" <**> "helps") <**> "val").toString

end PrettyFormat


-- Dette virkede på antagelsen af at der ikke er syntax i mit træ...
