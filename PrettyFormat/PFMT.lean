import Std.Data.HashSet
open Std
/-
Originally created by Henrik Böving() based on pretty expressive (https://arxiv.org/abs/2310.01530),
Frithjof added fail, endOfLineComment, and bubbleComment
-/
namespace Pfmt

/-
TODO list: nextcloud
-/

abbrev Bridge := UInt32

def bridgeEmpty :Bridge := 0
def bridgeFlex :Bridge := 1
def bridgeNl :Bridge := 2
def bridgeHardNl :Bridge := 4
def bridgeSpace :Bridge := 8
def bridgeImmediate :Bridge := 16

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
| text (s : String)
/--
Render a newline. Also contains an alternative rendering for the newline for `Doc.flatten`.
-/
| newline (s : String)
/--
Concatenate two documents unaligned. If `l` is the chars that we get from `lhs`
and `r` from `rhs` they will render as:
```
llllllllll
lllllrrrrrrrr
rrrrrr
```
-/
| concat (lhs rhs : Doc)
/--
Render `doc` width the indentation level increased by `nesting`.
-/
| nest (nesting : Nat) (doc : Doc)
/--
Render `doc` with the indentation level set to the column position.
-/
| align (doc : Doc)
/--
Make a choice between rendering either `lhs` or `rhs` by picking the prettier variant.
If one of the sides `fail`, then other side is chosen. If both sides `fail`, then the result is also `fail`
-/
| choice (lhs rhs : Doc)

/--
Reset the indentation level to 0.
-/
| reset (doc : Doc)
/--
The comment will be placed after the last newline before this line
-/
| bubbleComment (comment : String)
/--
These comments have been placed at the end of the line
This is enforced by failing any document, where the next character is not a newLine

Technically we know that these comments are legal syntax, because we were able to parse the document
But to follow the style of the library author we will only allow the comment if a newline is possible
The main reason for this is to respect the decision made by flatten. The intended use is to combine both comments (bubbleComment c <^> endOfLineComment c)
-/
| endOfLineComment (comment : String)
/--
Fail will never be rendered.
This error will propagate until the next choice, where branches containing errors are eliminated.
-/
| fail (err : String)
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
| provide (spacing : Bridge)
/--
expect must be preceded by a `provide` and will fail if the provided spacing does not contain the expected spacing
-/
| expect (spacing : Bridge)
-- TODO: Think about adding the cost constructor. It does however make type inference much harder
| rule (r : String) (doc : Doc)
deriving Inhabited, Repr

instance : Append Doc where
  append lhs rhs := .concat lhs rhs

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


instance : BEq (HashSet String) where
  beq s1 s2 := s1.toList == s2.toList  -- Compare by list representation

instance : BEq (Option (HashSet String)) where
  beq
    | some s1, some s2 => s1 == s2
    | none, none => true
    | _, _ => false

set_option diagnostics true

instance : Hashable (HashSet String) where
  hash s := s.toList.foldl (fun acc x => mixHash acc (hash x)) 0

def Bridge.subset (l r: Bridge) : Bool :=
  l &&& r == r

def Bridge.contains (l r: Bridge) : Bool :=
  l &&& r == l

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

def spacing (s : Bridge) : Doc := Doc.provide (s)
def expect (s : Bridge) : Doc := Doc.expect (s)


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


-- instance [Cost χ] : Append ((Measure χ)) where
--   append := Measure.concat
/--
A set of `Measure`s out of which we will pick an optimal `Doc` in the end.
-/
inductive MeasureSet (χ : Type) where
/--
If a branch of the rendering process would end up producing only invalid documents
it produces a `MeasureSet.tainted`. It consists of a thunk that we can evaluate
to a `Measure` if we end up finding no way to produce a valid document.
-/
| tainted (m : Unit → Measure χ)
/--
A list of `Measure`s that form a Pareto front for our rendering problem.
This list is ordered by the last line length in strict ascending order.
-/
| set (ms : List (Measure χ))
deriving Inhabited

structure MeasureGroup (χ : Type) where
  bridge: Bridge
  set: MeasureSet χ
deriving Inhabited

abbrev MeasureGroups (χ : Type) := List (MeasureGroup χ)


-- Can it be a bitmask?
-- intersection lhs rhs
-- lhs & rhs
-- subset lhs rhs
-- lhs & rhs == rhs

-- any 1 (In this case it is not allowed to have overlap with any other spacing option, )
-- space 2
-- hardNl 4
-- spaceNl 8
-- immediateValue 16
-- nospace 32 (might be useful in the case of parenthesis, but they should probably prefer any, since if their counterpart allows no space then it will be chosen)

/--
If `MeasureSet.merge` receives two `MeasureSet.set` we use this operation to combine them
into a new Pareto front with correct ordering.
-/
private partial def mergeSet [Cost χ] [DecidableRel (LE.le (α := χ))] (lhs rhs : List ((Measure χ))) (acc : List (Measure χ) := []) : List (Measure χ) :=
  match h1:lhs, h2:rhs with
  | [], _ => acc.reverse ++ rhs
  | _, [] => acc.reverse ++ lhs
  | l :: ls, r :: rs =>
    -- TODO: We do not have to compare bridge here because we know that they have the same bridge
    if l ≤ r && l.spacingR.lessThan r.spacingR then
      mergeSet lhs rs acc
    else if r ≤ l && r.spacingR.lessThan l.spacingR then
      mergeSet ls rhs acc
    else if l.last > r.last then
      mergeSet ls rhs (l :: acc)
    else
      mergeSet lhs rs (r :: acc)


/--
Combine the results from two `MeasureSet`s.
-/
def MeasureSet.merge [Cost χ] [DecidableRel (LE.le (α := χ))] (lhs rhs : MeasureSet χ) : MeasureSet χ :=
  match lhs, rhs with
  | _, .tainted .. => lhs
  | .tainted .., _ => rhs
  | .set lhs, .set rhs =>
    let lhs' := lhs.filter (fun s => s.fail.isNone)
    let rhs' := rhs.filter (fun s => s.fail.isNone)
    if (lhs'.length == 0 && rhs'.length == 0) then
      let addErrors (acc:List (List String)) (x:Measure χ):=
        match x.fail with
        | .some a => a++acc
        | .none => acc

      .set [Measure.mkFail (Cost.text 0 0 0) (lhs.foldl addErrors <| rhs.foldl addErrors [])]
    else
      .set (mergeSet lhs' rhs')

def MeasureSet.getSet! [Cost χ] [DecidableRel (LE.le (α := χ))] (m : MeasureSet χ) : List (Measure χ) :=
  match m with
  | .set s => s
  | .tainted _ => panic! "Cannot get tainted set"



-- def placeCommentReverse (indent : Nat) (comment : String) : List String → List String
-- | []        => [comment, "\n", "".pushn ' ' indent]
-- | "\n" :: xs => "\n" :: comment :: "".pushn ' ' indent :: "\n" :: xs
-- | s :: xs    =>
--   -- [toString (s :: xs)]
--   -- reconstruct the indentation level
--   let remainingCharacters := s.trimLeft.length
--   let whiteSpaceCharacters := s.length - remainingCharacters
--   let newIndentationLevel :=
--     if remainingCharacters > 0 then
--       whiteSpaceCharacters
--     else
--       whiteSpaceCharacters + indent
--   s :: (placeCommentReverse newIndentationLevel comment xs)

def placeComment (indent : Nat) (comment : String) : List String → List String
-- | a => (placeCommentReverse indent comment a.reverse).reverse
| []        => ["\n", comment, "".pushn ' ' indent]
| "\n" :: xs => "\n" :: comment :: "".pushn ' ' indent :: "\n" :: xs
| s :: xs    =>
  -- reconstruct the indentation level
  let remainingCharacters := s.trimLeft.length
  let whiteSpaceCharacters := s.length - remainingCharacters
  let newIndentationLevel :=
    if remainingCharacters > 0 then
      whiteSpaceCharacters
    else
      whiteSpaceCharacters + indent
  s :: (placeComment newIndentationLevel comment xs)

def removeMeasureFails (m : MeasureSet χ): MeasureSet χ:=
  match m with
  | .set xs =>
    .set (xs.filter (fun x => x.fail.isNone))
  | x => x

/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : Doc) (col indent widthLimit : Nat) : MeasureSet χ :=
  -- If we were to exceed the widthLimit we delay any attempt to optimize
  -- the layout of `doc` in hopes that another branch of this function finds
  -- a non tainted `MeasureSet`.
  let exceeds :=
    match doc with
    | .text s => indent > widthLimit || col + s.length > widthLimit
    | _ => indent > widthLimit || col > widthLimit
  if exceeds then
    .tainted (fun _ =>
      match core doc [] col indent bridgeFlex with
      | .tainted m => m ()
      | .set (m :: _) => m
      | .set [] => panic! "Empty measure sets are impossible"
    )
  else
    core doc [] col indent bridgeFlex
where
  /--
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (doc : Doc) (trace : List String) (col : Nat) (indent : Nat) (spacing : Bridge): MeasureSet χ :=
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match doc with
    | .text s =>
      if s.length == 0 then
        .set [{
          last := col + s.length,
          cost := Cost.text widthLimit col s.length
          layout := fun ss => s :: ss
          spacingR := spacing
        }]
      else
        if spacing == bridgeFlex then
          .set [{
            last := col + s.length,
            cost := Cost.text widthLimit col s.length
            layout := fun ss => s :: ss
            spacingR := bridgeFlex
          }]
        else
          core (concat (possibilitiesToDoc spacing) (.text s)) trace col indent bridgeFlex
          -- core ( .concat (.choice (.text "s") (.text "what")) (.text s)) trace col indent bridgeFlex

    | .newline _ =>
      if spacing == bridgeFlex then
        .set [{
          last := indent,
          cost := Cost.nl indent,
          layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
          spacingR := bridgeFlex
        }]
      else
        core (concat (possibilitiesToDoc (spacing)) (.newline " ")) trace col indent bridgeFlex

      -- match spacing with
      -- | some leftSpacing =>
      --   let possibilities := bridgeIntersection leftSpacing (spaceNl ||| spaceHardNl)
      --   if possibilities.isEmpty then
      --     core (.fail "no options newline") trace col indent spacing
      --   else
      --     .set [{
      --       last := indent,
      --       cost := Cost.text widthLimit col 0,
      --       layout := fun ss => ss
      --       spacingR := possibilities
      --     }]
      -- | none =>
      --   .set [{
      --     last := indent,
      --     cost := Cost.nl indent,
      --     layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
      --     spacingR := none
      --   }]
    | .concat lhs rhs => processConcat (core lhs trace col indent spacing) trace (fun l newSpacing => core rhs trace l.last indent newSpacing)
    | .choice lhs rhs => MeasureSet.merge (core lhs trace col indent spacing) (core rhs trace col indent spacing)
    | .nest indentOffset doc => core doc trace col (indent + indentOffset) spacing
    | .align doc => core doc trace col col spacing
    | .reset doc => core doc trace col 0 spacing
    | .bubbleComment comment => .set [{
      last := col
      -- prioritize placing comments where they were placed by the user
      cost := (Cost.text widthLimit (indent + widthLimit) comment.length) + Cost.nl indent
      layout := placeComment 0 comment
    }]
    | .endOfLineComment comment => .set [{
      last := col + comment.length
      cost := Cost.nl indent
      layout := (fun ss => comment :: ss)
      spacingR := bridgeHardNl ||| bridgeNl
    }]
    | .fail e => .set [{
      last := 0
      cost := Cost.nl indent
      layout := (fun _ => ["fail"])
      fail := [e::trace]
    }]
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provide s =>
      if spacing == bridgeFlex then
        .set [{
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := s
        }]
      else
        let possibilities := spacing.intersection s
        .set [{
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := possibilities
        }]

    | .expect s =>
      if spacing == bridgeFlex then
        core (.fail "no expect overlap") trace col indent bridgeFlex
      else
        let possibilities := spacing.intersection s
        let choices := possibilitiesToDoc possibilities
        core choices trace col indent bridgeFlex
      | .rule s doc =>
        core doc (s::trace) col indent spacing


  possibilitiesToDoc (possibilities : Bridge) : Doc :=
    if possibilities == 0 then
      .fail "No possibilities"
    else Id.run do
      let mut options : List (Doc) := [.newline " "]
      -- let list := possibilities.toList

      -- if bridgeContains possibilities bridgeNl || bridgeContains possibilities bridgeHardNl then
      --   options := .newline " "::options
      -- -- In any other case we we let the child handle the separation
      -- if bridgeContains possibilities bridgeSpace then
      --   options := .text " "::options

      -- -- if possibilities.any (fun f => f != space && f != spaceNl && f != spaceHardNl) then
      -- if possibilities.erase (bridgeSpace ||| bridgeNl ||| bridgeHardNl) != 0 then
      --   options := (text "")::options

      let choices := options.tail.foldl (fun acc doc => Doc.choice acc doc) (options.head!)
      return choices

  impossibleMeasure (trace: List String): Measure χ := {
      last := indent,
      cost := Cost.nl indent + Cost.nl indent + Cost.nl indent,
      layout := fun ss => "(no possible formatter)" :: "\n" :: ss
      spacingR := bridgeFlex
      fail := ["impossible"::trace]
    }

  /--
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/

  processConcat (leftSet : MeasureSet χ) (trace : List String)(processRight : Measure χ → Bridge → MeasureSet χ) : MeasureSet χ :=
    match leftSet with
    | .tainted leftThunk =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.

      .tainted (fun _ =>
        let left := leftThunk ()
        match processRight left (left.spacingR) with
        | .tainted rightThunk => left.concat (rightThunk ())
        | .set (right :: _) => left.concat right
        | .set [] => impossibleMeasure trace
      )
    | .set lefts =>
      let concatOneWithRight (l : Measure χ) : MeasureSet χ :=
         -- This is an optimized version of dedup from the paper. We use it to maintain
         -- the Pareto front invariant.
        -- let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
        --   match rights with
        --   | [] => List.reverse (currentBest :: result)
        --   | r :: rights =>
        --     let current := l.concat r
        --     if current.cost ≤ currentBest.cost then
        --       -- if the cost is less than or equal, then this should be a part of the result
        --       dedup rights result current
        --     else
        --       dedup rights (currentBest :: result) current

        let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
          match rights with
          | [] => List.reverse (currentBest :: result)
          | r :: rights =>
            let current := l.concat r
            -- TODO: It should not be necessary to check spacing here
            if current.cost ≤ currentBest.cost && current.spacingR.lessThan currentBest.spacingR then
              -- if the cost is less than or equal, then this should be a part of the result
              dedup rights (result) current
            else
              dedup rights (currentBest :: result) current

        let rights := processRight l (l.spacingR)
        match rights |> removeMeasureFails with
        | .tainted rightThunk => .tainted (fun _ => l.concat (rightThunk ()))
        -- | .set (rights) => .set (rights.map (fun r => l.concat r))
        | .set (r :: rights) => .set (dedup rights [] (l.concat r))
        | .set [] => .set [{impossibleMeasure trace with fail := some (rights.getSet!.foldl (
            fun acc (a:Measure χ) =>
            match a.fail with
            | none => acc
            | some err => acc ++ err) [])}]

      let rec concatAllWithRight (lefts : List (Measure χ)) : MeasureSet χ :=
        match lefts |>.filter (fun x => x.fail.isNone) with
        | [] => .set [{impossibleMeasure trace with fail := some (lefts.foldl (
            fun acc (a:Measure χ) =>
            match a.fail with
            | none => acc
            | some err => acc ++ err) [])}]
        | [l] => concatOneWithRight l
        | l :: ls => MeasureSet.merge (concatOneWithRight l) (concatAllWithRight ls)

      concatAllWithRight lefts

structure PrintResult (χ : Type) where
  layout : String
  isTainted : Bool
  cost : χ
deriving Inhabited

/--
Render a choice less `Doc`. For choiceful documents use `Doc.prettyPrint`.
-/
-- def Doc.render (doc : Doc) (col : Nat) : String :=
--   String.intercalate "\n" (go doc col 0).toList
-- where
--   /--
--   A straight forward implementation of the choice less document semantics from Fig 8.
--   -/
--   go (doc : Doc) (col indent : Nat) : Array String := Id.run do
--     match doc with
--     | .text str => #[str]
--     | .newline _ => #["", "".pushn ' ' indent]
--     | .align doc => go doc col col
--     | .nest indentOffset doc => go doc col (indent + indentOffset)
--     | .concat lhs rhs =>
--       let mut lrender := go lhs col indent
--       if lrender.size == 1 then
--         let lfirst := lrender[0]!
--         let mut rrender := go rhs (col + lfirst.length) indent
--         let rfirst := rrender[0]!
--         rrender := rrender.set! 0 (lfirst ++ rfirst)
--         rrender
--       else
--         let llast := lrender[lrender.size - 1]!
--         let rrender := go rhs (llast.length) indent
--         let rfirst := rrender[0]!
--         lrender := lrender.set! (lrender.size - 1) (llast ++ rfirst)
--         lrender := lrender ++ rrender[0:(rrender.size - 1)]
--         lrender
--     | .reset doc => go doc col 0
--     | .choice .. => panic! "Not a choice less document"
--     | .endOfLineComment comment => #[comment]
--     | .bubbleComment comment => #[comment]
--     | .fail => panic! "A choice less document does not allow fail"
def Doc.render (doc : Doc) (col : Nat) : String :=
  String.join (go doc col 0 []).reverse
where
  /--
  A straight forward implementation of the choice less document semantics from Fig 8.
  -/
  go (doc : Doc) (col indent : Nat) (prev : List String): List String := Id.run do
    match doc with
    | .text str =>
      str :: prev
    | .newline _ => "".pushn ' ' indent :: "\n" :: prev
    | .align doc => go doc col col prev
    | .nest indentOffset doc => go doc col (indent + indentOffset) @ prev
    | .concat lhs rhs =>
      let mut lrender := go lhs col indent prev
      go rhs (lineLength lrender) indent lrender
      -- if lrender.length == 1 then
      --   let lfirst := lrender[0]!
      --   let mut rrender := go rhs (col + lfirst.length) indent
      --   let rfirst := rrender[0]!
      --   rrender := rrender.set! 0 (lfirst ++ rfirst)
      --   rrender
      -- else
      --   let llast := lrender[lrender.size - 1]!
      --   let rrender := go rhs (llast.length) indent
      --   let rfirst := rrender[0]!
      --   lrender := lrender.set! (lrender.size - 1) (llast ++ rfirst)
      --   lrender := lrender ++ rrender[0:(rrender.size - 1)]
      --   lrender
    | .reset doc => go doc col 0 prev
    | .choice .. => panic! "Not a choice less document"
    | .endOfLineComment comment => comment :: prev
    | .bubbleComment comment => placeComment 0 comment prev
    | .fail e => panic! "A choice less document does not allow fail"
    | .provide s => [toString s] ++ prev
    | .expect s => [toString s] ++ prev
    | .rule _ doc =>
        go doc col indent prev

  lineLength : List String → Nat
    | [] => 0
    | "\n"::_ => 0
    | x :: xs => x.length + lineLength xs


/--
Find an optimal layout for a document and render it.
-/
def Doc.print (χ : Type) [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : Doc) (col widthLimit : Nat) : PrintResult χ :=
  let measures := doc.resolve (χ := χ) col 0 widthLimit
  let (measure, isTainted) :=
    match measures with
    | .tainted thunk => (thunk (), true)
    | .set (measure :: _) => (measure, false)
    | .set [] => panic! "Empty measure sets are impossible"
        let c :=match measures with
    | .tainted _ => 0
    | .set a => a.length
  match measure.fail with
  | none =>
    {
      layout := String.join (measure.layout []).reverse,
      isTainted := isTainted,
      cost := measure.cost
    }
  | some failure =>
    let sorted := failure.mergeSort (fun a b => a.length < b.length)
    let x := sorted.foldl (fun (acc: String) (errs:List String) => acc ++ "\n" ++ (String.intercalate "::" errs.reverse)) ""
    {
      layout := if x.trim.length == 0 then s!"(unknown failure {isTainted} c {c})" else x,
      -- layout := "definite error",
      isTainted := isTainted,
      cost := measure.cost
    }

/--
Find an optimal layout for a document and render it.
-/
def Doc.prettyPrint (χ : Type) [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : Doc) (col widthLimit : Nat) : String :=
  Doc.print χ doc col widthLimit |>.layout

def Doc.comma : Doc := .text ","
def Doc.lbrack : Doc := .text "["
def Doc.rbrack : Doc := .text "]"
def Doc.lbrace : Doc := .text "{"
def Doc.rbrace : Doc := .text "}"
def Doc.lparen : Doc := .text "("
def Doc.rparen : Doc := .text ")"
def Doc.dquote : Doc := .text "\""
def Doc.empty : Doc := .text ""
def Doc.space : Doc := .text " "
def Doc.nl : Doc := .newline " "
def Doc.break : Doc := .newline ""
-- TODO: hard_nl and definitions based on it if necessary

/--
Replace all newlines in the `Doc` with their flat string.
-/
def Doc.flatten (doc : Doc) : Doc :=
  match doc with
  | .text str => .text str
  | .newline s => .text s
  | .align doc | .reset doc | .nest _ doc => doc.flatten
  | .concat lhs rhs => .concat lhs.flatten rhs.flatten
  | .choice lhs rhs => .choice lhs.flatten rhs.flatten
  | .bubbleComment comment => .bubbleComment comment
  /-
  This does not instantly fail, because the following document allows a endOfLineComment embedded in a flatten section
  `flatten (text "content" <> endOfLineComment comment) <> nl`
  -/
  | .endOfLineComment comment => .endOfLineComment comment
  | .fail e => .fail e
  | .provide s =>
    let s := s.erase bridgeHardNl
    let s := if s.contains bridgeNl then s.erase bridgeNl|>.union bridgeSpace else s
    if s.isEmpty then
      .fail "Provide Flattened to nothing"
    else
      .provide s
  | .expect s =>
    let s := s.erase bridgeHardNl
    let s := if s.contains bridgeNl then s.erase bridgeNl|>.union bridgeSpace else s
    if s.isEmpty then
      .fail "Expect flattened to nothing"
    else
      .expect s
  | .rule s doc => .rule s doc.flatten

/--
Lay out a `Doc` or its `Doc.flatten`ed version.
-/
def Doc.group (doc : Doc) : Doc := .choice doc doc.flatten

/--
Aligned concatenation, joins two sub-layouts horizontally, aligning the whole right sub-layout at the
column where it is to be placed in. Aka the `<+>` operator.
-/
def Doc.alignedConcat (lhs rhs : Doc) : Doc := lhs ++ .align rhs
/--
TODO: Better name
-/
def Doc.flattenedAlignedConcat (lhs rhs : Doc) : Doc := .alignedConcat (.flatten lhs) rhs

def Doc.fold (f : Doc → Doc → Doc) (ds : List Doc) : Doc :=
  match ds with
  | [] => empty
  | x :: xs => List.foldl f x xs

/--
Lay out a list of `Doc`s line by line. Aka `vcat`.
-/
def Doc.lines (ds : List Doc) : Doc := Doc.fold (· ++ .nl ++ ·) ds
def Doc.hcat (ds : List Doc) : Doc := Doc.fold .flattenedAlignedConcat ds

-- TODO: See how we can get some nicer choice operator
@[inherit_doc] scoped infixl:65 " <|||> "  => Doc.choice
@[inherit_doc] scoped infixl:65 " <+> "  => Doc.alignedConcat
@[inherit_doc] scoped infixl:65 " <-> "  => Doc.flattenedAlignedConcat

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

-- #eval
--   let argD := (.nl ++ .text "arg1" ++ .nl ++ .text "arg2")
--   let d :=
--     .text "let ident :=" ++
--     (
--      (.space ++ .text "func" ++ .flatten argD)
--      <|||>
--      (.nest 2 (.nl ++ .text "func" ++ (.nest 2 argD)))
--     )
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   IO.println out

#eval
  let d := Doc.concat (.provide bridgeHardNl) (.text "simple")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  IO.println out

-- #eval (DefaultCost.le (DefaultCost.nl 3) (DefaultCost.text 100 2 0))
-- #eval (DefaultCost.le (DefaultCost.text 100 2 0) (DefaultCost.nl 3))

-- #eval (DefaultCost.add (DefaultCost.text 100 2 0) (DefaultCost.nl 3))
-- #eval (DefaultCost.add (DefaultCost.nl 3) (DefaultCost.nl 3))

end Pfmt
