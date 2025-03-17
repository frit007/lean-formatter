import Std.Data.HashSet
open Std
/-
Originally created by Henrik Böving(https://github.com/hargoniX/pfmt) based on pretty expressive (https://arxiv.org/abs/2310.01530),
Frithjof added fail, endOfLineComment, and bubbleComment
-/
namespace Pfmt

/-
TODO list: nextcloud
-/

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
| fail
-- TODO: Think about adding the cost constructor. It does however make type inference much harder
-- TODO: Think about adding fail.
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
  /--
  Force the next character to be newline. If it is not then fail
  -/
  forcedNewLine : Bool
  /--

  -/
  startsWithNewLine : Bool
  /--
  -/
  fail: Bool
deriving Inhabited

instance [Cost χ] : LE (Measure χ) where
  le lhs rhs := lhs.last ≤ rhs.last ∧ lhs.cost ≤ rhs.cost

instance [Cost χ] [DecidableRel (LE.le (α := χ))] (lhs rhs : Measure χ) : Decidable (lhs ≤ rhs) :=
  inferInstanceAs (Decidable (lhs.last ≤ rhs.last ∧ lhs.cost ≤ rhs.cost))


def Measure.mkFail [Cost χ] (cost : χ ) : Measure χ := {last := 0, cost:=cost, layout := fun _ => panic! "We never want to print fail", forcedNewLine := false, startsWithNewLine := false, fail := true}

/--
Lifting `Doc.concat` to `Measure`.
-/
def Measure.concat [Cost χ] (lhs rhs : Measure χ) :Measure χ :=
  match lhs.fail || rhs.fail || (lhs.forcedNewLine && !rhs.startsWithNewLine) with
  | true => Measure.mkFail lhs.cost
  | _ => { last := rhs.last, cost := lhs.cost + rhs.cost, layout := fun ss => rhs.layout (lhs.layout ss), forcedNewLine := rhs.forcedNewLine, startsWithNewLine := lhs.startsWithNewLine, fail := false }


instance [Cost χ] : Append ((Measure χ)) where
  append := Measure.concat

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

/--
If `MeasureSet.merge` receives two `MeasureSet.set` we use this operation to combine them
into a new Pareto front with correct ordering.
-/
private partial def mergeSet [Cost χ] [DecidableRel (LE.le (α := χ))] (lhs rhs : List ((Measure χ))) (acc : List (Measure χ) := []) : List (Measure χ) :=
  match h1:lhs, h2:rhs with
  | [], _ => acc ++ rhs
  | _, [] => acc ++ lhs
  | l :: ls, r :: rs =>
    if l ≤ r then
      mergeSet lhs rs acc
    else if r ≤ l then
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
    let lhs' := lhs.filter (fun s => !s.fail)
    let rhs' := rhs.filter (fun s => !s.fail)
    .set (mergeSet lhs' rhs')



def placeCommentReverse (indent : Nat) (comment : String) : List String → List String
| []        => [comment, "\n", "".pushn ' ' indent]
| "\n" :: xs => "\n" :: comment :: "".pushn ' ' indent :: "\n" :: xs
| s :: xs    =>
  -- [toString (s :: xs)]
  -- reconstruct the indentation level
  let remainingCharacters := s.trimLeft.length
  let whiteSpaceCharacters := s.length - remainingCharacters
  let newIndentationLevel :=
    if remainingCharacters > 0 then
      whiteSpaceCharacters
    else
      whiteSpaceCharacters + indent
  s :: (placeCommentReverse newIndentationLevel comment xs)

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

/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.
-/
def Doc.resolve [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : Doc) (col indent widthLimit : Nat) : MeasureSet χ :=
  -- If we were to exceed the widthLimit we delay any attempt to optimize
  -- the layout of `doc` in hopes that another branch of this function finds
  -- a non tainted `MeasureSet`.
  let exceeds :=
    match doc with
    | .text s => indent > widthLimit || col + s.length > widthLimit
    | _ => indent > widthLimit || col > widthLimit
  if exceeds then
    .tainted (fun _ =>
      match core doc col indent with
      | .tainted m => m ()
      | .set (m :: _) => m
      | .set [] => panic! "Empty measure sets are impossible"
    )
  else
    core doc col indent
where
  /--
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (doc : Doc) (col : Nat) (indent : Nat) : MeasureSet χ :=
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match doc with
    | .text s =>
      .set [{
        last := col + s.length,
        cost := Cost.text widthLimit col s.length
        layout := fun ss => s :: ss
        startsWithNewLine := s.startsWith "\n"
        forcedNewLine := false
        fail := false
      }]
    | .newline _ =>
      .set [{
        last := indent,
        cost := Cost.nl indent,
        layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
        startsWithNewLine := true
        forcedNewLine := false
        fail := false
      }]
    | .concat lhs rhs => processConcat (fun l => core rhs l.last indent) (core lhs col indent)
    | .choice lhs rhs => MeasureSet.merge (core lhs col indent) (core rhs col indent)
    | .nest indentOffset doc => core doc col (indent + indentOffset)
    | .align doc => core doc col col
    | .reset doc => core doc col 0
    | .bubbleComment comment => .set [{
      last := col
      -- prioritize placing comments where they were placed by the user
      cost := (Cost.text widthLimit (indent + widthLimit) comment.length) + Cost.nl indent
      layout := placeComment 0 comment
      forcedNewLine := false
      startsWithNewLine := false
      fail := false
    }]
    | .endOfLineComment comment => .set [{
      last := col + comment.length
      cost := Cost.nl indent
      layout := (fun ss => comment :: ss)
      forcedNewLine := true
      startsWithNewLine := false
      fail := false
    }]
    | .fail => .set [{
      last := 0
      cost := Cost.nl indent
      layout := (fun ss => ss)
      forcedNewLine := false
      startsWithNewLine := false
      fail := true
    }]

  /--
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcat (processLeft : Measure χ → MeasureSet χ) (leftSet : MeasureSet χ) : MeasureSet χ :=
    match leftSet with
    | .tainted leftThunk =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.
      .tainted (fun _ =>
        let left := leftThunk ()
        match processLeft left with
        | .tainted rightThunk => left ++ rightThunk ()
        | .set (right :: _) => left ++ right
        | .set [] => panic! "Empty measure sets are impossible"
      )
    | .set lefts =>
       let concatOneWithRight (l : Measure χ) : MeasureSet χ :=
         -- This is an optimized version of dedup from the paper. We use it to maintain
         -- the Pareto front invariant.
         let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
           match rights with
           | [] => List.reverse (currentBest :: result)
           | r :: rights =>
             let current := l ++ r
             if current.cost ≤ currentBest.cost then
               dedup rights result current
             else
               dedup rights (currentBest :: result) current
         match processLeft l with
         | .tainted rightThunk => .tainted (fun _ => l ++ rightThunk ())
         | .set (r :: rights) => .set (dedup rights [] (l ++ r))
         | .set [] => panic! "Empty measure sets are impossible"

       let rec concatAllWithRight (lefts : List (Measure χ)) : MeasureSet χ :=
         match lefts with
         | [] => panic! "Empty measure sets are impossible"
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
    | .fail => panic! "A choice less document does not allow fail"

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
  {
    layout := String.join (measure.layout []).reverse,
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
  | .fail => .fail

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

#eval
  let argD := (.nl ++ .text "arg1" ++ .nl ++ .text "arg2")
  let d :=
    .text "let ident :=" ++
    (
     (.space ++ .text "func" ++ .flatten argD)
     <|||>
     (.nest 2 (.nl ++ .text "func" ++ (.nest 2 argD)))
    )
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
  IO.println out

end Pfmt
