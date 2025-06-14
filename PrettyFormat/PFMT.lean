import Std.Data.HashSet
import Doc

open Std

/-
Based on the PFMT created by Henrik Böving(https://github.com/hargoniX/pfmt) and based on pretty expressive (https://arxiv.org/abs/2310.01530),
-/
namespace PrettyFormat

/--
If `MeasureSet.merge` receives two `MeasureSet.set` we use this operation to combine them
into a new Pareto front with correct ordering.
-/
private def mergeSet [Cost χ] (lhs rhs : List ((Measure χ))) (acc : List (Measure χ) := []) : List (Measure χ) :=
  match h1:lhs, h2:rhs with
  | [], _ => acc.reverse ++ rhs
  | _, [] => acc.reverse ++ lhs
  | l :: ls, r :: rs =>
    if LEB.leq l r then
      mergeSet lhs rs acc
    else if LEB.leq r l then
      mergeSet ls rhs acc
    else if l.last > r.last then
      mergeSet ls rhs (l :: acc)
    else
      mergeSet lhs rs (r :: acc)
termination_by lhs.length + rhs.length

def enableDebugging := false

structure FlattenState where
  nextId : Nat
  cached : Std.HashMap (Nat × Bool × Bool) Doc

abbrev FlattenStateM a := (StateM FlattenState) a


def FlattenStateM.genId : FlattenStateM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId

@[inline] def leafSet [Inhabited χ] [Cost χ] (m : Measure χ): MeasureResult χ (MeasureSet χ) :=
  return .set [m]

/--
Combine the results from two `MeasureSet`s.
-/
def MeasureSet.merge [Cost χ] (left right : MeasureSet χ) : MeasureSet χ :=
  match left, right with
  | set lhs, set rhs =>
    let lhs' := lhs.filter (fun s => !s.fail)
    let rhs' := rhs.filter (fun s => !s.fail)

    if (lhs'.length == 0 && rhs'.length == 0) then
      left
    else
      if lhs'.length != lhs.length then
        let l := lhs.filter (fun s => s.fail) |>.map (fun x => x.layout [])
        dbg_trace s!"lhs contained failure {l}"
        .set (mergeSet lhs' rhs')
      else if rhs'.length != rhs.length then
        let r := rhs.filter (fun s => s.fail) |>.map (fun x => x.layout [])
        dbg_trace s!"rhs contained failure {r}"
        .set (mergeSet lhs' rhs')
      else
        .set (mergeSet lhs' rhs')
  | _, .tainted _ => left
  | .tainted _, _ => right


def placeComment (indent : Nat) (comment : String) : List String → List String
| []        => ["\n", comment, "".pushn ' ' indent]
| "\n" :: xs => "\n" :: comment :: "".pushn ' ' indent :: "\n" :: xs
| s :: xs    =>
  -- reconstruct the indentation level so we can match it
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

leftBridge: the bridges before this document, these limit the types of documents we can create
rightBridge: the bridges after this document, these are the bridges that will be followed by leafNodes, they are created by provideR
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [Repr χ] (doc : Doc) (col indent widthLimit computationWidth : Nat): MeasureResult χ (MeasureSet χ) := do
  if doc.meta.shouldBeCached then
    let key := createKey col indent
    match (← get).content[doc.meta.id]!.find? key with
    | .found ms =>
      return ms
    | .miss index =>
      let value ← core doc
      let _ ← modify (fun cacheStore => {
        cacheStore with
        content := cacheStore.content.modify doc.meta.id (fun cacheArr => cacheArr.insertIdx! index {key:=key, result:=value})
        })
      -- addToCache doc.meta.id indent col leftBridge rightBridge flatten value
      return value
  else
    core doc
where
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (doc : Doc)  : MeasureResult χ (MeasureSet χ) := do
    match doc with
    | .text s _ =>
      if s.length == 0 then
        leafSet {
          last := col + s.length,
          cost := Cost.text widthLimit col s.length
          layout := fun ss => s :: ss
        }
      else
        let measure: Measure χ := {
            last := col + s.length,
            cost := Cost.text widthLimit col s.length
            layout := fun ss => s :: ss
          }
        if measure.last <= computationWidth then
          return .set [measure]
        else
          return .tainted (TaintedTrunk.value measure)

    | .newline flattened _ =>
      leafSet {
          last := indent,
          cost := Cost.nl,
          layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss,
        }
    | .concat lhs rhs m =>
      -- measureDiff "before calc concat"


      let left ← (lhs.resolve col indent widthLimit computationWidth)
      let taintedState : TaintedState := {col:=col, indent:=indent, widthLimit:=widthLimit, computationWidth := computationWidth}
      processConcat left rhs taintedState m.id
    | .choice lhs rhs _ => do
      -- let leftHasSolution := (lhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)

      let left ← (lhs.resolve col indent widthLimit computationWidth)
      let right ← (rhs.resolve col indent widthLimit computationWidth)
      if rhs.meta.nlCount < lhs.meta.nlCount then
        return left.merge right
      else
        return right.merge left
    | .nest indentOffset doc _ => doc.resolve col (indent + indentOffset) widthLimit computationWidth
    | .align doc _ => doc.resolve col col widthLimit computationWidth
    | .reset doc _ => doc.resolve col 0 widthLimit computationWidth

    | .rule _ doc _ =>
      doc.resolve col indent widthLimit computationWidth
    | .flatten inner _ =>
      inner.resolve col indent widthLimit computationWidth
    | .stx _ _ =>
      panic! "Syntax should be expanded before reaching this point"
    | .cost c _ =>
      let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
      leafSet {
        cost := lineCost,
        last := col,
        layout := id
      }
    | .bubbleComment comment _ =>
      leafSet {
        cost := Cost.text 0 0 0,
        last := col,
        layout := placeComment indent comment
      }

  /-
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcat (left : MeasureSet χ) (right : Doc) (state: TaintedState) (concatId : Nat): MeasureResult χ (MeasureSet χ) := do
    match left with
    | .tainted leftThunk =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.
      -- dbg_trace s!"tainted lb{state.leftBridge} rb{state.rightBridge}"
      return .tainted (TaintedTrunk.leftTainted leftThunk right state concatId)
    | .set lefts =>
      let concatOneWithRight (l : Measure χ) : MeasureResult χ (MeasureSet χ) := do
        -- This is an optimized version of dedup from the paper. We use it to maintain
        -- the Pareto front invariant.
        -- TODO: is it faster to not declare the function every time?
        let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
          match rights with
          | [] => List.reverse (currentBest :: result)
          | r :: rights =>
            let current := l.concat r
            if LEB.leq current.cost currentBest.cost then
              dedup rights result current
            else
              dedup rights (currentBest :: result) current

        match ← (right.resolve l.last state.indent widthLimit computationWidth) with
        | .tainted rightThunk => return .tainted (TaintedTrunk.rightTainted l rightThunk state concatId)
        | .set (r :: rights) => return .set (dedup rights [] (l.concat r))
        | .set [] =>
          dbg_trace "concat::no right solution"
          return impossibleMeasureSet "concat::no right solution"

      let rec concatAllWithRight  : List (Measure χ) →  MeasureResult χ (MeasureSet χ)
         | [] =>
            dbg_trace "concat::no left solution"
           return impossibleMeasureSet "concat::no left solution"
         | [l] => concatOneWithRight l

         | l :: ls => do return (← concatOneWithRight l).merge (← concatAllWithRight ls)
      concatAllWithRight lefts

partial def expandTainted [Inhabited χ] [Repr χ] [Cost χ] (trunk :TaintedTrunk χ): MeasureResult χ (Measure χ) := do
    expandTainted' trunk
  where
  expandTainted' : TaintedTrunk χ → MeasureResult χ (Measure χ)
  | .leftTainted (left : (TaintedTrunk χ)) (right:Doc) (state:TaintedState) (_:Nat) => do
    let leftMeasure ← expandTainted left
    let r ← right.resolve leftMeasure.last state.indent state.widthLimit state.computationWidth
    match r with
    | .tainted t => return leftMeasure.concat (← expandTainted t)
    | .set (m::_) => return leftMeasure.concat m
    | _ => return impossibleMeasure "tainted::no right solution"
  | .rightTainted left right _ _ => do
    let r ← expandTainted right
    return left.concat r
  | .value m => do
    return m

structure PrintResult (χ : Type) where
  layout : String
  isTainted : Bool
  cost : χ
deriving Inhabited

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.print (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat): (PrintResult χ) := Id.run do
  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) col 0 widthLimit computationWidth).run (initCache cacheSize ))

  match preferredGroups with
  | .set ([]) =>
    return {
      layout := "No solution found",
      isTainted := false,
      cost := Cost.text 0 0 0
    }
  | .set (m::_) =>
    return {
      layout := String.join (m.layout []).reverse,
      isTainted := false,
      cost := m.cost
    }
  | .tainted t =>
    -- dbg_trace "tainted it was tainted..."
    let (m, cache) ← ((expandTainted t)|>.run cache)
    return {
      layout := String.join (m.layout []).reverse,
      isTainted := true,
      cost := m.cost
    }

where

  initCache (cacheSize:Nat) : CacheStore χ :=
    {size := cacheSize, lastMeasurement := 0, content := Array.mkArray cacheSize #[]}

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) : String :=
  Doc.print χ doc cacheSize col widthLimit computationWidth |>.layout

end PrettyFormat
