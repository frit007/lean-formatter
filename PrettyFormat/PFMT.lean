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
    if l.bridgeR < r.bridgeR then
      mergeSet ls rhs (l :: acc)
    else if r.bridgeR < l.bridgeR then
      mergeSet lhs rs (r :: acc)
    else
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


@[inline] def leafSet [Cost χ] (m : Measure χ): MeasureResult χ (MeasureSet χ) :=
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

def possibilitiesToMeasureSet [Cost χ] (possibilities : Bridge) (col indent widthLimit: Nat) (text : String) (expect:Bool) : MeasureSet χ := Id.run do
  let mut options : List (MeasureSet χ) := []

  if possibilities.overlapsWith bridgeNl then
    options := (MeasureSet.set [{
      last := indent + text.length,
      bridgeR := bridgeFlex,
      cost := Cost.nl + Cost.text widthLimit indent (text.length),
      layout := fun ss => text :: "".pushn ' ' indent :: "\n" :: ss
    }])::options

  -- In any other case we we let the child handle the separation
  if possibilities.overlapsWith bridgeSpace then
    options := (MeasureSet.set [{
      last := col + text.length + 1,
      bridgeR := bridgeFlex,
      cost := Cost.text widthLimit col (text.length + 1)
      layout := fun ss => text :: " " :: ss
    }])::options

  -- anything other than space or newline get shortened to nothing
  if expect then
    -- To accept an immediate bridge you must expect it, to avoid accidental immediate bridges
    if (possibilities.erase (bridgeSpace ||| bridgeNl)) != 0 then
      options := (MeasureSet.set [{
        last := col + text.length,
        bridgeR := bridgeFlex,
        cost := Cost.text widthLimit col (text.length)
        layout := fun ss => text :: ss
      }])::options
  else
    if possibilities.overlapsWith bridgeNone then
      options := (MeasureSet.set [{
        last := col + text.length,
        bridgeR := bridgeFlex,
        cost := Cost.text widthLimit col (text.length)
        layout := fun ss => text :: ss
      }]) :: options

  if options.length == 0 then
    impossibleMeasureSet s!"possibilites to set:: no options {possibilities.str}"
  else
    options.foldl (fun acc x => x.merge acc) (MeasureSet.set [])


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
partial def Doc.resolve [Cost χ] (doc : Doc) (col indent widthLimit computationWidth : Nat) (leftBridge rightBridge: Bridge) (flatten : Flatten) : MeasureResult χ (MeasureSet χ) := do
  if enableDebugging then
    dbg_trace s!"doc : lb {leftBridge} rb {rightBridge} kind {doc.kind} flatten: {repr flatten} :::: {doc.toString} path:({doc.meta.findPath flatten |> repr})"
  if doc.meta.shouldBeCached then
    let key := createKey col indent flatten leftBridge rightBridge
    match (← get).content[doc.meta.id]!.find? key with
    | .found x =>
      return x
    | .miss index =>
      let value ← core doc
      let _ ← modify (fun cacheStore => {
        cacheStore with
        content := cacheStore.content.modify doc.meta.id (fun cacheArr => cacheArr.insertSorted index {key:=key, result:=value})
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
      if s == "abacination" then
        dbg_trace s!"{widthLimit} {col} {s.length}"
      if s.length == 0 then
        leafSet {
          last := col + s.length,
          cost := Cost.text widthLimit col s.length
          layout := fun ss => s :: ss
          bridgeR := leftBridge
        }
      else
        let ms : MeasureSet χ:= if leftBridge == bridgeFlex then
          .set [{
              last := col + s.length,
              cost := Cost.text widthLimit col s.length
              layout := fun ss => s :: ss
              bridgeR := bridgeFlex
            }]
        else
          possibilitiesToMeasureSet leftBridge col indent widthLimit s false

        match ms with
        | .set ms =>
          let ms' := ms.filter (fun m => m.last <= computationWidth)
          if ms'.length > 0 then
            return .set ms'
          else
            match ms with
            | head::_ =>
              return .tainted (TaintedTrunk.value head)
            | _ => panic! "There should at least be one piece of text in the original set"
        | _ => panic! "There is no way for us to generate a tainted value yet"
    | .newline flattened _ =>
      if flatten.shouldFlattenNl then
        -- TODO: should we learn
        match flattened with
        | some s =>
            leafSet {
              last := col + s.length,
              cost := Cost.text widthLimit col s.length
              layout := fun ss => s :: ss
              bridgeR := bridgeFlex
            }
        | none =>
          dbg_trace "nl::unable to flatten"
          return impossibleMeasureSet "nl::unable to flatten"
      else
        if leftBridge == bridgeFlex || leftBridge.overlapsWith bridgeAny then
          leafSet {
            last := indent,
            cost := Cost.nl,
            layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss,
            bridgeR := bridgeFlex
          }
        else
          dbg_trace s!"nl:: no overlap with {leftBridge}"
          return impossibleMeasureSet s!"nl:: no overlap with {leftBridge}"
    | .concat lhs rhs m =>
      -- measureDiff "before calc concat"
      let (flattenLhs, flattenRhs) := concatFlatten flatten lhs.meta.collapses rhs.meta.collapses
      if enableDebugging then
        dbg_trace s!"concat bridges: {repr flattenLhs} {repr flattenRhs} leftCollapses: {lhs.meta.collapses} rightCollapses: {rhs.meta.collapses}"
      let newRight := (rhs.meta.findPath flattenRhs).restrictBridge rightBridge
      if enableDebugging then
        dbg_trace s!"concat: new right: {newRight} currentRight: {rightBridge}  rhs path: {rhs.meta.findPath flattenRhs|> repr} lhs : {lhs.toString} rhs : {rhs.toString}"


      let left ← (lhs.resolve col indent widthLimit computationWidth leftBridge newRight flattenLhs)
      let taintedState : TaintedState := {col:=col, indent:=indent, widthLimit:=widthLimit, computationWidth := computationWidth, leftBridge := leftBridge, rightBridge := rightBridge, flatten := flattenRhs}
      processConcat left rhs taintedState flattenRhs
    | .choice lhs rhs _ => do
      -- let leftHasSolution := (lhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)
      let leftHasSolution := (lhs.meta.findPath flatten).overlapsWidth leftBridge rightBridge
      let rightHasSolution := (rhs.meta.findPath flatten).overlapsWidth leftBridge rightBridge

      if enableDebugging then
        dbg_trace s!"choice::l {leftHasSolution} val {lhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"
        dbg_trace s!"choice::r {rightHasSolution} val {rhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"

      match (leftHasSolution, rightHasSolution) with
      | (true, true) =>
        if rhs.meta.nlCount < lhs.meta.nlCount then
          -- note: prefer searching the path with more newlines first, because it makes more likely to insert at the end of the cache
          let left ← (lhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
          let right ← (rhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
          return left.merge right
        else
          -- note: prefer searching the path with more newlines first, because it makes more likely to insert at the end of the cache
          let right ← (rhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
          let left ← (lhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
          return right.merge left
      | (true, false) =>
        lhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten
      | _ =>
        rhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten

    | .nest indentOffset doc _ => doc.resolve col (indent + indentOffset) widthLimit computationWidth leftBridge rightBridge flatten
    | .align doc _ => doc.resolve col col widthLimit computationWidth leftBridge rightBridge flatten
    | .reset doc _ => doc.resolve col 0 widthLimit computationWidth leftBridge rightBridge flatten
    | .provide b _ =>
      let b := if flatten.isFlat then b.flatten else b
      let possibilities := leftBridge.provideIntersection b
      if possibilities == bridgeNull then
        return impossibleMeasureSet s!"provide::no overlap between leftbridge {leftBridge} and b:{b}"
      else
        leafSet {
          cost := Cost.text 0 0 0,
          last := col,
          layout := id
          bridgeR := possibilities
        }
    | .require b _ =>
      let b := if flatten.shouldFlattenNl then b.flatten else b
      let possibilities := leftBridge.requireIntersection b
      return possibilitiesToMeasureSet possibilities col indent widthLimit "" true
    | .rule _ doc _ =>
      doc.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten
    | .flatten inner _ =>
      inner.resolve col indent widthLimit computationWidth leftBridge rightBridge (flatten.startFlatten)
    | .stx _ _ =>
      panic! "Syntax should be expanded before reaching this point"
    | .cost c _ =>
      let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
      leafSet {
        cost := lineCost,
        last := col,
        layout := id
        bridgeR := leftBridge
      }
    | .bubbleComment comment _ =>
      leafSet {
        cost := Cost.text 0 0 0,
        last := col,
        layout := placeComment indent comment
        bridgeR := leftBridge
      }

  /-
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcat (left : MeasureSet χ) (right : Doc) (state: TaintedState) (flattenRhs : Flatten) : MeasureResult χ (MeasureSet χ) := do
    match left with
    | .tainted leftThunk =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.
      -- dbg_trace s!"tainted lb{state.leftBridge} rb{state.rightBridge}"
      return .tainted (TaintedTrunk.leftTainted leftThunk right state)
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

        match ← (right.resolve l.last state.indent widthLimit computationWidth l.bridgeR rightBridge flattenRhs) with
        | .tainted rightThunk => return .tainted (TaintedTrunk.rightTainted l rightThunk {state with rightBridge := rightBridge})
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

partial def expandTainted [Cost χ] (trunk :TaintedTrunk χ): MeasureResult χ (Measure χ) := do
    expandTainted' trunk
  where
  expandTainted' : TaintedTrunk χ → MeasureResult χ (Measure χ)
  | .leftTainted (left : (TaintedTrunk χ)) (right:Doc) (state:TaintedState)=> do
    let leftMeasure ← expandTainted left
    let r ← right.resolve leftMeasure.last state.indent state.widthLimit state.computationWidth leftMeasure.bridgeR state.rightBridge state.flatten
    match r with
    | .tainted t => return leftMeasure.concat (← expandTainted t)
    | .set (m::_) => return leftMeasure.concat m
    | _ => return impossibleMeasure "tainted::no right solution"
  | .rightTainted left right _ => do
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
partial def Doc.print (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) : (PrintResult χ) := Id.run do
  if !((doc.meta.findPath Flatten.notFlattened).overlapsWidth (bridgeFlex) (bridgeEnding)) then
    dbg_trace s!"WARNING: document does not contain a solution"
    -- IO.FS.writeFile ("doc_print.json") (s!"{doc.toJSON}")
    -- dbg_trace s!"WARNING: after writting "

  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) col 0 widthLimit computationWidth bridgeFlex bridgeEnding Flatten.notFlattened).run (initCache cacheSize))

  match preferredGroups with
  | .set ([]) =>
    return {
      layout := "No solution found",
      isTainted := false,
      cost := Cost.text 0 0 0
    }
  | .set (ms) =>

    let m := (removeEndingBridges ms).head!
    return {
      layout := String.join (m.layout []).reverse,
      isTainted := false,
      cost := m.cost
    }
  | .tainted t =>
    -- dbg_trace "tainted it was tainted..."
    let (m, _) ← ((expandTainted t)|>.run cache)
    return {
      layout := String.join (m.layout []).reverse,
      isTainted := true,
      cost := m.cost
    }

where
  removeEndingBridges [Cost χ] (ms : List (Measure χ)) : List (Measure χ) :=
    ms.foldl (fun acc m => mergeSet acc [{m with bridgeR := bridgeFlex}]) []
  initCache (cacheSize:Nat): CacheStore χ :=
    {size := cacheSize, lastMeasurement := 0, content := Array.mkArray cacheSize #[]}

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) : String :=
  Doc.print χ doc cacheSize col widthLimit computationWidth |>.layout


end PrettyFormat
