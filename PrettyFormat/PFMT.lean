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
-- private def mergeSet [Cost χ] (lhs rhs : List ((Measure χ))) (acc : List (Measure χ) := []) : List (Measure χ) :=
--   match h1:lhs, h2:rhs with
--   | [], _ => acc.reverse ++ rhs
--   | _, [] => acc.reverse ++ lhs
--   | l :: ls, r :: rs =>
--     if l.bridgeR < r.bridgeR then
--       mergeSet ls rhs (l :: acc)
--     else if r.bridgeR < l.bridgeR then
--       mergeSet lhs rs (r :: acc)
--     else
--       if LEB.leq l r then
--         mergeSet lhs rs acc
--       else if LEB.leq r l then
--         mergeSet ls rhs acc
--       else if l.last > r.last then
--         mergeSet ls rhs (l :: acc)
--       else
--         mergeSet lhs rs (r :: acc)
-- termination_by lhs.length + rhs.length
private def mergeSet [Cost χ] (lhs rhs : List ((Measure χ))) : List (Measure χ) :=
  match h1:lhs, h2:rhs with
  | [], _ => rhs
  | _, [] => lhs
  | l :: ls, r :: rs =>
    if l.bridgeR < r.bridgeR then
      dbg_trace "there are no bridges"
      l :: mergeSet ls rhs
    else if r.bridgeR < l.bridgeR then
      dbg_trace "there are no bridges"
      r :: mergeSet lhs rs
    else
      if LEB.leq l r then
        mergeSet lhs rs
      else if LEB.leq r l then
        mergeSet ls rhs
      else if l.last > r.last then
        l :: mergeSet ls rhs
      else
        r :: mergeSet lhs rs
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

def passthrough : Array (Bridge × Bridge) :=
  -- meta constructs like cost, bubblecomment and text "", do not affect bridges
  #[
    (bridgeFlex, bridgeFlex),
    (bridgeSpaceNl, bridgeSpaceNl),
    (bridgeHardNl, bridgeHardNl),
    (bridgeSpace, bridgeSpace),
    (bridgeNone, bridgeNone),
    (bridgeImmediate, bridgeImmediate)
  ]

def acceptFlex : Array (Bridge × Bridge) :=
  #[
    (bridgeFlex, bridgeFlex ||| bridgeSpace ||| bridgeNl),
    (bridgeSpaceNl, bridgeFlex ||| bridgeSpace ||| bridgeNl),
    (bridgeHardNl, bridgeFlex ||| bridgeSpace ||| bridgeNl),
    (bridgeSpace, bridgeFlex ||| bridgeSpace ||| bridgeNl),
    (bridgeNone, bridgeFlex ||| bridgeSpace ||| bridgeNl)
  ]

--   return merged
partial def mergePaths (lhs rhs: Array (Bridge × Bridge)): (Array (Bridge × Bridge)) :=
  mergePaths' lhs rhs #[] 0 0
where mergePaths' (lhs rhs merged: Array (Bridge × Bridge)) (li ri : Nat): (Array (Bridge × Bridge)) :=
  if li < lhs.size && ri < rhs.size then
    let lb := lhs[li]!
    let rb := rhs[ri]!
    if lb.fst < rb.fst then
      mergePaths' lhs rhs (merged.push (lb)) (li + 1) ri
    else if rb.fst < lb.fst then
      mergePaths' lhs rhs (merged.push (rb)) li (ri + 1)
    else
      mergePaths' lhs rhs (merged.push (rb.fst, rb.snd ||| lb.snd)) (li + 1) (ri + 1)
  else if li < lhs.size then
    mergePaths' lhs rhs (merged.push (lhs[li]!)) (li + 1) ri
  else if ri < rhs.size then
    mergePaths' lhs rhs (merged.push (rhs[ri]!)) li (ri + 1)
  else
    merged


def concatPaths (lhs rhs : Array (Bridge × Bridge)) : Array (Bridge × Bridge) :=
  lhs.foldl (fun acc (ll, lr) =>
    let leadsTo :Bridge := rhs.foldl (fun acc (rl, rr) =>
      if rl.overlapsWith lr then
        -- since we are iterating through the array based on the left side, the array remains sorted
        acc ||| rr
      else
        acc
    ) bridgeNull

    if leadsTo != bridgeNull then
      acc.push (ll, leadsTo)
    else
      acc
  ) #[]



def leafSet [Inhabited χ] [Cost χ] (m : Measure χ): MeasureResult χ (MeasureSet χ) :=
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
  -- dbg_trace s!"to measureset {possibilities}"

  if possibilities.overlapsWith bridgeNl then
    -- dbg_trace s!"huh newline?"
    options := (MeasureSet.set [{
      last := indent,
      bridgeR := bridgeFlex,
      cost := Cost.nl,
      layout := fun ss => text :: "".pushn ' ' indent :: "\n" :: ss
    }])::options
    -- options := Doc.newline " " {collapsesBridges := Ternary.yes, paths := acceptFlex}::options
  -- In any other case we we let the child handle the separation
  if possibilities.overlapsWith bridgeSpace then
    options := (MeasureSet.set [{
      last := col + text.length + 1,
      bridgeR := bridgeFlex,
      cost := Cost.text widthLimit col (text.length + 1)
      layout := fun ss => text :: " " :: ss
    }])::options

  -- anything other than space or newline get shortened to nothing
  if expect then -- TODO:
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

-- def foundSolutions [Cost χ] (indent col: Nat) (leftBridge rightBridge : Bridge) (flatten : Flatten) : List (Cache χ) → Option (Cache χ)
--   | c::rest =>
--     if (c.leftBridge.subsetOf leftBridge && c.rightBridge.subsetOf rightBridge && c.flatten = flatten && c.column == col && c.indent == indent ) then
--       some c
--     else
--       foundSolutions indent col leftBridge rightBridge flatten rest
--    | [] => none


def cacheKey (id indent col: Nat) (leftBridge rightBridge : Bridge) (flatten : Flatten) : (UInt64 × UInt64) :=
  -- assume that indent and col are max 16 bits
  let indentAndCol := (indent.toUInt64) ||| (col.toUInt64 <<< 16)
  -- assume that there are max 2^32 ids
  let idAndIndentAndCol := id.toUInt64 ||| (indentAndCol <<< 32)
  -- for now there are fewer than 16 bridges flatten only needs 5 values
  let bridgesAndFlatten := leftBridge.toUInt64 ||| (rightBridge.toUInt64 <<< 16) ||| (flatten.toInt.toUInt64 <<< 32)
  -- Funny story: the runtime changes from ~21 seconds to ~110 seconds if return idAndIndentAndCol instead of the tuple
  -- In the benchmark SExpRandom.lean --size 4 --page-width 80 --computation-width (https://github.com/frit007/pretty-expressive-tests)
  --   Note: that this benchmark does not depend on bridges, or flatten and they reach the same conclusion
  -- There might be an optimation that assumes scalar numbers are small
  (idAndIndentAndCol, bridgesAndFlatten)

def getCached [Cost χ] (id indent col: Nat) (leftBridge rightBridge : Bridge) (flatten : Flatten): MeasureResult χ (Option (MeasureSet χ)) := do
  let cacheStore ← get
  return cacheStore.content.get? (cacheKey id indent col leftBridge rightBridge flatten)

def addToCache [Cost χ] (id indent column: Nat) (leftBridges rightBridges : Bridge) (flatten : Flatten) (results:MeasureSet χ): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    {cacheStore with content := cacheStore.content.insert (cacheKey id indent column leftBridges rightBridges flatten) results}
  )

def removeFromCache [Cost χ] (id indent column: Nat) (leftBridges rightBridges : Bridge) (flatten : Flatten): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    {cacheStore with content := cacheStore.content.erase (cacheKey id indent column leftBridges rightBridges flatten)}
  )


def MeasureSet.size [Cost χ] : (MeasureSet χ) → Nat
| set x => x.length
| _ => 1


/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.

leftBridge: the bridges before this document, these limit the types of documents we can create
rightBridge: the bridges after this document, these are the bridges that will be followed by leafNodes, they are created by provideR
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [Repr χ] (doc : Doc) (col indent widthLimit computationWidth : Nat) (leftBridge rightBridge: Bridge) (flatten : Flatten) : MeasureResult χ (MeasureSet χ) := do
  if enableDebugging then
    dbg_trace s!"doc : lb {leftBridge} rb {rightBridge} kind {doc.kind} flatten: {repr flatten} :::: {doc.toString} path:({doc.meta.findPath flatten})"
  if doc.meta.shouldBeCached then
    match ← getCached doc.meta.id indent col leftBridge rightBridge flatten with
    | some x =>
      return x
    | _ =>
      let value ← core doc
      addToCache doc.meta.id indent col leftBridge rightBridge flatten value
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
        | .set s =>
          let s' := s.filter (fun m => m.last <= computationWidth)
          if s'.length > 0 then
            return .set s'
          else
            match s with
            | head::_ =>
              return .tainted (TaintedTrunk.value head)
            | _ => panic! "There should at least be one piece of text in thhe original set"
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

      let (flattenLhs, flattenRhs) :=
        match (flatten, lhs.meta.collapses, rhs.meta.collapses) with
        | (Flatten.flattened, _, _) =>
          (flatten, flatten)
        | (Flatten.flattenEventually, true, true) =>
          (Flatten.flattenRight, Flatten.flattenLeft)
        | (Flatten.flattenEventually, false, true) =>
          (Flatten.notFlattened, Flatten.flattenEventually)
        | (Flatten.flattenEventually, true, false) =>
          (Flatten.flattenEventually, Flatten.notFlattened)
        | (Flatten.flattenEventually, false, false) =>
          (Flatten.notFlattened, Flatten.notFlattened)
        | (Flatten.flattenLeft, _, f) =>
          if f then
            (Flatten.flattened, Flatten.flattenLeft)
          else
            (Flatten.flattenLeft, Flatten.notFlattened)
        | (Flatten.flattenRight, f, _) =>
          if f then
            (Flatten.flattenRight, Flatten.flattened)
          else
            (Flatten.notFlattened, Flatten.flattenRight)
        | _ =>
          (flatten, flatten)

      if enableDebugging then
        dbg_trace s!"concat bridges: {repr flattenLhs} {repr flattenRhs} leftCollapses: {lhs.meta.collapses} rightCollapses: {rhs.meta.collapses}"
      let newRight := (rhs.meta.findPath flattenRhs).foldl (fun acc (rl, rr) => if rr.overlapsWith rightBridge then rl ||| acc else acc) bridgeNull
      if enableDebugging then
        dbg_trace s!"concat: new right: {newRight} currentRight: {rightBridge}  rhs path: {rhs.meta.findPath flattenRhs} lhs : {lhs.toString} rhs : {rhs.toString}"


      let left ← (lhs.resolve col indent widthLimit computationWidth leftBridge newRight flattenLhs)
      let taintedState : TaintedState := {col:=col, indent:=indent, widthLimit:=widthLimit, computationWidth := computationWidth, leftBridge := leftBridge, rightBridge := rightBridge, flatten := flattenRhs}
      processConcat left rhs taintedState m.id flattenRhs
    | .choice lhs rhs _ => do
      let leftHasSolution := (lhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)
      let rightHasSolution := (rhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)

      if enableDebugging then
        dbg_trace s!"choice::l {leftHasSolution} val {lhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"
        dbg_trace s!"choice::r {rightHasSolution} val {rhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"

      match (leftHasSolution, rightHasSolution) with
      | (true, true) =>
        let left ← (lhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
        let right ← (rhs.resolve col indent widthLimit computationWidth leftBridge rightBridge flatten)
        if rhs.meta.nlCount < lhs.meta.nlCount then
          return left.merge right
        else
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
      let b := if flatten.isFlat then b.flatten else b
      if leftBridge == bridgeFlex && b != bridgeFlex then
        return impossibleMeasureSet "require::leftBridge is missing"
      else
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
  processConcat (left : MeasureSet χ) (right : Doc) (state: TaintedState) (concatId : Nat) (flattenRhs : Flatten) : MeasureResult χ (MeasureSet χ) := do
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

        match ← (right.resolve l.last state.indent widthLimit computationWidth l.bridgeR rightBridge flattenRhs) with
        | .tainted rightThunk => return .tainted (TaintedTrunk.rightTainted l rightThunk {state with rightBridge := rightBridge} concatId)
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
  match trunk.cacheInfo with
  | some (state, id) =>
    if id != 0 then
      let result ← getCached id state.col state.indent state.leftBridge state.rightBridge state.flatten
      match result with
      | some r =>
        match r with
        | .tainted t =>
          let m ← expandTainted' t
          removeFromCache id state.indent state.col state.leftBridge state.rightBridge state.flatten
          addToCache id state.indent state.col state.leftBridge state.rightBridge state.flatten (.set [m])
          return m
        | .set (m::_) => return m
        | .set [] => panic! "The cache should never contain an empty answer"
      | _ =>
        let m ← expandTainted' trunk
        addToCache id state.indent state.col state.leftBridge state.rightBridge state.flatten (.set [m])
        return m
    else
      expandTainted' trunk
  | none =>
    expandTainted' trunk
  where
  expandTainted' : TaintedTrunk χ → MeasureResult χ (Measure χ)
  | .leftTainted (left : (TaintedTrunk χ)) (right:Doc) (state:TaintedState) (_:Nat) => do
    let leftMeasure ← expandTainted left
    let r ← right.resolve leftMeasure.last state.indent state.widthLimit state.computationWidth leftMeasure.bridgeR state.rightBridge state.flatten
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
  log : Option (List String)
  layout : String
  isTainted : Bool
  cost : χ
deriving Inhabited

inductive IntermediateResult (χ : Type) where
| noIdealSolution (failure : MeasureSet χ) (tainted : List (TaintedTrunk χ))
| noSolution (tainted : List (TaintedTrunk χ))
| idealSolution (best : MeasureSet χ)


def Doc.isDead (d : Doc) : Bool :=
  d.meta.flattenLPath.size == 0 &&
  d.meta.flattenRPath.size == 0 &&
  d.meta.flattenPath.size == 0 &&
  d.meta.path.size == 0 &&
  d.meta.eventuallyFlattenPath.size == 0

def Doc.findErr (d : Doc) (path : String) (errs : Std.HashMap String Nat) : (Std.HashMap String Nat) :=
  if !d.isDead then
    errs.alter ((s!"{path}::{d.toString}::{repr d.meta}")) (fun curr =>
      match curr with
      | some x => return x + 1
      | none => return 1
    )
  else
    match d with
      | .text _ _=> errs
      | .newline _ _=> errs
      | .choice left right _=> right.findErr path (left.findErr path errs)
      | .flatten inner _=> inner.findErr path errs
      | .align inner _=> inner.findErr path errs
      | .nest _ inner _=> inner.findErr path errs
      | .concat left right _=> right.findErr path (left.findErr path errs)
      | .stx _ _=> errs
      | .reset inner _=> inner.findErr path errs
      | .rule r inner _=> inner.findErr (path++"/"++r) errs
      | .provide _ _=> errs
      | .require _ _=> errs
      | .bubbleComment _ _=> errs
      | .cost _ _=> errs

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.print (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) (log : Option (List String)): IO (PrintResult χ) := do
  if (doc.meta.findPath Flatten.notFlattened).size == 0 then
    dbg_trace s!"WARNING: document does not contain a solution"
    IO.FS.writeFile ("doc_print.json") (s!"{doc.toJSON}")
    dbg_trace s!"WARNING: after writting "
    -- let errs := doc.findErr "" {}
    -- dbg_trace s!"WARNING: {repr errs}"
    -- dbg_trace s!"WARNING: {printOrder doc}"
  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) col 0 widthLimit computationWidth bridgeFlex bridgeEnding Flatten.notFlattened).run (initCache cacheSize log))
  -- dbg_trace s!"how many ids? {cache.content.size}"

  -- for c in cache.content do
  --   if c.length > 0 then
  --     dbg_trace s!"length {c.length}"
  match preferredGroups with
  | .set ([]) =>
    return {
      log := cache.log,
      layout := "No solution found",
      isTainted := false,
      cost := Cost.text 0 0 0
    }
  | .set (ms) =>

    let m := (removeEndingBridges ms).head!
    return {
      log := cache.log,
      layout := String.join (m.layout []).reverse,
      isTainted := false,
      cost := m.cost
    }
  | .tainted t =>
    -- dbg_trace "tainted it was tainted..."
    let (m, cache) ← ((expandTainted t)|>.run cache)
    return {
      log := cache.log,
      layout := String.join (m.layout []).reverse,
      isTainted := true,
      cost := m.cost
    }

where
  removeEndingBridges [Cost χ] (ms : List (Measure χ)) : List (Measure χ) :=
    ms.foldl (fun acc m => mergeSet acc [{m with bridgeR := bridgeFlex}]) []
  initCache (n:Nat) (log : Option (List String)): CacheStore χ :=
    -- allocate twice the space needed, so flatten is separated into its own category
    -- {size := n, content := Array.mkArray (n*2) [], log := log, giveUp := 1000, lastMeasurement := 0}
    {size := n, content := {}, log := log, giveUp := 1000, lastMeasurement := 0}

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) : IO String := do
  return (← Doc.print χ doc cacheSize col widthLimit computationWidth (none)) |>.layout

partial def Doc.prettyPrintLog (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit computationWidth : Nat) : IO String := do
  let l ← Doc.print χ doc cacheSize col widthLimit computationWidth (some [])
  match l.log with
  | none => return l.layout
  | some log =>
    return (s!"Log: {String.join (log.intersperse "\n\n")} {l.layout}")

#eval (ruleDoc "hey" ("a" <_> "b") ).prettyPrint DefaultCost 1 0 100 100

#eval ((provideDoc bridgeSpace <^> provideDoc bridgeNl) <_> "c").prettyPrint DefaultCost 1 0 3 3

end PrettyFormat
