import Std.Data.HashSet
import Doc

open Std

/-
Based on the PFMT created by Henrik Böving(https://github.com/hargoniX/pfmt) based on pretty expressive (https://arxiv.org/abs/2310.01530),
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

-- def mergePaths (lhs rhs: Array (Bridge × Bridge)): (Array (Bridge × Bridge)) := Id.run do
--   let mut merged := #[]
--   let mut li := 0
--   let mut ri := 0
--   while li < lhs.size && ri < rhs.size do
--     let lb := lhs[li]!
--     let rb := rhs[ri]!
--     if lb.fst < rb.fst then
--       merged := merged.push (lb)
--       li := li + 1
--     else if rb.fst < lb.fst then
--       merged := merged.push (rb)
--       ri := ri + 1
--     else
--       merged := merged.push ((rb.fst, rb.snd ||| lb.snd))
--       ri := ri + 1
--       li := li + 1


--   while li < lhs.size do
--     let lb := lhs[li]!
--     merged := merged.push (lb)
--     li := li + 1
--   while ri < rhs.size do
--     let rb := rhs[ri]!
--     merged := merged.push rb
--     ri := ri + 1

--   return merged
partial def mergePaths (lhs rhs: Array (Bridge × Bridge)): (Array (Bridge × Bridge)) :=
  -- dbg_trace s!"{lhs} ::merge:: {rhs}"
  mergePaths' lhs rhs #[] 0 0
  -- #[]
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



def sortPaths (p : Array (Bridge × Bridge)): Array (Bridge × Bridge):=
  p.qsort (fun a b => a.fst < b.fst)

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

#eval mergePaths #[(bridgeSpace, bridgeSpace)] #[(bridgeNl, bridgeNl), (bridgeSpace, bridgeNl)]
#eval sortPaths #[(bridgeSpace, bridgeNl), (bridgeNl, bridgeNl)]

def perfTest (n:Nat) (lhs rhs : Array (Nat × Nat)): Nat :=
  let leftBridge := n
  let rightBridge := 1 ||| 8 ||| 4 ||| 2 ||| 16
  let targetLeft := rhs.foldl (fun acc (rl,rr) => if (rr &&& rightBridge != 0) then rl ||| acc else acc ) 0

  let newRight := lhs.foldl (fun acc (ll,lr) => if ((ll &&& leftBridge) != 0) && ((lr &&& targetLeft) != 0) then lr ||| acc else acc) 0
  newRight
  -- concatPaths lhs rhs |>.size


def perfTests (c:Nat) (lhs rhs:Array (Nat × Nat)) : Nat → Nat
| 0 => c
| x + 1 =>
  perfTests (c + perfTest x lhs rhs) lhs rhs (x)

-- #eval measureTime (fun _ => return (perfTests 0 4200000))


#eval concatPaths #[(1, 2), (4, 8)] #[(2, 4), (8, 2)]

#eval concatPaths acceptFlex passthrough

-- assume that children have already been calculated


/-
Funny sideNote: if we change provide bridgeNl to always be attached to a document it would be nicer to work with from the formatters point of view

but the alternative is easier to write Syntax transformers for
-/
/-
We choose to preprocess flatten to simplify formatting later

Flatten converts all newlines to spaces

The interaction between flatten and bridges is less obvious but the rule is:
"flatten only flattens the bridges inside the flattened section"
This was chosen to allow comments at the end of a flattened section
example:
"a" <**> flatten ("b" <**> "c" <> Provide bridgeNl) <**> "d"
Is flattened to
"a" <**> ("b" <_> "c" <> Provide bridgeNl) <**> "d"

-/
-- partial def flattenPreprocessor (flattenLeft flattenInner: Bool) (d :Doc) : FlattenStateM Doc := do
--   let meta := d.meta
--   if meta.shouldBeCached then
--     let state ← get
--     let key := (meta.id, flattenLeft, flattenInner)
--     match state.cached.get? key with
--     | some d => return d
--     | _ =>
--       let doc ← flattenPreprocessor' d
--       let newId ← FlattenStateM.genId
--       let m : DocMeta := {doc.calcMeta with paths := calculatePaths doc}
--       let doc := if flattenInner then
--         {m with id := newId} |> doc.setMeta
--       else
--         doc.setMeta m

--       modify (fun s => {s with cached := s.cached.insert key doc})
--       return doc
--   else
--     let doc ← flattenPreprocessor' d
--     let doc := doc.calcMeta |> (fun m =>{m with paths := calculatePaths doc}) |> doc.setMeta
--     return doc
--   -- TODO: update meta
-- where
--   flattenPreprocessor'  (doc : Doc):  FlattenStateM (Doc) :=
--     match doc with
--     | .fail s m => return (.fail s m)
--     | .text s m => return (.text s m)
--     | .newline a m =>
--       match a with
--       | some s => return .text s m
--       | _ => return .fail "cannot flatten" m
--     | .choice left right m=> do
--       let l ← flattenPreprocessor flattenLeft flattenInner left
--       let r ← flattenPreprocessor flattenLeft flattenInner right
--       return Doc.choice l r m
--     | .flatten inner _=> do
--       let i ← flattenPreprocessor flattenLeft true inner
--       -- remove flatten from the state
--       return i
--     | .align inner m => do
--       let i ← flattenPreprocessor flattenLeft flattenInner inner
--       return Doc.align i m
--     | .nest i inner m => do
--       let inner ← flattenPreprocessor flattenLeft flattenInner inner
--       return Doc.nest i inner m
--     | .concat l r m => do
--       -- TODO:
--       if flattenInner then
--         let l ← flattenPreprocessor flattenLeft true l
--         let r ← flattenPreprocessor true true r
--         return Doc.concat l r m
--       else
--         let l ← flattenPreprocessor false false l
--         let r ← flattenPreprocessor false false r
--         return Doc.concat l r m
--     | .stx _ _=> panic! "can't flatten syntax"
--     | .reset inner m=> do
--       let inner ← flattenPreprocessor flattenLeft flattenInner inner
--       return Doc.reset inner m
--     | .rule r inner m => do
--       let inner ← flattenPreprocessor flattenLeft flattenInner inner
--       return Doc.rule r inner m
--     | .provide b m=> do
--       -- let inner ← flattenPreprocessor flattenLeft flattenInner inner
--       if flattenInner then
--         return Doc.provide b.flatten m
--       else
--         return Doc.provide b m
--     | .require b m =>
--       if flattenLeft then
--         return Doc.require b.flatten m
--       else
--         return Doc.require b m
--     | .bubbleComment c m => do
--       return Doc.bubbleComment c m
--     | .cost c m => do
--       return Doc.cost c m


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
  | set lhs, _ => .set lhs
  | _, set rhs => .set rhs
  | tainted lhs true, tainted _ true  => .tainted lhs true
  | tainted _ true, tainted rhs false  => .tainted rhs false
  | tainted lhs false, _  => .tainted lhs false

def possibilitiesToMeasureSet [Cost χ] (possibilities : Bridge) (col indent widthLimit : Nat) (text : String) (expect:Bool) : MeasureSet χ := Id.run do
  let mut options : List (MeasureSet χ) := []
  -- dbg_trace s!"to measureset {possibilities}"

  if possibilities.overlapsWith bridgeNl then
    -- dbg_trace s!"huh newline?"
    options := (MeasureSet.set [{
      last := indent,
      bridgeR := bridgeFlex,
      cost := Cost.nl + Cost.text widthLimit 0 (text.length + indent)
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
    -- options := Doc.text " " {collapsesBridges := Ternary.yes, paths := acceptFlex}::options

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

def foundSolutions [Cost χ] (indent col: Nat) (leftBridge rightBridge : Bridge) (flatten : Flatten) : List (Cache χ) → Option (Cache χ)
  | c::rest =>
    if (c.leftBridge.subsetOf leftBridge && c.rightBridge.subsetOf rightBridge && c.flatten = flatten && c.column == col && c.indent == indent ) then
      some c
    else
      foundSolutions indent col leftBridge rightBridge flatten rest
   | [] => none

def getCached [Cost χ] (id indent col: Nat) (leftBridge rightBridge : Bridge) (flatten : Flatten): MeasureResult χ (Option (MeasureSet χ)) := do
  let cacheStore ← get
  match cacheStore.content.get? id with
  | some bucket =>
    match foundSolutions indent col leftBridge rightBridge flatten bucket with
    | some c => return some c.results
    | none   => return none
  | none => return none
where
  combineResults [Cost χ] : List (Cache χ) → (MeasureSet χ)
  | x :: [] => x.results
  | x :: xs => ((combineResults xs).merge x.results)
  | [] =>
    .set []
  -- TODO: if the leftside of the cached bridge is contains the entire searched for leftBridge then we can limit the search of the rightBridge.


def addToCache [Cost χ] (id indent column: Nat) (leftBridges rightBridges : Bridge) (flatten : Flatten) (results:MeasureSet χ): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    let updatedCache := cacheStore.content.modify id (fun caches =>
      {leftBridge:=leftBridges, rightBridge := rightBridges, indent := indent, column := column, results := results, flatten := flatten}::caches
    )
    {cacheStore with content := updatedCache}
  )

def removeFromCache [Cost χ] (id indent column: Nat) (leftBridges rightBridges : Bridge) (flatten : Flatten): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    let updatedCache := cacheStore.content.modify id (fun caches =>
      caches.filter (fun c => !(c.leftBridge != leftBridges && c.rightBridge == rightBridges && c.flatten == flatten && c.indent = indent && c.column == column))
    )
    {cacheStore with content := updatedCache}
  )

def MeasureSet.size [Cost χ] : (MeasureSet χ) → Nat
| set x => x.length
| _ => 1


/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.

leftBridge: the bridges before this document, these limit the types of documents we can create
rightBridge: the bridges after this document, these are the bridges that will be followed by leafNodes, they are created by provideR
expectBridge: the bridges after this document, these limit the types of documents that can follow this document
 - expectBridge is primarily used in a tainted context where we want to provide any legal answer.
 - but to accomplish this safely we must ensure that we provide legal answers to all possible right bridges.
   - This comes with the issue that if there are no solutions for all expectBridge, then we will try all of the solutions
forceExpand: When evaluating tainted TODO: remove
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [Repr χ] (doc : Doc) (col indent widthLimit : Nat) (leftBridge rightBridge: Bridge) (flatten : Flatten) : MeasureResult χ (MeasureSet χ) := do
  -- if (← get).giveUp == 0 then
  --   -- let
  --   return impossibleMeasureSet trace
  -- modify (fun cacheStore =>
  --   {cacheStore with giveUp := cacheStore.giveUp - 1}
  -- )
  -- If we were to exceed the widthLimit we delay any attempt to optimize
  -- the layout of `doc1` in hopes that another branch of this function finds
  -- a non tainted `MeasureSet`.
    if enableDebugging then
      dbg_trace s!"doc : lb {leftBridge} rb {rightBridge} kind {doc.kind} flatten: {repr flatten} :::: {doc.toString} path:({doc.meta.findPath flatten})"
    if doc.meta.shouldBeCached then
      match ← getCached doc.meta.id indent col leftBridge rightBridge flatten with
      | some x =>
        return x
      | _ =>
        let value ← core doc col indent widthLimit
        addToCache doc.meta.id indent col leftBridge rightBridge flatten value
        return value
    else
      core doc col indent widthLimit


where
  -- exceedCheck (doc : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge : Bridge) (forceTainted: Bool) : MeasureResult χ (MeasureSet χ) := do
  --   --measureDiff s!"exceed check {doc.kind}"
  --   let exceeds :=
  --     match doc with
  --     | .text s _ => indent > widthLimit || col + s.length > widthLimit
  --     | _ => indent > widthLimit || col > widthLimit
  --   if exceeds && !forceTainted then
  --     let state :TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge, flatten := flatten}
  --     let tainted := (TaintedTrunk.center doc state doc.meta.id)
  --     return .tainted tainted false
  --   else
  --     return (← core doc trace col indent widthLimit forceTainted)
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (ppl : Doc) (col indent widthLimit : Nat) : MeasureResult χ (MeasureSet χ) := do
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match ppl with
    | .text s _ =>
      -- dbg_trace s!"print text: {s} lb: {leftBridge} rb {rightBridge}"

      if s.length == 0 then
        -- dbg_trace s!"pass through bridge {leftBridge}"

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

        if col + widthLimit > 0 then
          match ms with
          | .set s =>
            let s' := s.filter (fun m => m.last < widthLimit)
            if s'.length > 0 then
              return .set s'
            else
              match s with
              | head::_ =>
                return .tainted (TaintedTrunk.value head) (false)
              | _ => panic ""
            -- return .set s
          | _ => panic! ""
        else
          return ms
          -- let expandedBridge := possibilitiesToDoc leftBridge false <> (toDoc s|>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex}) |>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex}
          -- core expandedBridge trace col indent widthLimit bridgeFlex forceExpand
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
            cost := Cost.nl + Cost.text widthLimit 0 indent,
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

        -- if flatten != Flatten.notFlattened then
        --   if rhs.meta.collapses && lhs.meta.collapses then
        --     (flatten ||| flattenRight, flatten ||| flattenLeft)
        --   else
        --     (flatten, flatten)
        -- else
        --   (
        --     if rhs.meta.collapses && flatten == flattenLeft then flattened else flatten,
        --     if lhs.meta.collapses && flatten == flattenRight then flattened else flatten
        --   )

      -- let flattenRhs := if flatten.shouldFlatten && lhs.meta.collapses then
      --   flatten ||| flattenRight
      -- else
      --   flatten
      if enableDebugging then
        dbg_trace s!"concat bridges: {repr flattenLhs} {repr flattenRhs} leftCollapses: {lhs.meta.collapses} rightCollapses: {rhs.meta.collapses}"
      let newRight := (rhs.meta.findPath flattenRhs).foldl (fun acc (rl, rr) => if rr.overlapsWith rightBridge then rl ||| acc else acc) bridgeNull
      if enableDebugging then
        dbg_trace s!"concat: new right: {newRight} currentRight: {rightBridge}  rhs path: {rhs.meta.findPath flattenRhs} lhs : {lhs.toString} rhs : {rhs.toString}"
      -- Do we need this calculation?
      -- no because
      -- if leftbridge does not fit then it will be discarded later
      -- if the left bridge can't reach a given right bridge then there is no reason to tell it not to try reach it
      -- let newRight := lhs.meta.paths.foldl (fun acc (ll, lr) => if ll.overlapsWith leftBridge && lr.overlapsWith targetLeft then lr ||| acc else acc) bridgeNull

      -- -- dbg_trace "concat!"
      -- measureDiff "after calc concat"
      -- dbg_trace s!"targetLeft: {targetLeft} new right: {newRight}  existing {rightBridge} left: {leftBridge} leftPaths {lhs.meta.paths} rightPaths {rhs.meta.paths} lhs{lhs.toString} rhs {rhs.toString}"


      let left ← (lhs.resolve col indent widthLimit leftBridge newRight flattenLhs)
      let taintedState : TaintedState := {col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge, flatten := flattenRhs}
      processConcat left rhs taintedState m.id flattenRhs
      -- let targetLeft := rhs.meta.paths.foldl (fun acc (rl, rr) => if rr.overlapsWith rightBridge then rl ||| acc else acc) bridgeNull
      -- let newRight := lhs.meta.paths.foldl (fun acc (ll, lr) => if ll.overlapsWith leftBridge && lr.overlapsWith targetLeft then lr ||| acc else acc) bridgeNull
      -- let left ← (lhs.resolve trace col indent widthLimit leftBridge newRight forceExpand)
      -- let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge}
      -- processConcat left rhs forceExpand taintedState m.id
      -- processConcatList (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) trace (fun l newSpacing => rhs.resolve trace l.last indent widthLimit newSpacing flatten forceExpand)
    | .choice lhs rhs _ => do
      -- check if there is a chance for the algorithm to complete successfully
      -- lhs.meta.paths.foldl (fun (accl, accr) (l, r) => (accl, accr))
      -- measureDiff "Before checkSol"
      -- TODO: different path sets
      -- Should failure be tainted? maybe, but then I need to mark tainted as failure or not, and results over failures
      let leftHasSolution := (lhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)
      let rightHasSolution := (rhs.meta.findPath flatten).any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)

      if enableDebugging then
        dbg_trace s!"choice::l {leftHasSolution} val {lhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"
        dbg_trace s!"choice::r {rightHasSolution} val {rhs.toString} lbridge : {leftBridge} rbridge : {rightBridge}"
      -- let leftHasSolution := true
      -- let rightHasSolution := true
      -- measureDiff "after checkSol"
      match (leftHasSolution, rightHasSolution) with
      | (true, true) =>
        let left ← (lhs.resolve col indent widthLimit leftBridge rightBridge flatten)
        let right ← (rhs.resolve col indent widthLimit leftBridge rightBridge flatten)
        return left.merge right
      | (true, false) =>
        lhs.resolve col indent widthLimit leftBridge rightBridge flatten
      | _ =>
        rhs.resolve col indent widthLimit leftBridge rightBridge flatten

    | .nest indentOffset doc _ => doc.resolve col (indent + indentOffset) widthLimit leftBridge rightBridge flatten
    | .align doc _ => doc.resolve col col widthLimit leftBridge rightBridge flatten
    | .reset doc _ => doc.resolve col 0 widthLimit leftBridge rightBridge flatten
    | .fail _ => leafSet {
      last := 0
      cost := Cost.nl
      bridgeR := bridgeNull
      layout := (fun _ => ["fail"])
      fail := true
    }
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provide b _ =>
      let b := if flatten.isFlat then b.flatten else b
      let possibilities := leftBridge.provideIntersection b
      -- dbg_trace s!"provide {b} {possibilities}"
      if possibilities == bridgeNull then
        -- dbg_trace s!"provide::no overlap between leftbridge {leftBridge} and b:{b}"
        return impossibleMeasureSet s!"provide::no overlap between leftbridge {leftBridge} and b:{b}"
        -- (Doc.fail "impossible bridge").resolve trace col indent widthLimit (bridgeFlex) forceExpand
      else
        -- dbg_trace s!"provide gives {possibilities}"
        leafSet {
          cost := Cost.text 0 0 0,
          last := col,
          layout := id
          bridgeR := possibilities
        }
      -- else
      --   inner.resolve trace col indent widthLimit possibilities forceExpand
    | .require b _ =>
      let b := if flatten.isFlat then b.flatten else b
      if leftBridge == bridgeFlex && b != bridgeFlex then
        -- let fail : Doc := Doc.fail "require given no bridges"
        -- fail.resolve trace col indent widthLimit bridgeFlex forceExpand
        -- dbg_trace "require::leftBridge is missing"
        return impossibleMeasureSet "require::leftBridge is missing"
      else
        let possibilities := leftBridge.requireIntersection b
        -- let choices := (possibilitiesToDoc possibilities true)
        -- (choices).resolve trace col indent widthLimit bridgeFlex bridgeFlex forceExpand
        return possibilitiesToMeasureSet possibilities col indent widthLimit "" true
    | .rule _ doc _ =>
      doc.resolve col indent widthLimit leftBridge rightBridge flatten
    | .flatten inner _ =>
      -- doc.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge true forceExpand
      inner.resolve col indent widthLimit leftBridge rightBridge (flatten.startFlatten)
    | .stx _ _ =>
      panic! "Syntax should be expanded before reaching this point"
    | .cost c _ =>
      -- let inner ← doc.resolve trace col indent widthLimit leftBridge forceExpand
      let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
      leafSet {
        cost := lineCost,
        last := col,
        layout := id
        bridgeR := leftBridge
      }
      -- match inner with
      -- | .tainted t e => return .tainted (TaintedTrunk.cost c t doc.meta.id) e
      -- | .set ms =>
      --   let withCost := ms.map (fun m => m.addCost (lineCost))
      --   return .set withCost
    | .bubbleComment comment _ =>
      leafSet {
        cost := Cost.text 0 0 0,
        last := col,
        layout := placeComment indent comment
        bridgeR := leftBridge
      }
      -- let inner ← doc.resolve trace col indent widthLimit leftBridge forceExpand
      -- match inner with
      -- | .tainted t e => return .tainted (TaintedTrunk.bubbleComment comment t doc.meta.id) e
      -- | .set ms => return .set (ms.map (fun m => m.prependLayout (placeComment 0 comment)))
      -- let withComment := inner.fst.map (fun ms => {ms with set := ms.set.map (fun m => m.prependLayout (placeComment 0 comment))})
      -- return (withComment, [TaintedTrunk.bubbleComment comment inner.snd])

  /-
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcat (left : MeasureSet χ) (right : Doc) (state: TaintedState) (concatId : Nat) (flattenRhs : Flatten) : MeasureResult χ (MeasureSet χ) := do
    match left with
    | .tainted leftThunk e =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.
      -- dbg_trace s!"tainted lb{state.leftBridge} rb{state.rightBridge}"
      return .tainted (TaintedTrunk.leftTainted leftThunk right state concatId) e
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

        -- let thereIsAPossibleSolution := right.meta.paths.any (fun (lb, rb) => lb.overlapsWith l.bridgeR && rb.overlapsWith rightBridge)
        -- dbg_trace s!"call again? {l.bridgeR}"
        match ← (right.resolve l.last state.indent widthLimit l.bridgeR rightBridge flattenRhs) with
        | .tainted rightThunk e => return .tainted (TaintedTrunk.rightTainted l rightThunk {state with rightBridge := rightBridge} concatId) e
        | .set (r :: rights) => return .set (dedup rights [] (l.concat r)) --TODO: dedup probably does not work if there are different bridges.
        | .set [] =>
          dbg_trace "concat::no right solution"
          return impossibleMeasureSet "concat::no right solution"

       let rec concatAllWithRight  : List (Measure χ) →  MeasureResult χ (MeasureSet χ)
         | [] =>
            dbg_trace "concat::no left solution"
           return impossibleMeasureSet "concat::no left solution"
         | [l] => concatOneWithRight l
          -- Do we need to sort the bridges?
          -- no because

         | l :: ls => do return MeasureSet.merge (← concatOneWithRight l) (← concatAllWithRight ls)
       concatAllWithRight lefts

-- When we are in a tainted state we no longer guarantee that we find the best solution
-- instead we just try to find any solution as fast as possible
-- Therefore as soon as we a solution we will return it
-- This is complicated by bridges, because we need to find a solution for all bridges that the right side expects
-- Therefore we will return as soon as we find a solution to all of the expected bridges

-- for this to work I must pass the expected bridge through the entire program
--  - I don' necessarily have an expected bridge which would be bridgeFlex
partial def expandTainted [Inhabited χ] [Repr χ] [Cost χ] (trunk :TaintedTrunk χ): MeasureResult χ (Measure χ) := do
  match trunk.cacheInfo with
  | some (state, id) =>
    if id != 0 then
      let result ← getCached id state.col state.indent state.leftBridge state.rightBridge state.flatten
      match result with
      | some r =>
        match r with
        | .tainted t _ =>
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
    let r ← right.resolve leftMeasure.last state.indent state.widthLimit leftMeasure.bridgeR state.rightBridge state.flatten
    match r with
    | .tainted t _ => return leftMeasure.concat (← expandTainted t)
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
      | .fail _=> errs
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
partial def Doc.print (χ : Type) [Inhabited χ] [Repr χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) (log : Option (List String)): IO (PrintResult χ) := do
  -- let (preferredGroups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeFlex false false).run (initCache cacheSize log)).run
  if (doc.meta.findPath Flatten.notFlattened).size == 0 then
    dbg_trace s!"WARNING: document does not contain a solution"
    -- let errs := doc.findErr "" {}
    -- dbg_trace s!"WARNING: {repr errs}"
    -- dbg_trace s!"WARNING: {printOrder doc}"
  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) col 0 widthLimit bridgeFlex bridgeEnding Flatten.notFlattened).run (initCache cacheSize log))

  match preferredGroups with
  | .set (m::ms) =>
    -- dbg_trace "taken first response, ignored{ms.length}"
    return {
      log := cache.log,
      layout := String.join (m.layout []).reverse,
      isTainted := false,
      cost := m.cost
    }
  | .set ([]) =>
    -- dbg_trace "it was empty set"
    return {
      log := cache.log,
      layout := "No solution found",
      isTainted := false,
      cost := Cost.text 0 0 0
    }
  | .tainted t _ =>
    -- dbg_trace "tainted it was tainted..."
    let (m, cache) ← ((expandTainted t)|>.run cache)
    return {
      log := cache.log,
      layout := String.join (m.layout []).reverse,
      isTainted := true,
      cost := m.cost
    }

where
  initCache (n:Nat) (log : Option (List String)): CacheStore χ :=
    -- allocate twice the space needed, so flatten is separated into its own category
    {size := n, content := Array.mkArray (n*2) [], log := log, giveUp := 1000, lastMeasurement := 0}

-- partial def runFlatten (nextId : Nat) (doc : Doc) : (Doc × Nat) :=
--   let (doc, cache2) := (flattenPreprocessor false false doc).run {nextId := nextId, cached := Std.HashMap.empty}
--   (doc, cache2.nextId)

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  -- let a ← (--measureDiff "start")
  -- let ((doc, cacheSize), t) ← measureTime (fun _ => return (runFlatten cacheSize doc))
  -- -- dbg_trace s!"time taken{(t).toFloat / 1000000000.0} s"
  -- --measureDiff "flattenTime"
  return (← Doc.print χ doc cacheSize col widthLimit (none)) |>.layout

partial def Doc.prettyPrintLog (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  -- let (doc, cacheSize) := (runFlatten cacheSize doc)
  let l ← Doc.print χ doc cacheSize col widthLimit (some [])
  match l.log with
  | none => return l.layout
  | some log =>
    return (s!"Log: {String.join (log.intersperse "\n\n")} {l.layout}")
  -- return l.layout

#eval (ruleDoc "hey" ("a" <_> "b") ).prettyPrint DefaultCost 1 0 100
-- #eval (("a" <_> "b") <**> "c" <> nestDoc 4 ("d" <**>"a")  ).prettyPrint DefaultCost 1 0 3
#eval ((provideDoc bridgeSpace <^> provideDoc bridgeNl) <_> "c").prettyPrint DefaultCost 1 0 3
-- #eval do
--   let (d, t) := (runFlatten 1 ("Hello" <> "" <> "you"))
--   d.prettyPrint DefaultCost 1 0 10
-- #eval (runFlatten 1 ((provideDoc bridgeSpace <^> provideDoc bridgeNl) <_> "c"))
#eval concatPaths #[(2, 2), (1, 2), (4, 4), (1, 4), (8, 8), (1, 8)] #[(8, 8), (1, 8)]
-- #eval ("Hello" <> "" <> "you").print DefaultCost 1 0 100 (some [])
#eval concatPaths #[(1,1)] #[(1,8)]
end PrettyFormat
