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
    -- TODO: We do not have to compare bridge here because we know that they have the same bridge
    if LEB.leq l r then
      mergeSet lhs rs acc
    else if LEB.leq r l then
      mergeSet ls rhs acc
    else if l.last > r.last then
      mergeSet ls rhs (l :: acc)
    else
      mergeSet lhs rs (r :: acc)
termination_by lhs.length + rhs.length



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
    (bridgeFlex, bridgeFlex),
    (bridgeSpaceNl, bridgeFlex),
    (bridgeHardNl, bridgeFlex),
    (bridgeSpace, bridgeFlex),
    (bridgeNone, bridgeFlex)
  ]

def mergePaths (lhs rhs: Array (Bridge × Bridge)): (Array (Bridge × Bridge)) := Id.run do
  let mut merged := #[]
  let mut li := 0
  let mut ri := 0
  while li < lhs.size && ri < rhs.size do
    let lb := lhs[li]!
    let rb := rhs[ri]!
    if lb.fst < rb.fst then
      merged := merged.push (lb)
      li := li + 1
    else if rb.fst < lb.fst then
      merged := merged.push (rb)
      ri := ri + 1
    else
      merged := merged.push ((rb.fst, rb.snd ||| lb.snd))
      ri := ri + 1
      li := li + 1


  while li < lhs.size do
    let lb := lhs[li]!
    merged := merged.push (lb)
    li := li + 1
  while ri < rhs.size do
    let rb := rhs[ri]!
    merged := merged.push rb
    ri := ri + 1

  return merged

def sortPaths (p : Array (Bridge × Bridge)): Array (Bridge × Bridge):=
  p.qsort (fun a b => a.fst < b.fst)

def concatPaths (lhs rhs : Array (Bridge × Bridge)) : Array (Bridge × Bridge) :=
  rhs.foldl (fun acc (rl, rr) =>
    lhs.foldl (fun acc (ll, lr) =>
      if rl.intersection lr != bridgeNull then
        mergePaths acc #[(ll, rr)]
      else
        acc
    ) acc
  ) #[]

-- #eval mergePaths #[(bridgeSpace, bridgeSpace)] #[(bridgeNl, bridgeNl), (bridgeSpace, bridgeNl)]
#eval sortPaths #[(bridgeSpace, bridgeNl), (bridgeNl, bridgeNl)]

#eval concatPaths #[(1, 2), (4, 8)] #[(2, 4), (8, 2)]

#eval concatPaths acceptFlex passthrough

-- assume that children have already been calculated
def calculateFilter: Doc → (Array (Bridge × Bridge))
| .fail _ _=> #[]
| .text s _=>
  if s.length == 0 then
    passthrough
  else
    acceptFlex
| .newline _ _=> acceptFlex
| .choice left right _=>
  mergePaths left.meta.paths right.meta.paths
| .flatten inner _=> inner.meta.paths -- TODO:
| .align inner _=> inner.meta.paths
| .nest _ inner _=> inner.meta.paths
| .concat left right _=>
  concatPaths left.meta.paths right.meta.paths
| .stx _ _=> panic! "Syntax should have been handled before this"
| .reset inner _=> inner.meta.paths
| .rule _ inner _=> inner.meta.paths
| .provide b _=>
  let parts := b.parts
  parts.foldl (fun acc b' =>
    -- acc.push (b',b')
    let acc := acc.push (b',b')
    if bridgeAny.contains b' then
      acc.push (bridgeFlex, b')
    else
      acc
  ) #[] |> sortPaths
| .require b _=>
  let parts := b.parts
  parts.foldl (fun acc b' =>
    let acc := acc.push (b',b')
    if bridgeAny.contains b' then
      acc.push (bridgeFlex, b')
    else
      acc
  ) #[] |> sortPaths
| .bubbleComment _ _=> passthrough
| .cost _ _=> passthrough

/-
Funny sideNote: if we change provide bridgeNl to always be attached to a document it would be nicer to work with from the formatters point of view

but the alternative is easier to write Syntax transformers for
-/
/--
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
partial def flattenPreprocessor (flattenLeft flattenInner: Bool) (d :Doc) : FlattenStateM Doc := do
  let meta := d.meta
  if meta.shouldBeCached then
    let state ← get
    let key := (meta.id, flattenLeft, flattenInner)
    match state.cached.get? key with
    | some d => return d
    | _ =>
      let doc ← flattenPreprocessor' d
      let newId ← FlattenStateM.genId
      let m : DocMeta := {doc.calcMeta with paths := calculateFilter doc}
      let doc := if flattenInner then
        {m with id := newId} |> doc.setMeta
      else
        doc.setMeta m

      modify (fun s => {s with cached := s.cached.insert key doc})
      return doc
  else
    let doc ← flattenPreprocessor' d
    let doc := doc.calcMeta |> (fun m =>{m with paths := calculateFilter doc}) |> doc.setMeta
    return doc
  -- TODO: update meta
where
  flattenPreprocessor'  (doc : Doc):  FlattenStateM (Doc) :=
    match doc with
    | .fail s m => return (.fail s m)
    | .text s m => return (.text s m)
    | .newline a m =>
      match a with
      | some s => return .text s m
      | _ => return .fail "cannot flatten" m
    | .choice left right m=> do
      let l ← flattenPreprocessor flattenLeft flattenInner left
      let r ← flattenPreprocessor flattenLeft flattenInner right
      return Doc.choice l r m
    | .flatten inner _=> do
      let i ← flattenPreprocessor flattenLeft true inner
      -- remove flatten from the state
      return i
    | .align inner m => do
      let i ← flattenPreprocessor flattenLeft flattenInner inner
      return Doc.align i m
    | .nest i inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner inner
      return Doc.nest i inner m
    | .concat l r m => do
      -- TODO:
      if flattenInner then
        let l ← flattenPreprocessor flattenLeft true l
        let r ← flattenPreprocessor true true r
        return Doc.concat l r m
      else
        let l ← flattenPreprocessor false false l
        let r ← flattenPreprocessor false false r
        return Doc.concat l r m
    | .stx _ _=> panic! "can't flatten syntax"
    | .reset inner m=> do
      let inner ← flattenPreprocessor flattenLeft flattenInner inner
      return Doc.reset inner m
    | .rule r inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner inner
      return Doc.rule r inner m
    | .provide b m=> do
      -- let inner ← flattenPreprocessor flattenLeft flattenInner inner
      if flattenInner then
        return Doc.provide b.flatten m
      else
        return Doc.provide b m
    | .require b m =>
      if flattenLeft then
        return Doc.require b.flatten m
      else
        return Doc.require b m
    | .bubbleComment c m => do
      return Doc.bubbleComment c m
    | .cost c m => do
      return Doc.cost c m


/--
Combine the results from two `MeasureSet`s.
-/
def MeasureSet.merge [Cost χ] (lhs rhs : MeasureSet χ) : MeasureSet χ :=
  match lhs, rhs with
  | set lhs, set rhs =>
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
  | set lhs, _ => .set lhs
  | _, set rhs => .set rhs
  | tainted lhs true, tainted _ true  => .tainted lhs true
  | tainted _ true, tainted rhs false  => .tainted rhs false
  | tainted lhs false, _  => .tainted lhs false

def possibilitiesToDoc (possibilities : Bridge) (expect:Bool) : Doc := Id.run do
  let mut options : List (Doc) := []

  if possibilities.overlapsWith bridgeNl then
    options := Doc.newline " " {collapsesBridges := Ternary.yes, paths := acceptFlex}::options
  -- In any other case we we let the child handle the separation
  if possibilities.overlapsWith bridgeSpace then
    options := Doc.text " " {collapsesBridges := Ternary.yes, paths := acceptFlex}::options

  -- anything other than space or newline get shortened to nothing
  if expect then
    -- To accept an immediate bridge you must expect it, to avoid accidental immediate bridges
    if (possibilities.erase (bridgeSpace ||| bridgeNl)) != 0 then
      options := (Doc.text "" {collapsesBridges := Ternary.yes, paths := acceptFlex})::options
  else
    if possibilities.overlapsWith bridgeNone then
      options := (Doc.text "" {collapsesBridges := Ternary.yes, paths := acceptFlex})::options

  if options.isEmpty then
    (Doc.fail "No possibilities")
  else
    -- panic! s!"How did we get here? No options? {possibilities} bridgeSpace:{bridgeSpace} bridgeNl:{bridgeNl} bridgeHardNl:{bridgeHardNl}"
    let choices : Doc := options.tail.foldl (fun (acc : Doc) (d : Doc) => (acc) <^> (d) |>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex} ) (options.head!)
    return choices

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

def getCached [Cost χ] (id indent col: Nat) (bridges : Bridge) (allowTainted : Bool): MeasureResult χ ((MeasureSet χ) × Bridge) := do
  let cacheStore ← get
  let bucket := cacheStore.content.get! id
  let (caches, bridges) := foundSolutions indent col [] bridges allowTainted bridges (bucket)

  return (combineResults caches, bridges)
where
  combineResults : List (Cache χ) → (MeasureSet χ)
  | x :: [] => x.results
  | x :: xs => ((combineResults xs).merge x.results)
  | [] =>
    .set []
  -- TODO: consider optimizing by considering previous results, if their maxWidth does not exceed the widthLimit
  -- Note: we need the original bridge here to check for the following scenario:
  --  - We have caches for 110 and 011, and are looking for 111 but when we find 110 we can erase 011 and therefore can't find 011, since it is not a subset of 001
  foundSolutions (indent col: Nat) (acc : List (Cache χ)) (originalBridge : Bridge) (forceTainted : Bool): Bridge → List (Cache χ) → (List (Cache χ) × Bridge)
  | 0, _ => (acc, 0)
  | bridges, [] => (acc, bridges)
  | bridges, c::rest =>
    if (c.leftBridge.subsetOf originalBridge && c.column == col) && ((c.indent == indent && !c.isTainted) || (!forceTainted || c.indent >= indent)) then
      foundSolutions indent col (c::acc) originalBridge forceTainted (bridges.erase c.leftBridge) rest
    else
      foundSolutions indent col acc originalBridge forceTainted bridges rest

def addToCache [Inhabited χ] [Cost χ] (id indent column: Nat) (isTainted : Bool) (leftBridges : Bridge) (results:MeasureSet χ): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    let updatedCache := cacheStore.content.modify id (fun caches =>
      {leftBridge:=leftBridges, indent := indent, column := column, isTainted := isTainted, results := results}::caches
    )
    {cacheStore with content := updatedCache}
  )

def leafSet [Inhabited χ] [Cost χ] (m : Measure χ): MeasureResult χ (MeasureSet χ) :=
  return .set [m]

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
forceExpand: When evaluating tainted
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [Repr χ] (doc : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge rightBridge: Bridge) (forceTainted: Bool) : MeasureResult χ (MeasureSet χ) := do
  -- if (← get).giveUp == 0 then
  --   return ← leafSet {
  --     last := col
  --     cost := Cost.text widthLimit 0 0
  --     layout := fun ss => "(giveup)"::ss
  --     spacingR := bridgeFlex
  --   }
  -- modify (fun cacheStore =>
  --   {cacheStore with giveUp := cacheStore.giveUp - 1}
  -- )
  -- If we were to exceed the widthLimit we delay any attempt to optimize
  -- the layout of `doc1` in hopes that another branch of this function finds
  -- a non tainted `MeasureSet`.
    if doc.meta.shouldBeCached then
      --measureDiff "start check cache"
      let (measureResults, remainingBridges) ← getCached doc.meta.id indent col leftBridge forceTainted
      if remainingBridges.isEmpty then
        -- if the cache found results for all ingoing bridges then return existing result
        -- dbg_trace s!"Cache hit for {doc.meta.id} with {remainingBridges} at {col} {indent}"
        --measureDiff "cache hit to cache"
        return measureResults
      else
        -- only check the bridges that have not already been checked yet
      -- dbg_trace s!"Cache miss for {doc.meta.id} with {remainingBridges} at {col} {indent}"

      let value ← exceedCheck doc trace col indent widthLimit remainingBridges forceTainted
      addToCache doc.meta.id indent col (!forceTainted) remainingBridges value
      --measureDiff s!"added to cache"
      -- dbg_trace s!"Cache add for {doc.meta.id} for {remainingBridges} at {col} {indent} :: setSize: {value.size}"
      return value
    else
      exceedCheck doc trace col indent widthLimit leftBridge forceTainted


where
  exceedCheck (doc : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge : Bridge) (forceTainted: Bool) : MeasureResult χ (MeasureSet χ) := do
    --measureDiff s!"exceed check {doc.kind}"
    let exceeds :=
      match doc with
      | .text s _ => indent > widthLimit || col + s.length > widthLimit
      | _ => indent > widthLimit || col > widthLimit
    if exceeds && !forceTainted then
      let state :TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge}
      let tainted := (TaintedTrunk.center doc state doc.meta.id)
      return .tainted tainted false
    else
      return (← core doc trace col indent widthLimit leftBridge forceTainted)
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (ppl : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge: Bridge) (forceExpand : Bool): MeasureResult χ (MeasureSet χ) := do
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match ppl with
    | .text s _ =>
      if s.length == 0 then
        leafSet {
          last := col + s.length,
          cost := Cost.text widthLimit col s.length
          layout := fun ss => s :: ss
          bridgeR := rightBridge
        }
      else
        if leftBridge == bridgeFlex then
          leafSet {
              last := col + s.length,
              cost := Cost.text widthLimit col s.length
              layout := fun ss => s :: ss
              bridgeR := bridgeFlex
            }
        else
          let expandedBridge := possibilitiesToDoc leftBridge false <> (toDoc s|>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex}) |>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex}
          core expandedBridge trace col indent widthLimit bridgeFlex forceExpand
    | .newline flattened _ =>
      if leftBridge == bridgeFlex then
        leafSet {
          last := indent,
          cost := Cost.nl,
          layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss,
          bridgeR := bridgeFlex
        }
      else
        -- TODO: consider stopping force expand here
        core (possibilitiesToDoc leftBridge false <> (nl) |>.setMeta {collapsesBridges := Ternary.yes, paths := acceptFlex}) trace col indent widthLimit bridgeFlex forceExpand
    | .concat lhs rhs m =>
      --measureDiff "before calc concat"
      let targetLeft := rhs.meta.paths.foldl (fun acc (rl, rr) => if rr.overlapsWith rightBridge then rl ||| acc else acc) bridgeNull
      let newRight := lhs.meta.paths.foldl (fun acc (ll, lr) => if ll.overlapsWith leftBridge && lr.overlapsWith targetLeft then lr ||| acc else acc) bridgeNull
      --measureDiff "after calc concat"
      -- -- dbg_trace s!"targetLeft: {targetLeft} new right: {newRight}  existing {rightBridge} left: {leftBridge} leftPaths {lhs.meta.paths} rightPaths {rhs.meta.paths} lhs{lhs.toString} rhs {rhs.toString}"
      let left ← (lhs.resolve trace col indent widthLimit leftBridge newRight forceExpand)
      let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge}
      processConcat left rhs forceExpand taintedState m.id
      -- let targetLeft := rhs.meta.paths.foldl (fun acc (rl, rr) => if rr.overlapsWith rightBridge then rl ||| acc else acc) bridgeNull
      -- let newRight := lhs.meta.paths.foldl (fun acc (ll, lr) => if ll.overlapsWith leftBridge && lr.overlapsWith targetLeft then lr ||| acc else acc) bridgeNull
      -- let left ← (lhs.resolve trace col indent widthLimit leftBridge newRight forceExpand)
      -- let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := rightBridge}
      -- processConcat left rhs forceExpand taintedState m.id
      -- processConcatList (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) trace (fun l newSpacing => rhs.resolve trace l.last indent widthLimit newSpacing flatten forceExpand)
    | .choice lhs rhs _ => do
      -- check if there is a chance for the algorithm to complete successfully
      -- lhs.meta.paths.foldl (fun (accl, accr) (l, r) => (accl, accr))
      --measureDiff "Before checkSol"
      let leftHasSolution := lhs.meta.paths.any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)
      let rightHasSolution := rhs.meta.paths.any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)
      --measureDiff "after checkSol"
      match (leftHasSolution, rightHasSolution) with
      | (true, true) =>
        let left ← (lhs.resolve trace col indent widthLimit leftBridge rightBridge forceExpand)
        let right ← (rhs.resolve trace col indent widthLimit leftBridge rightBridge forceExpand)
        return left.merge right
      | (true, false) =>
        lhs.resolve trace col indent widthLimit leftBridge rightBridge forceExpand
      | _ =>
        rhs.resolve trace col indent widthLimit leftBridge rightBridge forceExpand

    | .nest indentOffset doc _ => doc.resolve trace col (indent + indentOffset) widthLimit leftBridge rightBridge forceExpand
    | .align doc _ => doc.resolve trace col col widthLimit leftBridge rightBridge forceExpand
    | .reset doc _ => doc.resolve trace col 0 widthLimit leftBridge rightBridge forceExpand
    | .fail e _ => leafSet {
      last := 0
      cost := Cost.nl
      bridgeR := bridgeNull
      layout := (fun _ => ["fail"])
      fail := [e::trace]
    }
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provide b _ =>
      let possibilities := leftBridge.provideIntersection b
      if possibilities == bridgeNull then
        return impossibleMeasureSet trace
        -- (Doc.fail "impossible bridge").resolve trace col indent widthLimit (bridgeFlex) forceExpand
      else
        leafSet {
          cost := Cost.text 0 0 0,
          fail := none,
          last := col,
          layout := id
          bridgeR := possibilities
        }
      -- else
      --   inner.resolve trace col indent widthLimit possibilities forceExpand
    | .require b _ =>
      if leftBridge == bridgeFlex then
        -- let fail : Doc := Doc.fail "require given no bridges"
        -- fail.resolve trace col indent widthLimit bridgeFlex forceExpand
        return impossibleMeasureSet trace
      else
        let possibilities := leftBridge.requireIntersection b
        let choices := (possibilitiesToDoc possibilities true)
        (choices).resolve trace col indent widthLimit bridgeFlex bridgeFlex forceExpand
    | .rule s doc _ =>
      doc.resolve (s::trace) col indent widthLimit leftBridge rightBridge forceExpand
    | .flatten _ _ =>
      -- doc.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge true forceExpand
      panic! "flatten should be handled before"
    | .stx _ _ =>
      panic! "Syntax should be expanded before reaching this point"
    | .cost c _ =>
      -- let inner ← doc.resolve trace col indent widthLimit leftBridge forceExpand
      let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
      leafSet {
        cost := lineCost,
        fail := none,
        last := col,
        layout := id
        bridgeR := rightBridge
      }
      -- match inner with
      -- | .tainted t e => return .tainted (TaintedTrunk.cost c t doc.meta.id) e
      -- | .set ms =>
      --   let withCost := ms.map (fun m => m.addCost (lineCost))
      --   return .set withCost
    | .bubbleComment comment _ =>
      leafSet {
        cost := Cost.text 0 0 0,
        fail := none,
        last := col,
        layout := placeComment indent comment
        bridgeR := rightBridge
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
  processConcat (left : MeasureSet χ) (right : Doc) (forceExpand : Bool) (state: TaintedState) (concatId : Nat): MeasureResult χ (MeasureSet χ) := do
    match left with
    | .tainted leftThunk e =>
      -- If the lhs is already tainted we can wrap the computation of the rhs
      -- in a tainted thunk, thus prunning it away.
      return .tainted (TaintedTrunk.leftTainted leftThunk right state concatId) e
      -- .tainted (fun _ =>
      --   let left := expandTainted leftThunk
      --   match processLeft left with
      --   | .tainted rightThunk => left ++ rightThunk ()
      --   | .set (right :: _) => left ++ right
      --   | .set [] => panic! "Empty measure sets are impossible"
      -- )
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

        match ← (right.resolve state.trace l.last state.indent widthLimit l.bridgeR rightBridge forceExpand) with
        | .tainted rightThunk e => return .tainted (TaintedTrunk.rightTainted l rightThunk state concatId) e
        | .set (r :: rights) => return .set (dedup rights [] (l.concat r))
        | .set [] => return impossibleMeasureSet trace

       let rec concatAllWithRight  : List (Measure χ) →  MeasureResult χ (MeasureSet χ)
         | [] => return impossibleMeasureSet trace
         | [l] => concatOneWithRight l
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
      let (result, remainingBridges) ← getCached id state.col state.indent state.leftBridge true
      if remainingBridges == bridgeNull then
        match result with
        | .tainted t _ =>
          let m ← expandTainted' t
          addToCache id state.indent state.col true state.leftBridge (.set [m])
          return m
        | .set (m :: _) =>
          return m
        | .set [] =>
          return impossibleMeasure state.trace
      else
        let m ← expandTainted' trunk
        addToCache id state.indent state.col true state.leftBridge (.set [m])
        return m
    else
      expandTainted' trunk
  | none =>
    expandTainted' trunk
  where
  expandTainted' : TaintedTrunk χ → MeasureResult χ (Measure χ)
  | .leftTainted (left : (TaintedTrunk χ)) (right:Doc) (state:TaintedState) (_:Nat) => do
    let leftMeasure ← expandTainted left
    let r ← right.resolve state.trace leftMeasure.last state.indent state.widthLimit state.leftBridge state.rightBridge true
    match r with
    | .tainted t _ => return leftMeasure.concat (← expandTainted t)
    | .set (m::_) => return leftMeasure.concat m
    | _ => return impossibleMeasure state.trace
  | .rightTainted left right _ _ => do
    let r ← expandTainted right
    return left.concat r
  | .center doc state _ => do
    -- let mut result : Measure χ := []
    let r ← doc.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.rightBridge true
    match r with
    | .tainted t _ => expandTainted t
    | .set (m::_) => return m
    | _ => return impossibleMeasure state.trace



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


/--
Find an optimal layout for a document and render it.
-/
partial def Doc.print (χ : Type) [Inhabited χ] [Repr χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) (log : Option (List String)): IO (PrintResult χ) := do
  -- let (preferredGroups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeFlex false false).run (initCache cacheSize log)).run
  if doc.meta.paths.size == 0 then
    dbg_trace s!"WARNING: document does not contain a solution"
  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeEnding false).run (initCache cacheSize log))

  match preferredGroups with
  | .set (m::_) =>
    return {
      log := cache.log,
      layout := String.join (m.layout []).reverse,
      isTainted := false,
      cost := m.cost
    }
  | .set ([]) =>
    return {
      log := cache.log,
      layout := "No solution found",
      isTainted := false,
      cost := Cost.text 0 0 0
    }
  | .tainted t _ =>
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

partial def runFlatten (nextId : Nat) (doc : Doc) : (Doc × Nat) :=
  let (doc, cache2) := (flattenPreprocessor false false doc).run {nextId := nextId, cached := Std.HashMap.empty}
  (doc, cache2.nextId)

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  -- let a ← (--measureDiff "start")
  let ((doc, cacheSize), t) ← measureTime (fun _ => return (runFlatten cacheSize doc))
  -- dbg_trace s!"time taken{(t).toFloat / 1000000000.0} s"
  -- --measureDiff "flattenTime"
  return (← Doc.print χ doc cacheSize col widthLimit (none)) |>.layout

partial def Doc.prettyPrintLog (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  let (doc, cacheSize) := (runFlatten cacheSize doc)
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
#eval (runFlatten 1 ((provideDoc bridgeSpace <^> provideDoc bridgeNl) <_> "c"))
#eval concatPaths #[(2, 2), (1, 2), (4, 4), (1, 4), (8, 8), (1, 8)] #[(8, 8), (1, 8)]
-- #eval ("Hello" <> "" <> "you").print DefaultCost 1 0 100 (some [])
#eval concatPaths #[(1,1)] #[(1,8)]
end PrettyFormat
