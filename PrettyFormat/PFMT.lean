import Std.Data.HashSet
import Doc

open Std
/-
Originally created by Henrik Böving() based on pretty expressive (https://arxiv.org/abs/2310.01530),
Frithjof added fail, endOfLineComment, and bubbleComment
-/
namespace PrettyFormat

/--
If `MeasureSet.merge` receives two `MeasureSet.set` we use this operation to combine them
into a new Pareto front with correct ordering.
-/
private partial def mergeSet [Cost χ] (lhs rhs : List ((Measure χ))) (acc : List (Measure χ) := []) : List (Measure χ) :=
  match h1:lhs, h2:rhs with
  | [], _ => acc.reverse ++ rhs
  | _, [] => acc.reverse ++ lhs
  | l :: ls, r :: rs =>
    -- TODO: We do not have to compare bridge here because we know that they have the same bridge
    if LEB.leq l r && l.spacingR.lessThan r.spacingR then
      mergeSet lhs rs acc
    else if LEB.leq r l && r.spacingR.lessThan l.spacingR then
      mergeSet ls rhs acc
    else if l.last > r.last then
      mergeSet ls rhs (l :: acc)
    else
      mergeSet lhs rs (r :: acc)

def readableBridge (bridge : Bridge) : String := Id.run do
  let mut res := ""
  if bridge.overlapsWith bridgeSpace then
    res := s!"{res}space "
  if bridge.overlapsWith bridgeNl then
    res := s!"{res}newline "
  else
    if bridge.overlapsWith bridgeSpaceNl then
      res := s!"{res}spaceNl "
    if bridge.overlapsWith bridgeHardNl then
      res := s!"{res}hardNl "
  if bridge.overlapsWith bridgeNone then
    res := s!"{res}none "
  if bridge.overlapsWith bridgeFlex then
    res := s!"{res}flex "
  if bridge.overlapsWith bridgeImmediate then
    res := s!"{res}immediate "
  return res ++ s!"({bridge})"

def shallowSummary (mss : List (MeasureSet χ)) : String := Id.run do
  let mut res := ""
  if mss.length == 0 then
    return "no options"
  for ms in mss do
    match ms.set with
    | [] =>
      res := s!"{res}\n\n{readableBridge ms.rightBridge} ==> impossible"
    | x::_ =>
      if x.fail.isSome then
        res := s!"{res}\n\n{readableBridge ms.rightBridge} ==> {x.fail.get!}"
      else
        let formatted := String.join (x.layout []).reverse
        res := s!"{res}\n\n{readableBridge ms.rightBridge} => {formatted}"
  return res


/--
Combine the results from two `MeasureSet`s.
-/
def MeasureSet.merge [Cost χ] (lhs rhs : MeasureSet χ) : MeasureSet χ :=
  let lhs' := lhs.set.filter (fun s => s.fail.isNone)
  let rhs' := rhs.set.filter (fun s => s.fail.isNone)
  if (lhs'.length == 0 && rhs'.length == 0) then
    let addErrors (acc:List (List String)) (x:Measure χ):=
      match x.fail with
      | .some a => a++acc
      | .none => acc

    {
      rightBridge := lhs.rightBridge
      set := [Measure.mkFail (Cost.text 0 0 0) (lhs.set.foldl addErrors <| rhs.set.foldl addErrors [])]
    }
  else
    {
      rightBridge := lhs.rightBridge
      set := mergeSet lhs' rhs'
    }

def possibilitiesToDoc (possibilities : Bridge) (flatten : Bool) (expect:Bool) : Doc :=
  let possibilities := if flatten then
    if possibilities.overlapsWith bridgeSpaceNl then
      possibilities.add bridgeSpace |>.erase bridgeNl
    else
      possibilities.erase bridgeNl
  else
    possibilities

  Id.run do
    let mut options : List (Doc) := []

    if possibilities.overlapsWith bridgeNl then
      options := Doc.newline " "::options
    -- In any other case we we let the child handle the separation
    if possibilities.overlapsWith bridgeSpace then
      options := Doc.text " "::options

    -- anything other than space or newline get shortened to nothing
    if expect then
      -- To accept an immediate bridge you must expect it, to avoid accidental immediate bridges
      if (possibilities.erase (bridgeSpace ||| bridgeNl)) != 0 then
        options := (Doc.text "")::options
    else
      if possibilities.overlapsWith bridgeNone then
        options := (Doc.text "")::options

    if options.isEmpty then
      (Doc.fail "No possibilities")
    else
      -- panic! s!"How did we get here? No options? {possibilities} bridgeSpace:{bridgeSpace} bridgeNl:{bridgeNl} bridgeHardNl:{bridgeHardNl}"
      let choices : Doc := options.tail.foldl (fun (acc : Doc) (d : Doc) => (acc) <^> (d) ) (options.head!)
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

-- I need to pass in a lot of extra information:
-- I need to pass the rules so we can transform the syntax tree
-- what if: I only allow caching on syntax elements?
--   - Does not generalize well
-- How do I identify if 2 syntax are the same?
--   - I need to pass in the syntax tree
--   - maybe I can identify the syntax tree by the hash of the syntax
--      - why would that be bad?
--         - slow: I need to hash the syntax tree. The syntax tree is large
def impossibleMeasure [Cost χ] (trace: List String): Measure χ := {
      last := 0,
      cost := Cost.text 0 0 0,
      layout := fun ss => "(no possible formatter)" :: "\n" :: ss
      spacingR := bridgeFlex
      fail := ["impossible"::trace]
    }

partial def combineMeasureSetGroups [Cost χ] (l r : MeasureGroups χ) : MeasureGroups χ :=
  let (ml,tl) := l
  let (mr,tr) := r
  let tainted := tl.append tr
  (combineInner ml mr, tainted)
where
  combineInner (ml mr : (List (MeasureSet χ))) : (List (MeasureSet χ)) :=
  match ml, mr with
  | [], rs => rs
  | ls, [] => ls
  | l::ls, r::rs =>
    let lbridge : Bridge := l.rightBridge
    let rbridge : Bridge := r.rightBridge

    if lbridge < rbridge then
      r :: combineInner (l::ls) rs
    else if rbridge < lbridge then
      l :: combineInner ls (r::rs)
    else
      let merged := MeasureSet.merge l r
      let rest := combineInner ls rs
      merged::rest


partial def combineMeasureSetGroupsExpand [Cost χ] (l : MeasureGroups χ) (r : Bridge → Measure χ → MeasureResult χ (MeasureGroups χ)) : MeasureResult χ (MeasureGroups χ) := do
  let (ml,tl) := l
  let mut res : MeasureGroups χ := ([], tl)

  for ms in ml do
    for m in ms.set do
      let result ← r ms.rightBridge m
      res := combineMeasureSetGroups res result

  return res

partial def orderMeasureGroup [Cost χ] : MeasureGroups χ → MeasureGroups χ
  | (m,t) =>
    (m.mergeSort (fun a b => a.rightBridge > b.rightBridge), t)

partial def getId (id:Nat) (flatten:Bool) (cacheCount:Nat): Nat:=
  if flatten then
    id + cacheCount
  else
    id

partial def getCached [Inhabited χ] [Cost χ] (id indent col: Nat) (bridges : Bridge) (flatten : Bool) (allowTainted : Bool): MeasureResult χ (MeasureGroups χ × Bridge) := do
  let cacheStore ← get
  let bucket := cacheStore.content.get! (getId id flatten cacheStore.size)
  cacheLog (fun () => s!"Bucket size {bucket.length} the id {id}")
  let (caches, bridges) := foundSolutions indent col [] bridges allowTainted bridges (bucket)

  let measureSets := caches |>.foldl (fun (acc : MeasureGroups χ) (cache : Cache χ) =>
      combineMeasureSetGroups acc cache.results
    ) ([], [])
  return (measureSets, bridges)
where
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

def addToCache [Inhabited χ] [Cost χ] (id indent column: Nat) (flatten:Bool) (isTainted : Bool) (leftBridges : Bridge) (results:MeasureGroups χ): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    let updatedCache := cacheStore.content.modify (getId id flatten cacheStore.size) (fun caches =>
      {leftBridge:=leftBridges, indent := indent, column := column, flatten, isTainted := isTainted, results := results}::caches
    )
    {cacheStore with content := updatedCache}
  )

def leafSet [Inhabited χ] [Cost χ] (m : Measure χ): MeasureResult χ (MeasureGroups χ) :=
  let measureSet : MeasureSet χ := {
    rightBridge := m.spacingR
    set := [m]
  }
  return ([measureSet], [])

/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.

leftBridge: the bridges before this document, these limit the types of documents we can create
rightBridge: the bridges after this document, these limit the types of documents that can follow this document
 - rightBridge is primarily used in a tainted context where we want to provide any legal answer.
 - but to accomplish this safely we must ensure that we provide legal answers to all possible right bridges.
   - This comes with the issue that if there are no solutions for all rightbridges, then we will try all of the solutions
forceExpand: When evaluating tainted
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] (ppl : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge rightBridge: Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do
  -- if (← get).giveUp == 0 then
  --   cacheLog fun _ => (s!"Cache::giveup {ppl.meta.id} {trace.length} {col} {indent} {widthLimit}")
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
  if ppl.meta.shouldBeCached then
    let (measureResults, remainingBridges) ← getCached ppl.meta.id indent col leftBridge flatten forceTainted
    if remainingBridges.isEmpty then
      cacheLog fun _ => (s!"Cache::hit for {ppl.meta.id} with {remainingBridges.str} remaining bridges")
      -- if the cache found results for all ingoing bridges then return existing result
      return measureResults
    else
      cacheLog fun _ => (s!"Cache::miss for {ppl.meta.id} with {remainingBridges.str} remaining bridges (got {measureResults.fst.length} results)")
      -- only check the bridges that have not already been checked yet
      let value ← exceedCheck ppl trace col indent widthLimit remainingBridges rightBridge flatten forceTainted
      addToCache ppl.meta.id indent col flatten (!forceTainted) remainingBridges value
      return value
  else
    exceedCheck ppl trace col indent widthLimit leftBridge rightBridge flatten forceTainted
where
  exceedCheck (ppl : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge rightBridge: Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do
    let exceeds :=
      match ppl with
      | .text s _ => indent > widthLimit || col + s.length > widthLimit
      | _ => indent > widthLimit || col > widthLimit
    if exceeds && !forceTainted then
      let state :TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := rightBridge, expectBridge:=rightBridge, flatten:=flatten}
      let tainted := (TaintedTrunk.center ppl state)
      return ([], [tainted])
    else
      return orderMeasureGroup (← core ppl trace col indent widthLimit leftBridge flatten forceTainted)
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (ppl : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge : Bridge) (flatten forceExpand : Bool): MeasureResult χ (MeasureGroups χ) := do
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match ppl with
    | .text s _ =>
      if s.length == 0 then
        -- panic! s!"leftbridge do nothing {leftBridge} s:{s}"
        leafSet {
          last := col + s.length,
          cost := Cost.text widthLimit col s.length
          layout := fun ss => s :: ss
          spacingR := leftBridge
          }
      else
        if leftBridge == bridgeFlex then
          leafSet {
              last := col + s.length,
              cost := Cost.text widthLimit col s.length
              layout := fun ss => s :: ss
              spacingR := bridgeFlex
            }
        else
          let expandedBridge := possibilitiesToDoc leftBridge flatten false <> s
          -- cacheLog (s!"TODO: expandBridge {leftBridge} => {expandedBridge.toString}}")
          core expandedBridge trace col indent widthLimit bridgeFlex flatten forceExpand
    | .newline flattened _ =>
      if leftBridge == bridgeFlex then
        if flatten then
          match flattened with
          | some s =>
            core (Doc.text s) trace col indent widthLimit leftBridge flatten forceExpand
          | none =>
            core (Doc.fail "flattened newline") trace col indent widthLimit leftBridge flatten forceExpand
        else
          leafSet {
            last := indent,
            cost := Cost.nl indent,
            layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
            spacingR := bridgeFlex
          }
      else
        core (possibilitiesToDoc leftBridge flatten false <> (nl)) trace col indent widthLimit bridgeFlex flatten forceExpand
    | .concat lhs rhs m =>
      let expectedBridge := match rhs.isMetaConstruct with
      | Trilean.True => rightBridge
      | Trilean.False => rhs.meta.leftBridge
      | Trilean.Unknown => rhs.meta.leftBridge ||| rightBridge

      let left ← (lhs.resolve trace col indent widthLimit leftBridge expectedBridge flatten forceExpand)
      cacheLog fun _ => (s!"CONCAT: left ? {shallowSummary left.fst} tainted ??{left.snd.length}")
      let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, expectBridge:=rightBridge, flatten:=flatten}
      processConcatGroups left rhs forceExpand taintedState m.id
      -- processConcatList (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) trace (fun l newSpacing => rhs.resolve trace l.last indent widthLimit newSpacing flatten forceExpand)
    | .choice lhs rhs _ => do
      let left ← (lhs.resolve trace col indent widthLimit leftBridge rightBridge flatten forceExpand)
      let right ← (rhs.resolve trace col indent widthLimit leftBridge rightBridge flatten forceExpand)
      let combined := combineMeasureSetGroups left right
      -- cacheLog (s!"TODO: combine left ({shallowSummary left.fst}) right ({shallowSummary right.fst}) combined ({shallowSummary combined.fst})")
      return combined
    | .nest indentOffset doc _ => doc.resolve trace col (indent + indentOffset) widthLimit leftBridge rightBridge flatten forceExpand
    | .align doc _ => doc.resolve trace col col widthLimit leftBridge rightBridge flatten forceExpand
    | .reset doc _ => doc.resolve trace col 0 widthLimit leftBridge rightBridge flatten forceExpand
    | .bubbleComment comment _ => leafSet {
      last := col
      -- prioritize placing comments where they were placed by the user
      cost := (Cost.text widthLimit (indent + widthLimit) comment.length) + Cost.nl indent
      layout := placeComment 0 comment
    }
    | .fail e _ => leafSet {
      last := 0
      cost := Cost.nl indent
      layout := (fun _ => ["fail"])
      fail := [e::trace]
    }
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provide s _ =>
      if leftBridge == bridgeFlex then
        leafSet {
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := s
        }
      else
        let possibilities := leftBridge.intersection s
        leafSet {
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := possibilities
        }

    | .require s _ =>
      if leftBridge == bridgeFlex then
        let fail : Doc := Doc.fail "require given no bridges"
        fail.resolve trace col indent widthLimit bridgeFlex rightBridge flatten forceExpand
      else
        let possibilities := leftBridge.intersection s
        let choices := (possibilitiesToDoc possibilities flatten true)
        choices.resolve trace col indent widthLimit bridgeFlex rightBridge flatten forceExpand
      | .rule s doc _ =>
        doc.resolve (s::trace) col indent widthLimit leftBridge rightBridge flatten forceExpand
      | .flatten doc _ =>
        doc.resolve trace col indent widthLimit leftBridge rightBridge true forceExpand
      | .stx _ _ =>
        panic! "Syntax should be expanded before reaching this point"
      | .cost c _ => leafSet {
          last := col
          cost := Cost.text widthLimit 0 0
          layout := fun ss => ss
          spacingR := leftBridge
        }

  /-
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcatGroups (left : MeasureGroups χ) (right : Doc) (forceExpand : Bool) (state: TaintedState) (concatId : Nat): MeasureResult χ (MeasureGroups χ) := do
    let concatOneWithRight (l : Measure χ) : MeasureResult χ (MeasureGroups χ) := do
       -- This is an optimized version of dedup from the paper. We use it to maintain
       -- the Pareto front invariant.
      let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
        match rights with
        | [] => List.reverse (currentBest :: result)
        | r :: rights =>
          let current := l.concat r
          -- TODO: It should not be necessary to check spacing here
          if LEB.leq current.cost currentBest.cost && current.spacingR.lessThan currentBest.spacingR then
            -- if the cost is less than or equal, then this should be a part of the result
            dedup rights (result) current
          else
            dedup rights (currentBest :: result) current

      -- let rights := processRight l (l.spacingR)
      let (rightResults, rightTainted) ← right.resolve state.trace l.last state.indent state.widthLimit (l.spacingR) state.expectBridge state.flatten forceExpand
      -- return (rightResults, rightTainted)
      -- cacheLog fun _ => s!"CONCAT::LEFT  {l.layout []} rightDoc:{right.toString}"
      cacheLog fun _ => s!"CONCAT::LEFT  {l.layout []} "
      let tainted := if rightTainted.length > 0 then
          [TaintedTrunk.rightTainted l rightTainted state concatId]
        else
          []
      let mut res : MeasureGroups χ := ([], tainted)
      -- panic! s!"TODO: remove this panic {rightResults.length}"
      for rightSets in rightResults do
        -- dedup like pretty expressive
        -- TODO: test if dedup is worth it here
        let measureSets : List (Measure χ) := match rightSets.set |>.filter (fun m => m.fail.isNone) with
        | (r :: rights) =>
          -- let llll := String.join (l.layout [])
          -- let rrrr := String.join (r.layout [])
          -- let combined := l.concat r
          -- let cccc := String.join ((combined.layout [])|>.reverse)
          -- panic! s!"TODO: remove this panic {llll} {rrrr} {cccc}"
          (dedup rights [] (l.concat r))
        | [] =>
          [{impossibleMeasure trace with fail := some (rightSets.set.foldl (
            fun acc (a:Measure χ) =>
            match a.fail with
            | none => acc
            | some err => acc ++ err) [])}]

        -- let a : List (MeasureSet χ):= [{rightBridge := rightSets.rightBridge, set := measureSets}]
        -- panic! s!"TODO: arientso {shallowSummary (a)} ??? {shallowSummary (res.fst)}"
        res := combineMeasureSetGroups res ([{rightBridge := rightSets.rightBridge, set := measureSets}], [])

      return res
    let (ml, taintedLeft) := left

    -- panic! s!"TODO: left ? {shallowSummary ml}"
    -- cacheLog (s!"TODO: left ? {shallowSummary ml}")
    -- cacheLog "a"

    let (t, taintedRight) ← combineMeasureSetGroupsExpand (ml, []) (fun _ m =>
      concatOneWithRight m
    )
    let tainted := if taintedLeft.length > 0 then
      taintedRight.append [TaintedTrunk.leftTainted taintedLeft right state concatId]
    else
      taintedRight

    return (t, tainted)


-- When we are in a tainted state we no longer guarantee that we find the best solution
-- instead we just try to find any solution as fast as possible
-- Therefore as soon as we a solution we will return it
-- This is complicated by bridges, because we need to find a solution for all bridges that the right side expects
-- Therefore we will return as soon as we find a solution to all of the expected bridges

-- for this to work I must pass the expected bridge through the entire program
--  - I don' necessarily have an expected bridge which would be bridgeFlex
partial def expandTainted [Inhabited χ] [Cost χ] (trunk :TaintedTrunk χ): MeasureResult χ (TaintedResult χ) := do
  -- We are able to give up once we provide a solution to any bridge the right side expects
  --
  -- When we are in a tainted state do we want to combine all the results?
  -- (getCached) will we ever run the algorithm normally once we have begun processing tainted?
  -- I think we should always run the algorithm normally once we have begun processing tainted
  --  - The reason is that this allows us to find a good solution even if the first line is too long
  -- We could reset tainted when indent is below the width limit
  --  - This introduces the mixed cache problem: we could mark the cache as a tainted result
  --     - and then we would have to check if the cache is tainted or not
  --  - is it cleaner to keep tainted cache separate?
  --     - If we keep tainted cache separate then the core of the algorithm is easier to prove
  --     - the tainted cache can use the normal cache to find the best solution, if available
  --       - when tainted it does not have to care about the indentation of the cache, since we accept any solution anyway
  match trunk.cacheInfo with
  | some (state, id) =>
    if id != 0 then
      let (result, _) ← getCached id state.col state.indent state.leftBridge state.flatten true
      let mut cachedResults : TaintedResult χ := []
      let mut remainingBridges := state.expectBridge
      -- let a := result.fst
      for right in result.fst do
        match right.set with
        | [] => cachedResults := cachedResults
        | cachedResult :: _ =>
          cachedResults := mergeTaintedMeasures (right.rightBridge, cachedResult) cachedResults

      if remainingBridges == bridgeNull then
        cacheLog (fun _ => s!"Tainted::cache::hit::{id}")
        return cachedResults
      cacheLog (fun _ => s!"Tainted::cache::miss::{id} missing {remainingBridges.str} originally {state.expectBridge.str}")
      let foundResults ← expandTainted' remainingBridges trunk
      let foundBridges := foundResults.foldl (fun acc b => acc ||| b.fst) 0

      if foundResults.length > 0 then

        let measureGroups := taintedMeasureToMeasureGroups foundResults
        cacheLog (fun _ => s!"Tainted::cache::add::{id} for bridges {foundBridges.str} ({foundResults.length})")
        addToCache id state.indent state.col state.flatten true state.leftBridge measureGroups
      else
        cacheLog (fun _ => s!"Tainted::cache::fail did not expand to anything")
      return foundResults
    else
      expandTainted' state.expectBridge trunk
  | none =>
    expandTainted' bridgeFlex trunk
  where
  taintedMeasureToMeasureGroups (res:TaintedResult χ) : MeasureGroups χ:= Id.run do
    let mut measureSet := ([], [])

    for (rightBridge, result) in res do
      measureSet := combineMeasureSetGroups ([{set:=[result], rightBridge := rightBridge}],[]) measureSet

    return measureSet

  expandTainted' (rightBridge : Bridge): TaintedTrunk χ → MeasureResult χ (TaintedResult χ)
  | .leftTainted (left : List (TaintedTrunk χ)) (right:Doc) (state:TaintedState) (id:Nat) => do
    let mut result : TaintedResult χ := []
    let mut coveredBridges := bridgeNull
    if id != 0 then
      cacheLog fun _ => (s!"Tainted::Left::cache::{id}")

    cacheLog fun _ => (s!"Tainted::Left::{id} options {left.length}")
    for l in left do
      let leftExpanded ← expandTainted l
      cacheLog fun _ => (s!"Tainted::Left::{id} expanded to {leftExpanded.length} options")
      for (leftBridge, leftMeasure) in leftExpanded do
        if rightBridge.contains coveredBridges then
          return result -- we have found a possible solution to all bridges the next item requires
        cacheLog fun _ => (s!"Tainted::Left::{id} left measure: {leftMeasure.layout []} last:{leftMeasure.last}")

        let (rights, tainted) ← right.resolve state.trace leftMeasure.last state.indent state.widthLimit leftBridge rightBridge state.flatten true
        for t in tainted do
          if rightBridge.contains coveredBridges then
            return result
          -- cacheLog (s!"Tainted::Left tainted left {t} last:{t.last}")
          for (rightBridge, rightMeasure) in (← expandTainted t) do
            coveredBridges := coveredBridges ||| rightBridge
            -- cacheLog (s!"Tainted::Left tainted left {leftMeasure.layout []} last:{leftMeasure.last} right {rightMeasure.layout []} last:{rightMeasure.last}")
            result := mergeTaintedMeasures (rightBridge, leftMeasure.concat rightMeasure) result
        cacheLog fun _ => (s!"Tainted::Left::{id} found rights: {rights.length} options")
        for right in rights do
          coveredBridges := coveredBridges ||| right.rightBridge
          -- take the first valid options
          match right.set with
          | [] => result := result
          | rightMeasure :: _ =>
            cacheLog fun _ => (s!"Tainted::Left::{id} previous left {rightMeasure.layout []} combined with {(leftMeasure.concat rightMeasure).layout []} ")
            result := mergeTaintedMeasures (right.rightBridge, leftMeasure.concat rightMeasure) result

    return result
  | .rightTainted left rights s (id:Nat) => do
    if id != 0 then
      cacheLog fun _ => (s!"Tainted::Right::cache::{id}")
    cacheLog fun _ => (s!"Tainted::Right::{id} tainted Right layout :{left.layout []} last:{left.last} rightOptions:{rights.length}")
    let mut result : TaintedResult χ := []
    let mut coveredBridges := bridgeNull

    for right in rights do
      if rightBridge.contains coveredBridges then
        cacheLog (fun _ => s!"Tainted::Right we have found enough bridges wanted:{s.expectBridge} have {coveredBridges}")
        return result -- we have found a possible solution to all bridges the next item requires
      let expanded ← expandTainted right
      cacheLog (fun _ => s!"Tainted::Right expanded to {expanded.length}")
      for (rightBridge, rightMeasure) in expanded do
        let combined := left.concat rightMeasure
        cacheLog (fun _ => s!"Tainted::Right a solution? {combined.layout []}")
        result := mergeTaintedMeasures (rightBridge, combined) result

    return result
  | .center doc state => do
    let mut result : TaintedResult χ := []
    let (resolved, tainted) ← doc.resolve state.trace state.col state.indent state.widthLimit state.expectBridge state.expectBridge state.flatten true
    cacheLog fun _ => (s!"Tainted::Center and return... {resolved.length}")
    for t in tainted do
      result := mergeTaintedResults (← expandTainted t) result
    for ms in resolved do
      for m in ms.set do
        result := mergeTaintedMeasures (ms.rightBridge, m) result
    return result

  mergeTaintedMeasures : (Bridge × Measure χ) → TaintedResult χ → TaintedResult χ
  | (b, m), [] => [(b, m)]
  | (b, m), (b', m')::xs =>
    if m.fail.isSome then
      (b', m')::xs
    else if m'.fail.isSome then
      (b', m')::xs
    else
      match compare b b' with
      | Ordering.lt => (b, m)::(b', m')::xs
      | Ordering.gt => (b', m')::(mergeTaintedMeasures (b, m) xs)
      | Ordering.eq =>
        if LEB.leq m m' then
          (b, m)::xs
        else
          (b', m')::(mergeTaintedMeasures (b, m) xs)

  mergeTaintedResults : TaintedResult χ → TaintedResult χ → TaintedResult χ
  | xs, [] => xs
  | [], xs => xs
  | (b, m)::xs, (b', m')::xs' =>
    match compare b b' with
    | Ordering.lt => (b, m)::(mergeTaintedResults xs ((b', m')::xs'))
    | Ordering.gt => (b', m')::(mergeTaintedResults ((b, m)::xs) xs')
    | Ordering.eq =>
      if LEB.leq m m' then
        (b, m)::(mergeTaintedResults xs xs')
      else
        (b', m')::(mergeTaintedResults xs xs')




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
partial def Doc.print (χ : Type) [Inhabited χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) (log : Option (List String)): PrintResult χ :=
  let (preferredGroups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeFlex false false).run (initCache cacheSize log)).run
  let (goodSolution, solutions, tainted) := removeEndingBridges preferredGroups
  if goodSolution then
    printMeasureSet false solutions cache.log
  else
    let (taintedSolution, cache) := (firstTaintedOption tainted).run cache|>.run
    {taintedSolution with log := cache.log}
  -- {}
  -- The problem is I want to do, if there is an ideal nonfailing solution then do that
  -- otherwise try tainted
  -- if there is no tainted then output whatever the best solution tried to do
  -- can this be sorted into a line? yep a boolean

  -- let (groups, tainted) := removeEndingBridges preferredGroups
  -- match printMeasureSet false groups with
  -- | none =>
  --   let (taintedSolution, _) := (firstTaintedOption tainted).run cache|>.run
  --   {taintedSolution with log := cache.log ++ [s!"\n\n tainted solution?? {tainted.length}"]}
  -- | some measureSet => Id.run do
  --   -- let bb := groupsa.fst
  --   -- bb.foldl (fun acc m =>
  --   --   panic! s!"fst: {measureSet.layout} |||"
  --   -- ) measureSet
  --   -- for a in bb do
  --   --   panic! s!"sols: {a.set.length}"

  --   return {measureSet with log := cache.log ++ [s!"\n\n best?{measureSet.layout} tainted{tainted.length}"]}
where
  initCache (n:Nat) (log : Option (List String)): CacheStore χ :=
    -- allocate twice the space needed, so flatten is separated into its own category
    {size := n, content := Array.mkArray (n*2) [], log := log, giveUp := 1000}

  -- after the function is done
  removeEndingBridges (measures : MeasureGroups χ) : (Bool × MeasureSet χ × List (TaintedTrunk χ)) := Id.run do
    let (ms,t) := measures
    let mut res : MeasureGroups χ:= ([], t)
    for m in ms do
      let removedBridge := {m with rightBridge := bridgeFlex}
      res := combineMeasureSetGroups res ([removedBridge], [])
    match res with
    | (m::_, t) =>
      let noFailures := m.set.filter (fun ms => ms.fail.isNone)
      if !noFailures.isEmpty then
        return (true, m, t)
        -- return IntermediateResult.noIdealSolution m t
      else
        let bestSolution := noFailures.head!
        let bestSet := {m with set := [bestSolution]}
        return (false, bestSet, t)
        -- return IntermediateResult.idealSolution bestSet
    | ([], t) =>
      return (false, {rightBridge := bridgeFlex, set := []}, t)




  printMeasureSet (isTainted : Bool) (m : (MeasureSet χ)) (log : Option (List String)): (PrintResult χ) :=
    match m.set with
    | [] => panic! s!"TODO: no solution found"
    | bestSolution::_ =>
      {
        log := log,
        layout := String.join (bestSolution.layout []).reverse,
        isTainted := isTainted,
        cost := bestSolution.cost
      }

  firstTaintedOption : List (TaintedTrunk χ) → MeasureResult χ (PrintResult χ)
  | [] =>
    return {
      log := (← get).log,
      layout := "No solution found",
      isTainted := true,
      cost := Cost.text 0 0 0
    }
  | t::ts => do
    let expanded ← expandTainted t
    let rec firstNonFailure (taintedResult: (TaintedResult χ)) : Option (Bridge × Measure χ) :=
      match taintedResult with
      | [] => none
      | (b, m)::xs =>
        if m.fail.isSome then
          firstNonFailure xs
        else
          some (b, m)
    let first := firstNonFailure expanded

    match first with
    | none =>
      firstTaintedOption ts
    | some (_,m) =>
      if m.fail.isSome then
        firstTaintedOption ts
      else
        return {
          log := (← get).log,
          layout := String.join (m.layout []).reverse,
          isTainted := true,
          cost := m.cost
        }

/--
Find an optimal layout for a document and render it.
-/
partial def Doc.prettyPrint (χ : Type) [Inhabited χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : String :=
  Doc.print χ doc cacheSize col widthLimit (none) |>.layout

partial def Doc.prettyPrintLog (χ : Type) [Inhabited χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  let l := Doc.print χ doc cacheSize col widthLimit (some [])
  match l.log with
  | none => return ""
  | some log =>
    IO.println (s!"Log: {String.join (log.intersperse "\n\n")}")
  return l.layout

end PrettyFormat
