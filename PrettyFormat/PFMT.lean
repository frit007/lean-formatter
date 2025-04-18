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
  -- match lhs, rhs with
  -- | .set b lhs, .set _ rhs =>
  let lhs' := lhs.set.filter (fun s => s.fail.isNone)
  let rhs' := rhs.set.filter (fun s => s.fail.isNone)
  if (lhs'.length == 0 && rhs'.length == 0) then
    let addErrors (acc:List (List String)) (x:Measure χ):=
      match x.fail with
      | .some a => a++acc
      | .none => acc

    {
      bridge := lhs.bridge
      set := [Measure.mkFail (Cost.text 0 0 0) (lhs.set.foldl addErrors <| rhs.set.foldl addErrors [])]
    }
  else
    {
      bridge := lhs.bridge
      set := mergeSet lhs' rhs'
    }

-- def MeasureSet.getSet! [Cost χ] (m : MeasureSet χ) : List (Measure χ) :=
--   match m with
--   | .set _ s => s
--   | .tainted _ _ => panic! "Cannot get tainted set"

-- def MeasureSet.getBridge [Cost χ] (m : MeasureSet χ) : Bridge :=
--   match m with
--   | .set b _ => b
--   | .tainted b _ => b

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

-- def removeMeasureFails (m : MeasureSet χ): MeasureSet χ:=
--   match m with
--   | .set b xs =>
--     .set b (xs.filter (fun x => x.fail.isNone))
--   | x => x


-- def listToMeasureGroups [Cost χ] [DecidableRel (LE.le (α := χ))] (m : List (MeasureSet χ)) : MeasureGroups χ :=
--   m.map (fun x => {
--     bridge := x.getSet!,
--     set := x
--   })

-- I need to pass in a lot of extra information:
-- I need to pass the rules so we can transform the syntax tree
-- what if: I only allow caching on syntax elements?
--   - Does not generalize well
-- How do I identify if 2 syntax are the same?
--   - I need to pass in the syntax tree
--   - maybe I can identify the syntax tree by the hash of the syntax
--      - why would that be bad?
--         - slow: I need to hash the syntax tree. The syntax tree is large
--
def impossibleMeasure [Cost χ] [DecidableRel (LE.le (α := χ))] (trace: List String): Measure χ := {
      last := 0,
      cost := Cost.text 0 0 0,
      layout := fun ss => "(no possible formatter)" :: "\n" :: ss
      spacingR := bridgeFlex
      fail := ["impossible"::trace]
    }

partial def combineMeasureSetGroups [Cost χ] [DecidableRel (LE.le (α := χ))] (l r : MeasureGroups χ) : MeasureGroups χ :=
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
    let lbridge : Bridge := l.bridge
    let rbridge : Bridge := r.bridge

    if lbridge < rbridge then
      r :: combineInner ls (r::rs)
    else if rbridge < lbridge then
      l :: combineInner (l::ls) rs
    else
      let merged := MeasureSet.merge l r
      let rest := combineInner ls rs
      merged::rest


partial def combineMeasureSetGroupsExpand [Cost χ] [DecidableRel (LE.le (α := χ))] (l : MeasureGroups χ) (r : Bridge → Measure χ → MeasureResult χ (MeasureGroups χ)) : MeasureResult χ (MeasureGroups χ) := do
  let (ml,tl) := l
  let mut res : MeasureGroups χ := ([], tl)

  for ms in ml do
    for m in ms.set do
      let result ← r ms.bridge m
      res := combineMeasureSetGroups res result

  return l

  -- ml.foldl (fun (acc : MeasureGroups χ) (m : MeasureSet χ) =>

  -- ) ([], tl)

-- partial def combineMeasureSetGroupsExpand [Cost χ] [DecidableRel (LE.le (α := χ))] (ml : MeasureGroups χ) (mr : Bridge → Measure χ → MeasureGroups χ) : MeasureGroups χ :=
--   ml.foldl
--     (fun acc m =>
--       match m with
--       | .tainted b' trunk =>
--         let merged := m ()
--         -- take the first none failure
--         match merged.filter (fun (_, x) => x.fail.isNone) with
--         | (b, r) :: _ => -- We are in a tainted context, so we no longer care about the optimal solution and instead take the first solution
--           (mr b r)
--         | [] => [.set b' [impossibleMeasure []]]
--       | .set b ms =>
--         ms.foldl (fun acc x => combineMeasureSetGroups acc (mr b x)) acc
--     )
--     []

-- partial def combineMeasureSetGroupsClosed [Cost χ] [DecidableRel (LE.le (α := χ))] (ml : MeasureGroups χ) (mr : Bridge → Measure χ → MeasureGroups χ) : MeasureGroups χ :=
--   ml.foldl
--     (fun acc m =>
--       match m with
--       | .tainted b m =>
--         -- combineMeasureSetGroups acc ([.tainted b m])

--         let a := [.tainted b (fun _ =>
--           let lefts := m ()
--           let leftSets : List (MeasureSet χ):= lefts.map (fun (b, l) => .set b [l])
--           let combined := combineMeasureSetGroups acc (combineMeasureSetGroupsExpand leftSets mr)
--           -- is it a domain problem?
--           -- the problem is that we call a function that returns a measure group
--           -- that function might be a tainted function
--           -- at the moment we discard tainted results
--           -- but the desired result is to take a result, no matter how bad it is
--           -- essentially give up on the optimal solution
--           -- therefore Expand must continue to expand
--           combined.foldl (fun acc m =>
--             match m with
--             | .set b' (m::_) =>
--               (b', m)::acc
--             | .set _ _ =>
--               acc
--             | .tainted _ _ =>
--               acc
--           ) []
--           -- take the first none failure
--           -- match merged.filter (fun (_, x) => x.fail.isNone) with
--           -- | (b, r) :: _ => -- We are in a tainted context, so we no longer care about the optimal solution and instead take the first solution
--           --   (mr b r)
--           -- | [] => [.set b [impossibleMeasure []]]
--         )]
--         combineMeasureSetGroups acc a
--       | .set b ms =>
--         ms.foldl (fun acc x => combineMeasureSetGroups acc (mr b x)) acc
--     )
--     []

def orderMeasureGroup [Cost χ] [DecidableRel (LE.le (α := χ))] : MeasureGroups χ → MeasureGroups χ
  | (m,t) =>
    (m.mergeSort (fun a b => a.bridge > b.bridge), t)

def getId (id:Nat) (flatten:Bool) (cacheCount:Nat): Nat:=
  if flatten then
    id + cacheCount
  else
    id

def getCached [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : PPL) (indent col: Nat) (bridges : Bridge) (flatten : Bool) : MeasureResult χ (MeasureGroups χ × Bridge) := do
  let cacheStore ← get

  let (caches, bridges) := foundSolutions indent col [] bridges bridges (cacheStore.content.get! (getId doc.id flatten cacheStore.size))

  let measureSets := caches |>.foldl (fun (acc : MeasureGroups χ) (cache : Cache χ) =>
      combineMeasureSetGroups acc cache.results
    ) ([], [])
  return (measureSets, bridges)
where
  -- TODO: consider optimizing by considering previous results, if their maxWidth does not exceed the widthLimit
  -- Note: we need the original bridge here to check for the following scenario:
  --  - We have caches for 110 and 011, and are looking for 111 but when we find 110 we can erase 011 and therefore can't find 011, since it is not a subset of 001
  foundSolutions (indent col: Nat) (acc : List (Cache χ)) (originalBridge : Bridge): Bridge → List (Cache χ) → (List (Cache χ) × Bridge)
  | 0, _ => (acc, 0)
  | bridges, [] => (acc, bridges)
  | bridges, c::rest =>
    if c.leftBridge.subset originalBridge && c.indent == indent && c.column == col then
      foundSolutions indent col (c::acc) originalBridge (bridges.erase c.leftBridge) rest
    else
      foundSolutions indent col acc originalBridge bridges rest

def addToCache [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : PPL) (indent column: Nat) (flatten:Bool)(bridges : Bridge) (results:MeasureGroups χ): MeasureResult χ Unit := do
  modify (fun cacheStore =>
    let updatedCache := cacheStore.content.modify (getId doc.id flatten cacheStore.size) (fun caches =>
      {leftBridge:=bridges, indent := indent, column := column, flatten, results := results}::caches
    )
    {cacheStore with content := updatedCache}
  )

def leafSet [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (m : Measure χ): MeasureResult χ (MeasureGroups χ) :=
  let measureSet : MeasureSet χ := {
    bridge := m.spacingR
    set := [m]
  }
  return ([measureSet], [])

/--
This function efficiently computes a Pareto front for the problem of rendering
a `Doc` at a certain column position with a certain indentation level and width limit.

forceExpand: When evaluating tainted
-/
partial def PPL.resolve [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (ppl : PPL) (trace : List String) (col indent widthLimit : Nat) (lBridge : Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do

  -- If we were to exceed the widthLimit we delay any attempt to optimize
  -- the layout of `doc` in hopes that another branch of this function finds
  -- a non tainted `MeasureSet`.
  if ppl.shouldCache then
    let (measureResults, remainingBridges) ← getCached ppl indent col lBridge flatten
    if remainingBridges.isEmpty then
      -- if the cache found results for all ingoing bridges then return existing result
      return measureResults
    else
      -- only check the bridges that have not already been checked yet
      let value ← exceedCheck ppl trace col indent widthLimit remainingBridges flatten forceTainted
      addToCache ppl indent col flatten remainingBridges value
      return value
  else
    exceedCheck ppl trace col indent widthLimit lBridge flatten forceTainted
where
  exceedCheck (ppl : PPL) (trace : List String) (col indent widthLimit : Nat) (leftBridge: Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do
    let exceeds :=
      match ppl.d with
      | .text s => indent > widthLimit || col + s.length > widthLimit
      | _ => indent > widthLimit || col > widthLimit
    if exceeds && !forceTainted then
      let state :TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge:=leftBridge, flatten:=flatten}
      let tainted := (TaintedTrunk.center ppl state)
      return ([], [tainted])
      -- let a := MeasureSet.tainted spacing (fun _ =>
      --   let l : List (MeasureSet χ) ← core doc trace col indent widthLimit spacing
      --   let m := l.map (fun (m : MeasureSet χ) =>
      --     match m with
      --     | .tainted _ m =>
      --       m () |>.map (fun (_,x) => x)
      --     | .set _ (m :: _) => [m]
      --     | .set _ [] => panic! "Empty measure sets are impossible"
      --   )
      --   m
      -- )
      -- []
    else
      return orderMeasureGroup (← core ppl trace col indent widthLimit lBridge flatten forceTainted)
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (ppl : PPL) (trace : List String) (col indent widthLimit : Nat) (leftBridge : Bridge) (flatten forceExpand : Bool): MeasureResult χ (MeasureGroups χ) := do
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match ppl.d with
    | .text s =>
      if s.length == 0 then
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
          let expandedBridge := possibilitiesToDoc leftBridge <> s
          core expandedBridge trace col indent widthLimit bridgeFlex flatten forceExpand
    | .newline _ =>
      if leftBridge == bridgeFlex then
        leafSet {
          last := indent,
          cost := Cost.nl indent,
          layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
          spacingR := bridgeFlex
        }
      else
        core ((possibilitiesToDoc leftBridge) <> (nl)) trace col indent widthLimit bridgeFlex flatten forceExpand
    | .concat lhs rhs =>
      let left ← (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand)
      let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge:=leftBridge, flatten:=flatten}
      processConcatGroups left rhs forceExpand taintedState
      -- processConcatList (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) trace (fun l newSpacing => rhs.resolve trace l.last indent widthLimit newSpacing flatten forceExpand)
    | .choice lhs rhs =>
      return combineMeasureSetGroups (← lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) (← rhs.resolve trace col indent widthLimit leftBridge flatten forceExpand)
    | .nest indentOffset doc => doc.resolve trace col (indent + indentOffset) widthLimit leftBridge flatten forceExpand
    | .align doc => doc.resolve trace col col widthLimit leftBridge flatten forceExpand
    | .reset doc => doc.resolve trace col 0 widthLimit leftBridge flatten forceExpand
    | .bubbleComment comment => leafSet {
      last := col
      -- prioritize placing comments where they were placed by the user
      cost := (Cost.text widthLimit (indent + widthLimit) comment.length) + Cost.nl indent
      layout := placeComment 0 comment
    }
    | .endOfLineComment comment => leafSet {
      last := col + comment.length
      cost := Cost.nl indent
      layout := (fun ss => comment :: ss)
      spacingR := bridgeHardNl ||| bridgeNl
    }
    | .fail e => leafSet {
      last := 0
      cost := Cost.nl indent
      layout := (fun _ => ["fail"])
      fail := [e::trace]
    }
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provide s =>
      if leftBridge == bridgeFlex then
        -- [.set s [{
        --   last := col
        --   cost := Cost.text widthLimit col 0
        --   layout := fun ss => ss
        --   spacingR := s
        -- }]]
        leafSet {
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := s
        }
      else
        let possibilities := leftBridge.intersection s
        -- [.set possibilities [{
        --   last := col
        --   cost := Cost.text widthLimit col 0
        --   layout := fun ss => ss
        --   spacingR := possibilities
        -- }]]
        leafSet {
          last := col
          cost := Cost.text widthLimit col 0
          layout := fun ss => ss
          spacingR := possibilities
        }

    | .expect s =>
      if leftBridge == bridgeFlex then
        let fail : PPL := PPL.mk (Doc.fail "expect given no bridges")
        fail.resolve trace col indent widthLimit bridgeFlex flatten forceExpand
      else
        let possibilities := leftBridge.intersection s
        let choices := toPPL (possibilitiesToDoc possibilities)
        choices.resolve trace col indent widthLimit bridgeFlex flatten forceExpand
      | .rule s doc =>
        doc.resolve (s::trace) col indent widthLimit leftBridge flatten forceExpand
      | .flatten doc =>
        doc.resolve trace col indent widthLimit leftBridge true forceExpand
      | .stx _ =>
        panic! "Syntax should be expanded before reaching this point"

  possibilitiesToDoc (possibilities : Bridge) : Doc :=
    if possibilities == 0 then
      (Doc.fail "No possibilities")
    else Id.run do
      let mut options : List (Doc) := [.newline " "]

      if possibilities.contains bridgeNl || possibilities.contains bridgeHardNl then
        options := Doc.newline " "::options
      -- In any other case we we let the child handle the separation
      if possibilities.contains bridgeSpace then
        options := Doc.text " "::options

      -- if possibilities.any (fun f => f != space && f != spaceNl && f != spaceHardNl) then
      if possibilities.erase (bridgeSpace ||| bridgeNl ||| bridgeHardNl) != 0 then
        options := (Doc.text "")::options

      let choices : Doc := options.tail.foldl (fun (acc : Doc) (d : Doc) => Doc.concat (toPPL acc) (toPPL d) ) (options.head!)
      return choices



  /-
  Compute the set that contains the concatenations of all possible lhs measures
  with their corresponding rhs measure.
  -/
  processConcatGroups (left : MeasureGroups χ) (right : PPL) (forceExpand : Bool) (state: TaintedState) : MeasureResult χ (MeasureGroups χ) := do
    let concatOneWithRight (l : Measure χ) : MeasureResult χ (MeasureGroups χ) := do
       -- This is an optimized version of dedup from the paper. We use it to maintain
       -- the Pareto front invariant.
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

      -- let rights := processRight l (l.spacingR)
      let (rightResults, rightTainted) ← right.resolve state.trace state.col l.last state.widthLimit (l.spacingR) state.flatten false
      -- return (rightResults, rightTainted)
      let mut res : MeasureGroups χ := ([], [TaintedTrunk.rightTainted l rightTainted state])

      for rightSets in rightResults do
        -- dedup like pretty expressive
        -- TODO: test if dedup is worth it here
        let measureSets : List (Measure χ) := match rightSets.set |>.filter (fun m => m.fail.isNone) with
        | (r :: rights) => (dedup rights [] (l.concat r))
        | [] => [{impossibleMeasure trace with fail := some (rightSets.set.foldl (
            fun acc (a:Measure χ) =>
            match a.fail with
            | none => acc
            | some err => acc ++ err) [])}]

        res := combineMeasureSetGroups res ([{bridge := rightSets.bridge, set := measureSets}], [])

      return res
    let (ml, taintedLeft) := left

    let (t, taintedRight) ← combineMeasureSetGroupsExpand (ml, []) (fun b m =>
      concatOneWithRight m
    )

    return (t, taintedRight.append [TaintedTrunk.leftTainted taintedLeft right state])


  -- processConcatList (leftSet : List (MeasureSet χ)) (trace : List String) (processRight : Measure χ → Bridge → List (MeasureSet χ)) : MeasureGroups χ :=
  --   leftSet.foldl (fun acc (l : MeasureSet χ) =>
  --     combineMeasureSetGroups acc (processConcat l trace processRight)
  --   ) []

  -- processConcat (leftSet : MeasureSet χ) (trace : List String) (processRight : Measure χ → Bridge → List (MeasureSet χ)) : MeasureGroups χ :=
  --   match leftSet with
  --   | .tainted b leftThunk =>
  --     -- If the lhs is already tainted we can wrap the computation of the rhs
  --     -- in a tainted thunk, thus prunning it away.

  --     [.tainted b (fun _ =>
  --       let left := leftThunk ()
  --       let leftSets := left.map (fun (b, l) => .set b [l])
  --       let groups := combineMeasureSetGroupsExpand leftSets (fun b l =>
  --         let right := processRight l b
  --         combineMeasureSetGroupsClosed right (fun b r =>
  --           [.set b [l.concat r]]
  --         )
  --       )

  --       groups.foldl (fun acc m =>
  --         match m with
  --         | .set b' (m::_) =>
  --           (b', m)::acc
  --         | .set b' _ =>
  --           acc
  --         | .tainted b' m =>
  --           acc
  --       ) []
  --       )
  --     ]
  --   | .set b lefts =>
  --     let concatOneWithRight (l : Measure χ) : MeasureSet χ :=
  --        -- This is an optimized version of dedup from the paper. We use it to maintain
  --        -- the Pareto front invariant.
  --       -- let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
  --       --   match rights with
  --       --   | [] => List.reverse (currentBest :: result)
  --       --   | r :: rights =>
  --       --     let current := l.concat r
  --       --     if current.cost ≤ currentBest.cost then
  --       --       -- if the cost is less than or equal, then this should be a part of the result
  --       --       dedup rights result current
  --       --     else
  --       --       dedup rights (currentBest :: result) current

  --       let rec dedup (rights result : List (Measure χ)) (currentBest : Measure χ) : List (Measure χ) :=
  --         match rights with
  --         | [] => List.reverse (currentBest :: result)
  --         | r :: rights =>
  --           let current := l.concat r
  --           -- TODO: It should not be necessary to check spacing here
  --           if current.cost ≤ currentBest.cost && current.spacingR.lessThan currentBest.spacingR then
  --             -- if the cost is less than or equal, then this should be a part of the result
  --             dedup rights (result) current
  --           else
  --             dedup rights (currentBest :: result) current

  --       let rights := processRight l (l.spacingR)

  --       match rights |> removeMeasureFails with
  --       | .tainted rightThunk => .tainted (fun _ => l.concat (rightThunk ()))
  --       -- | .set (rights) => .set (rights.map (fun r => l.concat r))
  --       | .set (r :: rights) => .set (dedup rights [] (l.concat r))
  --       | .set [] => .set [{impossibleMeasure trace with fail := some (rights.getSet!.foldl (
  --           fun acc (a:Measure χ) =>
  --           match a.fail with
  --           | none => acc
  --           | some err => acc ++ err) [])}]

  --     let rec concatAllWithRight (lefts : List (Measure χ)) : MeasureSet χ :=
  --       match lefts |>.filter (fun x => x.fail.isNone) with
  --       | [] => .set [{impossibleMeasure trace with fail := some (lefts.foldl (
  --           fun acc (a:Measure χ) =>
  --           match a.fail with
  --           | none => acc
  --           | some err => acc ++ err) [])}]
  --       | [l] => concatOneWithRight l
  --       | l :: ls => MeasureSet.merge (concatOneWithRight l) (concatAllWithRight ls)

  --     concatAllWithRight lefts

  -- When we process tainted expand until we find a valid solution

-- when expanding tainted we take the first solution that does not fail to speed up computation
partial def expandTainted [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] : TaintedTrunk χ → MeasureResult χ (TaintedResult χ)
  | .leftTainted (left : List (TaintedTrunk χ)) (right:PPL) (state:TaintedState) => do
    let mut result : TaintedResult χ := []
    for l in left do
      let leftExpanded ← expandTainted l
      for (leftBridge, leftMeasure) in leftExpanded do

        let (rights, tainted) ← right.resolve state.trace state.col leftMeasure.last state.widthLimit leftBridge state.flatten true
        for t in tainted do
          result := mergeTaintedResults (← expandTainted t) result

        for right in rights do
          result := match right.set with
          | [] => result
          | rightMeasure :: _ => mergeTaintedResult (right.bridge, leftMeasure.concat rightMeasure) result

    -- match left with
    -- | l :: ls =>
    --   let l ← expandTainted l
    -- for l in left do
    --   let l ← expandTainted l
    --   let c ← right.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
      -- at this point I would like to return the result, and leave the rest unprocessed
      -- The idea here was to stop processing when we have uncovered all the bridges
      -- this is possible here, but it is not possible for right tainted
      -- if we can delay processing tainted, then we do not need to examine the right side to figure out which bridges they want

    -- we can't reach tainted at this point
    -- let (leftResults, _) 0← left.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
    -- let (rightResults, _) ← right.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
    -- return (leftResults ++ rightResults, [])
    return result
  | .rightTainted left rights _ => do
    let mut result : TaintedResult χ := []

    -- let (rights, _) ← right.resolve state.trace state.col leftMeasure.last state.widthLimit leftBridge state.flatten true
    for right in rights do
      for (rightBridge, rightMeasure) in (← expandTainted right) do
        let combined := left.concat rightMeasure
        result := mergeTaintedResult (rightBridge, combined) result
    -- we can't reach tainted at this point
    -- let (leftResults, _) ← left.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
    -- let (rightResults, _) ← right.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
    -- return (leftResults ++ rightResults, leftTainted ++ rightTainted)
    return []
  | .center doc state => do
    let mut result : TaintedResult χ := []
    let (resolved, tainted) ← doc.resolve state.trace state.col state.indent state.widthLimit state.leftBridge state.flatten true
    for t in tainted do
      result := mergeTaintedResults (← expandTainted t) result
    for ms in resolved do
      for m in ms.set do
        result := mergeTaintedResult (ms.bridge, m) result
    return result

  -- .center (doc : PPL) (state : TaintedState)
where
mergeTaintedResult : (Bridge × Measure χ) → TaintedResult χ → TaintedResult χ
| (b, m), [] => [(b, m)]
| (b, m), (b', m')::xs =>
  match compare b b' with
  | Ordering.lt => (b, m)::(b', m')::xs
  | Ordering.gt => (b', m')::(mergeTaintedResult (b, m) xs)
  | Ordering.eq =>
    if m ≤ m' then
      (b, m)::xs
    else
      (b', m')::(mergeTaintedResult (b, m) xs)
mergeTaintedResults : TaintedResult χ → TaintedResult χ → TaintedResult χ
| xs, [] => xs
| [], xs => xs
| (b, m)::xs, (b', m')::xs' =>
  match compare b b' with
  | Ordering.lt => (b, m)::(mergeTaintedResults xs ((b', m')::xs'))
  | Ordering.gt => (b', m')::(mergeTaintedResults ((b, m)::xs) xs')
  | Ordering.eq =>
    if m ≤ m' then
      (b, m)::(mergeTaintedResults xs xs')
    else
      (b', m')::(mergeTaintedResults xs xs')




structure PrintResult (χ : Type) where
  layout : String
  isTainted : Bool
  cost : χ
deriving Inhabited

-- /--
-- Render a choice less `Doc`. For choiceful documents use `Doc.prettyPrint`.
-- -/
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
-- def Doc.render (doc : Doc) (col : Nat) : String :=
--   String.join (go doc col 0 []).reverse
-- where
--   /--
--   A straight forward implementation of the choice less document semantics from Fig 8.
--   -/
--   go (doc : Doc) (col indent : Nat) (prev : List String): List String := Id.run do
--     match doc with
--     | .text str =>
--       str :: prev
--     | .newline _ => "".pushn ' ' indent :: "\n" :: prev
--     | .align doc => go doc col col prev
--     | .nest indentOffset doc => go doc col (indent + indentOffset) @ prev
--     | .concat lhs rhs =>
--       let mut lrender := go lhs col indent prev
--       go rhs (lineLength lrender) indent lrender
--       -- if lrender.length == 1 then
--       --   let lfirst := lrender[0]!
--       --   let mut rrender := go rhs (col + lfirst.length) indent
--       --   let rfirst := rrender[0]!
--       --   rrender := rrender.set! 0 (lfirst ++ rfirst)
--       --   rrender
--       -- else
--       --   let llast := lrender[lrender.size - 1]!
--       --   let rrender := go rhs (llast.length) indent
--       --   let rfirst := rrender[0]!
--       --   lrender := lrender.set! (lrender.size - 1) (llast ++ rfirst)
--       --   lrender := lrender ++ rrender[0:(rrender.size - 1)]
--       --   lrender
--     | .reset doc => go doc col 0 prev
--     | .choice .. => panic! "Not a choice less document"
--     | .endOfLineComment comment => comment :: prev
--     | .bubbleComment comment => placeComment 0 comment prev
--     | .fail e => panic! "A choice less document does not allow fail"
--     | .provide s => [toString s] ++ prev
--     | .expect s => [toString s] ++ prev
--     | .rule _ doc =>
--         go doc col indent prev

--   lineLength : List String → Nat
--     | [] => 0
--     | "\n"::_ => 0
--     | x :: xs => x.length + lineLength xs


/--
Find an optimal layout for a document and render it.
-/
def PPL.print (χ : Type) [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : PPL) (col widthLimit : Nat) : PrintResult χ :=
  let (groups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex false false).run {size:= 0, content := #[]}).run
  let (groups, tainted) := removeEndingBridges groups
  match printMeasureSet false groups with
  | none =>
    let (taintedSolution, _) := (firstTaintedOption tainted).run cache|>.run
    taintedSolution
  | some measureSet =>
    measureSet
where
  -- after the function is done
  removeEndingBridges (measures : MeasureGroups χ) : (Option (MeasureSet χ) × List (TaintedTrunk χ)) := Id.run do
    let (ms,t) := measures
    let mut res : MeasureGroups χ:= ([], t)
    for m in ms do
      let removedBridge := {m with bridge := bridgeFlex}
      res := combineMeasureSetGroups res ([removedBridge], [])

    match res with
    | (m::_, t) =>
      (some m, t)
    | ([], t) => (none, t)

  printMeasureSet (isTainted : Bool) (measureOpt : Option (MeasureSet χ)) : Option (PrintResult χ) :=
    match measureOpt with
    | none => none
    | some m =>
      match m.set with
      | [] => none
      | bestSolution::_ =>
        some {
          layout := String.join (bestSolution.layout []).reverse,
          isTainted := isTainted,
          cost := bestSolution.cost
        }

  firstTaintedOption : List (TaintedTrunk χ) → MeasureResult χ (PrintResult χ)
  | [] =>
    return {
      layout := "No solution found",
      isTainted := true,
      cost := Cost.text 0 0 0
    }
  | t::ts => do
    let expanded ← expandTainted t
    match expanded with
    | [] =>
      firstTaintedOption ts
    | (_,m)::_ =>
      return {
        layout := String.join (m.layout []).reverse,
        isTainted := true,
        cost := m.cost
      }


    -- let (groups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex false true).run {size:= 0, content := #[]}).run


  -- let (measure, isTainted) :=
  --   match measures with
  --   | .tainted thunk => (thunk (), true)
  --   | .set (measure :: _) => (measure, false)
  --   | .set [] => panic! "Empty measure sets are impossible"
  --       let c :=match measures with
  --   | .tainted _ => 0
  --   | .set a => a.length
  -- match measure.fail with
  -- | none =>
  --   {
  --     layout := String.join (measure.layout []).reverse,
  --     isTainted := isTainted,
  --     cost := measure.cost
  --   }
  -- | some failure =>
  --   let sorted := failure.mergeSort (fun a b => a.length < b.length)
  --   let x := sorted.foldl (fun (acc: String) (errs:List String) => acc ++ "\n" ++ (String.intercalate "::" errs.reverse)) ""
  --   {
  --     layout := if x.trim.length == 0 then s!"(unknown failure {isTainted} c {c})" else x,
  --     -- layout := "definite error",
  --     isTainted := isTainted,
  --     cost := measure.cost
  --   }

/--
Find an optimal layout for a document and render it.
-/
def PPL.prettyPrint (χ : Type) [Inhabited χ] [Cost χ] [DecidableRel (LE.le (α := χ))] (doc : PPL) (col widthLimit : Nat) : String :=
  PPL.print χ doc col widthLimit |>.layout

-- def Doc.comma : Doc := .text ","
-- def Doc.lbrack : Doc := .text "["
-- def Doc.rbrack : Doc := .text "]"
-- def Doc.lbrace : Doc := .text "{"
-- def Doc.rbrace : Doc := .text "}"
-- def Doc.lparen : Doc := .text "("
-- def Doc.rparen : Doc := .text ")"
-- def Doc.dquote : Doc := .text "\""
-- def Doc.empty : Doc := .text ""
-- def Doc.space : Doc := .text " "
-- def Doc.nl : Doc := .newline " "
-- def Doc.break : Doc := .newline ""
-- TODO: hard_nl and definitions based on it if necessary


  -- match doc with
  -- | .text str => .text str
  -- | .newline s => .text s
  -- | .align doc | .reset doc | .nest _ doc => doc.flatten
  -- | .concat lhs rhs => .concat lhs.flatten rhs.flatten
  -- | .choice lhs rhs => .choice lhs.flatten rhs.flatten
  -- | .bubbleComment comment => .bubbleComment comment
  -- /-
  -- This does not instantly fail, because the following document allows a endOfLineComment embedded in a flatten section
  -- `flatten (text "content" <> endOfLineComment comment) <> nl`
  -- -/
  -- | .endOfLineComment comment => .endOfLineComment comment
  -- | .fail e => .fail e
  -- | .provide s =>
  --   let s := s.erase bridgeHardNl
  --   let s := if s.contains bridgeNl then s.erase bridgeNl|>.union bridgeSpace else s
  --   if s.isEmpty then
  --     .fail "Provide Flattened to nothing"
  --   else
  --     .provide s
  -- | .expect s =>
  --   let s := s.erase bridgeHardNl
  --   let s := if s.contains bridgeNl then s.erase bridgeNl|>.union bridgeSpace else s
  --   if s.isEmpty then
  --     .fail "Expect flattened to nothing"
  --   else
  --     .expect s
  -- | .rule s doc => .rule s doc.flatten




-- def Doc.fold (f : Doc → Doc → Doc) (ds : List Doc) : Doc :=
--   match ds with
--   | [] => empty
--   | x :: xs => List.foldl f x xs

-- /--
-- Lay out a list of `Doc`s line by line. Aka `vcat`.
-- -/
-- def Doc.lines (ds : List Doc) : Doc := Doc.fold (· ++ .nl ++ ·) ds
-- def Doc.hcat (ds : List Doc) : Doc := Doc.fold .flattenedAlignedConcat ds

-- -- TODO: See how we can get some nicer choice operator
-- @[inherit_doc] scoped infixl:65 " <|||> "  => Doc.choice
-- @[inherit_doc] scoped infixl:65 " <+> "  => Doc.alignedConcat
-- @[inherit_doc] scoped infixl:65 " <-> "  => Doc.flattenedAlignedConcat



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

-- #eval
--   let d := Doc.concat (.provide bridgeHardNl) (.text "simple")
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   IO.println out

-- #eval (DefaultCost.le (DefaultCost.nl 3) (DefaultCost.text 100 2 0))
-- #eval (DefaultCost.le (DefaultCost.text 100 2 0) (DefaultCost.nl 3))

-- #eval (DefaultCost.add (DefaultCost.text 100 2 0) (DefaultCost.nl 3))
-- #eval (DefaultCost.add (DefaultCost.nl 3) (DefaultCost.nl 3))

end PrettyFormat
