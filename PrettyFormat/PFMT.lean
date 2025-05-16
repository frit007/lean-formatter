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



structure FlattenState where
  nextId : Nat
  cached : Std.HashMap (Nat × Bool × Bool × Bool) Doc

abbrev FlattenStateM a := (StateM FlattenState) a


def FlattenStateM.genId : FlattenStateM Nat := do
  let state ← get
  let _ ← set {state with nextId := state.nextId + 1}
  return state.nextId

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
partial def flattenPreprocessor (flattenLeft flattenInner flattenRight: Bool) (d :Doc) : FlattenStateM Doc := do
  let meta := d.meta
  if meta.shouldBeCached then
    let state ← get
    let key := (meta.id, flattenLeft, flattenInner, flattenRight)
    match state.cached.get? key with
    | some d => return d
    | _ =>
      let doc ← flattenPreprocessor' d
      let newId ← FlattenStateM.genId
      let m : DocMeta := doc.calcMeta
      let doc := {m with id := newId} |> doc.setMeta
      modify (fun s => {s with cached := s.cached.insert key doc})
      return doc
  else
    let doc ← flattenPreprocessor' d
    let doc := doc.calcMeta |> doc.setMeta
    return doc
  -- TODO: update meta
where
  flattenPreprocessor'  : Doc → FlattenStateM (Doc)
    | .fail s m => return (.fail s m)
    | .text s m => return (.text s m)
    | .newline a m =>
      match a with
      | some s => return .text s m
      | _ => return .fail "cannot flatten" m
    | .choice left right m=> do
      let l ← flattenPreprocessor flattenLeft flattenInner flattenRight left
      let r ← flattenPreprocessor flattenLeft flattenInner flattenRight right
      return .choice l r m
    | .flatten inner _=> do
      let i ← flattenPreprocessor flattenLeft true flattenRight inner
      return i
    | .align inner m => do
      let i ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .align i m
    | .nest i inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .nest i inner m
    | .concat l r m => do
      if flattenInner then
        let l ← flattenPreprocessor flattenLeft true true l
        let r ← flattenPreprocessor true true flattenRight r
        return .concat l r m
      else
        let l ← flattenPreprocessor false false false l
        let r ← flattenPreprocessor false false false r
        return .concat l r m
    | .stx s _=> panic! "can't flatten syntax"
    | .reset inner m=> do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .reset inner m
    | .rule r inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .rule r inner m
    | .provideL b inner m=> do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      if flattenLeft then
        return .provideL b.flatten inner m
      else
        return .provideL b inner m
    | .provideR b inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      if flattenRight then
        return .provideR b.flatten inner m
      else
        return .provideR b inner m
    | .require b m =>
      if flattenLeft then
        return .require b.flatten m
      else
        return .require b m
    | .bubbleComment c inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .bubbleComment c inner m
    | .cost c inner m => do
      let inner ← flattenPreprocessor flattenLeft flattenInner flattenRight inner
      return .cost c inner m

def shallowSummary (mss : List (MeasureSet χ)) : String := Id.run do
  let mut res := ""
  if mss.length == 0 then
    return "no options"
  for ms in mss do
    match ms.set with
    | [] =>
      res := s!"{res}\n\n{ms.rightBridge.str} ==> impossible"
    | x::_ =>
      if x.fail.isSome then
        res := s!"{res}\n\n{ms.rightBridge.str} ==> {x.fail.get!}"
      else
        let formatted := String.join (x.layout []).reverse
        res := s!"{res}\n\n{ms.rightBridge.str} => {formatted}"
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
      layout := fun ss => "(no possible formatter)" :: (String.join (trace.intersperse "::")):: "\n" :: ss
      spacingR := bridgeFlex
      fail := ["impossible"::trace]
    }

def combineMeasureSetGroups [Cost χ] (l r : MeasureGroups χ) : MeasureGroups χ :=
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

def roughSizeOfMeasureSet (mg:MeasureGroups χ) : (Nat × Nat) := Id.run do
  let mut c := 0
  for ms in mg.fst do
    c := c + ms.set.length

  return (c, mg.snd.length)


def combineMeasureSetGroupsExpand [Cost χ] (l : MeasureGroups χ) (r : Bridge → Measure χ → MeasureResult χ (MeasureGroups χ)) : MeasureResult χ (MeasureGroups χ) := do
  let (ml,tl) := l
  let mut res : MeasureGroups χ := ([], tl)

  for ms in ml do
    for m in ms.set do
      let result ← r ms.rightBridge m
      res := combineMeasureSetGroups res result

  return res

def orderMeasureGroup [Cost χ] : MeasureGroups χ → MeasureGroups χ
  | (m,t) =>
    (m.mergeSort (fun a b => a.rightBridge > b.rightBridge), t)

def getId (id:Nat) (flatten:Bool) (cacheCount:Nat): Nat:=
  if flatten then
    id + cacheCount
  else
    id

def getCached [Cost χ] (id indent col: Nat) (bridges : Bridge) (flatten : Bool) (allowTainted : Bool): MeasureResult χ (MeasureGroups χ × Bridge) := do
  let cacheStore ← get
  let bucket := cacheStore.content.get! (getId id flatten cacheStore.size)
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
rightBridge: the bridges after this document, these are the bridges that will be followed by leafNodes, they are created by provideR
expectBridge: the bridges after this document, these limit the types of documents that can follow this document
 - expectBridge is primarily used in a tainted context where we want to provide any legal answer.
 - but to accomplish this safely we must ensure that we provide legal answers to all possible right bridges.
   - This comes with the issue that if there are no solutions for all expectBridge, then we will try all of the solutions
forceExpand: When evaluating tainted
-/
partial def Doc.resolve [Inhabited χ] [Cost χ] [Repr χ] (doc : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge NewRightBridge expectBridge: Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do
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
      let (measureResults, remainingBridges) ← getCached doc.meta.id indent col leftBridge flatten forceTainted
      if remainingBridges.isEmpty then
        -- if the cache found results for all ingoing bridges then return existing result
        return measureResults
      else
        -- only check the bridges that have not already been checked yet

      let value ← exceedCheck doc trace col indent widthLimit remainingBridges flatten forceTainted
      addToCache doc.meta.id indent col flatten (!forceTainted) remainingBridges value
      return value
    else
      let SIMPLIFY ← exceedCheck doc trace col indent widthLimit leftBridge flatten forceTainted
      return SIMPLIFY


where
  exceedCheck (doc : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge : Bridge) (flatten forceTainted: Bool) : MeasureResult χ (MeasureGroups χ) := do
    let exceeds :=
      match doc with
      | .text s _ => indent > widthLimit || col + s.length > widthLimit
      | _ => indent > widthLimit || col > widthLimit
    if exceeds && !forceTainted then
      let state :TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge := NewRightBridge, expectBridge:=expectBridge, flatten:=flatten}
      let tainted := (TaintedTrunk.center doc state)
      return ([], [tainted])
    else
      return orderMeasureGroup (← core doc trace col indent widthLimit leftBridge flatten forceTainted)
  /-
  The core resolver that actually computes the `MeasureSet`s that result from rendering `doc`
  in the given context.
  -/
  core (ppl : Doc) (trace : List String) (col indent widthLimit : Nat) (leftBridge: Bridge) (flatten forceExpand : Bool): MeasureResult χ (MeasureGroups χ) := do
    -- If we end up in this function we know that this cannot exceed the widthLimit
    -- and can thus savely return a set in all cases except concat.
    match ppl with
    | .text s _ =>
      if leftBridge == bridgeFlex then
        leafSet {
            last := col + s.length,
            cost := Cost.text widthLimit col s.length
            layout := fun ss => s :: ss
            spacingR := NewRightBridge
          }
      else
        let expandedBridge := possibilitiesToDoc leftBridge flatten false <> s
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
            cost := Cost.nl,
            layout := fun ss =>  "".pushn ' ' indent :: "\n" :: ss
            spacingR := bridgeFlex
          }
      else
        core (possibilitiesToDoc leftBridge flatten false <> (nl)) trace col indent widthLimit bridgeFlex flatten forceExpand
    | .concat lhs rhs m =>
      let left ← (lhs.resolve trace col indent widthLimit leftBridge bridgeFlex rhs.meta.leftBridge flatten forceExpand)
      let taintedState : TaintedState := {trace:=trace, col:=col, indent:=indent, widthLimit:=widthLimit, leftBridge := leftBridge, rightBridge:= NewRightBridge, expectBridge:=expectBridge, flatten:=flatten}
      processConcatGroups left rhs forceExpand taintedState m.id
      -- processConcatList (lhs.resolve trace col indent widthLimit leftBridge flatten forceExpand) trace (fun l newSpacing => rhs.resolve trace l.last indent widthLimit newSpacing flatten forceExpand)
    | .choice lhs rhs _ => do
      let left ← (lhs.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand)
      let right ← (rhs.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand)
      let combined := combineMeasureSetGroups left right
      return combined
    | .nest indentOffset doc _ => doc.resolve trace col (indent + indentOffset) widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
    | .align doc _ => doc.resolve trace col col widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
    | .reset doc _ => doc.resolve trace col 0 widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
    | .fail e _ => leafSet {
      last := 0
      cost := Cost.nl
      layout := (fun _ => ["fail"])
      fail := [e::trace]
    }
    -- At the moment we can't narrow down the spacing options for a `spacing` document.
    -- this could be done by
    -- desugaring spacing to choice
    | .provideL b inner _ =>
      let possibilities := leftBridge.provideIntersection b
      if possibilities == bridgeNull then
        (Doc.fail "impossible bridge").resolve trace col indent widthLimit bridgeFlex NewRightBridge (expectBridge.provideIntersection b) flatten forceExpand
      else
        inner.resolve trace col indent widthLimit possibilities NewRightBridge expectBridge flatten forceExpand
    | .provideR b inner _ =>
      let possibilities := NewRightBridge.provideIntersection b
      if possibilities == bridgeNull then
        (Doc.fail "impossible bridge").resolve trace col indent widthLimit bridgeFlex NewRightBridge (expectBridge.provideIntersection b) flatten forceExpand
      else
        inner.resolve trace col indent widthLimit possibilities NewRightBridge expectBridge flatten forceExpand
    | .require b _ =>
      if leftBridge == bridgeFlex then
        let fail : Doc := Doc.fail "require given no bridges"
        fail.resolve trace col indent widthLimit bridgeFlex NewRightBridge expectBridge flatten forceExpand
      else
        let possibilities := leftBridge.requireIntersection b
        let choices := (possibilitiesToDoc possibilities flatten true)
        (choices).resolve trace col indent widthLimit bridgeFlex NewRightBridge expectBridge flatten forceExpand
    | .rule s doc _ =>
      doc.resolve (s::trace) col indent widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
    | .flatten doc _ =>
      -- doc.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge true forceExpand
      panic! "flatten should be handled before"
    | .stx _ _ =>
      panic! "Syntax should be expanded before reaching this point"
    | .cost c doc _ =>
      let inner ← doc.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
      let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
      let withCost := inner.fst.map (fun ms => {ms with set := ms.set.map (fun m => m.addCost (lineCost))})

      -- IO.println s!"withCost {repr withCost[0]!.set[0]!.cost}"
      return (withCost, [TaintedTrunk.cost c inner.snd])
    | .bubbleComment comment doc _ =>
      let inner ← doc.resolve trace col indent widthLimit leftBridge NewRightBridge expectBridge flatten forceExpand
      let withComment := inner.fst.map (fun ms => {ms with set := ms.set.map (fun m => m.prependLayout (placeComment 0 comment))})
      return (withComment, [TaintedTrunk.bubbleComment comment inner.snd])

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
      let (rightResults, rightTainted) ← right.resolve state.trace l.last state.indent state.widthLimit (l.spacingR) state.rightBridge state.expectBridge state.flatten forceExpand
      -- return (rightResults, rightTainted)
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

    let (t, taintedRight) ← combineMeasureSetGroupsExpand (ml, []) (fun _ m =>
      concatOneWithRight m
    )


    -- if we provide a solution to all required bridges then we can discard left tainted, because we already have a possible solution to all scenarios

    -- all the edge cases
    --  - flatten
    --    - right side goes through flatten
    --       -
    let providedBridges := left.fst.foldl (fun acc ms => ms.rightBridge ||| acc) bridgeNull

    let expected := if state.flatten then state.expectBridge.flatten else state.expectBridge

    -- let providedBridges := if state.flatten then providedBridges.flatten else providedBridges
    let tainted := if taintedLeft.length > 0 && !(providedBridges.canHandle expected) then
    -- let tainted := if taintedLeft.length > 0 then
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
partial def expandTainted [Inhabited χ] [Repr χ] [Cost χ] (trunk :TaintedTrunk χ): MeasureResult χ (TaintedResult χ) := do
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
        return cachedResults
      let foundResults ← expandTainted' remainingBridges trunk
      let foundBridges := foundResults.foldl (fun acc b => acc ||| b.fst) 0

      if foundResults.length > 0 then
        let measureGroups := taintedMeasureToMeasureGroups foundResults
        addToCache id state.indent state.col state.flatten true state.leftBridge measureGroups

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

    for l in left do
      let leftExpanded ← expandTainted l
      for (leftBridge, leftMeasure) in leftExpanded do
        if rightBridge.contains coveredBridges then
          return result -- we have found a possible solution to all bridges the next item requires

        let (rights, tainted) ← right.resolve state.trace leftMeasure.last state.indent state.widthLimit leftBridge rightBridge state.expectBridge state.flatten true
        for t in tainted do
          if rightBridge.contains coveredBridges then
            return result
          for (rightBridge, rightMeasure) in (← expandTainted t) do
            if rightMeasure.fail.isNone then
              coveredBridges := coveredBridges ||| rightBridge
            result := mergeTaintedMeasures (rightBridge, leftMeasure.concat rightMeasure) result
        for right in rights do
          if right.set.any (fun m => m.fail.isNone) then
            coveredBridges := coveredBridges ||| right.rightBridge
          -- take the first valid options
          match right.set with
          | [] => result := result
          | rightMeasure :: _ =>
            result := mergeTaintedMeasures (right.rightBridge, leftMeasure.concat rightMeasure) result

    return result
  | .rightTainted left rights s (id:Nat) => do
    let mut result : TaintedResult χ := []
    let mut coveredBridges := bridgeNull

    for right in rights do
      if rightBridge.contains coveredBridges then
        return result -- we have found a possible solution to all bridges the next item requires
      let expanded ← expandTainted right
      for (rightBridge, rightMeasure) in expanded do
        let combined := left.concat rightMeasure
        result := mergeTaintedMeasures (rightBridge, combined) result

    return result
  | .center doc state => do
    let mut result : TaintedResult χ := []
    let (resolved, tainted) ← doc.resolve state.trace state.col state.indent state.widthLimit state.expectBridge state.rightBridge state.expectBridge state.flatten true
    for t in tainted do
      result := mergeTaintedResults (← expandTainted t) result
    for ms in resolved do
      for m in ms.set do
        result := mergeTaintedMeasures (ms.rightBridge, m) result
    return result
  | .cost c trunks => do
    let mut result : TaintedResult χ := []

    for t in trunks do
      result := mergeTaintedResults (← expandTainted t) result

    let lineCost : χ := (List.range c).foldl (fun (acc: χ) _ => acc + (Cost.nl)) (Cost.text 0 0 0)
    return result.map (fun m => (m.fst, m.snd.addCost (lineCost)))
  | .bubbleComment c trunks => do
    let mut result : TaintedResult χ := []

    for t in trunks do
      result := mergeTaintedResults (← expandTainted t) result

    return result.map (fun m => (m.fst, m.snd.prependLayout (placeComment 0 c)))

  mergeTaintedMeasures : (Bridge × Measure χ) → TaintedResult χ → TaintedResult χ
  | (b, m), [] => [(b, m)]
  | (b, m), (b', m')::xs =>
    match compare b b' with
    | Ordering.lt => (b, m)::(b', m')::xs
    | Ordering.gt => (b', m')::(mergeTaintedMeasures (b, m) xs)
    | Ordering.eq =>
      if m.fail.isSome then
        (b', m')::xs
      else if m'.fail.isSome then
        (b, m)::xs
      else
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
partial def Doc.print (χ : Type) [Inhabited χ] [Repr χ] [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) (log : Option (List String)): IO (PrintResult χ) := do
  -- let (preferredGroups, cache) := ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeFlex false false).run (initCache cacheSize log)).run
  let (preferredGroups, cache) ← ((doc.resolve (χ := χ) [] col 0 widthLimit bridgeFlex bridgeFlex bridgeFlex false false).run (initCache cacheSize log))
  let (goodSolution, solutions, tainted) := removeEndingBridges preferredGroups
  let (failedResult, cache) ← theFailedSolution preferredGroups |>.run cache
  if goodSolution then
    return printMeasureSet failedResult false solutions cache.log
  else
    let (taintedSolution, cache) ← (firstTaintedOption failedResult tainted).run cache
    return {taintedSolution with log := cache.log}
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
  -- TODO: convert to a thunk to avoid unnecessary string concatenation
  theFailedSolution (mg :  MeasureGroups χ) : MeasureResult χ (PrintResult χ) := do
    for ms in mg.fst do
      for m in ms.set do
        return {
          log := log,
          layout := String.join (m.layout []).reverse,
          isTainted := false,
          cost := m.cost
        }

    return {
      log := (← get).log,
      layout := "No solution found",
      isTainted := true,
      cost := Cost.text 0 0 0
    }

  initCache (n:Nat) (log : Option (List String)): CacheStore χ :=
    -- allocate twice the space needed, so flatten is separated into its own category
    {size := n, content := Array.mkArray (n*2) [], log := log, giveUp := 1000, lastMeasurement := 0}

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

  printMeasureSet (failure : PrintResult χ) (isTainted : Bool) (m : (MeasureSet χ)) (log : Option (List String)): (PrintResult χ) :=
    match m.set with
    | [] => failure
    | bestSolution::_ =>
      {
        log := log,
        layout := String.join (bestSolution.layout []).reverse,
        isTainted := isTainted,
        cost := bestSolution.cost
      }

  firstTaintedOption (failure : PrintResult χ): List (TaintedTrunk χ) → MeasureResult χ (PrintResult χ)
  | [] =>
    return failure
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
      firstTaintedOption failure ts
    | some (_,m) =>
      if m.fail.isSome then
        firstTaintedOption failure ts
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
partial def Doc.prettyPrint (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  return (← Doc.print χ doc cacheSize col widthLimit (none)) |>.layout

partial def Doc.prettyPrintLog (χ : Type) [Cost χ] (doc : Doc) (cacheSize col widthLimit : Nat) : IO String := do
  let l ← Doc.print χ doc cacheSize col widthLimit (some [])
  match l.log with
  | none => return l.layout
  | some log =>
    return (s!"Log: {String.join (log.intersperse "\n\n")} {l.layout}")
  -- return l.layout

end PrettyFormat
