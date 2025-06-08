import Bridge

namespace PrettyFormat

@[inline] def passthrough : Array (Bridge × Bridge) :=
  -- meta constructs like cost, bubblecomment and text "", do not affect bridges
  #[
    (bridgeFlex, bridgeFlex),
    (bridgeSpaceNl, bridgeSpaceNl),
    (bridgeHardNl, bridgeHardNl),
    (bridgeSpace, bridgeSpace),
    (bridgeNone, bridgeNone),
    (bridgeImmediate, bridgeImmediate)
  ]

@[inline] partial def mergeConstraints (lhs rhs: Array (Bridge × Bridge)): (Array (Bridge × Bridge)) :=
  mergeConstraints' lhs rhs #[] 0 0
where mergeConstraints' (lhs rhs merged: Array (Bridge × Bridge)) (li ri : Nat): (Array (Bridge × Bridge)) :=
  if li < lhs.size && ri < rhs.size then
    let lb := lhs[li]!
    let rb := rhs[ri]!
    if lb.fst < rb.fst then
      mergeConstraints' lhs rhs (merged.push (lb)) (li + 1) ri
    else if rb.fst < lb.fst then
      mergeConstraints' lhs rhs (merged.push (rb)) li (ri + 1)
    else
      mergeConstraints' lhs rhs (merged.push (rb.fst, rb.snd ||| lb.snd)) (li + 1) (ri + 1)
  else if li < lhs.size then
    mergeConstraints' lhs rhs (merged.push (lhs[li]!)) (li + 1) ri
  else if ri < rhs.size then
    mergeConstraints' lhs rhs (merged.push (rhs[ri]!)) li (ri + 1)
  else
    merged

@[inline] def concatPaths (lhs rhs : Array (Bridge × Bridge)) : Array (Bridge × Bridge) :=
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
/--
The goal is to avoid to avoid paying for the complexity of bridges when they are not used.
We want to achieve this using to methods:
 - We want to avoid following the pointer to
-/
inductive Constraint where
/--
all bridges in the left side can lead to all bridges in the right side.
-/
| uniform (left : Bridge) (right : Bridge)
/--
`cost` & `bubbleComment` & `text ""` do not affect bridges
-/
| passthrough
/--
There are no options
-/
| impossible
/--
Delay a provide statement until it is needed.
-/
| provide (b : Bridge)
| complex (c : Array (Bridge × Bridge))
deriving Inhabited, Repr

@[inline] def acceptFlex : Constraint :=
  Constraint.uniform (bridgeFlex|||bridgeAny|||bridgeNone) (bridgeFlex ||| bridgeSpace ||| bridgeNl)


@[inline] def Constraint.toComplex : Constraint → Array (Bridge × Bridge)
| .uniform left right =>
  left.parts.foldl (fun acc b' =>
    acc.push (b',right)
  ) #[]
| .passthrough => PrettyFormat.passthrough
| .impossible => #[]
| .provide b =>
  let parts := b.parts
  let paths := parts.foldl (fun acc b' =>
    acc.push (b', b')
  ) #[(bridgeFlex, b)]
  paths
| complex c => c


@[inline] def Constraint.simplify (a:Array (Bridge × Bridge)) : Constraint :=
  match a with
  | #[] => Constraint.impossible
  | #[(l,r)] => Constraint.uniform l r
  | args =>
    match uniformRight args with
    | some r =>
      Constraint.uniform (args.foldl (fun acc (l,_) => acc ||| l) bridgeNull) r
    | _ => Constraint.complex args
where
  uniformRight (arr : Array (Bridge × Bridge)) : Option Bridge :=
    let (_, firstRight) := arr.get! 0
    if arr.all (fun (_, right) => right == firstRight) then
      some firstRight
    else
      none

-- We need to satisfy the following property
-- (union a b).toComplex <=> (union a.toComplex b.toComplex).toComplex
@[inline] def Constraint.union (lhs rhs : Constraint): Constraint :=
  match (lhs, rhs) with
  | (.impossible, _) => rhs
  | (_, .impossible) => lhs
  | (.uniform ll lr, .uniform rl rr) =>
    if ll.subsetOf rl && lr.subsetOf rr then
      .uniform rl rr
    else if rl.subsetOf ll && rr.subsetOf lr then
      .uniform ll lr
    else
      let paths := mergeConstraints lhs.toComplex rhs.toComplex
      Constraint.simplify paths
  | (.provide bl, .provide br) => .provide (bl ||| br)
  | (.passthrough, .passthrough) => .passthrough -- if both are passthrough then remain passthrough
  | _ =>
    let paths := mergeConstraints lhs.toComplex rhs.toComplex
    Constraint.simplify paths

-- (concat a b).toComplex <=> (concat a.toComplex b.toComplex).toComplex
def Constraint.concat (lhs rhs : Constraint) : Constraint :=
  match (lhs, rhs) with
  | (.impossible, _) => .impossible
  | (_, .impossible) => .impossible
  -- | (.uniform ll lr, .provide b) =>
    -- this is likely calculateable
  | (.uniform ll lr, .uniform rl rr) =>
    if lr.overlapsWith rl then
      .uniform ll rr
    else
      .impossible
  | _ =>
    let paths :=concatPaths lhs.toComplex rhs.toComplex
    Constraint.simplify paths

@[inline] def Constraint.restrictBridge (constraint : Constraint) (target : Bridge) : Bridge :=
  match constraint with
  | .impossible => bridgeNull
  | .passthrough => target
  | .uniform l r =>
    if r.overlapsWith target then
      l
    else
      bridgeNull
  | _ =>
    let newRight := constraint.toComplex.foldl (fun acc (rl, rr) => if rr.overlapsWith target then rl ||| acc else acc) bridgeNull
    newRight

@[inline] def Constraint.overlapsWidth (constraint:Constraint) (leftBridge rightBridge:Bridge) : Bool :=
  match constraint with
  | .impossible => false
  | .passthrough => leftBridge.overlapsWith leftBridge
  | .uniform l r =>
    l.overlapsWith leftBridge && r.overlapsWith rightBridge
  | _ =>
    constraint.toComplex.any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)

@[inline] def concatFlatten (flatten : Flatten) (leftIsNotEmpty rightIsNotEmpty : Bool) : (Flatten × Flatten) :=
    match (flatten, leftIsNotEmpty, rightIsNotEmpty) with
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


end PrettyFormat
