import Bridge

namespace PrettyFormat

abbrev Constraint := Array (Bridge × Bridge)

@[inline] def passthrough : Constraint :=
  -- meta constructs like cost, bubblecomment and text "", do not affect bridges
  #[
    (bridgeFlex, bridgeFlex),
    (bridgeSpaceNl, bridgeSpaceNl),
    (bridgeHardNl, bridgeHardNl),
    (bridgeSpace, bridgeSpace),
    (bridgeNone, bridgeNone),
    (bridgeImmediate, bridgeImmediate)
  ]

def constraintUniformToComplex (left right : Bridge) : Constraint :=
  left.parts.foldl (fun acc b' =>
    acc.push (b',right)
  ) #[]

def provideConstraint (b: Bridge) : Constraint:=
  let parts := b.parts
  parts.foldl (fun acc b' =>
    acc.push (b', b')
  ) #[(bridgeFlex, b)]


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


@[inline] def acceptFlex : Constraint :=
  constraintUniformToComplex (bridgeFlex|||bridgeAny|||bridgeNone) (bridgeFlex ||| bridgeSpace ||| bridgeNl)



-- We need to satisfy the following property
-- (union a b).toComplex <=> (union a.toComplex b.toComplex).toComplex
@[inline] def Constraint.union (lhs rhs : Constraint): Constraint :=
  mergeConstraints lhs rhs

-- (concat a b).toComplex <=> (concat a.toComplex b.toComplex).toComplex
def Constraint.concat (lhs rhs : Constraint) : Constraint :=
  concatPaths lhs rhs

@[inline] def Constraint.restrictBridge (constraint : Constraint) (target : Bridge) : Bridge :=
  let newRight := constraint.foldl (fun acc (rl, rr) => if rr.overlapsWith target then rl ||| acc else acc) bridgeNull
  newRight

@[inline] def Constraint.overlapsWidth (constraint:Constraint) (leftBridge rightBridge:Bridge) : Bool :=
  constraint.any (fun (l, r) => l.overlapsWith leftBridge && r.overlapsWith rightBridge)

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
