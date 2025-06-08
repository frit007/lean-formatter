import BaseFormatter

open PrettyFormat



def testConcat (l r:Constraint) : String:=
  let fast := (l.concat r).toComplex
  let slow := ((Constraint.complex l.toComplex).concat (Constraint.complex r.toComplex)).toComplex
  if fast == slow then
    s!"correct: {repr (Constraint.simplify fast)}"
  else
    s!"fast:{fast} slow{slow}"


/-- info: "correct: PrettyFormat.Constraint.uniform 14 14" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeAny, bridgeAny)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])


/-- info: "correct: PrettyFormat.Constraint.uniform 14 14" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeAny), (bridgeNl, bridgeAny)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.uniform 8 14" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeAny), (bridgeNl, bridgeFlex)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.uniform 8 14" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeImmediate|||bridgeSpace), (bridgeImmediate, bridgeImmediate)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/- Provide -/
/-- info: "correct: PrettyFormat.Constraint.uniform 5 4" -/
#guard_msgs in
#eval testConcat (Constraint.provide bridgeNl) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.uniform bridgeFlex bridgeFlex) (Constraint.complex #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.uniform 1 1" -/
#guard_msgs in
#eval testConcat Constraint.passthrough (Constraint.uniform bridgeFlex bridgeFlex)

/-- info: "correct: PrettyFormat.Constraint.uniform 7 14" -/
#guard_msgs in
#eval testConcat (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeNl, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeSpace, bridgeImmediate)])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.uniform 6 14" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeNl, bridgeHardNl)]) (Constraint.simplify #[(bridgeNl, bridgeAny)])

/--
info: "correct: PrettyFormat.Constraint.complex #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)]"
-/
#guard_msgs in
#eval testConcat (Constraint.passthrough) (Constraint.passthrough)

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.passthrough) (Constraint.simplify #[])

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.impossible)

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.impossible) (Constraint.impossible)

/-- info: "correct: PrettyFormat.Constraint.uniform 4 4" -/
#guard_msgs in
#eval testConcat (Constraint.simplify #[(bridgeHardNl, bridgeHardNl)]) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testConcat (Constraint.provide bridgeSpace) (Constraint.provide bridgeHardNl)


------------------------ test merge ------------------------
def testUnion (l r:Constraint) : String:=
  let fast := (l.union r).toComplex
  let slow := ((Constraint.complex l.toComplex).union (Constraint.complex r.toComplex)).toComplex
  if fast == slow then
    s!"correct: {repr (Constraint.simplify fast)}"
  else
    s!"fast:{fast} slow{slow}"


/-- info: "correct: PrettyFormat.Constraint.uniform 14 14" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeAny, bridgeAny)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])


/-- info: "correct: PrettyFormat.Constraint.uniform 14 14" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeAny), (bridgeNl, bridgeAny)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(8, 14), (6, 1)]" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeAny), (bridgeNl, bridgeFlex)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.uniform 8 14" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.uniform 8 46" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(8, 46), (32, 32)]" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeImmediate|||bridgeSpace), (bridgeImmediate, bridgeImmediate)]) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 6), (2, 2), (4, 4)]" -/
#guard_msgs in
#eval testUnion (Constraint.provide bridgeNl) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 6), (2, 2), (4, 4), (8, 14)]" -/
#guard_msgs in
#eval testUnion (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeSpace, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 1), (8, 14)]" -/
#guard_msgs in
#eval testUnion (Constraint.uniform bridgeFlex bridgeFlex) (Constraint.complex #[(bridgeSpace, bridgeAny)])

/--
info: "correct: PrettyFormat.Constraint.complex #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)]"
-/
#guard_msgs in
#eval testUnion Constraint.passthrough (Constraint.uniform bridgeFlex bridgeFlex)

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 6), (2, 14), (4, 14)]" -/
#guard_msgs in
#eval testUnion (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeNl, bridgeAny)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 6), (2, 2), (4, 4), (8, 32)]" -/
#guard_msgs in
#eval testUnion (Constraint.provide bridgeNl) (Constraint.simplify #[(bridgeSpace, bridgeImmediate)])

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 4), (4, 4), (8, 32)]" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.uniform 6 14" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeNl, bridgeHardNl)]) (Constraint.simplify #[(bridgeNl, bridgeAny)])

/--
info: "correct: PrettyFormat.Constraint.complex #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)]"
-/
#guard_msgs in
#eval testUnion (Constraint.passthrough) (Constraint.passthrough)

/--
info: "correct: PrettyFormat.Constraint.complex #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)]"
-/
#guard_msgs in
#eval testUnion (Constraint.passthrough) (Constraint.simplify #[])

/-- info: "correct: PrettyFormat.Constraint.uniform 8 32" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeSpace, bridgeImmediate)]) (Constraint.impossible)

/-- info: "correct: PrettyFormat.Constraint.impossible" -/
#guard_msgs in
#eval testUnion (Constraint.impossible) (Constraint.impossible)

/-- info: "correct: PrettyFormat.Constraint.uniform 5 4" -/
#guard_msgs in
#eval testUnion (Constraint.simplify #[(bridgeHardNl, bridgeHardNl)]) (Constraint.provide bridgeHardNl)

/-- info: "correct: PrettyFormat.Constraint.complex #[(1, 12), (4, 4), (8, 8)]" -/
#guard_msgs in
#eval testUnion (Constraint.provide bridgeSpace) (Constraint.provide bridgeHardNl)
