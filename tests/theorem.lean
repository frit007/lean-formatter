import CoreFormatters
import LSPformat
import Lean

open Lean
open Vector
/--
info:
@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl
-/
#guard_msgs in
#format
@[simp] theorem uget_mk (a : Array α) (h : a.size = n) (i) (hi : i.toNat < n) :
    (Vector.mk a h).uget i hi = a.uget i (by simp [h, hi]) := rfl





/--
info:
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
    have hp : p := And.left hpq
    have hq : q := And.right hpq
    show q ∧ p from And.intro hq hp
-/
#guard_msgs in
#format
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

set_option pf.debugSyntax 1
set_option pf.debugMissingFormatters 1
set_option pf.debugPPL 1
