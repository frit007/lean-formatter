import CoreFormatters
import LSPformat
import Lean

open Lean
open Vector

/--
info:
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p := fun hpq : p ∧ q =>
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

/--
info:
example : (1 + 2) + 3 = 1 + (2 + 3) := by
  rw [Nat.add_assoc] -- Uses associativity of addition
  rfl
-/
#guard_msgs in
#format
example : (1 + 2) + 3 = 1 + (2 + 3) := by
  rw [Nat.add_assoc] -- Uses associativity of addition
  rfl

/--
info:
example (a b : Nat) : a + b + 0 = a + b := by
  rw [Nat.add_zero] -- Rewrite `b + 0` as `b`
  rfl -- Reflexivity solves the goal
-/
#guard_msgs in
#format
example (a b : Nat) : a + b + 0 = a + b := by
  rw [Nat.add_zero]  -- Rewrite `b + 0` as `b`
  rfl                -- Reflexivity solves the goal

-- set_option pf.debugSyntax 1
-- set_option pf.debugMissingFormatters 1
-- set_option pf.debugPPL 1


example : (1 + 2) + 3 = 1 + (2 + 3) := by
  rw [Nat.add_assoc]  -- Uses associativity of addition


-- set_option pf.debugMissingFormatters true
-- set_option pf.debugErrors true
set_option pf.debugNoSolution true
