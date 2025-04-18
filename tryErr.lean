import Std.Data.HashMap

open Std

inductive Streams (α : Type) where
  | cons : α → Streams α → Streams α  -- a non-terminating stream

-- A non-terminating function that generates an infinite stream
partial def streamExample (n:Nat): Streams Nat :=
  Streams.cons n (streamExample n)  -- This will never terminate!

inductive Good where
  | leaf : Nat → Good
  | node : List Good → Good

inductive Other where
  | leaf (m:Nat) (n:Other)
  | val (m:Nat)
  | node (m:List Other) (n:Other)

mutual
  structure AST where
    expr : Expr

  structure Expr where
    kind : ExprKind
    parent : Option AST

  inductive ExprKind
    | const : Nat → ExprKind
    | plus : Expr → Expr → ExprKind
end


inductive MeasureSetM (χ : Type) (τ : Type) where
/--
If a branch of the rendering process would end up producing only invalid documents
it produces a `MeasureSet.tainted`. It consists of a thunk that we can evaluate
to a `Measure` if we end up finding no way to produce a valid document.
-/
| tainted (bridge: Bridge) (m : τ → List (Bridge × Measure χ))
/--
A list of `Measure`s that form a Pareto front for our rendering problem.
This list is ordered by the last line length in strict ascending order.
-/
| set (bridge: Bridge) (ms : List (Measure χ))
deriving Inhabited

abbrev MeasureGroupsM (χ : Type) (τ : Type) := List (MeasureSetM χ τ)


structure CacheM (χ : Type) (τ : Type) where
  /--
  It was tried to format this piece with the following left bridge
  -/
  leftBridge : Bridge
  indent : Nat
  flatten: Bool --
  column: Nat --
  /-
  In the future we could add maxWidth to allow caching across different indents as long as indent-newIndent+maxWidth < maxWidth
  -/
  -- maxWidth : Nat
  -- if there are no results it is considered a failure
  results : MeasureGroupsM χ τ
