import Lean

structure Point where
  x : Nat
  y : Nat

-- Define an instance of `ToString` for `Point`
instance : ToString Point where
  toString p := s!"({p.x}, {p.y})"

#eval
  let p := Point.mk 10 20
  toString p
