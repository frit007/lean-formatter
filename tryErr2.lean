abbrev Bridge := Nat

structure Measure where
  last : Nat
  cost : Nat -- simplificeret for at gøre eksemplet kortere
  layout : List String → List String
  spacingR : Bridge := 0
  fail: Option (List (List String)) := none

mutual

inductive MeasureSet where
/--
If a branch of the rendering process would end up producing only invalid documents
it produces a `MeasureSet.tainted`. It consists of a thunk that we can evaluate
to a `Measure` if we end up finding no way to produce a valid document.
-/
-- We need to pass the cache to tainted, because it has to call resolve again.
-- And resolve needs to
| tainted (bridge: Bridge) (m : Unit →(List (Bridge × Measure × Array (List (Cache)))))
-- Or maybe pass it the cache and get it back later
-- | tainted (bridge: Bridge) (m : Array (List (Cache)) → (List (Bridge × Measure)) × Array(List (Cache)))
| set (bridge: Bridge) (ms : List (Measure))



end

structure Cache where
  leftBridge : Bridge
  indent : Nat
  flatten: Bool
  column: Nat
  results : List (MeasureSet)
