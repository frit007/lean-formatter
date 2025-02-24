import Lean

open Lean

-- structure Tree (α : Type) where
--   value : α
-- deriving Repr

-- abbrev PPL := Nat

-- -- Now define FormatContext
-- structure FormatContext (α : Type)where
--   env : Environment
--   coreFormatters : Std.HashMap Name α
--   options: Options

-- structure FormatState where
--   indent : Nat := 0

-- structure FormatError where
--   msg : String
-- mutual
--   -- Define Rule first (even though it refers to FormatContext)
--   abbrev FormatM (a : Type) := ReaderT (FormatContext Rule) (StateM FormatState) a
--   abbrev RuleM (a : Type) := ExceptT FormatError FormatM a
--   abbrev Rule := Array Syntax → (RuleM PPL)
-- end

-- def Dynamic2 := Σ α : Type, α

-- def storeDynamic (x : α) : Dynamic2 := ⟨α, x⟩

-- -- def getDynamicType (d : Dynamic2) : Type := d.1
-- -- def getDynamicValue {T : Type} (d : Dynamic2) : T := d.2

-- inductive AnyValue
--   | mk {α : Type} (val : α) : AnyValue

-- def store (x : α) : AnyValue := AnyValue.mk x

-- -- def extract? (T : Type) (v : AnyValue) : Option T :=
-- --   match v with
-- --   | AnyValue.mk val =>
-- --     match h : val with  -- Type annotation ensures correct extraction
-- --     | _ => if h == T then some (h : T) else none

-- def extract? {T : Type} : AnyValue → Option T
--   | AnyValue.mk (val : Tm) =>
--     match h : Tm with
--     | T => some (val : T)  -- This only works if T' = T
--     | _ => none

-- structure mine where
--   a : AnyValue


-- def main (args : List String) : IO Unit := do
--   let x := mine.mk ⟨ ("hello") ⟩
--   match x.a with
--   | (AnyValue.mk val) =>
--   pure ()

-- -- Example usage:
-- #check storeDynamic 42      -- Dynamic (stores Nat)
-- #check storeDynamic "hello" -- Dynamic (stores String)


-- def Dynamic2 := Σ α : Type, α  -- Existential type pairing type and value

-- def storeDynamic (x : α) : Dynamic2 := ⟨α, x⟩

-- set_option diagnostics true

-- def extractDynamic {T : Type} (d : Dynamic2) : Option T :=
--   match d with
--   | ⟨T', val⟩ =>
--     match eq : T' = T with
--     | rfl => some (Eq.rec val eq)  -- Use `Eq.rec` for safe type casting
--     | _ => none
    -- match h : T' with`
    -- | T => some (val : T)  -- Only extracts if types match
    -- | _ => none
