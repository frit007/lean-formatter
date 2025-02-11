import Lean
import PrettyFormat
-- import Formatter

-- set_option pf.lineLength 113

-- -- Hello before definition
private def b(y:Nat):Nat:=
  -- comment on empty line
  -- new comment 2
  3 * y
  --tmp / 2 --and content
  -- let x := y

-- set_option pf.lineLength 99

-- private def c (y:Nat) (a1:Nat) (a2:Nat) (a3:Nat) (a4:Nat) (a5:Nat) (a6:Nat) (a7:Nat) (a8:Nat) (a9:Nat) :Nat :=
--   -- comment on empty line
--   let tmp :Nat := y / 2 / 3 + 2 * 3 - 2
--   let tmp2 := tmp * 5
--   tmp2

-- private def d (y:Nat) (a1:Nat) (a2:Nat) (a3:Nat) (a4:Nat) (a5:Nat) (a6:Nat) (a7:Nat) (a8:Nat) (a9:Nat) :Nat :=
--   -- comment on empty line
--   let tmp :Nat := y / 2 / 3 + 2 * 3 - 2
--   let tmp2 := tmp * 5
--   tmp2
-- #eval 1 + 1

-- #eval 2 + 3

--def a (x:Nat): Nat :=
  -- before declaration
  --b x * 2 +1 -- after declaration
