import Lean
import PrettyFormat
import Formatter

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable
  deriving Repr


declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

syntax " ⟪ " arith " ⟫ " : term

macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )



#eval ⟪ 2 + 3 ⟫

-- -- Hello before definition
private def b (y:Nat) (a1:Nat) :Nat :=
  -- comment on empty line
  -- new comment 2
  let tmp :Nat := y / 2 / 3 + 2 * 3 - 2
  let tmp2 := tmp * 5
  tmp2
  --tmp / 2 --and content
  -- let x := y


-- private def b (y:Nat) (a1:Nat) (a2:Nat) (a3:Nat) (a4:Nat) (a5:Nat) (a6:Nat) (a7:Nat) (a8:Nat) (a9:Nat) :Nat :=
--   -- comment on empty line
--   let tmp :Nat := y / 2 / 3 + 2 * 3 - 2
--   let tmp2 := tmp * 5
--   tmp2
--def a (x:Nat): Nat :=
  -- before declaration
  --b x * 2 +1 -- after declaration
