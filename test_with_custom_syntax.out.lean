import Lean
import PrettyFormat
import Formatter

 inductive Arith  : Type where| add : Arith→Arith→Arith-- e + f
 | mul : Arith→Arith→Arith-- e * f
 | nat : Nat→Arith-- constant
 | var : String→Arith-- variable
 derivingRepr
declare_syntax_catarith
syntaxnum:arith-- nat for Arith.nat

syntaxstr:arith-- strings for Arith.var

syntax:50arith:50" + "arith:51:arith-- Arith.add

syntax:60arith:60" * "arith:61:arith-- Arith.mul

syntax" ( "arith" ) ":arith-- bracketed expressions

syntax" ⟪ "arith" ⟫ ":term
macro_rules|`(⟪$s:str⟫)=>`(Arith.var$s)|`(⟪$num:num⟫)=>`(Arith.nat$num)|`(⟪ -- TODO: improve custom formatter for arith_+_ 22
⟫)=>`(Arith.add⟪$x⟫⟪$y⟫)|`(⟪$x:arith*$y:arith⟫)=>`(Arith.mul⟪$x⟫⟪$y⟫)|`(⟪($x)⟫)=>`(⟪$x⟫)
#eval⟪ -- TODO: improve custom formatter for arith_+_ 22
⟫
-- -- Hello before definition
private def b (y :Nat) (a1 :Nat) : Nat :=
  -- comment on empty line
  -- new comment 2
  let tmp : Nat := y/2/3+2*3-2
  let tmp2 := tmp*5
  tmp2