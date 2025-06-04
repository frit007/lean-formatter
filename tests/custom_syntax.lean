import CoreFormatters
import LSPformat
import Lean


namespace CustomSyntax

infixr:45 " <*-> " => fun l r => l *r - r


#fmt CustomSyntax.«term_<*->_» termOperator

#eval (10 <*-> 3)

/--
info:
def add (x y : Nat) : Nat := 2 <*-> 3
-/
#guard_msgs in
#format
def add (x y:Nat): Nat :=
  2 <*-> 3

end CustomSyntax

set_option pf.debugMissingFormatters true
