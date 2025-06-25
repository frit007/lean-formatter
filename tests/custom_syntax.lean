import CoreFormatters
import LSPformat
import Lean


namespace CustomSyntax

infixr:110 " <+/> " => fun l r => l + r / r

open PrettyFormat

#fmt CustomSyntax.«term_<+/>_» fun
| #[l, atom, right] => do
  return l <$$$> atom <$$$> right
| _ => failure





#eval (10 <+/> 3)

/--
info:
def addDivide (x y : Nat) : Nat :=
  2
  <+/>
  3
-/
#guard_msgs in
#format
def addDivide (x y:Nat): Nat :=
  2 <+/> 3

#fmt «term_+_» fun
| #[l, atom, r] => do
  if r.getKind == `CustomSyntax.«term_<+/>_» then
    return l <$$$> atom <$$$> r
  else
    failure
| _ => failure

/--
info:
def add (x y : Nat) : Nat :=
  1
  +
  2
  <+/>
  3
-/
#guard_msgs in
#format
def add (x y:Nat): Nat :=
  1 + 2 <+/> 3

end CustomSyntax
