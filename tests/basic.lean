import CoreFormatters
import LSPformat
import Lean


open Lean PrettyFormat

-- set_option pf.debugPPL true


#format
instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n


#format
instance : Add DefaultCost where
  add := DefaultCost.add

/--
info:
def a : Nat := 2
-/
#guard_msgs in
#format
def a : Nat := 2

/--
info:
def a (b : Nat) : Nat := b * 2
-/
#guard_msgs in
#format
def a (b:Nat) : Nat := b * 2



/--
info:
instance : Singleton Name NameSet where singleton := fun n => (∅ : NameSet).insert n
-/
#guard_msgs in
#format
instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n


/--
info:
namespace Lean.NameSet
-/
#guard_msgs in
#format
namespace Lean.NameSet

/--
info:
/-- Create a `Lean.NameSet` from a `List`. This operation is `O(n)` in the length of the list. -/
def ofList (l : List Name) : NameSet :=
  l.foldl (fun s n => s.insert n) {}
-/
#guard_msgs in
#format
/-- Create a `Lean.NameSet` from a `List`. This operation is `O(n)` in the length of the list. -/
def ofList (l : List Name) : NameSet :=
  l.foldl (fun s n => s.insert n) {}

/--
info:
instance : Inter NameSet where
  inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}
-/
#guard_msgs in
#format
instance : Inter NameSet where
  inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

set_option pf.lineLength 70 -- Test that the code will be folded if the line length is reduced

/--
info:
instance : Inter NameSet where
  inter := fun s t =>
    s.fold (fun r n => if t.contains n then r.insert n else r) {}
-/
#guard_msgs in
#format
instance : Inter NameSet where
  inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

/--
info:
open Lean Elab Parser.Command
-/
#guard_msgs in
#format
open Lean Elab Parser.Command



#fmt Lean.Parser.Command.inductive fun
| #[inductiveAtom,decl,optDeclSig,whereContainer,terms,unknown1,derive ] =>
  do
    assumeMissing unknown1
    return (combine (.<_>.)
      #[toDoc inductiveAtom, toDoc decl,toDoc optDeclSig,combine (.<_>.)
      whereContainer.getArgs])<>(nestDoc 2 (""<$$>combine (.<$$>.)
      terms.getArgs<>(""<$$>""<?derive)))
| _ => failure

/--
info:
inductive AliasInfo where
  /-- Plain alias -/
  | plain (n : Name)
  /-- Forward direction of an iff alias -/
  | forward (n : Name)
  /-- Reverse direction of an iff alias -/
  | reverse (n : Name)
  deriving Inhabited
-/
#guard_msgs in
#formatinductive AliasInfo where
  /-- Plain alias -/
  | plain (n : Name)
  /-- Forward direction of an iff alias -/
  | forward (n : Name)
  /-- Reverse direction of an iff alias -/
  | reverse (n : Name)
  deriving Inhabited

/--
info:
def matchNat (nat : Nat) : Nat :=
  match nat with
  | 0 => 99
  | numWithWidth => numWithWidth * 2
-/
#guard_msgs in
#format
def matchNat (nat : Nat) : Nat :=
  match nat with
  | 0 => 99
  | numWithWidth => numWithWidth * 2

/--
info:
def double (n : Nat) := go n
where
  go : Nat → Nat
  | n => n * 2
-/
#guard_msgs in
#format
def double (n : Nat) := go n
where
  go: Nat → Nat
  | n => n * 2

/--
info:
def double (n : Nat) := go n
where
  go : Nat → Nat
  | n => n * 2 * 3 * 4 * 5 * 6
-/
#guard_msgs in
#format
def double (n : Nat) := go n
where
  go: Nat → Nat
  | n => n * 2 * 3 * 4 * 5 * 6

open PrettyFormat



-- set_option pf.debugLog true
-- set_option pf.debugSyntax true
