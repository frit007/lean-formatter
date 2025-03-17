import CoreFormatters
import LSPformat
import Lean


open Lean



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
instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n
-/
#guard_msgs in
#format
instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n

/--
info:
def a (b : Nat) : Nat := b * 2
-/
#guard_msgs in
#format
def a (b:Nat) : Nat := b * 2

#eval 1

/--
info:
namespace Lean.NameSet
-/
#guard_msgs in
#format
namespace Lean.NameSet

/--
info:
/--
Create a `Lean.NameSet` from a `List`. This operation is `O(n)` in the length of the list. -/
def ofList (l : List Name) : NameSet := l.foldl (fun s n => s.insert n) {}
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
#format
inductive AliasInfo where
  /-- Plain alias -/
  | plain (n : Name)
  /-- Forward direction of an iff alias -/
  | forward (n : Name)
  /-- Reverse direction of an iff alias -/
  | reverse (n : Name)
deriving Inhabited

set_option pf.debugSyntax 1
set_option pf.debugMissingFormatters 1
set_option pf.lineLength 200
set_option pf.debugDoc 1
set_option pf.debugPPL 1



-- instance : Inter NameSet where
--   inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

-- #eval 2
