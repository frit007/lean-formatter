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
namespace Lean.NameSet
-/
#guard_msgs in
#format
namespace Lean.NameSet

/--
info:
/-- Create a `Lean.NameSet` from a `List`. This operation is `O(n)` in the length of the list. -/
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
  go: Nat → Nat
  | n => n * 2
-/
#guard_msgs in
#format
def double (n : Nat) := go n
where
  go: Nat → Nat
  | n => n * 2

set_option pf.debugSyntax true
set_option pf.debugMissingFormatters true
set_option pf.lineLength 100
-- set_option pf.debugDoc true
set_option pf.debugPPL true


def double (n : Nat) := go n
where
  go: Nat → Nat
  | n => n * 2 * 3 * 4 * 5 * 6


#format
def a : Nat := 2 * 3

open PrettyFormat

def formatPPL (p : PrettyFormat.PPL) : (PrettyFormat.PPL × Pfmt.Doc × String) :=
  let d := PrettyFormat.toDoc p
  (p, d, d|>.prettyPrint Pfmt.DefaultCost (col := 0) (widthLimit := PrettyFormat.getPFLineLength {}))


def badTest :PPL :=
  let last := ((PPL.provide [immediateValue]) <> (PPL.rule "«term_*_»"
       ((((((PPL.rule "num"
         (text "2")
        ) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (text "*")) <> (" ")) <> (PPL.rule "num"
         (text "3")
        ))<^>(((PPL.rule "num"
         (text "2")
        ) <> (" ")) <> ((text "*") <> ((PPL.provide [immediateValue]) <> (PPL.rule "num"
         (text "3")
        ))))
        )
      ))
  (PPL.rule "Lean.Parser.Command.declaration"
  (PPL.rule "Lean.Parser.Command.definition"
    ((((text "def") <> (PPL.nest 2 ((" ") <> (((PPL.rule "Lean.Parser.Command.declId"
      ((text "a") <> (PPL.provide [space, spaceNl, spaceHardNl]))
      ) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (PPL.rule "Lean.Parser.Command.optDeclSig"
      (PPL.rule "Lean.Parser.Term.typeSpec"
        (((text ":") <> (" ")) <> (text "Nat"))
        )
      ))))) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (PPL.rule "Lean.Parser.Command.declValSimple"
      (PPL.nest 2 ((text ":=") <> ((((" ") <> (PPL.flatten (PPL.rule "«term_*_»"
        ((((((PPL.rule "num"
          (text "2")
          ) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (text "*")) <> (" ")) <> (PPL.rule "num"
          (text "3")
          ))<^>(((PPL.rule "num"
          (text "2")
          ) <> (" ")) <> ((text "*") <> ((PPL.provide [immediateValue]) <> (PPL.rule "num"
          (text "3")
          ))))
          )
        )))<^>((PPL.provide [spaceHardNl]) <> (PPL.rule "«term_*_»"
        ((((((PPL.rule "num" (text "2")
          ) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (text "*")) <> (" ")) <> (PPL.rule "num"
          (text "3")
          ))<^>(((PPL.rule "num"
          (text "2")
          ) <> (" ")) <> ((text "*") <> ((PPL.provide [immediateValue]) <> (PPL.rule "num"
          (text "3")
          ))))
          )
        ))
        )
        <^> last
        )))
      ))
    ))

def badTest2 :PPL :=
  let last := ((PPL.provide [immediateValue]) <> (PPL.rule "«term_*_»"
       ((((((PPL.rule "num"
         (text "2")
        ) <> (PPL.provide [space, spaceNl, spaceHardNl])) <> (text "*")) <> (" ")) <> (PPL.rule "num"
         (text "3")
        ))<^>(((PPL.rule "num"
         (text "2")
        ) <> (" ")) <> ((text "*") <> ((PPL.provide [immediateValue]) <> (PPL.rule "num"
         (text "3")
        ))))
        )
      ))
  -- ("start" <> (" " <^> PPL.nl) <>
  --     (PPL.nest 2 ((text ":=") <> ((((" ") <> (PPL.flatten (((((
  --         (text "2")
  --         <> (" " <^> PPL.nl)) <> (text "*")) <> (" ")) <> text "3")
  --         )
  --       )) <^> ((PPL.nl) <>
  --       ((((( (text "2")
  --          <> (PPL.nl <^> " ")) <> (text "*")) <> (" ")) <> (text "3")
  --         )
  --         )
  --       ))

  --       )))
  --     )
    let first := " " <> PPL.flatten ((" ") <>" 3")
    let second := PPL.nl <> ((" " <^> PPL.nl) <>" 3")

    ("s" <> ((PPL.nl) <^> " ") <>
      (PPL.nest 2 ((text ":=") <> ( first <^> second

        ))))



#eval formatPPL (badTest2)


set_option pf.debugPPL true
