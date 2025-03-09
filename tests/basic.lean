import CoreFormatters
import LSPformat
import Lean


open Lean



/--
info:
def a : Nat :=
  2
-/
#guard_msgs in
#format
def a : Nat := 2

/--
info:
def a (b : Nat) : Nat :=
  b * 2
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
def a (b : Nat) : Nat :=
  b * 2
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


set_option pf.debugSyntax 1
-- set_option pf.debugMissingFormatters 1


-- instance : Inter NameSet where
--   inter := fun s t => s.fold (fun r n => if t.contains n then r.insert n else r) {}

-- #eval 2

/-FORMAT DEBUG:
---- Could not parse syntax again ----
Could not parse syntax again: Expected 2 commands to be generated, your top level command and end of file
 But generated 3 commands Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Command.declaration
  #[Lean.Syntax.node
      (Lean.SourceInfo.none)
      `Lean.Parser.Command.declModifiers
      #[Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `Lean.Parser.Command.definition
      #[Lean.Syntax.atom
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 0 } " ".toSubstring { byteIdx := 3 })
          "def",
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.declId
          #[Lean.Syntax.ident
              (Lean.SourceInfo.original "".toSubstring { byteIdx := 4 } " ".toSubstring { byteIdx := 8 })
              "mine".toSubstring
              `mine
              [],
            Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.optDeclSig
          #[Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.explicitBinder
                  #[Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 9 } "".toSubstring { byteIdx := 10 })
                      "(",
                    Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `null
                      #[Lean.Syntax.ident
                          (Lean.SourceInfo.original "".toSubstring { byteIdx := 10 } " ".toSubstring { byteIdx := 13 })
                          "stx".toSubstring
                          `stx
                          []],
                    Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `null
                      #[Lean.Syntax.atom
                          (Lean.SourceInfo.original "".toSubstring { byteIdx := 14 } " ".toSubstring { byteIdx := 15 })
                          ":",
                        Lean.Syntax.ident
                          (Lean.SourceInfo.original "".toSubstring { byteIdx := 16 } "".toSubstring { byteIdx := 22 })
                          "Syntax".toSubstring
                          `Syntax
                          []],
                    Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                    Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 22 } " ".toSubstring { byteIdx := 23 })
                      ")"]],
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.typeSpec
                  #[Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 24 } " ".toSubstring { byteIdx := 25 })
                      ":",
                    Lean.Syntax.ident
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 26 } " ".toSubstring { byteIdx := 30 })
                      "Unit".toSubstring
                      `Unit
                      []]]],
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.declValSimple
          #[Lean.Syntax.atom
              (Lean.SourceInfo.original "".toSubstring { byteIdx := 31 } "\n  ".toSubstring { byteIdx := 33 })
              ":=",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `Lean.Parser.Term.let
              #[Lean.Syntax.atom
                  (Lean.SourceInfo.original "".toSubstring { byteIdx := 36 } " ".toSubstring { byteIdx := 39 })
                  "let",
                Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.letDecl
                  #[Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `Lean.Parser.Term.letIdDecl
                      #[Lean.Syntax.node
                          (Lean.SourceInfo.none)
                          `Lean.Parser.Term.hole
                          #[Lean.Syntax.atom
                              (Lean.SourceInfo.original
                                "".toSubstring
                                { byteIdx := 40 }
                                " ".toSubstring
                                { byteIdx := 41 })
                              "_"],
                        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                        Lean.Syntax.atom
                          (Lean.SourceInfo.original "".toSubstring { byteIdx := 42 } " ".toSubstring { byteIdx := 44 })
                          ":=",
                        Lean.Syntax.ident
                          (Lean.SourceInfo.original "".toSubstring { byteIdx := 45 } "".toSubstring { byteIdx := 57 })
                          "matchstxwith".toSubstring
                          `matchstxwith
                          []]],
                Lean.Syntax.missing]]]]
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `coreFmtCmd
  #[Lean.Syntax.atom
      (Lean.SourceInfo.original "".toSubstring { byteIdx := 60 } "".toSubstring { byteIdx := 68 })
      "#coreFmt",
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `ident.antiquot
      #[Lean.Syntax.atom
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 68 } "".toSubstring { byteIdx := 69 })
          "$",
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.ident
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 69 } "".toSubstring { byteIdx := 77 })
          "typeExpr".toSubstring
          `typeExpr
          [],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `term.pseudo.antiquot
      #[Lean.Syntax.atom
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 77 } "".toSubstring { byteIdx := 78 })
          "$",
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.ident
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 78 } "".toSubstring { byteIdx := 84 })
          "fnExpr".toSubstring
          `fnExpr
          [],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[]]]
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Command.eoi
  #[Lean.Syntax.atom (Lean.SourceInfo.original "".toSubstring { byteIdx := 98 } "".toSubstring { byteIdx := 98 }) ""]
---- Syntax before format ----
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Command.declaration
  #[Lean.Syntax.node
      (Lean.SourceInfo.none)
      `Lean.Parser.Command.declModifiers
      #[Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `Lean.Parser.Command.definition
      #[Lean.Syntax.atom
          (Lean.SourceInfo.original "".toSubstring { byteIdx := 1507 } " ".toSubstring { byteIdx := 1510 })
          "def",
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.declId
          #[Lean.Syntax.ident
              (Lean.SourceInfo.original "".toSubstring { byteIdx := 1511 } " ".toSubstring { byteIdx := 1515 })
              "mine".toSubstring
              `mine
              [],
            Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.optDeclSig
          #[Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.explicitBinder
                  #[Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1516 } "".toSubstring { byteIdx := 1517 })
                      "(",
                    Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `null
                      #[Lean.Syntax.ident
                          (Lean.SourceInfo.original
                            "".toSubstring
                            { byteIdx := 1517 }
                            "".toSubstring
                            { byteIdx := 1520 })
                          "stx".toSubstring
                          `stx
                          []],
                    Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `null
                      #[Lean.Syntax.atom
                          (Lean.SourceInfo.original
                            "".toSubstring
                            { byteIdx := 1520 }
                            "".toSubstring
                            { byteIdx := 1521 })
                          ":",
                        Lean.Syntax.ident
                          (Lean.SourceInfo.original
                            "".toSubstring
                            { byteIdx := 1521 }
                            "".toSubstring
                            { byteIdx := 1527 })
                          "Syntax".toSubstring
                          `Syntax
                          []],
                    Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                    Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1527 } " ".toSubstring { byteIdx := 1528 })
                      ")"]],
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.typeSpec
                  #[Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1529 } " ".toSubstring { byteIdx := 1530 })
                      ":",
                    Lean.Syntax.ident
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1531 } " ".toSubstring { byteIdx := 1535 })
                      "Unit".toSubstring
                      `Unit
                      []]]],
        Lean.Syntax.node
          (Lean.SourceInfo.none)
          `Lean.Parser.Command.declValSimple
          #[Lean.Syntax.atom
              (Lean.SourceInfo.original "".toSubstring { byteIdx := 1536 } "\n  ".toSubstring { byteIdx := 1538 })
              ":=",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `Lean.Parser.Term.let
              #[Lean.Syntax.atom
                  (Lean.SourceInfo.original "".toSubstring { byteIdx := 1541 } " ".toSubstring { byteIdx := 1544 })
                  "let",
                Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.letDecl
                  #[Lean.Syntax.node
                      (Lean.SourceInfo.none)
                      `Lean.Parser.Term.letIdDecl
                      #[Lean.Syntax.node
                          (Lean.SourceInfo.none)
                          `Lean.Parser.Term.hole
                          #[Lean.Syntax.atom
                              (Lean.SourceInfo.original
                                "".toSubstring
                                { byteIdx := 1545 }
                                " ".toSubstring
                                { byteIdx := 1546 })
                              "_"],
                        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                        Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                        Lean.Syntax.atom
                          (Lean.SourceInfo.original
                            "".toSubstring
                            { byteIdx := 1547 }
                            " ".toSubstring
                            { byteIdx := 1549 })
                          ":=",
                        Lean.Syntax.node
                          (Lean.SourceInfo.none)
                          `Lean.Parser.Term.match
                          #[Lean.Syntax.atom
                              (Lean.SourceInfo.original
                                "".toSubstring
                                { byteIdx := 1550 }
                                " ".toSubstring
                                { byteIdx := 1555 })
                              "match",
                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                            Lean.Syntax.node
                              (Lean.SourceInfo.none)
                              `null
                              #[Lean.Syntax.node
                                  (Lean.SourceInfo.none)
                                  `Lean.Parser.Term.matchDiscr
                                  #[Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                                    Lean.Syntax.ident
                                      (Lean.SourceInfo.original
                                        "".toSubstring
                                        { byteIdx := 1556 }
                                        " ".toSubstring
                                        { byteIdx := 1559 })
                                      "stx".toSubstring
                                      `stx
                                      []]],
                            Lean.Syntax.atom
                              (Lean.SourceInfo.original
                                "".toSubstring
                                { byteIdx := 1560 }
                                "\n  ".toSubstring
                                { byteIdx := 1564 })
                              "with",
                            Lean.Syntax.node
                              (Lean.SourceInfo.none)
                              `Lean.Parser.Term.matchAlts
                              #[Lean.Syntax.node
                                  (Lean.SourceInfo.none)
                                  `null
                                  #[Lean.Syntax.node
                                      (Lean.SourceInfo.none)
                                      `Lean.Parser.Term.matchAlt
                                      #[Lean.Syntax.atom
                                          (Lean.SourceInfo.original
                                            "".toSubstring
                                            { byteIdx := 1567 }
                                            " ".toSubstring
                                            { byteIdx := 1568 })
                                          "|",
                                        Lean.Syntax.node
                                          (Lean.SourceInfo.none)
                                          `null
                                          #[Lean.Syntax.node
                                              (Lean.SourceInfo.none)
                                              `null
                                              #[Lean.Syntax.node
                                                  (Lean.SourceInfo.none)
                                                  `Lean.Parser.Command.quot
                                                  #[Lean.Syntax.atom
                                                      (Lean.SourceInfo.original
                                                        "".toSubstring
                                                        { byteIdx := 1569 }
                                                        "".toSubstring
                                                        { byteIdx := 1571 })
                                                      "`(",
                                                    Lean.Syntax.node
                                                      (Lean.SourceInfo.none)
                                                      `coreFmtCmd
                                                      #[Lean.Syntax.atom
                                                          (Lean.SourceInfo.original
                                                            "".toSubstring
                                                            { byteIdx := 1571 }
                                                            " ".toSubstring
                                                            { byteIdx := 1579 })
                                                          "#coreFmt",
                                                        Lean.Syntax.node
                                                          (Lean.SourceInfo.none)
                                                          `ident.antiquot
                                                          #[Lean.Syntax.atom
                                                              (Lean.SourceInfo.original
                                                                "".toSubstring
                                                                { byteIdx := 1580 }
                                                                "".toSubstring
                                                                { byteIdx := 1581 })
                                                              "$",
                                                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                                                            Lean.Syntax.ident
                                                              (Lean.SourceInfo.original
                                                                "".toSubstring
                                                                { byteIdx := 1581 }
                                                                " ".toSubstring
                                                                { byteIdx := 1589 })
                                                              "typeExpr".toSubstring
                                                              `typeExpr
                                                              [],
                                                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
                                                        Lean.Syntax.node
                                                          (Lean.SourceInfo.none)
                                                          `term.pseudo.antiquot
                                                          #[Lean.Syntax.atom
                                                              (Lean.SourceInfo.original
                                                                "".toSubstring
                                                                { byteIdx := 1590 }
                                                                "".toSubstring
                                                                { byteIdx := 1591 })
                                                              "$",
                                                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                                                            Lean.Syntax.ident
                                                              (Lean.SourceInfo.original
                                                                "".toSubstring
                                                                { byteIdx := 1591 }
                                                                "".toSubstring
                                                                { byteIdx := 1597 })
                                                              "fnExpr".toSubstring
                                                              `fnExpr
                                                              [],
                                                            Lean.Syntax.node (Lean.SourceInfo.none) `null #[]]],
                                                    Lean.Syntax.atom
                                                      (Lean.SourceInfo.original
                                                        "".toSubstring
                                                        { byteIdx := 1597 }
                                                        " ".toSubstring
                                                        { byteIdx := 1598 })
                                                      ")"]]],
                                        Lean.Syntax.atom
                                          (Lean.SourceInfo.original
                                            "".toSubstring
                                            { byteIdx := 1599 }
                                            " ".toSubstring
                                            { byteIdx := 1601 })
                                          "=>",
                                        Lean.Syntax.node
                                          (Lean.SourceInfo.none)
                                          `num
                                          #[Lean.Syntax.atom
                                              (Lean.SourceInfo.original
                                                "".toSubstring
                                                { byteIdx := 1602 }
                                                "\n  ".toSubstring
                                                { byteIdx := 1603 })
                                              "2"]],
                                    Lean.Syntax.node
                                      (Lean.SourceInfo.none)
                                      `Lean.Parser.Term.matchAlt
                                      #[Lean.Syntax.atom
                                          (Lean.SourceInfo.original
                                            "".toSubstring
                                            { byteIdx := 1606 }
                                            " ".toSubstring
                                            { byteIdx := 1607 })
                                          "|",
                                        Lean.Syntax.node
                                          (Lean.SourceInfo.none)
                                          `null
                                          #[Lean.Syntax.node
                                              (Lean.SourceInfo.none)
                                              `null
                                              #[Lean.Syntax.node
                                                  (Lean.SourceInfo.none)
                                                  `Lean.Parser.Term.hole
                                                  #[Lean.Syntax.atom
                                                      (Lean.SourceInfo.original
                                                        "".toSubstring
                                                        { byteIdx := 1608 }
                                                        " ".toSubstring
                                                        { byteIdx := 1609 })
                                                      "_"]]],
                                        Lean.Syntax.atom
                                          (Lean.SourceInfo.original
                                            "".toSubstring
                                            { byteIdx := 1610 }
                                            " ".toSubstring
                                            { byteIdx := 1612 })
                                          "=>",
                                        Lean.Syntax.node
                                          (Lean.SourceInfo.none)
                                          `num
                                          #[Lean.Syntax.atom
                                              (Lean.SourceInfo.original
                                                "".toSubstring
                                                { byteIdx := 1613 }
                                                "\n  ".toSubstring
                                                { byteIdx := 1614 })
                                              "3"]]]]]]],
                Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                Lean.Syntax.node
                  (Lean.SourceInfo.none)
                  `Lean.Parser.Term.tuple
                  #[Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1617 } "".toSubstring { byteIdx := 1618 })
                      "(",
                    Lean.Syntax.node (Lean.SourceInfo.none) `null #[],
                    Lean.Syntax.atom
                      (Lean.SourceInfo.original "".toSubstring { byteIdx := 1618 } "\n".toSubstring { byteIdx := 1619 })
                      ")"]],
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `Lean.Parser.Termination.suffix
              #[Lean.Syntax.node (Lean.SourceInfo.none) `null #[], Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
            Lean.Syntax.node (Lean.SourceInfo.none) `null #[]],
        Lean.Syntax.node (Lean.SourceInfo.none) `null #[]]]

-/
def mine (stx : Syntax) : Unit :=
  let _ := matchstxwith|`(#coreFmt$typeExpr$fnExpr)=>2|_=>3
  ()
