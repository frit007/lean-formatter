import PFMT
import BaseFormatter

open PrettyFormat
-- without restrictions it will choose the hard newline
/--
info: nln
after
-/
#guard_msgs in
#eval do
  let d := "nln" <>(Doc.hardNl<> "after" <^> " after")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 2) (computationWidth := 100) d
  IO.println s!"{out}"


/--
info: nln
after
-/
#guard_msgs in
#eval do
  let d := "nln" <>(" after" <^> Doc.hardNl<> "after")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 2) (computationWidth := 100) d
  IO.println s!"{out}"
