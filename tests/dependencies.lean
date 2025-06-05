import PFMT
import BaseFormatter




open Lean
open PrettyFormat

-- without restrictions it will choose the hard newline
/--
info: nl
after
-/
#guard_msgs in
#eval do
  let d := ("nl" <$$$> ""<^> "sp" <_> "") <> "after"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/--
info: (("nl") <> (provideDoc bridgeHardNl)) <> ("after")
nl
after
-/
#guard_msgs in
#eval do
  let d := ("nl" <$$$> "") <> "after"
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"




/--
info: ((("sp") <> (provideDoc bridgeSpace))<^>(("nl") <> (provideDoc bridgeHardNl))
) <> ((provideDoc bridgeNl) <> ("after"))
nl
after
-/
#guard_msgs in /- If right side demands newline, then it must be chosen-/
#eval do
  let d := ("sp" <_> "" <^> "nl" <$$$> "") <> (""<$$>"after")
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: ((("nl") <> (provideDoc bridgeHardNl))<^>(("sp") <> (provideDoc bridgeSpace))
) <> ((provideDoc bridgeNl) <> ("after"))
nl
after
-/
#guard_msgs in /- If right side demands newline, then it must be chosen (reversed)-/
#eval do
  let d := ( "nl" <$$$> "" <^> "sp" <_> "")  <> (""<$$>"after")
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/-- info: sp after -/
#guard_msgs in /- If right side demands newline, then it must be chosen-/
#eval do
  let d := flattenDoc (("sp" <> provideDoc bridgeSpace <^> "nl" <> provideDoc bridgeHardNl) <> (bridgeNl !> "after"))
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{repr d}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/-- info: (sp spafter) -/
#guard_msgs in /- If right side demands space, due to flatten it must be discovered-/
#eval do
  let d := flattenDoc ("(" <> ( ("e" <> provideDoc bridgeNone) <^> "sp" <_> "")
    <> ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter") <>")")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{d.printDependencies}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc (((("(") <> ((("sp") <> (provideDoc bridgeSpace))<^>(("e") <> (provideDoc bridgeNone))
)) <> (((((requireDoc bridgeNone) <> ("a")) <> (provideDoc bridgeHardNl)) <> ("nlafter"))<^>((provideDoc bridgeSpace) <> ("spafter"))
)) <> (")"))
(sp spafter)
-/
#guard_msgs in /- If right side demands space, due to flatten it must be discovered (switch)-/
#eval do
  let d := flattenDoc ("(" <> ("sp" <_> "" <^> ("e" <> provideDoc bridgeNone) )  <> ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter") <>")")
  IO.println s!"{d.toString}"
  -- let d2 := ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: ("before") <> (flattenDoc ((provideDoc bridgeNl) <> ("center")))
before
center
-/
#guard_msgs in /- allow bridges on the left side inside flatten-/
#eval do
  let d := "before"<>flattenDoc ("" <$$> "center")
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: /-1-/ (flattenDoc (("-- comment") <> (provideDoc bridgeHardNl))) <> ("after the comment")
-- comment
after the comment
-/
#guard_msgs in /- allow bridges on the right side inside flatten-/
#eval do
  let d := flattenDoc ("-- comment" <$$$> "") <> "after the comment"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: (("before") <> (flattenDoc (((provideDoc bridgeHardNl) <> (((("(") <> ("center")) <> (provideDoc bridgeNl)) <> ((("cookie") <> (")")) <> ("-- comment")))) <> (provideDoc bridgeHardNl)))) <> ("after the comment")
before
(center cookie)-- comment
after the comment
-/
#guard_msgs in /- Allow bridges on the sides but not inside-/
#eval do
  let d := "before"<>flattenDoc (""<$$$>"("<>"center"<$$>"cookie"<>")" <> "-- comment" <$$$> "") <> "after the comment"
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/--
info: ((("e") <> (provideDoc bridgeNone))<^>(("i") <> (provideDoc bridgeImmediate))
) <> (((requireDoc bridgeNone) <> ("!e"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)
e!e
-/
#guard_msgs in /- show that e would be picked in this scenario -/
#eval do
  let d := ("e" <>provideDoc bridgeNone <^> "i" <> provideDoc bridgeImmediate) <> (bridgeNone<!"!e" <^> bridgeImmediate<!"!i")
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: ((("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> (((((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")")
(i!i)
-/
#guard_msgs in /- Demonstrate that bridgeNone would be chosen if there are no requirements (to inform the next test) -/
#eval do
  let d := "("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later")<^> bridgeImmediate<!"!i") <> ")"
  IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"



/--
info: flattenDoc ((/-3-/ (/-1-/ ("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((/-2-/ (((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline -/ --TODO:
#eval do
  let d := flattenDoc ("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i") <> ")")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: /-3-/ flattenDoc ((("(") <> (/-2-/ ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
) <> ((/-1-/ (((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
))) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline -/
#eval do
  let d := flattenDoc ("("<>(("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i")) <> ")")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc ((/-3-/ (/-1-/ ("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((/-2-/ (((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline, why would order of operations change it? -/ --TODO:
#eval do
  let d := flattenDoc (("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone)) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i") <> ")")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"

/--
info: (/-1-/ ("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((requireDoc bridgeImmediate) <> ("!i"))
(i!i
-/
#guard_msgs in /- The right bridge constraint should persist even when going through children -/
#eval do
  let d := ("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone)) <> bridgeImmediate<!"!i"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/--
info: flattenDoc ((/-1-/ ("(") <> (flattenDoc (("--comment") <> (provideDoc bridgeNl)))) <> (")"))
(--comment )
-/
#guard_msgs in /- flatten does not "unflatten", we expect a space from the inner  -/
#eval do
  let d := flattenDoc ("("<>(flattenDoc ("--comment" <$$> ""))<>")")
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"



/--
info: (("basic") <> (provideDoc bridgeSpace)) <> ("space")
basic space
-/
#guard_msgs in /- basics: space after between elements  -/
#eval do
  let d := "basic" <_> "space"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/--
info: (("basic") <> (provideDoc bridgeAny)) <> ("any")
basic
any
-/
#guard_msgs in /- basics: any  -/
#eval do
  let d := "basic" <**> "any"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/--
info: Singleton Name
NameSet
-/
#guard_msgs in /- complex  -/
#eval do
  let d := (((/-2-/ (("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
    ) <> (provideDoc bridgeSpace)) <> ((((/-3-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
    ) <> (provideDoc bridgeAny)) <> ((/-4-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
    ))
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{d.toJSON}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"



/--
info: hello
world
-/
#guard_msgs in /- complex  -/
#eval do
  let d := "hello" <**> "world"
  let (d, cache) := simpleFormattingContext (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"


/-- info: a b -/
#guard_msgs in
#eval do
  -- let d := "" <_> ("" <_> "b" <^> "" <$$> "c")
  let d := "a" <_> ("" <_> "b" <^> "" <$$> "a")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) (computationWidth := 0) d
  IO.println s!"{out}"
