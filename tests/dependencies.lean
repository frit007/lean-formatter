import PFMT
import BaseFormatter

open Lean
open PrettyFormat

-- this functions assumes that there are no Syntax objects in the doc
partial def markCachedObject (doc:FormatM Doc) : (Doc × FormatState) :=
  let (doc, cache) := doc.run {formattingFunction := fun _ _ _ _ =>
    (toDoc "_", 0, {})}
  (doc, cache)

-- without restrictions it will choose the hard newline
/--
info: nl
after
-/
#guard_msgs in
#eval do
  let d := ("nl" <$$$> ""<^> "sp" <_> "") <> "after"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


/--
info: ((("nl") <> (provideDoc bridgeHardNl)) <> ("")) <> ("after")
nl
after
-/
#guard_msgs in
#eval do
  let d := ("nl" <$$$> "") <> "after"
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"




/--
info: (((("sp") <> (provideDoc bridgeSpace)) <> (""))<^>((("nl") <> (provideDoc bridgeHardNl)) <> (""))
) <> ((("") <> (provideDoc bridgeNl)) <> ("after"))
nl
after
-/
#guard_msgs in /- If right side demands newline, then it must be chosen-/
#eval do
  let d := ("sp" <_> "" <^> "nl" <$$$> "") <> (""<$$>"after")
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: (((("nl") <> (provideDoc bridgeHardNl)) <> (""))<^>((("sp") <> (provideDoc bridgeSpace)) <> (""))
) <> ((("") <> (provideDoc bridgeNl)) <> ("after"))
nl
after
-/
#guard_msgs in /- If right side demands newline, then it must be chosen (reversed)-/
#eval do
  let d := ( "nl" <$$$> "" <^> "sp" <_> "")  <> (""<$$>"after")
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: PrettyFormat.Doc.flatten
  (PrettyFormat.Doc.concat
    (PrettyFormat.Doc.choice
      (PrettyFormat.Doc.concat
        (PrettyFormat.Doc.text
          "sp"
          { id := 0,
            cacheWeight := 0,
            collapsesBridges := PrettyFormat.Ternary.yes,
            flattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            flattenRPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            flattenLPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            path := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] })
        (PrettyFormat.Doc.provide
          8
          { id := 0,
            cacheWeight := 1,
            collapsesBridges := PrettyFormat.Ternary.no,
            flattenPath := #[(24, 8), (8, 8)],
            flattenRPath := #[(1, 8), (8, 8)],
            flattenLPath := #[(1, 8), (8, 8)],
            eventuallyFlattenPath := #[(1, 8), (8, 8)],
            path := #[(1, 8), (8, 8)] })
        { id := 0,
          cacheWeight := 2,
          collapsesBridges := PrettyFormat.Ternary.yes,
          flattenPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
          flattenRPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
          flattenLPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
          eventuallyFlattenPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
          path := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)] })
      (PrettyFormat.Doc.concat
        (PrettyFormat.Doc.text
          "nl"
          { id := 0,
            cacheWeight := 0,
            collapsesBridges := PrettyFormat.Ternary.yes,
            flattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            flattenRPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            flattenLPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
            path := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] })
        (PrettyFormat.Doc.provide
          4
          { id := 0,
            cacheWeight := 1,
            collapsesBridges := PrettyFormat.Ternary.no,
            flattenPath := #[(24, 0), (0, 0)],
            flattenRPath := #[(1, 4), (4, 4)],
            flattenLPath := #[(1, 4), (4, 4)],
            eventuallyFlattenPath := #[(1, 4), (4, 4)],
            path := #[(1, 4), (4, 4)] })
        { id := 0,
          cacheWeight := 2,
          collapsesBridges := PrettyFormat.Ternary.yes,
          flattenPath := #[],
          flattenRPath := #[],
          flattenLPath := #[(1, 4), (2, 4), (4, 4), (8, 4), (16, 4)],
          eventuallyFlattenPath := #[(1, 4), (2, 4), (4, 4), (8, 4), (16, 4)],
          path := #[(1, 4), (2, 4), (4, 4), (8, 4), (16, 4)] })
      { id := 0,
        cacheWeight := 3,
        collapsesBridges := PrettyFormat.Ternary.yes,
        flattenPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
        flattenRPath := #[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)],
        flattenLPath := #[(1, 12), (2, 12), (4, 12), (8, 12), (16, 12)],
        eventuallyFlattenPath := #[(1, 12), (2, 12), (4, 12), (8, 12), (16, 12)],
        path := #[(1, 12), (2, 12), (4, 12), (8, 12), (16, 12)] })
    (PrettyFormat.Doc.concat
      (PrettyFormat.Doc.provide
        6
        { id := 0,
          cacheWeight := 1,
          collapsesBridges := PrettyFormat.Ternary.no,
          flattenPath := #[(24, 8), (8, 8), (0, 0)],
          flattenRPath := #[(1, 6), (2, 2), (4, 4)],
          flattenLPath := #[(1, 6), (2, 2), (4, 4)],
          eventuallyFlattenPath := #[(1, 6), (2, 2), (4, 4)],
          path := #[(1, 6), (2, 2), (4, 4)] })
      (PrettyFormat.Doc.text
        "after"
        { id := 0,
          cacheWeight := 0,
          collapsesBridges := PrettyFormat.Ternary.yes,
          flattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
          flattenRPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
          flattenLPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
          eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)],
          path := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] })
      { id := 0,
        cacheWeight := 2,
        collapsesBridges := PrettyFormat.Ternary.yes,
        flattenPath := #[(24, 15), (8, 15)],
        flattenRPath := #[(1, 15), (2, 15), (4, 15)],
        flattenLPath := #[(24, 15), (8, 15)],
        eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15)],
        path := #[(1, 15), (2, 15), (4, 15)] })
    { id := 0,
      cacheWeight := 0,
      collapsesBridges := PrettyFormat.Ternary.yes,
      flattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
      flattenRPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
      flattenLPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
      eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
      path := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)] })
  { id := 0,
    cacheWeight := 1,
    collapsesBridges := PrettyFormat.Ternary.yes,
    flattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
    flattenRPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
    flattenLPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
    eventuallyFlattenPath := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)],
    path := #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)] }
doc : lb 1 rb 15 kind flatten flatten: 0 :::: flattenDoc (((("sp") <> (provideDoc bridgeSpace))<^>(("nl") <> (provideDoc bridgeHardNl))
) <> ((provideDoc bridgeNl) <> ("after"))) path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
doc : lb 1 rb 15 kind concat flatten: 4 :::: ((("sp") <> (provideDoc bridgeSpace))<^>(("nl") <> (provideDoc bridgeHardNl))
) <> ((provideDoc bridgeNl) <> ("after")) path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
concat bridges: 6 5 leftCollapses: true rightCollapses: true
concat: new right: 24 currentRight: 15  rhs path: #[(24, 15), (8, 15)] lhs : (("sp") <> (provideDoc bridgeSpace))<^>(("nl") <> (provideDoc bridgeHardNl))
 rhs : (provideDoc bridgeNl) <> ("after")
doc : lb 1 rb 24 kind choice flatten: 6 :::: (("sp") <> (provideDoc bridgeSpace))<^>(("nl") <> (provideDoc bridgeHardNl))
 path:(#[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)])
choice::l true val ("sp") <> (provideDoc bridgeSpace) lbridge : 1 rbridge : 24
choice::r false val ("nl") <> (provideDoc bridgeHardNl) lbridge : 1 rbridge : 24
doc : lb 1 rb 24 kind concat flatten: 6 :::: ("sp") <> (provideDoc bridgeSpace) path:(#[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)])
concat bridges: 6 7 leftCollapses: true rightCollapses: false
concat: new right: 24 currentRight: 24  rhs path: #[(24, 8), (8, 8)] lhs : "sp" rhs : provideDoc bridgeSpace
doc : lb 1 rb 24 kind text sp flatten: 6 :::: "sp" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? lb1 rb 24
doc : lb 1 rb 24 kind text sp flatten: 6 :::: "sp" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? right MeasureSet.set 1 [(rightBridge 1, last:2)]
doc : lb 1 rb 24 kind provide flatten: 7 :::: provideDoc bridgeSpace path:(#[(24, 8), (8, 8)])
provide 8 8
provide gives 8
doc : lb 8 rb 15 kind concat flatten: 5 :::: (provideDoc bridgeNl) <> ("after") path:(#[(24, 15), (8, 15)])
concat bridges: 7 5 leftCollapses: false rightCollapses: true
concat: new right: 31 currentRight: 15  rhs path: #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] lhs : provideDoc bridgeNl rhs : "after"
doc : lb 8 rb 31 kind provide flatten: 7 :::: provideDoc bridgeNl path:(#[(24, 8), (8, 8), (0, 0)])
provide 8 8
provide gives 8
doc : lb 8 rb 15 kind text after flatten: 5 :::: "after" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
sp after
-/
#guard_msgs in /- If right side demands newline, then it must be chosen-/
#eval do
  let d := flattenDoc (("sp" <> provideDoc bridgeSpace <^> "nl" <> provideDoc bridgeHardNl) <> (bridgeNl !> "after"))
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{repr d}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc (((("(") <> ((("e") <> (provideDoc bridgeNone))<^>((("sp") <> (provideDoc bridgeSpace)) <> (""))
)) <> (((((requireDoc bridgeNone) <> ("a")) <> (provideDoc bridgeHardNl)) <> ("nlafter"))<^>((("") <> (provideDoc bridgeSpace)) <> ("spafter"))
)) <> (")"))
(sp spafter)
-/
#guard_msgs in /- If right side demands space, due to flatten it must be discovered-/
#eval do
  let d := flattenDoc ("(" <> ( ("e" <> provideDoc bridgeNone) <^> "sp" <_> "")  <> ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter") <>")")
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc (((("(") <> (((("sp") <> (provideDoc bridgeSpace)) <> (""))<^>(("e") <> (provideDoc bridgeNone))
)) <> (((((requireDoc bridgeNone) <> ("a")) <> (provideDoc bridgeHardNl)) <> ("nlafter"))<^>((("") <> (provideDoc bridgeSpace)) <> ("spafter"))
)) <> (")"))
(sp spafter)
-/
#guard_msgs in /- If right side demands space, due to flatten it must be discovered (switch)-/
#eval do
  let d := flattenDoc ("(" <> ("sp" <_> "" <^> ("e" <> provideDoc bridgeNone) )  <> ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter") <>")")
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: ("before") <> (flattenDoc ((("") <> (provideDoc bridgeNl)) <> ("center")))
before
center
-/
#guard_msgs in /- allow bridges on the left side inside flatten-/
#eval do
  let d := "before"<>flattenDoc ("" <$$> "center")
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: (flattenDoc ((("-- comment") <> (provideDoc bridgeHardNl)) <> (""))) <> ("after the comment")
-- comment
after the comment
-/
#guard_msgs in /- allow bridges on the right side inside flatten-/
#eval do
  let d := flattenDoc ("-- comment" <$$$> "") <> "after the comment"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: (("before") <> (flattenDoc ((((("") <> (provideDoc bridgeHardNl)) <> (((("(") <> ("center")) <> (provideDoc bridgeNl)) <> ((("cookie") <> (")")) <> ("-- comment")))) <> (provideDoc bridgeHardNl)) <> ("")))) <> ("after the comment")
before
(center cookie)-- comment
after the comment
-/
#guard_msgs in /- Allow bridges on the sides but not inside-/
#eval do
  let d := "before"<>flattenDoc (""<$$$>"("<>"center"<$$>"cookie"<>")" <> "-- comment" <$$$> "") <> "after the comment"
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
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
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: ((("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> (((((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")")
(e!e
later)
-/
#guard_msgs in /- Demonstrate that bridgeNone would be chosen if there are no requirements (to inform the next test) -/
#eval do
  let d := "("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later")<^> bridgeImmediate<!"!i") <> ")"
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"



/--
info: flattenDoc ((/-2-/ (("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((/-1-/ (((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline -/ --TODO:
#eval do
  let d := flattenDoc ("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i") <> ")")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc ((("(") <> (/-1-/ ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
) <> (((((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
))) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline -/
#eval do
  let d := flattenDoc ("("<>(("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i")) <> ")")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: flattenDoc ((/-2-/ (("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((/-1-/ (((requireDoc bridgeNone) <> ("!e")) <> (provideDoc bridgeHardNl)) <> ("later"))<^>((requireDoc bridgeImmediate) <> ("!i"))
)) <> (")"))
(i!i)
-/
#guard_msgs in /- bridgeNone can no longer be chosen because it leads to a hard newline, why would order of operations change it? -/ --TODO:
#eval do
  let d := flattenDoc (("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone)) <> ((bridgeNone<!"!e" <$$$> "later") <^> bridgeImmediate<!"!i") <> ")")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: (("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
)) <> ((requireDoc bridgeImmediate) <> ("!i"))
(i!i
-/
#guard_msgs in /- The right bridge constraint should persist even when going through children -/
#eval do
  let d := ("("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone)) <> bridgeImmediate<!"!i"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


/--
info: flattenDoc ((("(") <> (flattenDoc ((("--comment") <> (provideDoc bridgeNl)) <> ("")))) <> (")"))
(--comment )
-/
#guard_msgs in /- flatten does not "unflatten", we expect a space from the inner  -/
#eval do
  let d := flattenDoc ("("<>(flattenDoc ("--comment" <$$> ""))<>")")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"



/--
info: (("basic") <> (provideDoc bridgeSpace)) <> ("space")
doc : lb 1 rb 15 kind concat flatten: 0 :::: (("basic") <> (provideDoc bridgeSpace)) <> ("space") path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
concat bridges: 0 0 leftCollapses: true rightCollapses: true
concat: new right: 31 currentRight: 15  rhs path: #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] lhs : ("basic") <> (provideDoc bridgeSpace) rhs : "space"
doc : lb 1 rb 31 kind concat flatten: 0 :::: ("basic") <> (provideDoc bridgeSpace) path:(#[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)])
concat bridges: 0 0 leftCollapses: true rightCollapses: false
concat: new right: 9 currentRight: 31  rhs path: #[(1, 8), (8, 8)] lhs : "basic" rhs : provideDoc bridgeSpace
doc : lb 1 rb 9 kind text basic flatten: 0 :::: "basic" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? lb1 rb 9
doc : lb 1 rb 9 kind text basic flatten: 0 :::: "basic" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? right MeasureSet.set 1 [(rightBridge 1, last:5)]
doc : lb 1 rb 31 kind provide flatten: 0 :::: provideDoc bridgeSpace path:(#[(1, 8), (8, 8)])
provide 8 8
provide gives 8
doc : lb 8 rb 15 kind text space flatten: 0 :::: "space" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
basic space
-/
#guard_msgs in /- basics: space after between elements  -/
#eval do
  let d := "basic" <_> "space"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


/--
info: (("basic") <> (provideDoc bridgeAny)) <> ("any")
doc : lb 1 rb 15 kind concat flatten: 0 :::: (("basic") <> (provideDoc bridgeAny)) <> ("any") path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
concat bridges: 0 0 leftCollapses: true rightCollapses: true
concat: new right: 31 currentRight: 15  rhs path: #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] lhs : ("basic") <> (provideDoc bridgeAny) rhs : "any"
doc : lb 1 rb 31 kind concat flatten: 0 :::: ("basic") <> (provideDoc bridgeAny) path:(#[(1, 14), (2, 14), (4, 14), (8, 14), (16, 14)])
concat bridges: 0 0 leftCollapses: true rightCollapses: false
concat: new right: 15 currentRight: 31  rhs path: #[(1, 14), (2, 2), (4, 4), (8, 8)] lhs : "basic" rhs : provideDoc bridgeAny
doc : lb 1 rb 15 kind text basic flatten: 0 :::: "basic" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? lb1 rb 15
doc : lb 1 rb 15 kind text basic flatten: 0 :::: "basic" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? right MeasureSet.set 1 [(rightBridge 1, last:5)]
doc : lb 1 rb 31 kind provide flatten: 0 :::: provideDoc bridgeAny path:(#[(1, 14), (2, 2), (4, 4), (8, 8)])
provide 14 14
provide gives 14
doc : lb 14 rb 15 kind text any flatten: 0 :::: "any" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
basic
any
-/
#guard_msgs in /- basics: any  -/
#eval do
  let d := "basic" <**> "any"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


/--
info: /-3-/ ((((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
) <> (provideDoc bridgeSpace)) <> ((((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny)) <> ((/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
))
doc : lb 1 rb 15 kind concat flatten: 0 :::: /-3-/ ((((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
) <> (provideDoc bridgeSpace)) <> ((((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny)) <> ((/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
)) path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
concat bridges: 0 0 leftCollapses: true rightCollapses: true
concat: new right: 31 currentRight: 15  rhs path: #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)] lhs : (((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
) <> (provideDoc bridgeSpace) rhs : (((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny)) <> ((/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
)
doc : lb 1 rb 31 kind concat flatten: 0 :::: (((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
) <> (provideDoc bridgeSpace) path:(#[(1, 8), (2, 8), (4, 8), (8, 8), (16, 8)])
concat bridges: 0 0 leftCollapses: true rightCollapses: false
concat: new right: 9 currentRight: 31  rhs path: #[(1, 8), (8, 8)] lhs : ((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
 rhs : provideDoc bridgeSpace
doc : lb 1 rb 9 kind choice flatten: 0 :::: ((("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
 path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
choice::l false val (("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")) lbridge : 1 rbridge : 9
choice::r true val "Singleton" lbridge : 1 rbridge : 9
doc : lb 1 rb 9 kind text Singleton flatten: 0 :::: "Singleton" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? lb1 rb 9
doc : lb 1 rb 9 kind text Singleton flatten: 0 :::: "Singleton" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
center? right MeasureSet.set 1 [(rightBridge 1, last:9)]
doc : lb 1 rb 31 kind provide flatten: 0 :::: provideDoc bridgeSpace path:(#[(1, 8), (8, 8)])
provide 8 8
provide gives 8
doc : lb 8 rb 15 kind concat flatten: 0 :::: (((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny)) <> ((/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
) path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 15)])
concat bridges: 0 0 leftCollapses: true rightCollapses: true
concat: new right: 31 currentRight: 15  rhs path: #[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)] lhs : ((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny) rhs : (/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")

doc : lb 8 rb 31 kind concat flatten: 0 :::: ((/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
) <> (provideDoc bridgeAny) path:(#[(1, 14), (2, 14), (4, 14), (8, 14), (16, 14)])
concat bridges: 0 0 leftCollapses: true rightCollapses: false
concat: new right: 15 currentRight: 31  rhs path: #[(1, 14), (2, 2), (4, 4), (8, 8)] lhs : (/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
 rhs : provideDoc bridgeAny
doc : lb 8 rb 15 kind choice flatten: 0 :::: (/-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
 path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
choice::l false val /-1-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")) lbridge : 8 rbridge : 15
choice::r true val "Name" lbridge : 8 rbridge : 15
doc : lb 8 rb 15 kind text Name flatten: 0 :::: "Name" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
doc : lb 1 rb 31 kind provide flatten: 0 :::: provideDoc bridgeAny path:(#[(1, 14), (2, 2), (4, 4), (8, 8)])
provide 14 14
provide gives 14
doc : lb 14 rb 15 kind choice flatten: 0 :::: (/-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
 path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
choice::l false val /-2-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")) lbridge : 14 rbridge : 15
choice::r true val "NameSet" lbridge : 14 rbridge : 15
doc : lb 14 rb 15 kind text NameSet flatten: 0 :::: "NameSet" path:(#[(1, 15), (2, 15), (4, 15), (8, 15), (16, 31)])
Singleton Name
NameSet
-/
#guard_msgs in /- complex  -/
#eval do
  let d := (((/-2-/ (("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
    ) <> (provideDoc bridgeSpace)) <> ((((/-3-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
    ) <> (provideDoc bridgeAny)) <> ((/-4-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
    ))
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


-- #guard_msgs in /- complex  -/
-- #eval do
--   let d := (nestDoc 4 (((((("instance") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("instance")
-- ) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Command.declSig"
--  (/-6-/ ruleDoc "Lean.Parser.Term.typeSpec"
--    ((((/-1-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--      (/-5-/ (((/-2-/ (("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
--       ) <> (provideDoc bridgeSpace)) <> ((((/-3-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
--       ) <> (provideDoc bridgeAny)) <> ((/-4-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
--       )))
--     ))
--   )
-- ))) <> ((provideDoc bridgeAny) <> (/-34-/ ruleDoc "Lean.Parser.Command.whereStructInst"
--  ((((/-7-/ ((("where") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("where")
--   ) <> (/-33-/ nestDoc 2 ((("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.structInstFields"
--    (/-32-/ ruleDoc "Lean.Parser.Term.structInstField"
--      (((/-9-/ ruleDoc "Lean.Parser.Term.structInstLVal"
--        ((("") <> ((/-8-/ (("singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("singleton")
--         )) <> (""))
--       ) <> (provideDoc bridgeSpace)) <> (/-31-/ ruleDoc "Lean.Parser.Term.structInstFieldDef"
--        ((((/-10-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--         ) <> (provideDoc bridgeSpace)) <> ((provideDoc (bridgeSpaceNl|||bridgeSpace|||bridgeImmediate)) <> (ruleDoc "Lean.Parser.Term.fun"
--          (/-30-/ ((((/-27-/ (("fun") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("fun")
--           ) <> (provideDoc bridgeAny)) <> (/-26-/ ruleDoc "Lean.Parser.Term.basicFun"
--            (((/-22-/ (requireDoc bridgeImmediate) <> ((((/-20-/ (("n") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("n")
--             ) <> (provideDoc bridgeSpace)) <> ((/-21-/ (("=>") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=>")
--             ))) <> ((Doc.newline (some " ")) <> (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))<^>(/-25-/ ((((/-23-/ (("n") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("n")
--             ) <> (provideDoc bridgeSpace)) <> ((/-24-/ (("=>") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=>")
--             )) <> ((nestDoc 2 ((Doc.newline (some " ")) <> (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))<^>((" ") <> (flattenDoc (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))
--             ))
--             )
--           ))<^>(/-29-/ (((requireDoc bridgeImmediate) <> (" ")) <> ((/-28-/ (("fun") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("fun")
--           )) <> ((provideDoc bridgeImmediate) <> (/-26-/ ruleDoc "Lean.Parser.Term.basicFun"
--            (((/-22-/ (requireDoc bridgeImmediate) <> ((((/-20-/ (("n") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("n")
--             ) <> (provideDoc bridgeSpace)) <> ((/-21-/ (("=>") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=>")
--             ))) <> ((Doc.newline (some " ")) <> (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))<^>(/-25-/ ((((/-23-/ (("n") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("n")
--             ) <> (provideDoc bridgeSpace)) <> ((/-24-/ (("=>") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=>")
--             )) <> ((nestDoc 2 ((Doc.newline (some " ")) <> (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))<^>((" ") <> (flattenDoc (/-19-/ ruleDoc "Lean.Parser.Term.app"
--              ((/-18-/ (ruleDoc "Lean.Parser.Term.proj"
--                ((/-15-/ (ruleDoc "Lean.Parser.Term.typeAscription"
--                  ((("(") <> (/-14-/ (((/-12-/ (ruleDoc "«term∅»"
--                    (("") <> ((/-11-/ (("∅") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("∅")
--                     ))
--                   ) <> (provideDoc bridgeSpace)) <> ((/-13-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--                   )) <> (provideDoc bridgeSpace)) <> (("") <> ("NameSet")))) <> (")"))
--                 ) <> (".")) <> ((/-16-/ (("insert") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("insert")
--                 ))
--               ) <> (provideDoc bridgeSpace)) <> (((/-17-/ ((("n") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("n")
--               ))
--             )))
--             ))
--             )
--           )))
--           )
--         )))
--       ))
--     )
--   ))))
-- ))
--   let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
--   IO.println s!"{d.toString}"
--   let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
--   IO.println s!"{out}"


/--
info: doc : lb 1 rb 15 kind text  flatten: 0 :::: "" path:(#[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)])
PrettyFormat.Doc.text
  ""
  { id := 0,
    cacheWeight := 1,
    collapsesBridges := PrettyFormat.Ternary.no,
    flattenPath := #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)],
    flattenRPath := #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)],
    flattenLPath := #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)],
    eventuallyFlattenPath := #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)],
    path := #[(1, 1), (2, 2), (4, 4), (8, 8), (16, 16), (32, 32)] }
-/
#guard_msgs in /- TODO: delete  -/
#eval do
  let d := (toDoc "")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{repr d}"
  IO.println s!"{out}"
