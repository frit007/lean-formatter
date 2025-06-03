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

/-- info: sp after -/
#guard_msgs in /- If right side demands newline, then it must be chosen-/
#eval do
  let d := flattenDoc (("sp" <> provideDoc bridgeSpace <^> "nl" <> provideDoc bridgeHardNl) <> (bridgeNl !> "after"))
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{repr d}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/-- info: (sp spafter) -/
#guard_msgs in /- If right side demands space, due to flatten it must be discovered-/
#eval do
  let d := flattenDoc ("(" <> ( ("e" <> provideDoc bridgeNone) <^> "sp" <_> "")
    <> ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter") <>")")
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{d.printDependencies}"
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
  -- let d2 := ((bridgeNone <! "a")<$$$>"nlafter" <^> ""<_>"spafter")
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
info: (/-1-/ flattenDoc ((("-- comment") <> (provideDoc bridgeHardNl)) <> (""))) <> ("after the comment")
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
(i!i)
-/
#guard_msgs in /- Demonstrate that bridgeNone would be chosen if there are no requirements (to inform the next test) -/
#eval do
  let d := "("<>("i" <> provideDoc bridgeImmediate <^> "e" <>provideDoc bridgeNone) <> ((bridgeNone<!"!e" <$$$> "later")<^> bridgeImmediate<!"!i") <> ")"
  IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
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
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
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
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
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
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toString}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"

/--
info: (/-1-/ ("(") <> ((("i") <> (provideDoc bridgeImmediate))<^>(("e") <> (provideDoc bridgeNone))
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
info: /-2-/ flattenDoc ((("(") <> (/-1-/ flattenDoc ((("--comment") <> (provideDoc bridgeNl)) <> ("")))) <> (")"))
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
info: Singleton Name
NameSet
-/
#guard_msgs in /- complex  -/
#eval do
  let d := (((/-2-/ (("Singleton") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Singleton")
    ) <> (provideDoc bridgeSpace)) <> ((((/-3-/ (("Name") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("Name")
    ) <> (provideDoc bridgeAny)) <> ((/-4-/ (("NameSet") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("NameSet")
    ))
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  -- IO.println s!"{d.toJSON}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"



/--
info: {
  "start":{"type": "concat",
  "meta": {
    "id": 0,
    "cacheWeight": 3,
    "collapsesBridges": "yes",
    "flattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
    "flattenRPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
    "flattenLPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
    "eventuallyFlattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
    "path": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]]
    },
  "lhs": {"type": "concat",
    "meta": {
      "id": 0,
      "cacheWeight": 2,
      "collapsesBridges": "yes",
      "flattenPath": [[1, 8], [2, 8], [4, 8], [8, 8], [16, 8]],
      "flattenRPath": [[1, 8], [2, 8], [4, 8], [8, 8], [16, 8]],
      "flattenLPath": [[1, 14], [2, 14], [4, 14], [8, 14], [16, 14]],
      "eventuallyFlattenPath": [[1, 14], [2, 14], [4, 14], [8, 14], [16, 14]],
      "path": [[1, 14], [2, 14], [4, 14], [8, 14], [16, 14]]
      },
    "lhs": {"type": "text", "s": "hello",
      "meta": {
        "id": 0,
        "cacheWeight": 1,
        "collapsesBridges": "yes",
        "flattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
        "flattenRPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
        "flattenLPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
        "eventuallyFlattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
        "path": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]]
        }},
    "rhs": {"type": "provide", "value": 14,
      "meta": {
        "id": 0,
        "cacheWeight": 1,
        "collapsesBridges": "no",
        "flattenPath": [[1, 8], [8, 8], [0, 0], [8, 8]],
        "flattenRPath": [[1, 14], [2, 2], [4, 4], [8, 8]],
        "flattenLPath": [[1, 14], [2, 2], [4, 4], [8, 8]],
        "eventuallyFlattenPath": [[1, 14], [2, 2], [4, 4], [8, 8]],
        "path": [[1, 14], [2, 2], [4, 4], [8, 8]]
        }}},
  "rhs": {"type": "text", "s": "world",
    "meta": {
      "id": 0,
      "cacheWeight": 1,
      "collapsesBridges": "yes",
      "flattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
      "flattenRPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
      "flattenLPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
      "eventuallyFlattenPath": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]],
      "path": [[1, 15], [2, 15], [4, 15], [8, 15], [16, 15]]
      }}}
}
hello
world
-/
#guard_msgs in /- complex  -/
#eval do
  let d := "hello" <**> "world"
  let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
  IO.println s!"{d.toJSON}"
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 0) d
  IO.println s!"{out}"


















/-
-- info: -- TODO: splitOn
-- theorem split_of_valid (s p) : split s p = (List.splitOnP p s.1).map mk := by simpa [split] using splitAux_of_valid p [] [] s.1 []
-- -/
-- #guard_msgs in /- TODO: delete  -/
-- #eval do
--   let d := (ruleDoc "Lean.Parser.Command.declaration"
--  ((/-83-/ ruleDoc "Lean.Parser.Command.theorem"
--    (((/-73-/ (((/-68-/ (("theorem") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("theorem")
--     ) <> (provideDoc bridgeAny)) <> (/-72-/ nestDoc 4 (((ruleDoc "Lean.Parser.Command.declId"
--      (/-70-/ (((/-69-/ (("split_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split_of_valid")
--       ) <> (provideDoc bridgeAny)) <> (""))
--     ) <> (provideDoc bridgeAny)) <> (/-71-/ (ruleDoc "Lean.Parser.Command.declSig"
--      ((/-8-/ (ruleDoc "Lean.Parser.Term.explicitBinder"
--        (("(") <> (/-7-/ ((/-1-/ ((((("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-2-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         ))<^>(/-6-/ flattenDoc ((/-4-/ (((/-3-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-5-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         )))
--         ))
--       ) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.typeSpec"
--        (/-29-/ (((/-9-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--         ) <> (provideDoc bridgeSpace)) <> (ruleDoc "«term_=_»"
--          (((/-26-/ (((ruleDoc "Lean.Parser.Term.app"
--            (/-14-/ (((/-10-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-13-/ (((/-11-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-12-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeAny)) <> ((/-25-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           )) <> (provideDoc bridgeSpace)) <> (/-24-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-22-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-20-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-19-/ (((/-15-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-18-/ (((/-16-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-17-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-21-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-23-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))<^>(/-28-/ ((ruleDoc "Lean.Parser.Term.app"
--            (/-14-/ (((/-10-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-13-/ (((/-11-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-12-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeSpace)) <> (((/-27-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           ) <> ((provideDoc bridgeImmediate) <> (/-24-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-22-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-20-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-19-/ (((/-15-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-18-/ (((/-16-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-17-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-21-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-23-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))))
--           )
--         ))
--       ))
--     ) <> ((("") <> (provideDoc bridgeAny)) <> (""))))))<^>(flattenDoc (/-79-/ (((/-74-/ (("theorem") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("theorem")
--     ) <> (provideDoc bridgeAny)) <> (/-78-/ nestDoc 4 (((ruleDoc "Lean.Parser.Command.declId"
--      (/-76-/ (((/-75-/ (("split_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split_of_valid")
--       ) <> (provideDoc bridgeAny)) <> (""))
--     ) <> (provideDoc bridgeAny)) <> (/-77-/ (ruleDoc "Lean.Parser.Command.declSig"
--      ((/-8-/ (ruleDoc "Lean.Parser.Term.explicitBinder"
--        (("(") <> (/-7-/ ((/-1-/ ((((("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-2-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         ))<^>(/-6-/ flattenDoc ((/-4-/ (((/-3-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-5-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         )))
--         ))
--       ) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.typeSpec"
--        (/-29-/ (((/-9-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--         ) <> (provideDoc bridgeSpace)) <> (ruleDoc "«term_=_»"
--          (((/-26-/ (((ruleDoc "Lean.Parser.Term.app"
--            (/-14-/ (((/-10-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-13-/ (((/-11-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-12-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeAny)) <> ((/-25-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           )) <> (provideDoc bridgeSpace)) <> (/-24-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-22-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-20-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-19-/ (((/-15-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-18-/ (((/-16-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-17-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-21-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-23-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))<^>(/-28-/ ((ruleDoc "Lean.Parser.Term.app"
--            (/-14-/ (((/-10-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-13-/ (((/-11-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-12-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeSpace)) <> (((/-27-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           ) <> ((provideDoc bridgeImmediate) <> (/-24-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-22-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-20-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-19-/ (((/-15-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-18-/ (((/-16-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-17-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-21-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-23-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))))
--           )
--         ))
--       ))
--     ) <> ((("") <> (provideDoc bridgeAny)) <> ("")))))))
--     ) <> (/-82-/ ((requireDoc bridgeSpace) <> ((provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-67-/ (((nestDoc 2 (/-63-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-59-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-62-/ (/-60-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-61-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-66-/ ((requireDoc bridgeImmediate) <> ((/-64-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-65-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     )))<^>((/-81-/ ((("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-67-/ (((nestDoc 2 (/-63-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-59-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-62-/ (/-60-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-61-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-66-/ ((requireDoc bridgeImmediate) <> ((/-64-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-65-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     ))<^>(/-80-/ flattenDoc ((("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-67-/ (((nestDoc 2 (/-63-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-59-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-62-/ (/-60-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-61-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-66-/ ((requireDoc bridgeImmediate) <> ((/-64-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-65-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-58-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-54-/ (/-53-/ (((/-52-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-57-/ (/-56-/ (((/-55-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-51-/ (((/-50-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-49-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-32-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-30-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-31-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-48-/ (((/-33-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-47-/ (((/-34-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-46-/ (((/-45-/ (((/-44-/ (((/-35-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-37-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-36-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-39-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-38-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-41-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-40-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-43-/ ((/-42-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     )))
--     ) <> (costDoc 3))
--     ))
--   )<^>(flattenDoc (/-167-/ ruleDoc "Lean.Parser.Command.theorem"
--    (((/-157-/ (((/-152-/ (("theorem") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("theorem")
--     ) <> (provideDoc bridgeAny)) <> (/-156-/ nestDoc 4 (((ruleDoc "Lean.Parser.Command.declId"
--      (/-154-/ (((/-153-/ (("split_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split_of_valid")
--       ) <> (provideDoc bridgeAny)) <> (""))
--     ) <> (provideDoc bridgeAny)) <> (/-155-/ (ruleDoc "Lean.Parser.Command.declSig"
--      ((/-92-/ (ruleDoc "Lean.Parser.Term.explicitBinder"
--        (("(") <> (/-91-/ ((/-85-/ (((/-84-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-86-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         ))<^>(/-90-/ flattenDoc ((/-88-/ (((/-87-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-89-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         )))
--         ))
--       ) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.typeSpec"
--        (/-113-/ (((/-93-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--         ) <> (provideDoc bridgeSpace)) <> (ruleDoc "«term_=_»"
--          (((/-110-/ (((ruleDoc "Lean.Parser.Term.app"
--            (/-98-/ (((/-94-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-97-/ (((/-95-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-96-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeAny)) <> ((/-109-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           )) <> (provideDoc bridgeSpace)) <> (/-108-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-106-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-104-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-103-/ (((/-99-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-102-/ (((/-100-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-101-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-105-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-107-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))<^>(/-112-/ ((ruleDoc "Lean.Parser.Term.app"
--            (/-98-/ (((/-94-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-97-/ (((/-95-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-96-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeSpace)) <> (((/-111-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           ) <> ((provideDoc bridgeImmediate) <> (/-108-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-106-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-104-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-103-/ (((/-99-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-102-/ (((/-100-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-101-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-105-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-107-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))))
--           )
--         ))
--       ))
--     ) <> ((("") <> (provideDoc bridgeAny)) <> (""))))))<^>(flattenDoc (/-163-/ (((/-158-/ (("theorem") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("theorem")
--     ) <> (provideDoc bridgeAny)) <> (/-162-/ nestDoc 4 (((ruleDoc "Lean.Parser.Command.declId"
--      (/-160-/ (((/-159-/ (("split_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split_of_valid")
--       ) <> (provideDoc bridgeAny)) <> (""))
--     ) <> (provideDoc bridgeAny)) <> (/-161-/ (ruleDoc "Lean.Parser.Command.declSig"
--      ((/-92-/ (ruleDoc "Lean.Parser.Term.explicitBinder"
--        (("(") <> (/-91-/ ((/-85-/ (((/-84-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-86-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         ))<^>(/-90-/ flattenDoc ((/-88-/ (((/-87-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--         ) <> (provideDoc bridgeSpace)) <> ("p")) <> ((/-89-/ ((")") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(")")
--         )))
--         ))
--       ) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.typeSpec"
--        (/-113-/ (((/-93-/ ((":") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":")
--         ) <> (provideDoc bridgeSpace)) <> (ruleDoc "«term_=_»"
--          (((/-110-/ (((ruleDoc "Lean.Parser.Term.app"
--            (/-98-/ (((/-94-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-97-/ (((/-95-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-96-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeAny)) <> ((/-109-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           )) <> (provideDoc bridgeSpace)) <> (/-108-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-106-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-104-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-103-/ (((/-99-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-102-/ (((/-100-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-101-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-105-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-107-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))<^>(/-112-/ ((ruleDoc "Lean.Parser.Term.app"
--            (/-98-/ (((/-94-/ (("split") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("split")
--             ) <> (provideDoc bridgeSpace)) <> (/-97-/ (((/-95-/ (("s") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("s")
--             ) <> (provideDoc bridgeAny)) <> ((/-96-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--             )))
--           ) <> (provideDoc bridgeSpace)) <> (((/-111-/ (("=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("=")
--           ) <> ((provideDoc bridgeImmediate) <> (/-108-/ ruleDoc "Lean.Parser.Term.app"
--            (((/-106-/ ruleDoc "Lean.Parser.Term.proj"
--              (((/-104-/ ruleDoc "Lean.Parser.Term.paren"
--                ((("(") <> (ruleDoc "Lean.Parser.Term.app"
--                  (/-103-/ (((/-99-/ (("List.splitOnP") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("List.splitOnP")
--                   ) <> (provideDoc bridgeSpace)) <> (/-102-/ (((/-100-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                   ) <> (provideDoc bridgeAny)) <> (/-101-/ ruleDoc "Lean.Parser.Term.proj"
--                    ((("s") <> (".")) <> (ruleDoc "fieldIdx"
--                      ("1")
--                     ))
--                   )))
--                 )) <> (")"))
--               ) <> (".")) <> ((/-105-/ (("map") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("map")
--               ))
--             ) <> (provideDoc bridgeSpace)) <> ((/-107-/ (("mk") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("mk")
--             ))
--           ))))
--           )
--         ))
--       ))
--     ) <> ((("") <> (provideDoc bridgeAny)) <> ("")))))))
--     ) <> (/-166-/ ((requireDoc bridgeSpace) <> ((provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-151-/ (((nestDoc 2 (/-147-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-143-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-146-/ (/-144-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-145-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-150-/ ((requireDoc bridgeImmediate) <> ((/-148-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-149-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     )))<^>((/-165-/ ((("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-151-/ (((nestDoc 2 (/-147-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-143-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-146-/ (/-144-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-145-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-150-/ ((requireDoc bridgeImmediate) <> ((/-148-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-149-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     ))<^>(/-164-/ flattenDoc ((("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Command.declValSimple"
--      (/-151-/ (((nestDoc 2 (/-147-/ ((requireDoc (bridgeSpace|||bridgeImmediate)) <> ((/-143-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-146-/ (/-144-/ (("") <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       ))<^>((("") <> (provideDoc bridgeSpace)) <> (/-145-/ flattenDoc (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       )))<^>(/-150-/ ((requireDoc bridgeImmediate) <> ((/-148-/ ((":=") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>(":=")
--       )) <> (/-149-/ (provideDoc bridgeImmediate) <> (ruleDoc "Lean.Parser.Term.byTactic"
--        (ruleDoc "by tactic result"
--          (ruleDoc "immediateBy"
--            (/-142-/ ((requireDoc bridgeImmediate) <> (" ")) <> (nestDoc 2 ((/-138-/ (/-137-/ (((/-136-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             ))<^>(flattenDoc (/-141-/ (/-140-/ (((/-139-/ ((("by") <> (provideDoc bridgeHardNl)) <> ("")) <> (provideDoc bridgeHardNl)) <> (""))<^>("by")
--             ) <> (provideDoc bridgeNl)) <> (ruleDoc "Lean.Parser.Tactic.tacticSeq"
--              (ruleDoc "Lean.Parser.Tactic.tacticSeq1Indented"
--                (ruleDoc "Lean.Parser.Tactic.simpa"
--                  (/-135-/ (((/-134-/ (("simpa") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("simpa")
--                   ) <> (provideDoc bridgeSpace)) <> (nestDoc 2 (/-133-/ ruleDoc "Lean.Parser.Tactic.simpaArgsRest"
--                    (((/-116-/ ruleDoc "Lean.Parser.Tactic.simpArgs"
--                      ((/-114-/ ("[") <> (("") <> (ruleDoc "Lean.Parser.Tactic.simpLemma"
--                        ("split")
--                       ))) <> ((/-115-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                       ))
--                     ) <> (provideDoc bridgeSpace)) <> (/-132-/ (((/-117-/ (("using") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("using")
--                     ) <> (provideDoc bridgeSpace)) <> (ruleDoc "Lean.Parser.Term.app"
--                      (/-131-/ (((/-118-/ (("splitAux_of_valid") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("splitAux_of_valid")
--                       ) <> (provideDoc bridgeSpace)) <> (/-130-/ (((/-129-/ (((/-128-/ (((/-119-/ (("p") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("p")
--                       ) <> (provideDoc bridgeAny)) <> (/-121-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-120-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (/-123-/ ruleDoc "«term[_]»"
--                        (("[") <> ((/-122-/ (("]") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("]")
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "Lean.Parser.Term.proj"
--                        (/-125-/ (("s") <> (".")) <> (ruleDoc "fieldIdx"
--                          ((/-124-/ (("1") <> (provideDoc bridgeSpace)) <> ((("") <> (provideDoc bridgeHardNl)) <> ("")))<^>("1")
--                           )
--                         ))
--                       )) <> (provideDoc bridgeAny)) <> (ruleDoc "«term[_]»"
--                        (("[") <> (/-127-/ ((/-126-/ ((("]") <> (provideDoc bridgeHardNl)) <> ("-- TODO: splitOn")) <> (provideDoc bridgeHardNl)) <> (""))<^>(((costDoc 3) <> (bubbleCommentDoc "-- TODO: splitOn")) <> ("]"))
--                         ))
--                       )))
--                     )))
--                   )))
--                 )
--               )
--             )))
--             )))
--           )
--         )
--       )))
--       ) <> ("")) <> (""))
--     )))
--     ) <> (costDoc 3))
--     ))
--   ))
--   )
--   )
--   let (d, cache) := markCachedObject (do expandSyntax RuleRec.placeHolder d)
--   let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
--   -- IO.println s!"{repr d}"
--   IO.println s!"{out}"
