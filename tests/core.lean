import Doc
import PFMT
import PrettyFormat
import BaseFormatter

open PrettyFormat


/-- info: "def he : too tll" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tll")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out

/-- info: "def he : too tl\n  more" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tl" <> (" " <^> Doc.nl) <> "more")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out


/-- info: "ab" -/
#guard_msgs in
#eval
  let d := "a" <> "b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

-- Basic minimal choice

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("short"<^>"longer") <> "b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("longer"<^>"short") <> "b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("short" <^> "longer")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("longer" <^> "short")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":= short" -/
#guard_msgs in
#eval
  let d := ((":=" <$$> "") <^> (":=" <_> "")) <> ("longer" <^> "short")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out


/-- info: ":=s short" -/
#guard_msgs in
#eval
  let d := ((":=s" <_> "") <^> (":=n" <$$> "")) <> ("longer" <^> "short")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s after" -/
#guard_msgs in
#eval
  let d := (":=s" <_> "after")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s after" -/
#guard_msgs in
#eval
  let d := ":=s" <**> "after"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := nestDoc 2 (":=s" <$$> "after")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ((":=s" <> (provideDoc bridgeImmediate <^> provideDoc bridgeNl)) <> "after")
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=safter" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ((":=s" <> (provideDoc bridgeImmediate <^> provideDoc bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <>"after"))
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) d
  out


/-- info: "five5longer\n  h" -/
#guard_msgs in
#eval
  let d := nestDoc 2 (("five5" <> (provideDoc bridgeImmediate <^> provideDoc bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <> "longer" <> (" h"<^> Doc.nl<>"h")))
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out

/-- info: "Hello world" -/
#guard_msgs in
#eval
  let d := flattenDoc ("Hello" <**> "world")
  -- dbg_trace s!"({repr d})"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out

/-- info: "Hello:=\n     world" -/
#guard_msgs in
#eval
  let d := ("Hello" <+> (":="<$$>"world"))
  -- dbg_trace s!"({repr d})"
  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out

/--
---
info: ":=2"
-/
#guard_msgs in
#eval
  let d := (ruleDoc "Lean.Parser.Command.declValSimple"
     (((nestDoc 2 (((":=")<^>(":=")
      ) <> (ruleDoc "num"
       ("2")
      )))<^>(nestDoc 2 (((":=")<^>(":=")
      ) <> (ruleDoc "num"
       ("2")
      )))
      )<^>(((nestDoc 2 (((":=")<^>(":=")
      ) <> (flattenDoc (ruleDoc "num"
       ("2")
      ))))<^>(nestDoc 2 (((":=")<^>(":=")
      ) <> (flattenDoc (ruleDoc "num"
       ("2")
      ))))
      )<^>((((requireDoc bridgeSpace) <> ((":=")<^>(":=")
      )) <> (ruleDoc "num"
       ("2")
      ))<^>(((requireDoc bridgeSpace) <> ((":=")<^>(":=")
      )) <> (ruleDoc "num"
       ("2")
      ))
      )
      )
      )
    )

  let (d, cache) := simpleFormattingContext (do return d)
  let out := Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) d
  out


#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) ("a"<>(provideDoc bridgeImmediate <^> provideDoc bridgeNl) <>"b")

#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (flattenDoc ("a" <> Doc.nl <> "b"))


/-- info: "bridgeHardNl" -/
#guard_msgs in
#eval bridgeFlex.provideIntersection (bridgeHardNl)|>.str

/-- info: "bridgeHardNl" -/
#guard_msgs in
#eval bridgeAny.provideIntersection (bridgeHardNl)|>.str
/-- info: "bridgeSpace" -/
#guard_msgs in
#eval bridgeAny.provideIntersection (bridgeSpace)|>.str

/-- info: "bridgeNull" -/
#guard_msgs in
#eval bridgeSpace.provideIntersection (bridgeHardNl)|>.str

/-- info: "bridgeNl" -/
#guard_msgs in
#eval bridgeAny.provideIntersection (bridgeNl)|>.str

/-- info: "bridgeNull" -/
#guard_msgs in
#eval bridgeNl.provideIntersection (bridgeSpace)|>.str


/-- info: true -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeHardNl)
/-- info: true -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeSpace)
/-- info: true -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeFlex)
/-- info: true -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeFlex)
/-- info: false -/
#guard_msgs in
#eval bridgeImmediate.canHandle (bridgeFlex)
/-- info: true -/
#guard_msgs in
#eval (bridgeImmediate|||bridgeSpace).canHandle (bridgeFlex)
/-- info: false -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeImmediate)
/-- info: false -/
#guard_msgs in
#eval bridgeFlex.canHandle (bridgeImmediate|||bridgeSpace)
/-- info: false -/
#guard_msgs in
#eval bridgeSpace.canHandle (bridgeAny)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeAny)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeSpace)
/-- info: false -/
#guard_msgs in
#eval bridgeNull.canHandle (bridgeNl)

/-- info: false -/
#guard_msgs in
#eval bridgeNull.subsetOf bridgeSpace


/-- info: "bridgeSpace" -/
#guard_msgs in
#eval bridgeAny.flatten.str

/-- info: "bridgeFlex" -/
#guard_msgs in
#eval bridgeFlex.flatten.str

/-- info: "bridgeImmediate" -/
#guard_msgs in
#eval bridgeImmediate.flatten.str

/-- info: "bridgeNull" -/
#guard_msgs in
#eval bridgeHardNl.flatten.str

/-- info: "bridgeSpace" -/
#guard_msgs in
#eval (bridgeSpaceNl.flatten).str
