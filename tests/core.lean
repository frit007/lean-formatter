import Doc
import PFMT
import PrettyFormat

open PrettyFormat

set_option pf.debugLog true

#eval
  let d := nestDoc 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tll")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out

/-- info: "def he\n  : too tl\n  more" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tl" <> (" " <^> Doc.nl) <> "more")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out


/-- info: "ab" -/
#guard_msgs in
#eval
  let d := "a" <> "b"
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

-- Basic minimal choice

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("short"<^>"longer") <> "b"
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("longer"<^>"short") <> "b"
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("short" <^> "longer")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":= short" -/
#guard_msgs in
#eval
  let d := ((":=" <$$> "") <^> (":=" <_> "")) <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out


/-- info: ":=s short" -/
#guard_msgs in
#eval
  let d := ((":=s" <_> "") <^> (":=n" <$$> "")) <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s after" -/
#guard_msgs in
#eval
  let d := (":=s" <_> "after")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s after" -/
#guard_msgs in
#eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (":=s" <**> "after")

/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := nestDoc 2 (":=s" <$$> "after")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ((":=s" <> (provideDoc' bridgeImmediate <^> provideDoc' bridgeNl)) <> "after")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=safter" -/
#guard_msgs in
#eval
  let d := nestDoc 2 ((":=s" <> (provideDoc' bridgeImmediate <^> provideDoc' bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <>"after"))
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out


/-- info: "five5\n  longer h" -/
#guard_msgs in
#eval
  let d := nestDoc 2 (("five5" <> (provideDoc' bridgeImmediate <^> provideDoc' bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <> "longer" <> (" h"<^> Doc.nl<>"h")))
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out

/--
info: (PrettyFormat.Doc.concat
  (PrettyFormat.Doc.text
    "Hello"
    { leftBridge := 1,
      id := 0,
      cacheWeight := 0,
      containsWhiteSpace := false,
      delayedProvide := none,
      shouldBeExpanded := false })
  (PrettyFormat.Doc.provide
    8
    (PrettyFormat.Doc.text
      "world"
      { leftBridge := 1,
        id := 0,
        cacheWeight := 0,
        containsWhiteSpace := false,
        delayedProvide := none,
        shouldBeExpanded := false })
    { leftBridge := 8,
      id := 0,
      cacheWeight := 0,
      containsWhiteSpace := false,
      delayedProvide := none,
      shouldBeExpanded := false })
  { leftBridge := 1,
    id := 0,
    cacheWeight := 0,
    containsWhiteSpace := false,
    delayedProvide := none,
    shouldBeExpanded := false })
---
info: "Hello world"
-/
#guard_msgs in
#eval
  let d := flattenDoc ("Hello" <**> "world")
  let d := runFlatten 3 d
  dbg_trace s!"({repr d})"
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out

/-- info: ":=2" -/
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
  let d := runFlatten 3 d
  -- dbg_trace s!"({repr d})"
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out


#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) ("a"<>(provideDoc' bridgeImmediate <^> provideDoc' bridgeNl) <>"b")

#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (flattenDoc ("a" <> Doc.nl <> "b"))

-- #eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (Doc.flatten (Doc.rule "termIfThenElse"
--                          ((Doc.flatten ((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "t.contains") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )) <> (Doc.text " ")) <> (Doc.text "then")) <> (nestDoc 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "r.insert") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )))) <> (provideDoc' 6)) <> ((Doc.text "else") <> (nestDoc 2 ((provideDoc' 6) <> (Doc.text "r"))))))<^>((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "t.contains") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )) <> (Doc.text " ")) <> (Doc.text "then")) <> (nestDoc 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "r.insert") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )))) <> (provideDoc' 6)) <> ((Doc.text "else") <> (nestDoc 2 ((provideDoc' 6) <> (Doc.text "r")))))
--   )))


-- #eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (flattenDoc ((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "t.contains") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )) <> (Doc.text " ")) <> (Doc.text "then"))))

-- #eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (flattenDoc ((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "t.contains") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )) <> (Doc.text " ")) <> (Doc.text "then")) <> (nestDoc 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
--                            (((Doc.text "r.insert") <> (provideDoc' 8)) <> (Doc.text "n"))
--                           )))) <> (provideDoc' 6)) <> ((Doc.text "else") <> (nestDoc 2 ((provideDoc' 6) <> (Doc.text "r"))))))

-- #eval
--   let d := "a" <> "b"
--   output d









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
