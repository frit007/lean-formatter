import Doc
import PFMT
import PrettyFormat

open PrettyFormat

set_option pf.debugLog true

#eval
  let d := Doc.nest 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tll")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out

/-- info: "def he\n  : too tl\n  more" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 ("def he" <> (" : " <^> Doc.nl <> ": " ) <> "too tl" <> (" " <^> Doc.nl) <> "more")
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
  let d := Doc.nest 2 (":=s" <$$> "after")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 ((":=s" <> (Doc.provide bridgeImmediate <^> Doc.provide bridgeNl)) <> "after")
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out

/-- info: ":=safter" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 ((":=s" <> (Doc.provide bridgeImmediate <^> Doc.provide bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <>"after"))
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) d
  out


/-- info: "five5\n  longer h" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 (("five5" <> (Doc.provide bridgeImmediate <^> Doc.provide bridgeNl)) <> ((Doc.require bridgeImmediate <^> Doc.require bridgeNl) <> "longer" <> (" h"<^> Doc.nl<>"h")))
  let out := Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 10) d
  out





#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) ("a"<>(Doc.provide bridgeImmediate <^> Doc.provide bridgeNl) <>"b")

#eval Doc.prettyPrintLog DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (PPL.flatten ("a" <> Doc.nl <> "b"))

#eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (Doc.flatten (Doc.rule "termIfThenElse"
                         ((Doc.flatten ((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "t.contains") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )) <> (Doc.text " ")) <> (Doc.text "then")) <> (Doc.nest 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "r.insert") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )))) <> (Doc.provide 6)) <> ((Doc.text "else") <> (Doc.nest 2 ((Doc.provide 6) <> (Doc.text "r"))))))<^>((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "t.contains") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )) <> (Doc.text " ")) <> (Doc.text "then")) <> (Doc.nest 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "r.insert") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )))) <> (Doc.provide 6)) <> ((Doc.text "else") <> (Doc.nest 2 ((Doc.provide 6) <> (Doc.text "r")))))
  )))


#eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (PPL.flatten ((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "t.contains") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )) <> (Doc.text " ")) <> (Doc.text "then"))))

#eval Doc.prettyPrint DefaultCost (cacheSize := 0) (col := 0) (widthLimit := 100) (PPL.flatten ((((((((Doc.text "if") <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "t.contains") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )) <> (Doc.text " ")) <> (Doc.text "then")) <> (Doc.nest 2 ((Doc.newline none) <> (Doc.rule "Lean.Parser.Term.app"
                           (((Doc.text "r.insert") <> (Doc.provide 8)) <> (Doc.text "n"))
                          )))) <> (Doc.provide 6)) <> ((Doc.text "else") <> (Doc.nest 2 ((Doc.provide 6) <> (Doc.text "r"))))))

-- #eval
--   let d := "a" <> "b"
--   output d
