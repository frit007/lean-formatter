import Doc
import PFMT
import PrettyFormat

open PrettyFormat

/-- info: "ab" -/
#guard_msgs in
#eval
  let d := "a" <> "b"
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

-- Basic minimal choice

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("short"<^>"longer") <> "b"
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: "shortb" -/
#guard_msgs in
#eval
  let d := ("longer"<^>"short") <> "b"
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("short" <^> "longer")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: "ashort" -/
#guard_msgs in
#eval
  let d := "a" <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: ":= short" -/
#guard_msgs in
#eval
  let d := ((":=" <$$> "") <^> (":=" <_> "")) <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out


/-- info: ":=s short" -/
#guard_msgs in
#eval
  let d := ((":=s" <_> "") <^> (":=n" <$$> "")) <> ("longer" <^> "short")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: ":=s after" -/
#guard_msgs in
#eval
  let d := (":=s" <_> "after")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out


/-- info: ":=s\n  after" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 (":=s" <$$> "after")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out

/-- info: "\n(no possible formatter)" -/
#guard_msgs in
#eval
  let d := Doc.nest 2 ((":=s" <> (Doc.provide bridgeImmediate <^> Doc.provide bridgeNl)) <> "after")
  let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 100) d
  out


#eval
  let d := "a" <> "b"
  output d
