import PFMT
import BaseFormatter

open Lean
open PrettyFormat


-- choose space bridge
/-- info: a b -/
#guard_msgs in
#eval do
  let d := "a" <_> ("" <_> "b" <^> "" <$$> "a")
  -- let d := "a" <_> "b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) (computationWidth := 20) d
  -- IO.println d.toJSON
  IO.println s!"{out}"

-- choose newline bridge
/--
info:
a
-/
#guard_msgs in
#eval do
  let d := "" <$$> ("" <_> "b" <^> "" <$$> "a")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) (computationWidth := 20) d
  IO.println s!"{out}"

-- prefer newline over too long string
/--
info:
a
-/
#guard_msgs in
#eval do
  let d := "" <**> ("" <_> "bbbbbbbbbbbbbbbbbbbb" <^> "" <$$> "a")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) (computationWidth := 20) d
  IO.println s!"{out}"

-- Choose tainted over an impossible option
/-- info: bbbbbbbbbbbbbbbbbbbb -/
#guard_msgs in
#eval do
  let d := provideDoc bridgeImmediate <> (bridgeImmediate <! "bbbbbbbbbbbbbbbbbbbb" <^> "" <$$> "a")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) (computationWidth := 20) d
  IO.println s!"{out}"

-- Choose tainted over an impossible option (reversed order)
/-- info: bbbbbbbbbbbbbbbbbbbb -/
#guard_msgs in
#eval do
  let d := provideDoc bridgeImmediate <> ( "" <$$> "a" <^> bridgeImmediate <! "bbbbbbbbbbbbbbbbbbbb")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) (computationWidth := 20) d
  IO.println s!"{out}"


-- do we still find all options if we start in a tainted context?
/-- info: aaacorrectb -/
#guard_msgs in
#eval do
  let d := "aaa" <> provideDoc bridgeImmediate <> ( "none" <^> bridgeImmediate<!"correct" <^> (provideDoc bridgeSpace)) <>"b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) (computationWidth := 1) d
  IO.println s!"{out}"

-- bridgeAny with tainted
/--
info: aaa
b
-/
#guard_msgs in
#eval do
  let d := "aaa" <> provideDoc bridgeAny <> "b"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) (computationWidth := 1) d
  IO.println s!"{out}"

/-- info: aaa none -/
#guard_msgs in
#eval do
  let d := "aaa" <> provideDoc bridgeSpace <> ( "none" <^> bridgeImmediate<!"correct")
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) (computationWidth := 1) d
  IO.println s!"{out}"

/--
info: aaa
after
-/
#guard_msgs in
#eval do
  let d := "aaa" <> ((provideDoc bridgeHardNl <^> " space " <_> "")) <> flattenDoc ("after")
  -- IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) (computationWidth := 1) d
  IO.println s!"{out}"

/-- info: longer -/
#guard_msgs in
#eval do
  let d := (costDoc 2 <> (toDoc "short")) <^> "longer"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) (computationWidth := 10) d
  IO.println s!"{out}"

/- We can add cost to -/
/--
info: longer
b
c
-/
#guard_msgs in
#eval do
  let d := (costDoc 2 <> (toDoc "short")) <^> ("longer" <$$> "b" <$$> "c")
  -- IO.println s!"{d.toString}"
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 10) (computationWidth := 10) d
  IO.println s!"{out}"

/- cost does not really matter for tainted since in a tainted state we take the first available solution-/
/-- info: short -/
#guard_msgs in
#eval do
  let d := (costDoc 2 <> "short") <^> "longer"
  -- let d := runFlatten 100 d
  let (d, cache) := simpleFormattingContext (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) (computationWidth := 1) d
  IO.println s!"{out}"

-- if run without caching this has exponential running time

partial def nchoice : Nat → FormatM Doc
| 0 => return toDoc "!end!"
| n + 1 => do
  let next ← expandSyntax RuleRec.placeHolder (← nchoice n)
  return "a" <> next <^> "b" <> next

partial def nchoicenl : Nat → FormatM Doc
| 0 => return toDoc "!end!"
| n + 1 => do
  let next ← expandSyntax RuleRec.placeHolder (← nchoicenl n)
  return "a" <_> next <^> "b" <$$> next

#eval do -- note that runtime drastically improves when compiled
  -- let (doc, cache) := simpleFormattingContext (nchoicenl 599)
  let ((doc, cache), timeCreate) ← measureTime (fun _ => do
    -- inFormatMSyntax 0 do
      return simpleFormattingContext (do
        let d ← nchoicenl (599)
        expandSyntax RuleRec.placeHolder d
      )
  )
  -- IO.println s!"{repr doc}"
  IO.println s!"Time create: {timeCreate.toFloat / 1000000000.0}s \n"

  -- IO.println s!"{cache.nextId}"

  let (out, timeDoc) ← measureTime (fun _ => do
    let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) (computationWidth := 100) doc
    return out
  )

  -- IO.println s!"Time: {timeDoc.toFloat / 1000000000.0}s \n{out} the doc\n{doc.toString}"
  IO.println s!"Time format: {timeDoc.toFloat / 1000000000.0}s \n{out}"

