import PFMT
import BaseFormatter

open PrettyFormat

-- #eval
--   let d := Doc.concat (Doc.provide bridgeSpace) (Doc.choice (Doc.concat (Doc.provide bridgeSpace)  (Doc.text "b")) (Doc.concat (Doc.provide bridgeSpaceNl) (Doc.text "a")))
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := Doc.concat (Doc.provide bridgeSpaceNl) (Doc.choice (Doc.concat (Doc.provide bridgeSpace)  (Doc.text "b")) (Doc.concat (Doc.provide bridgeSpaceNl) (Doc.text "a")))
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := Doc.concat (Doc.provide bridgeAny) (Doc.choice (Doc.concat (Doc.provide bridgeSpace)  (Doc.text "bbbbbbbbbbbbbbbbbbbb")) (Doc.concat (Doc.provide bridgeSpaceNl) (Doc.text "a")))
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := Doc.concat (Doc.provide bridgeImmediate) (Doc.choice (Doc.concat (Doc.require bridgeImmediate)  (Doc.text "bbbbbbbbbbbbbbbbbbbb")) (Doc.concat (Doc.provide bridgeSpaceNl) (Doc.text "a")))
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := (Doc.provide bridgeImmediate) <> (((Doc.require bridgeImmediate) <> (Doc.text "bbbbbbbbbbbbbbbbbbbbbb")) <^> ((Doc.provide bridgeSpaceNl) <> (Doc.text "a")))
--   let out := Doc.prettyPrint DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := (Doc.provide bridgeImmediate) <> ((Doc.provide bridgeSpaceNl) <> (Doc.text "a") <^> ((Doc.require bridgeImmediate) <> (Doc.text "bbbbbbbbbbbbbbbbbbaabbb")))
--   let out := Doc.prettyPrintLog DefaultCost (col := 0) (widthLimit := 20) d
--   out

-- #eval
--   let d := "aaa" <> Doc.rule "a" (toDoc "bbb") <> "ccc"
--   let out := Doc.prettyPrintLog DefaultCost (col := 0) (widthLimit := 1) d
--   out

-- #eval
--   let d := "#format" <> (bridgeSpace <> "rest")
--   let out := Doc.prettyPrintLog DefaultCost (col := 0) (widthLimit := 1) d
--   out

-- if run without caching this has exponential running time

partial def nchoice : Nat → FormatM Doc
| 0 => return toDoc "!end!"
| n + 1 => do
  let next ← expandSyntax RuleRec.placeHolder (← nchoice n)
  return "a" <> next <^> "b" <> next

-- this functions assumes that there are no Syntax objects in the doc
partial def markCachedObject (doc:FormatM Doc) : (Doc × FormatState) :=
  let (doc, cache) := doc.run {formattingFunction := fun _ _ _ _ =>
    (toDoc "_", 0, {})}
  (doc, cache)

-- #eval (bridgeSpaceNl ||| bridgeHardNl).toString



-- it takes a second without caching
#eval do
  let (doc, cache) := markCachedObject (nchoice 13)

  IO.println s!"{cache.nextId}"

  let (out, timeDoc) ← measureTime (fun _ => do
    let out ← Doc.prettyPrintLog DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) doc
    return out
  )

  IO.println s!"Time: {timeDoc.toFloat / 1000000000.0}s \n{out} the doc\n{doc.toString}"


-- #eval
--   let d := Doc.rule "formatCmd" ((Doc.text "#format") <> (Doc.rule "Lean.Parser.Command.declaration"
--    (Doc.rule "Lean.Parser.Command.inductive"
--      ((((((Doc.text "inductive") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Command.declId"
--        ((Doc.text "AliasInfo") <> (Doc.provide bridgeAny))
--       )) <> (Doc.provide bridgeSpace)) <> (Doc.text "where")) <> (Doc.nest 2 ((Doc.provide bridgeNl) <> ((((((Doc.rule "Lean.Parser.Command.ctor"
--        ((((Doc.rule "Lean.Parser.Command.docComment"
--          (((Doc.flatten (((Doc.text "/--") <> (Doc.provide bridgeSpace)) <> (((Doc.newline (some " ")) <> (Doc.text "Plain alias")) <> (Doc.text " -/"))))<^>((((Doc.text "/--") <> ((Doc.newline (some " ")) <> (Doc.text "Plain alias"))) <> (Doc.newline (some " "))) <> (Doc.text "-/"))
--           ) <> (Doc.provide bridgeHardNl))
--         ) <> (Doc.text "|")) <> (Doc.text " ")) <> (((Doc.text "plain") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Command.optDeclSig"
--          (Doc.rule "Lean.Parser.Term.explicitBinder"
--            (Doc.flatten (((Doc.text "(") <> (((Doc.text "n") <> (Doc.provide bridgeSpace)) <> (((Doc.text ":") <> (Doc.provide bridgeSpace)) <> (Doc.text "Name")))) <> (Doc.text ")")))
--           )
--         )))
--       ) <> (Doc.provide bridgeNl)) <> (Doc.rule "Lean.Parser.Command.ctor"
--        ((((Doc.rule "Lean.Parser.Command.docComment"
--          (((Doc.flatten (((Doc.text "/--") <> (Doc.provide bridgeSpace)) <> (((Doc.newline (some " ")) <> (Doc.text "Forward direction of an iff alias")) <> (Doc.text " -/"))))<^>((((Doc.text "/--") <> ((Doc.newline (some " ")) <> (Doc.text "Forward direction of an iff alias"))) <> (Doc.newline (some " "))) <> (Doc.text "-/"))
--           ) <> (Doc.provide bridgeHardNl))
--         ) <> (Doc.text "|")) <> (Doc.text " ")) <> (((Doc.text "forward") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Command.optDeclSig"
--          (Doc.rule "Lean.Parser.Term.explicitBinder"
--            (Doc.flatten (((Doc.text "(") <> (((Doc.text "n") <> (Doc.provide bridgeSpace)) <> (((Doc.text ":") <> (Doc.provide bridgeSpace)) <> (Doc.text "Name")))) <> (Doc.text ")")))
--           )
--         )))
--       )) <> (Doc.provide bridgeNl)) <> (Doc.rule "Lean.Parser.Command.ctor"
--        ((((Doc.rule "Lean.Parser.Command.docComment"
--          (((Doc.flatten (((Doc.text "/--") <> (Doc.provide bridgeSpace)) <> (((Doc.newline (some " ")) <> (Doc.text "Reverse direction of an iff alias")) <> (Doc.text " -/"))))<^>((((Doc.text "/--") <> ((Doc.newline (some " ")) <> (Doc.text "Reverse direction of an iff alias"))) <> (Doc.newline (some " "))) <> (Doc.text "-/"))
--           ) <> (Doc.provide bridgeHardNl))
--         ) <> (Doc.text "|")) <> (Doc.text " ")) <> (((Doc.text "reverse") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Command.optDeclSig"
--          (Doc.rule "Lean.Parser.Term.explicitBinder"
--            (Doc.flatten (((Doc.text "(") <> (((Doc.text "n") <> (Doc.provide bridgeSpace)) <> (((Doc.text ":") <> (Doc.provide bridgeSpace)) <> (Doc.text "Name")))) <> (Doc.text ")")))
--           )
--         )))
--       )) <> ((Doc.provide bridgeNl) <> (Doc.rule "Lean.Parser.Command.optDeriving"
--        (((Doc.text "deriving") <> (Doc.provide bridgeAny)) <> (Doc.text "Inhabited"))
--       ))))))
--     )
--   ))
--   let out := Doc.prettyPrintLog DefaultCost (col := 0) (widthLimit := 1) d
--   out
