import PFMT
import BaseFormatter

open PrettyFormat
-- this functions assumes that there are no Syntax objects in the doc
partial def markCachedObject (doc:FormatM Doc) : (Doc × FormatState) :=
  let (doc, cache) := doc.run {formattingFunction := fun _ _ _ _ =>
    (toDoc "_", 0, {})}
  (doc, cache)

-- choose space bridge
/-- info:  b -/
#guard_msgs in
#eval do
  let d := "" <_> ("" <_> "b" <^> "" <$$> "a")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) d
  IO.println s!"{out}"

-- choose newline bridge
/--
info:
a
-/
#guard_msgs in
#eval do
  let d := "" <$$> ("" <_> "b" <^> "" <$$> "a")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) d
  IO.println s!"{out}"

-- prefer newline over too long string
/--
info:
a
-/
#guard_msgs in
#eval do
  let d := "" <**> ("" <_> "bbbbbbbbbbbbbbbbbbbb" <^> "" <$$> "a")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) d
  IO.println s!"{out}"

-- Choose tainted over an impossible option
/-- info: bbbbbbbbbbbbbbbbbbbb -/
#guard_msgs in
#eval do
  let d := Doc.provide bridgeImmediate <> (bridgeImmediate <! "bbbbbbbbbbbbbbbbbbbb" <^> "" <$$> "a")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) d
  IO.println s!"{out}"

-- Choose tainted over an impossible option (reversed order)
/-- info: bbbbbbbbbbbbbbbbbbbb -/
#guard_msgs in
#eval do
  let d := Doc.provide bridgeImmediate <> ( "" <$$> "a" <^> bridgeImmediate <! "bbbbbbbbbbbbbbbbbbbb")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 20) d
  IO.println s!"{out}"


-- do we still find all options if we start in a tainted context?
/-- info: aaacorrect -/
#guard_msgs in
#eval do
  let d := "aaa" <> Doc.provide bridgeImmediate <> ( "none" <^> bridgeImmediate<!"correct" <^> (Doc.provide bridgeSpace))
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) d
  IO.println s!"{out}"

-- bridgeAny with tainted
/--
info: aaa
b
-/
#guard_msgs in
#eval do
  let d := "aaa" <> Doc.provide bridgeAny <> "b"
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) d
  IO.println s!"{out}"

/-- info: aaa none -/
#guard_msgs in
#eval do
  let d := "aaa" <> Doc.provide bridgeSpace <> ( "none" <^> bridgeImmediate<!"correct")
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) d
  IO.println s!"{out}"

/-- info: aaa space  after -/
#guard_msgs in
#eval do  
  let d := "aaa" <> ((Doc.provide bridgeHardNl <^> " space " <_> "")) <> flattenDoc ("after")
  -- IO.println s!"{d.toString}"
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1) d
  IO.println s!"{out}"

/--
info:  let ⟨ih₁, ih₂⟩ := merge' ht₁ ht₂
  exact ⟨⟨Nat.le_succ_of_le hr₁, this, ih₁.of_rankGT (ih₂ (iff_of_false hl₁ hl₂))⟩, fun _=>Nat.lt_succ_of_le hr₁⟩
-/
#guard_msgs in
#eval do
  let d := (Doc.nest 2 ((Doc.provide bridgeSpace) <> (Doc.rule "Lean.Parser.Tactic.tacticSeq"
                     (Doc.rule "Lean.Parser.Tactic.tacticSeq1Indented"
                       (((Doc.rule "Lean.Parser.Tactic.tacticLet_"
                         (((Doc.text "let") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Term.letDecl"
                           (Doc.rule "Lean.Parser.Term.letPatDecl"
                             (/-152-/ (((Doc.rule "Lean.Parser.Term.anonymousCtor"
                               ((/-150-/ (Doc.text "⟨") <> ((((Doc.text "ih₁") <> (Doc.text ",")) <> (Doc.text " ")) <> (Doc.text "ih₂"))) <> (Doc.text "⟩"))
                              ) <> (Doc.provide bridgeSpace)) <> (Doc.text ":=")) <> (Doc.nest 2 ((Doc.provide (bridgeSpaceNl|||bridgeSpace|||bridgeImmediate)) <> (Doc.rule "Lean.Parser.Term.app"
                               (/-151-/ ((Doc.text "merge'") <> (Doc.provide bridgeSpace)) <> (((Doc.text "ht₁") <> (Doc.provide bridgeSpace)) <> (Doc.text "ht₂")))
                              ))))
                            )
                          ))
                        ) <> (Doc.provide bridgeHardNl)) <> (Doc.rule "Lean.Parser.Tactic.exact"
                         (((Doc.text "exact") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Term.anonymousCtor"
                           ((/-161-/ (Doc.text "⟨") <> ((((Doc.rule "Lean.Parser.Term.anonymousCtor"
                             (/-155-/ ((Doc.text "⟨") <> (((/-153-/ ((((Doc.rule "Lean.Parser.Term.app"
                               (((Doc.text "Nat.le_succ_of_le") <> (Doc.provide bridgeSpace)) <> (Doc.text "hr₁"))
                              ) <> (Doc.text ",")) <> (Doc.text " ")) <> (Doc.text "this")) <> (Doc.text ",")) <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.app"
                               (((Doc.text "ih₁.of_rankGT") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Term.paren"
                                 (((Doc.text "(") <> (Doc.rule "Lean.Parser.Term.app"
                                   (((Doc.text "ih₂") <> (Doc.provide bridgeSpace)) <> (Doc.rule "Lean.Parser.Term.paren"
                                     (((Doc.text "(") <> (Doc.rule "Lean.Parser.Term.app"
                                       (/-154-/ ((Doc.text "iff_of_false") <> (Doc.provide bridgeSpace)) <> (((Doc.text "hl₁") <> (Doc.provide bridgeSpace)) <> (Doc.text "hl₂")))
                                      )) <> (Doc.text ")"))
                                    ))
                                  )) <> (Doc.text ")"))
                                ))
                              ))) <> (Doc.text "⟩"))
                            ) <> (Doc.text ",")) <> (Doc.text " ")) <> (Doc.rule "Lean.Parser.Term.fun"
                             (/-160-/ (((Doc.text "fun") <> (Doc.provide bridgeAny)) <> (/-157-/ Doc.rule "Lean.Parser.Term.basicFun"
                               (((Doc.rule ""
                                 (Doc.text "_")
                                ) <> (Doc.text "=>")) <> (/-156-/ Doc.rule "Lean.Parser.Term.app"
                                 (((Doc.text "Nat.lt_succ_of_le") <> (Doc.provide bridgeSpace)) <> (Doc.text "hr₁"))
                                ))
                              ))<^>(/-159-/ (((Doc.require bridgeImmediate) <> (Doc.text " ")) <> (Doc.text "fun")) <> ((Doc.provide bridgeImmediate) <> (/-158-/ Doc.rule "Lean.Parser.Term.basicFun"
                               (((Doc.rule ""
                                 (Doc.text "_")
                                ) <> (Doc.text "=>")) <> (/-156-/ Doc.rule "Lean.Parser.Term.app"
                                 (((Doc.text "Nat.lt_succ_of_le") <> (Doc.provide bridgeSpace)) <> (Doc.text "hr₁"))
                                ))
                              )))
                              )
                            ))) <> (Doc.text "⟩"))
                          ))
                        ))))))
  let (d, cache) := markCachedObject (do return d)
  let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 1000) d
  IO.println s!"{out}"

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

partial def nchoicenl : Nat → FormatM Doc
| 0 => return toDoc "!end!"
| n + 1 => do
  let next ← expandSyntax RuleRec.placeHolder (← nchoicenl n)
  return "a" <_> next <^> "b" <$$> next


-- #eval (bridgeSpaceNl ||| bridgeHardNl).toString





-- it takes a second without caching


#eval do
  let (doc, cache) := markCachedObject (nchoicenl 599)

  IO.println s!"{cache.nextId}"

  let (out, timeDoc) ← measureTime (fun _ => do
    let out ← Doc.prettyPrint DefaultCost (cacheSize := cache.nextId) (col := 0) (widthLimit := 100) doc
    return out
  )

  -- IO.println s!"Time: {timeDoc.toFloat / 1000000000.0}s \n{out} the doc\n{doc.toString}"
  IO.println s!"Time: {timeDoc.toFloat / 1000000000.0}s \n{out} the"


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
