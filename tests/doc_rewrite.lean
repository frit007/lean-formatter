-- import Doc

-- namespace PrettyFormat

-- #eval ("what"<>("hello" <^> PrettyFormat.costDoc 2 "") <> ("" <^> "world")).toString
-- #eval (("a"<^>"b")<>("c"<^>"d")).toString
-- #eval ((bridgeAny <! "") <> costDoc 3 "").toString
-- /-- info: "provideDoc bridgeSpace (\"hello\")" -/
-- #guard_msgs in
-- #eval ((provideDoc bridgeSpace "") <> "hello").toString

-- /-- info: "(provideDoc bridgeNl (\"hello\"))<^>(provideDoc bridgeSpace (\"hello\"))\n" -/
-- #guard_msgs in
-- #eval (((provideDoc bridgeSpace "") <^> (provideDoc bridgeNl "")) <> "hello").toString
-- /-- info: "(provideDoc bridgeSpace (\"hello\"))<^>(provideDoc bridgeNl (\"hello\"))\n" -/
-- #guard_msgs in
-- #eval (((""<$$>"") <^> (""<_>"")) <> "hello").toString
-- /-- info: "(\"Hello\") <> (provideDoc bridgeSpace (\"world\"))" -/
-- #guard_msgs in
-- #eval ((("Hello"<_>"")) <> "world").toString


-- /--
-- info: "((\"Hello\") <> (provideDoc bridgeNl (\"world\")))<^>((\"Hello\") <> (provideDoc bridgeSpace (\"world\")))\n"
-- -/
-- #guard_msgs in
-- #eval (("Hello"<>(""<$$>""<^>""<_>"")) <> "world").toString

-- /--
-- info: "((ruleDoc \"r\" \n (\"def \") \n) <> (provideDoc bridgeNl ((provideDoc bridgeSpace (\"2\"))<^>(provideDoc bridgeNl (\"2\"))\n)))<^>((ruleDoc \"r\" \n (\"def \") \n) <> (provideDoc bridgeSpace ((provideDoc bridgeSpace (\"2\"))<^>(provideDoc bridgeNl (\"2\"))\n)))\n"
-- -/
-- #guard_msgs in
-- #eval (("def " <> (ruleDoc "r" (""<$$>""<^>""<_>""))) <> (bridgeSpace !> "2" <^> bridgeNl !> "2")).toString

-- /--
-- info: "((costDoc 2 (\"def \")) <> (provideDoc bridgeNl ((provideDoc bridgeSpace (\"2\"))<^>(provideDoc bridgeNl (\"2\"))\n)))<^>((costDoc 2 (\"def \")) <> (provideDoc bridgeSpace ((provideDoc bridgeSpace (\"2\"))<^>(provideDoc bridgeNl (\"2\"))\n)))\n"
-- -/
-- #guard_msgs in
-- #eval (("def " <> (costDoc 2 (""<$$>""<^>""<_>""))) <> (bridgeSpace !> "2" <^> bridgeNl !> "2")).toString

-- #eval "def" <>costDoc 2 ((provideDoc' bridgeSpace) <^> (provideDoc' bridgeNl))

-- def declValTest (val:Doc) :=
--   nestDoc 2 (":=" <> (""<_> val <^> ""<$$>val))


-- #eval (declValTest ("" <_> "help")).toString

-- /-- info: "(costDoc 2 (\"def\"))<^>(costDoc 2 (\"def\"))\n" -/
-- #guard_msgs in
-- #eval ("def" <> costDoc 2 (""<$$>""<^>""<_>"")).toString

-- #eval ((provideDoc bridgeSpace) <> "hello").toString
-- #eval (provideDoc bridgeSpace)
-- /-- info: "provideDoc bridgeNl (provideDoc bridgeSpace (\"hey\"))" -/
-- #guard_msgs in
-- #eval (provideDoc bridgeSpace <> provideDoc bridgeNl <> "hey").toString
-- #eval (nestDoc 2 (toDoc "") <> (Doc.align (toDoc "") {})  <> costDoc 2 <> "hey" <> costDoc 3).toString


-- #guard_msgs in
-- #eval ("aaa" <> provideDoc' bridgeImmediate <> ( "none" <^> bridgeImmediate<!"correct" <^> ("r")))



-- #eval (("hello" <^> PrettyFormat.costDoc 2) <> ("" <^> "world")).toString
-- #eval ((PrettyFormat.costDoc 2) <> "final").toString
-- #eval ("final" <> PrettyFormat.costDoc 2 ).toString
-- end PrettyFormat
