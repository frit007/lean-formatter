open Pretty_expressive

(** Prints the example document [d] with the page width limit [w] *)
let print_doc (w : int) =
  let cf = Printer.default_cost_factory ~page_width:w () in
  let module P = Printer.Make (val cf) in
  let open P in

  (* let d = text "while (true) {" ^^
          nest 4
            (nl ^^ text "f();" ^^ nl ^^ text "if (done())" ^^
             (let exit_d = text "exit();" in
              (space ^^ exit_d) <|> nest 4 (nl ^^ exit_d))) ^^
          nl ^^ text "}" *)
  let d = (((((((((((((((((((((((((text "") ^^ (text "")) ^^ ((((text "") ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "Lean"))) ^^ (nl
))) ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "PrettyFormat"))) ^^ (nl
))) ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "Formatter"))) ^^ (nl
)))) ^^ (nl
)) ^^ (((text "") ^^ ((text "") ^^ (text " "))) ^^ ((((((((text "") ^^ ((text "") ^^ (text "inductive"))) ^^ (((text " ") ^^ (let exit_v1 = ((text "") ^^ (text "")) in (let exit_v0 = ((text "") ^^ (text "Arith")) in (((exit_v0) ^^ (exit_v1))
<|>(((exit_v0) ^^ (nl
)) ^^ (exit_v1)))
)
)) ^^ (text " "))) ^^ (((text "") ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text "Type"))) ^^ (text "")))) ^^ (text " ")))) ^^ ((text "") ^^ ((text "") ^^ (text "where")))) ^^ (((((text "") ^^ ((((((text "") ^^ (text "")) ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ (text " "))) ^^ ((text "") ^^ (text "add"))) ^^ (((text "") ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((((text "") ^^ ((text "") ^^ (text "Arith"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ ((text "") ^^ (text "Arith"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ (text "Arith")) ^^ (text "-- e + f"
)) ^^ (nl
)))))) ^^ (text " "))))) ^^ ((((((text "") ^^ (text "")) ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ (text " "))) ^^ ((text "") ^^ (text "mul"))) ^^ (((text "") ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((((text "") ^^ ((text "") ^^ (text "Arith"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ ((text "") ^^ (text "Arith"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ (text "Arith")) ^^ (text "-- e * f"
)) ^^ (nl
)))))) ^^ (text " "))))) ^^ ((((((text "") ^^ (text "")) ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ (text " "))) ^^ ((text "") ^^ (text "nat"))) ^^ (((text "") ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((((text "") ^^ ((text "") ^^ (text "Nat"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ (text "Arith")) ^^ (text "-- constant"
)) ^^ (nl
))))) ^^ (text " "))))) ^^ ((((((text "") ^^ (text "")) ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ (text " "))) ^^ ((text "") ^^ (text "var"))) ^^ (((text "") ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((((text "") ^^ ((text "") ^^ (text "String"))) ^^ ((text "") ^^ (text "→"))) ^^ ((((text "") ^^ (text "Arith")) ^^ (text "-- variable"
)) ^^ (nl
))))) ^^ (text " ")))))) ^^ (text "")) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text "deriving"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text "Repr"))) ^^ (text "")))))))) ^^ (nl
)) ^^ (((((text "") ^^ (text "")) ^^ ((text "") ^^ (text "declare_syntax_cat"))) ^^ ((text "") ^^ (text "arith"))) ^^ (text ""))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ (text "")) ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text "num"))) ^^ (text "")))) ^^ ((text "") ^^ (text ":"))) ^^ ((((text "") ^^ (text "arith")) ^^ (text "-- nat for Arith.nat"
)) ^^ (nl
)))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ (text "")) ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text "str"))) ^^ (text "")))) ^^ ((text "") ^^ (text ":"))) ^^ ((((text "") ^^ (text "arith")) ^^ (text "-- strings for Arith.var"
)) ^^ (nl
)))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "50")))))) ^^ (text "")) ^^ (text "")) ^^ ((((text "") ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "50"))))))) ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" + \""))))) ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "51")))))))) ^^ ((text "") ^^ (text ":"))) ^^ ((((text "") ^^ (text "arith")) ^^ (text "-- Arith.add"
)) ^^ (nl
)))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "60")))))) ^^ (text "")) ^^ (text "")) ^^ ((((text "") ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "60"))))))) ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" * \""))))) ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ ((text "") ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ ((text "") ^^ (text "61")))))))) ^^ ((text "") ^^ (text ":"))) ^^ ((((text "") ^^ (text "arith")) ^^ (text "-- Arith.mul"
)) ^^ (nl
)))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ (text "")) ^^ (text "")) ^^ (text "")) ^^ ((((text "") ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" ( \""))))) ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ (text ""))) ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" ) \"")))))) ^^ ((text "") ^^ (text ":"))) ^^ ((((text "") ^^ (text "arith")) ^^ (text "-- bracketed expressions"
)) ^^ (nl
)))) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "syntax"))) ^^ (text "")) ^^ (text "")) ^^ (text "")) ^^ ((((text "") ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" ⟪ \""))))) ^^ (((text "") ^^ ((text "") ^^ (text "arith"))) ^^ (text ""))) ^^ ((text "") ^^ ((text "") ^^ ((text "") ^^ (text "\" ⟫ \"")))))) ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "term")))) ^^ (nl
)) ^^ (((((((text "") ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ""))) ^^ ((text "") ^^ (text "macro_rules"))) ^^ (text "")) ^^ ((text "") ^^ ((((((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ ((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "s"))) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "str")))))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))) ^^ ((text "") ^^ (text "=>"))) ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ (((text "") ^^ ((text "") ^^ (text "Arith.var"))) ^^ ((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "s"))) ^^ (text ""))))) ^^ ((text "") ^^ (text ")"))))) ^^ (((((text "") ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ ((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "num"))) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "num")))))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))) ^^ ((text "") ^^ (text "=>"))) ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ (((text "") ^^ ((text "") ^^ (text "Arith.nat"))) ^^ ((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "num"))) ^^ (text ""))))) ^^ ((text "") ^^ (text ")"))))) ^^ (((((text "") ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ ((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((text " -- TODO: improve custom formatter for arith_+_ 22") ^^ (nl
))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))) ^^ ((text "") ^^ (text "=>"))) ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ (((text "") ^^ ((text "") ^^ (text "Arith.add"))) ^^ (((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "x"))) ^^ (text ""))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "y"))) ^^ (text ""))) ^^ ((text "") ^^ (text "⟫")))))) ^^ ((text "") ^^ (text ")"))))) ^^ (((((text "") ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ ((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((((text "") ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "x"))) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "arith"))))) ^^ ((text "") ^^ (text "*"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "y"))) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "arith")))))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))) ^^ ((text "") ^^ (text "=>"))) ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ (((text "") ^^ ((text "") ^^ (text "Arith.mul"))) ^^ (((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "x"))) ^^ (text ""))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "y"))) ^^ (text ""))) ^^ ((text "") ^^ (text "⟫")))))) ^^ ((text "") ^^ (text ")"))))) ^^ (((((text "") ^^ ((text "") ^^ (text "|"))) ^^ ((text "") ^^ ((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((((text "") ^^ ((text "") ^^ (text "("))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "x"))) ^^ (text ""))) ^^ ((text "") ^^ (text ")")))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))) ^^ ((text "") ^^ (text "=>"))) ^^ ((((text "") ^^ ((text "") ^^ (text "`("))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ (((((text "") ^^ ((text "") ^^ (text "$"))) ^^ (text "")) ^^ ((text "") ^^ (text "x"))) ^^ (text ""))) ^^ ((text "") ^^ (text "⟫")))) ^^ ((text "") ^^ (text ")")))))))) ^^ (nl
)) ^^ (((text "") ^^ ((text "") ^^ (text "#eval"))) ^^ ((((text "") ^^ ((text "") ^^ (text "⟪"))) ^^ ((text " -- TODO: improve custom formatter for arith_+_ 22") ^^ (nl
))) ^^ ((text "") ^^ (text "⟫"))))) ^^ (nl
)) ^^ (((text "") ^^ (((text "") ^^ ((text "") ^^ ((((text "") ^^ (text "-- -- Hello before definition"
)) ^^ (nl
)) ^^ (text "private")))) ^^ (text " "))) ^^ (nest 2 ((((((((text "") ^^ (text "def")) ^^ ((text "")
<|>(nl
))) ^^ (((text " ") ^^ (let exit_v3 = ((text "") ^^ (text "")) in (let exit_v2 = ((text "") ^^ (text "b")) in (((exit_v2) ^^ (exit_v3))
<|>(((exit_v2) ^^ (nl
)) ^^ (exit_v3)))
)
)) ^^ (text " "))) ^^ ((text "")
<|>(nl
))) ^^ ((((((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "y"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")"))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a1"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((text "") ^^ (text "Nat")))) ^^ (text " ")))) ^^ ((text "")
<|>(nl
))) ^^ ((((text "") ^^ (text ":=")) ^^ (nl
)) ^^ (((((((((((text "") ^^ (text "-- comment on empty line"
)) ^^ (nl
)) ^^ (text "-- new comment 2"
)) ^^ (nl
)) ^^ (text "let")) ^^ (text " ")) ^^ ((text "") ^^ (((((((text "") ^^ (text "tmp")) ^^ (text " ")) ^^ (text "")) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((text "") ^^ (text "Nat")))) ^^ (text " "))) ^^ ((text "") ^^ (text ":="))) ^^ (nest 2 (((text " ")
<|>(nl
)) ^^ ((((text "") ^^ ((((text "") ^^ ((((text "") ^^ ((((text "") ^^ ((text "") ^^ (text "y"))) ^^ ((text "") ^^ (text "/"))) ^^ ((text "") ^^ ((text "") ^^ (text "2"))))) ^^ ((text "") ^^ (text "/"))) ^^ ((text "") ^^ ((text "") ^^ (text "3"))))) ^^ ((text "") ^^ (text "+"))) ^^ ((((text "") ^^ ((text "") ^^ ((text "") ^^ (text "2")))) ^^ ((text "") ^^ (text "*"))) ^^ ((text "") ^^ ((text "") ^^ (text "3")))))) ^^ ((text "") ^^ (text "-"))) ^^ ((text "") ^^ ((text "") ^^ (text "2"))))))))) ^^ (text "")) ^^ (nl
)) ^^ (((((((text "") ^^ (text "let")) ^^ (text " ")) ^^ ((text "") ^^ (((((((text "") ^^ (text "tmp2")) ^^ (text " ")) ^^ (text "")) ^^ (text "")) ^^ ((text "") ^^ (text ":="))) ^^ (nest 2 (((text " ")
<|>(nl
)) ^^ ((((text "") ^^ ((text "") ^^ (text "tmp"))) ^^ ((text "") ^^ (text "*"))) ^^ ((text "") ^^ ((text "") ^^ (text "5"))))))))) ^^ (text "")) ^^ (nl
)) ^^ ((text "") ^^ (text "tmp2")))))))))
  in
  pretty_print print_string d

let () = print_doc 80