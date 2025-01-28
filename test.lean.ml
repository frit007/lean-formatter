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
  let d = (((((((text "") ^^ (text "")) ^^ ((((text "") ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "Lean"))) ^^ (nl
))) ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "PrettyFormat"))) ^^ (nl
))) ^^ (((((text "") ^^ (text "import")) ^^ (text " ")) ^^ ((text "") ^^ (text "Formatter"))) ^^ (nl
)))) ^^ (nl
)) ^^ (((text "") ^^ (((text "") ^^ ((text "") ^^ ((((text "") ^^ (text "-- -- Hello before definition"
)) ^^ (nl
)) ^^ (text "private")))) ^^ (text " "))) ^^ (nest 2 ((((((((text "") ^^ (text "def")) ^^ ((text "")
<|>(nl
))) ^^ (((text " ") ^^ (let exit_v1 = ((text "") ^^ (text "")) in (let exit_v0 = ((text "") ^^ (text "b")) in (((exit_v0) ^^ (exit_v1))
<|>(((exit_v0) ^^ (nl
)) ^^ (exit_v1)))
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
)) ^^ ((text "") ^^ (text "tmp2"))))))))) ^^ (nl
)) ^^ (((text "") ^^ (((text "") ^^ ((text "") ^^ ((((((text "") ^^ (text "-- tmp / 2 --and content"
)) ^^ (nl
)) ^^ (text "-- let x := y"
)) ^^ (nl
)) ^^ (text "private")))) ^^ (text " "))) ^^ (nest 2 ((((((((text "") ^^ (text "def")) ^^ ((text "")
<|>(nl
))) ^^ (((text " ") ^^ (let exit_v3 = ((text "") ^^ (text "")) in (let exit_v2 = ((text "") ^^ (text "c")) in (((exit_v2) ^^ (exit_v3))
<|>(((exit_v2) ^^ (nl
)) ^^ (exit_v3)))
)
)) ^^ (text " "))) ^^ ((text "")
<|>(nl
))) ^^ ((((((((((((((((((((((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "y"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")"))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a1"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a2"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a3"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a4"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a5"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a6"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a7"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a8"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ ((((text "") ^^ (text "(")) ^^ ((((text "") ^^ ((text "") ^^ (text "a9"))) ^^ (text " ")) ^^ (((text "") ^^ ((text "") ^^ (text ":"))) ^^ ((text "") ^^ (text "Nat"))))) ^^ ((text "") ^^ (text ")")))) ^^ ((text " ")
<|>(nl
))) ^^ (((text "") ^^ ((((text "") ^^ (text ":")) ^^ (text " ")) ^^ ((text "") ^^ (text "Nat")))) ^^ (text " ")))) ^^ ((text "")
<|>(nl
))) ^^ ((((text "") ^^ (text ":=")) ^^ (nl
)) ^^ (((((((((text "") ^^ (text "-- comment on empty line"
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