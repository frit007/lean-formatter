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
  let d = (((((((((((((text "") ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Module.header")) ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Command.syntaxCat")) ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Command.syntax")) ^^ (nl
)) ^^ (((text "") ^^ (text "could not find something for Lean.Parser.Command.declModifiers")) ^^ (nest 2 (((((((((((text "") ^^ ((text " ")
<|>(nl
))) ^^ ((text "") ^^ (text "def"))) ^^ ((text " ")
<|>(nl
))) ^^ ((let exit_v1 = ((text "") ^^ (text "could not find something for null")) in (let exit_v0 = ((text "") ^^ (text "formatPlusAlternative")) in (((exit_v0) ^^ (exit_v1))
<|>(((exit_v0) ^^ (nl
)) ^^ (exit_v1)))
)
) ^^ (text " "))) ^^ ((text " ")
<|>(nl
))) ^^ ((let exit_v3 = ((text "") ^^ (text "could not find something for null")) in (let exit_v2 = (text "could not find something for null") in (((exit_v2) ^^ (exit_v3))
<|>(((exit_v2) ^^ (nl
)) ^^ (exit_v3)))
)
) ^^ (text " "))) ^^ ((text " ")
<|>(nl
))) ^^ (((((((((text "") ^^ (nl
)) ^^ ((text "") ^^ (text ":="))) ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Term.app")) ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Termination.suffix")) ^^ (nl
)) ^^ (text "could not find something for null"))) ^^ ((text " ")
<|>(nl
))) ^^ (text "could not find something for null"))))) ^^ (nl
)) ^^ (((text "") ^^ (text "could not find something for Lean.Parser.Command.declModifiers")) ^^ (nest 2 (((((((((text "") ^^ ((text " ")
<|>(nl
))) ^^ ((text "") ^^ (text "def"))) ^^ ((text " ")
<|>(nl
))) ^^ ((let exit_v5 = ((text "") ^^ (text "could not find something for null")) in (let exit_v4 = ((text "") ^^ (text "b")) in (((exit_v4) ^^ (exit_v5))
<|>(((exit_v4) ^^ (nl
)) ^^ (exit_v5)))
)
) ^^ (text " "))) ^^ ((text " ")
<|>(nl
))) ^^ ((let exit_v7 = ((text "") ^^ (text "could not find something for null")) in (let exit_v6 = (text "could not find something for null") in (((exit_v6) ^^ (exit_v7))
<|>(((exit_v6) ^^ (nl
)) ^^ (exit_v7)))
)
) ^^ (text " "))) ^^ ((text " ")
<|>(nl
))) ^^ (((((text "") ^^ (nl
)) ^^ ((text "") ^^ (text ":="))) ^^ (nl
)) ^^ ((nl
) ^^ ((((text "") ^^ ((((((text "") ^^ (text "-- comment on empty line"
)) ^^ (nl
)) ^^ (text "-- new comment 2"
)) ^^ (nl
)) ^^ (text "let"))) ^^ (text "could not find something for Lean.Parser.Term.letDecl")) ^^ (text "")))))))) ^^ (nl
)) ^^ (text "could not find something for Lean.Parser.Command.eoi"))
  in
  pretty_print print_string d

let () = print_doc 80