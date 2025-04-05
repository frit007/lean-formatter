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

  (* let d = text "s " ^^ ((text " " <|> nl) ^^ ((text " 3") <|> (nl ^^ (text " " <|> nl) ^^ text " 3"))) *)
  (* let d = (text " " <|> nl) ^^ ((text " 3") <|> (nl ^^ ((text " " <|> nl) ^^ text " 3"))) *)
  let d = (text " " <|> nl) ^^ ((text " 3") <|> (nl ^^ (text " " <|> nl)))
  in
  pretty_print print_string d

let () = print_doc 80