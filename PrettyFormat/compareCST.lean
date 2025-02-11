import annotations
-- TODO: Support automaticalopen Lean Elab PrettyPrinter PrettyFormat
-- TODO: add debug information about where the difference in the CST is


open Lean Elab PrettyPrinter PrettyFormat

open Lean.Meta
open Lean.Elab

mutual
  partial def compareCst (left right: Syntax) : Bool:=
    match (left, right) with
    | (Syntax.missing, Syntax.missing) => true
    | (Syntax.node _ lkind largs, Syntax.node _ rkind rargs) => lkind == rkind && (compareCstArr largs rargs)
    | (Syntax.atom _ (lval : String), Syntax.atom _ (rval : String)) => lval == rval
    | (Syntax.ident  _ (lrawVal : Substring) (lval : Name) _, Syntax.ident  _ (rrawVal : Substring) (rval : Name) _) =>
      lrawVal == rrawVal
    | _ => false

  partial def compareCstArr (left right : Array Syntax) : Bool :=
    left.size == right.size
    && ((left.zip right) |>.foldl (fun acc x => acc && compareCst x.fst x.snd) true)
    
end
