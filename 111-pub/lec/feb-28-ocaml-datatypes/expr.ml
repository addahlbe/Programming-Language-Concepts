






type expr = 
    Plus of expr * expr
  | Times of expr * expr
  | Num of string
  | Parens of expr;;

let rec eval (e : expr) : int = 
  match e with
      Plus(e1,e2) -> (eval e1) + (eval e2) 
    | Times(e1,e2) -> (eval e1) * (eval e2) 
    | Num(s) -> int_of_string s
    | Parens(e) -> eval e
;;

  










let rec print_expr (e:expr) : unit = raise (Failure("Not implemented."));;

