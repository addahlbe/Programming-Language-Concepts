(* auto-generated by gt *)

open Gra2srs_util;;

(* This type is used for terminals.
We do this to have better position data.*)
type __terminal__ = (pd * string);;
type __term_not_in_ast__ = pd;;
type dummy = Dummy 
and args = | Empty of pd | Args of pd * term * args_args_comma0
and atom = | Id of pd * prim * post | Charset of pd * charset_atom_tilde1 * __term_not_in_ast__ * charset_atom_charset_prim2 * __term_not_in_ast__ * post | Paren of pd * __term_not_in_ast__ * form * __term_not_in_ast__ * post
and charset_prim = | Range of pd * __terminal__ * __term_not_in_ast__ * __terminal__ | Char of pd * __terminal__
and form = | Bar of pd * forma * __term_not_in_ast__ * form | Forma of pd * forma
and forma = | Seq of pd * seq_forma_atom3
and grammar = | Grammar of pd * __terminal__ * __term_not_in_ast__ * __terminal__ * grammar_grammar_whitespace4 * grammar_grammar_syntactic5 * grammar_grammar_lexical7 * grammar_grammar_vars9 * grammar_grammar_rules11
and lex = | Lex of pd * __terminal__ * lex_op * lex_lex_form13 * __term_not_in_ast__
and lex_op = | LexArrow of pd * __term_not_in_ast__ | LexThickArrow of pd * __term_not_in_ast__
and post = | Star of pd * __term_not_in_ast__ | Plus of pd * __term_not_in_ast__ | Qmark of pd * __term_not_in_ast__ | Plain of pd
and prim = | PrimId of pd * __terminal__ | PrimStringLit of pd * __terminal__
and prod = | Prod of pd * __terminal__ * __term_not_in_ast__ * __terminal__ * __term_not_in_ast__ * prod_prod_form14 * __term_not_in_ast__ | ProdUnnamed of pd * __terminal__ * __term_not_in_ast__ * produnnamed_prod_form15 * __term_not_in_ast__
and rule = | Rule of pd * term * __term_not_in_ast__ * term
and term = | App of pd * __terminal__ * __term_not_in_ast__ * args * __term_not_in_ast__ | Sym of pd * __terminal__
and produnnamed_prod_form15 = pd * ( form) option
and prod_prod_form14 = pd * ( form) option
and lex_lex_form13 = pd * ( form) option
and grammar_grammar_rules11 = pd * ( __term_not_in_ast__ * grammar_grammar_rule12) option
and grammar_grammar_rule12 = pd * ( rule) list
and grammar_grammar_vars9 = pd * ( __term_not_in_ast__ * grammar_grammar_id10) option
and grammar_grammar_id10 = pd * ( __terminal__) list
and grammar_grammar_lexical7 = pd * ( __term_not_in_ast__ * grammar_grammar_lex8) option
and grammar_grammar_lex8 = pd * ( lex) list
and grammar_grammar_syntactic5 = pd * ( __term_not_in_ast__ * grammar_grammar_prod6) option
and grammar_grammar_prod6 = pd * ( prod) list
and grammar_grammar_whitespace4 = pd * ( __term_not_in_ast__ * __terminal__) option
and seq_forma_atom3 = pd * ( atom) list
and charset_atom_charset_prim2 = pd * ( charset_prim) list
and charset_atom_tilde1 = pd * ( __term_not_in_ast__) option
and args_args_comma0 = pd * ( __term_not_in_ast__ * term) list;;

(* pd stands for pos (position) *)
let rec dummy () = () 
and get_terminal_pd = function
   | (pd,_) -> pd 
and get_term_pd_not_in_ast = function
   | (pd) -> pd 
and pd_args = function 
  | Empty(pd) -> pd
  | Args(pd,_,_) -> pd
and pd_atom = function 
  | Id(pd,_,_) -> pd
  | Charset(pd,_,_,_,_,_) -> pd
  | Paren(pd,_,_,_,_) -> pd
and pd_charset_prim = function 
  | Range(pd,_,_,_) -> pd
  | Char(pd,_) -> pd
and pd_form = function 
  | Bar(pd,_,_,_) -> pd
  | Forma(pd,_) -> pd
and pd_forma = function 
  | Seq(pd,_) -> pd
and pd_grammar = function 
  | Grammar(pd,_,_,_,_,_,_,_,_) -> pd
and pd_lex = function 
  | Lex(pd,_,_,_,_) -> pd
and pd_lex_op = function 
  | LexArrow(pd,_) -> pd
  | LexThickArrow(pd,_) -> pd
and pd_post = function 
  | Star(pd,_) -> pd
  | Plus(pd,_) -> pd
  | Qmark(pd,_) -> pd
  | Plain(pd) -> pd
and pd_prim = function 
  | PrimId(pd,_) -> pd
  | PrimStringLit(pd,_) -> pd
and pd_prod = function 
  | Prod(pd,_,_,_,_,_,_) -> pd
  | ProdUnnamed(pd,_,_,_,_) -> pd
and pd_rule = function 
  | Rule(pd,_,_,_) -> pd
and pd_term = function 
  | App(pd,_,_,_,_) -> pd
  | Sym(pd,_) -> pd
and pd_produnnamed_prod_form15 = function 
  | (pd,None) -> pd
  | (pd,Some(_)) -> pd
and pd_prod_prod_form14 = function 
  | (pd,None) -> pd
  | (pd,Some(_)) -> pd
and pd_lex_lex_form13 = function 
  | (pd,None) -> pd
  | (pd,Some(_)) -> pd
and pd_grammar_grammar_rules11 = function 
  | (pd,None) -> pd
  | (pd,Some(_,_)) -> pd
and pd_grammar_grammar_rule12 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_grammar_grammar_vars9 = function 
  | (pd,None) -> pd
  | (pd,Some(_,_)) -> pd
and pd_grammar_grammar_id10 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_grammar_grammar_lexical7 = function 
  | (pd,None) -> pd
  | (pd,Some(_,_)) -> pd
and pd_grammar_grammar_lex8 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_grammar_grammar_syntactic5 = function 
  | (pd,None) -> pd
  | (pd,Some(_,_)) -> pd
and pd_grammar_grammar_prod6 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_grammar_grammar_whitespace4 = function 
  | (pd,None) -> pd
  | (pd,Some(_,_)) -> pd
and pd_seq_forma_atom3 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_charset_atom_charset_prim2 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_charset_atom_tilde1 = function 
  | (pd,None) -> pd
  | (pd,Some(_)) -> pd
and pd_args_args_comma0 = function 
  | (pd,[]) -> pd
  | (pd,(_,_)::___tail___) -> pd;;
let pd e = pd_grammar e;;