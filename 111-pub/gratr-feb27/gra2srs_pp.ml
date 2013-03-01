(* auto-generated by gt *)

open Gra2srs_syntax;;

let cur_line = ref 1;;
let rec print_new_line (os:string->unit) (do_print:bool) (p:int) : unit =
	if(p > !cur_line && do_print) then ( 
		os "\n"; 
		incr cur_line;
		print_new_line os do_print p;
	)
;;

let rec dummy () = () 
and pp_terminal (os:string->unit) (to_pretty_print:bool) = function 
	(d,str1) -> print_new_line os to_pretty_print (fst d); os str1

and pp_args (os:string->unit) (to_pretty_print:bool) = function 
   |Empty (d) ->  () 
   |Args (d , term1 , args_args_comma02) -> pp_term os to_pretty_print term1;pp_args_args_comma0 os to_pretty_print args_args_comma02; () 

and pp_atom (os:string->unit) (to_pretty_print:bool) = function 
   |Id (d , prim1 , post2) -> pp_prim os to_pretty_print prim1;pp_post os to_pretty_print post2; () 
   |Charset (d , charset_atom_tilde11 , pd2 , charset_atom_charset_prim23 , pd4 , post5) -> pp_charset_atom_tilde1 os to_pretty_print charset_atom_tilde11;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "["; os " " ;pp_charset_atom_charset_prim2 os to_pretty_print charset_atom_charset_prim23;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "]"; os " " ;pp_post os to_pretty_print post5; () 
   |Paren (d , pd1 , form2 , pd3 , post4) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "("; os " " ;pp_form os to_pretty_print form2;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd3); os ")"; os " " ;pp_post os to_pretty_print post4; () 

and pp_charset_prim (os:string->unit) (to_pretty_print:bool) = function 
   |Range (d , str1 , pd2 , str3) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "-"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str3; os " " ; () 
   |Char (d , str1) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ; () 

and pp_form (os:string->unit) (to_pretty_print:bool) = function 
   |Bar (d , forma1 , pd2 , form3) -> pp_forma os to_pretty_print forma1;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "|"; os " " ;pp_form os to_pretty_print form3; () 
   |Forma (d , forma1) -> pp_forma os to_pretty_print forma1; () 

and pp_forma (os:string->unit) (to_pretty_print:bool) = function 
   |Seq (d , seq_forma_atom31) -> pp_seq_forma_atom3 os to_pretty_print seq_forma_atom31; () 

and pp_grammar (os:string->unit) (to_pretty_print:bool) = function 
   |Grammar (d , str1 , pd2 , str3 , grammar_grammar_whitespace44 , grammar_grammar_syntactic55 , grammar_grammar_lexical76 , grammar_grammar_vars97 , grammar_grammar_rules118) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "Start"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str3; os " " ;pp_grammar_grammar_whitespace4 os to_pretty_print grammar_grammar_whitespace44;pp_grammar_grammar_syntactic5 os to_pretty_print grammar_grammar_syntactic55;pp_grammar_grammar_lexical7 os to_pretty_print grammar_grammar_lexical76;pp_grammar_grammar_vars9 os to_pretty_print grammar_grammar_vars97;pp_grammar_grammar_rules11 os to_pretty_print grammar_grammar_rules118; () 

and pp_lex (os:string->unit) (to_pretty_print:bool) = function 
   |Lex (d , str1 , lex_op2 , lex_lex_form133 , pd4) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;pp_lex_op os to_pretty_print lex_op2;pp_lex_lex_form13 os to_pretty_print lex_lex_form133;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "."; os " " ; () 

and pp_lex_op (os:string->unit) (to_pretty_print:bool) = function 
   |LexArrow (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "->"; os " " ; () 
   |LexThickArrow (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "=>"; os " " ; () 

and pp_post (os:string->unit) (to_pretty_print:bool) = function 
   |Star (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "*"; os " " ; () 
   |Plus (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "+"; os " " ; () 
   |Qmark (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "?"; os " " ; () 
   |Plain (d) ->  () 

and pp_prim (os:string->unit) (to_pretty_print:bool) = function 
   |PrimId (d , str1) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ; () 
   |PrimStringLit (d , str1) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ; () 

and pp_prod (os:string->unit) (to_pretty_print:bool) = function 
   |Prod (d , str1 , pd2 , str3 , pd4 , prod_prod_form145 , pd6) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os ":"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str3; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "->"; os " " ;pp_prod_prod_form14 os to_pretty_print prod_prod_form145;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd6); os "."; os " " ; () 
   |ProdUnnamed (d , str1 , pd2 , produnnamed_prod_form153 , pd4) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "->"; os " " ;pp_produnnamed_prod_form15 os to_pretty_print produnnamed_prod_form153;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "."; os " " ; () 

and pp_rule (os:string->unit) (to_pretty_print:bool) = function 
   |Rule (d , term1 , pd2 , term3) -> pp_term os to_pretty_print term1;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "->"; os " " ;pp_term os to_pretty_print term3; () 

and pp_term (os:string->unit) (to_pretty_print:bool) = function 
   |App (d , str1 , pd2 , args3 , pd4) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "("; os " " ;pp_args os to_pretty_print args3;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os ")"; os " " ; () 
   |Sym (d , str1) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ; () 

and pp_produnnamed_prod_form15 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(form1)) -> pp_form os to_pretty_print form1; () 

and pp_prod_prod_form14 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(form1)) -> pp_form os to_pretty_print form1; () 

and pp_lex_lex_form13 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(form1)) -> pp_form os to_pretty_print form1; () 

and pp_grammar_grammar_rules11 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1 , grammar_grammar_rule122)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Rules"; os " " ;pp_grammar_grammar_rule12 os to_pretty_print grammar_grammar_rule122; () 

and pp_grammar_grammar_rule12 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (rule1)::grammar_grammar_rule122) -> pp_rule os to_pretty_print rule1;pp_grammar_grammar_rule12 os to_pretty_print  (d,grammar_grammar_rule122); () 

and pp_grammar_grammar_vars9 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1 , grammar_grammar_id102)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Vars"; os " " ;pp_grammar_grammar_id10 os to_pretty_print grammar_grammar_id102; () 

and pp_grammar_grammar_id10 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (str1)::grammar_grammar_id102) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;pp_grammar_grammar_id10 os to_pretty_print  (d,grammar_grammar_id102); () 

and pp_grammar_grammar_lexical7 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1 , grammar_grammar_lex82)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Lexical"; os " " ;pp_grammar_grammar_lex8 os to_pretty_print grammar_grammar_lex82; () 

and pp_grammar_grammar_lex8 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (lex1)::grammar_grammar_lex82) -> pp_lex os to_pretty_print lex1;pp_grammar_grammar_lex8 os to_pretty_print  (d,grammar_grammar_lex82); () 

and pp_grammar_grammar_syntactic5 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1 , grammar_grammar_prod62)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Syntactic"; os " " ;pp_grammar_grammar_prod6 os to_pretty_print grammar_grammar_prod62; () 

and pp_grammar_grammar_prod6 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (prod1)::grammar_grammar_prod62) -> pp_prod os to_pretty_print prod1;pp_grammar_grammar_prod6 os to_pretty_print  (d,grammar_grammar_prod62); () 

and pp_grammar_grammar_whitespace4 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1 , str2)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Whitespace"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ; () 

and pp_seq_forma_atom3 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (atom1)::seq_forma_atom32) -> pp_atom os to_pretty_print atom1;pp_seq_forma_atom3 os to_pretty_print  (d,seq_forma_atom32); () 

and pp_charset_atom_charset_prim2 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (charset_prim1)::charset_atom_charset_prim22) -> pp_charset_prim os to_pretty_print charset_prim1;pp_charset_atom_charset_prim2 os to_pretty_print  (d,charset_atom_charset_prim22); () 

and pp_charset_atom_tilde1 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,None) ->  () 
   | (d , Some(pd1)) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "~"; os " " ; () 

and pp_args_args_comma0 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (pd1 , term2)::args_args_comma03) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os ","; os " " ;pp_term os to_pretty_print term2;pp_args_args_comma0 os to_pretty_print  (d,args_args_comma03); () ;;

let pp (os:string->unit) (to_pretty_print:bool) e = pp_grammar os to_pretty_print e;;