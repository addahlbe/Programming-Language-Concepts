open Util;;
open Grammar;;
open Trs;;
open Trie;;
open Term;;

let dbg_convert_grammar = ref false;;

type ast_type = NotInAst | SymOnly | SubAst;;

(* (name, lhs , rhs, r) means that we will rewrite lists of
   terms whose top symbols match lhs to rhs, where if r is Reading,
   we will build an AST including each element of lhs in the way
   indicated by ast_type:
     -- NotInAst: do not include the element at all
     -- SymOnly: we literally include the element (this is for terminals) 
     -- SubAst: we include the sub-ast for the element.
   The root of the AST will be labeled with name. 
   If r is not Reading, we will not build an AST.  
*)
type prule = string * ((ast_type * string) list) * string * role;;

type parsing_trs = prule list;;

(* convert grammar (abstract syntax) to a parsing TRS.
*)
let convert_grammar (Grammar(name,ostart,ows,o,ps,lexs,Trs(rs))) : parsing_trs =
  match o with
      (SyntacticNts(syn_nts),ReadingNts(read_nts),RecognizingNts(recog_nts),Terminals(ter_syms)) ->
	(*let dbg = debugger dbg_convert_grammar in*)
	let prodname_arities = trie_new() in
	let helper (name:string) (include_terminals:bool) (r:role) (lhs:string) (rhs:string list) : prule =
	  let get_ast_type s = 
	    if trie_contains syn_nts s || trie_contains read_nts s then
	      SubAst
	    else if (include_terminals && trie_contains ter_syms s) then
	      SymOnly
	    else
	      NotInAst
	  in
	  let ss = List.map (fun s -> (get_ast_type s, s)) rhs in
	    (* update the arities table *)
	    (match r with
		 Reading ->
		   (* we are assuming productions have distinct names *)
		   trie_insert prodname_arities name (List.length (List.filter (fun (b,_) -> b <> NotInAst) ss))
	       | _ -> ());
	    (name,ss,lhs,r)
	in
	let ptrs = ((List.map (fun (Prod(rn,s,ss)) -> helper rn false Reading s ss) ps) 
		 @ (List.map (fun (Lex(r,s,ss)) -> helper "odot" (r=Reading) r s ss) lexs)) in

	(* make sure the grammar's rewrite rules only use production names at
	   the correct arities *)
	let rec check_trs_term (r:rule) (t:term) : unit =
	  match t with
	      Normal(t') -> check_trs_term r t' (* shouldn't happen *)
	    | Var(_) -> ()
	    | App(f,args) -> 
		(match trie_lookup prodname_arities f with
		    None ->
		      (print_string "A rewrite rule is using a function symbol which is not the name of a production.\n";
		       print_string "1. the rewrite rule: ";
		       print_rule print_string r;
		       print_string "\n2. the function symbol: ";
		       print_string f;
		       print_string "\n";
		       exit 1);
		  | Some(a) ->
		      if List.length args <> a then
			(print_string "A rewrite rule is using a production name with the wrong number of arguments.\n";
			 print_string "1. the rewrite rule: ";
			 print_rule print_string r;
			 print_string "\n2. the production name: ";
			 print_string f;
			 print_string "\n3. the expected number of arguments: ";
			 print_string (string_of_int a);
			 print_string "\n";
			 exit 1);
		      List.iter (check_trs_term r) args)
	in

	  List.iter (fun r ->
		       let (Rule(_,lhs,rhs)) = r in 
			 check_trs_term r lhs;
			 check_trs_term r rhs) rs;
	  ptrs
;;


let print_prule_sym os b s =
  if b = NotInAst then os "#"; os s;;

let print_prule (os:string -> unit) (r:prule) =
  let (name,lhs,rhs,r) = r in
    os name;
    os " :";
    List.iter (fun (b,s) -> os " "; print_prule_sym os b s) lhs;
    os " -> ";
    (match r with Recognizing -> os "#" | _ -> ());
    os rhs;
    os "\n"
;;

let prule_to_string (r:prule) : string =
  let s = ref "" in
    print_prule (fun s' -> s := s' ^ !s) r;
    !s;;

let print_parsing_trs (os:string -> unit) (s:parsing_trs) : unit = 
  os "(\n";
  List.iter (print_prule os) s;
  os ")\n";;       
