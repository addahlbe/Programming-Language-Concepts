open Util;;
open Grammar;;
open Trs;;
open Trie;;
open Term;;

let dbg_convert_grammar = ref false;;

type ast_type = NotInAst | SymOnly | SubAst of int;;

(* (lhs , rhs, r) means that we will rewrite lists of
   terms whose top symbols match lhs to rhs, where if r is Some(t),
   we will build AST t by including each element of lhs in the way
   indicated by ast_type:
     -- NotInAst: do not include the element at all
     -- SymOnly: we literally include the element (this is for terminals) 
     -- SubAst: we include the sub-ast for the element.
   The root of the AST will be labeled with name. 
   If r is None, we are not to build an AST.  
*)
type prule = ((ast_type * string) list) * string * (term option);;

type parsing_trs = prule list;;

(* an intermediate type similar to ast_type *)
type ast_typei = Ast_type of ast_type | Nulled of role (* the role for the nulled nonterminal *);;

let print_prule_sym os b s =
  match b with
      NotInAst -> os "#"; os s
    | SubAst(i) -> os s; os "["; os (string_of_int i); os "]"
    | SymOnly -> os s;;

let print_intermed (os:string -> unit) (ss:(ast_typei * string) list) : unit =
  List.iter
    (fun (tp,s) ->
       (match tp with
	   Ast_type(t) -> print_prule_sym os t s; 
	 | Nulled(r) -> os "(nulled "; os s; (match r with Reading -> os " Reading" | _ -> os " Recognizing"); os ")");
       os " ")
    ss;;	     

(* convert grammar (abstract syntax) to a parsing TRS.
*)
let convert_grammar (Grammar(name,ostart,ows,o,ps,lexs,Trs(rs))) : parsing_trs =
  let dbg = debugger dbg_convert_grammar in
    dbg "(convert_grammar begins.\n";
    match o with
      (SyntacticNts(syn_nts),ReadingNts(read_nts),RecognizingNts(recog_nts),Terminals(ter_syms), Nullable(nullable)) ->
	let prodname_arities = trie_new() in
	  (* we return a list because we might be eliminating nullable symbols by introducing several rules *)
	let helper (name:string) (include_terminals:bool) (r:role) (lhs:string) (rhs:string list) : prule list =
	  let nextvar = ref 0 in
	  let get_nextvar() = 
	    let v = !nextvar in
	      incr nextvar;
	      v
	  in

	  (* compute a list of rhs's with intermediate annotations *)
	  let rec get_ast_typei (ss : string list) : (ast_typei * string) list list = 
	    match ss with
		[] -> [[]]
	      | s::ss' ->
		  let grow ls tp = List.map (fun ss -> (tp,s)::ss) ls in
		    if trie_contains syn_nts s || trie_contains read_nts s then
			let v = get_nextvar() in
			let ls = get_ast_typei ss' in
			let ret = grow ls (Ast_type(SubAst(v))) in
			  if trie_contains nullable s then
			    ret @ (grow ls (Nulled(Reading)))
			  else
			    ret
		    else
		      let ls = get_ast_typei ss' in
			if (include_terminals && trie_contains ter_syms s) then
			  grow ls (Ast_type(SymOnly))
			else
			  let ret = grow ls (Ast_type(NotInAst)) in
			    if trie_contains nullable s then
			      ret @ (grow ls (Nulled(Recognizing)))
			    else
			      ret
	  in

	  (* here are the rhs's with intermediate annotations *)
	  let rhssi = get_ast_typei rhs in
	    
	  (* compute an rhs with ast_type annotations from one with intermediate annotations *)
	  let rec to_rhs (ss:(ast_typei * string) list) : (ast_type * string) list = 
	    match ss with
		[] -> []
	      | (Ast_type(x),s)::ss' -> (x,s)::(to_rhs ss')
	      | (Nulled(b),_)::ss' -> (to_rhs ss')
	  in

	  (* args converts an rhs with intermediate annotations to a
	     list of terms, which will be arguments to the
	     constructor *)
	  let rec args ss = 
	    match ss with
		[] -> []
	      | (Ast_type(NotInAst),_)::ss' -> args ss'
	      | (Ast_type(SymOnly),s)::ss' -> (const s)::(args ss')
	      | (Ast_type(SubAst(i)),s)::ss' -> (var i)::(args ss')
	      | (Nulled(r),s)::ss' -> 
		  let a = args ss' in
		  (match r with
		       Reading -> (const ("Empty_"^s)::a)
		     | Recognizing -> a)
	  in

	    keep_some
	      (List.map
		 (fun ss ->
		    (* for each rhs with intermediate annotations *)

		    let rhs = to_rhs ss in

		      if empty rhs then
			None
		      else
			(dbg "(Considering intermediately annotated rhs ";
			 print_intermed dbg ss;
			 dbg ")\n";
			 if empty ss then
			   None
			 else
			   match r with
			       Reading ->
				 let a = args ss in
				   
				   (* update the arities table; we are assuming productions have distinct names *)
				   trie_insert prodname_arities name (List.length a);
				   
				   Some(rhs, lhs, Some(App(name,a)))
			     | Recognizing -> 
				 Some(rhs, lhs, None)))
		 rhssi)
	in

	(* this is now the ptrs: *)
	let ptrs = 
	  List.concat 
	    ((List.map (fun (Prod(rn,s,ss)) -> helper rn false Reading s ss) ps) 
	     @ (List.map (fun (Lex(r,s,ss)) -> helper "odot" (r=Reading) r s ss) lexs))
	in

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

	  dbg "convert_grammar ends.)\n";
	  ptrs
;;


let print_prule (os:string -> unit) (r:prule) =
  let (lhs,rhs,ot) = r in
    List.iter (fun (b,s) -> os " "; print_prule_sym os b s) lhs;
    os " -> ";
    os rhs;
    os "[";
    (match ot with
	 None -> ()
       | Some(t) -> print_term os t);
    os "]\n"
;;

let prule_to_string (r:prule) : string =
  let s = ref "" in
    print_prule (fun s' -> s := s' ^ !s) r;
    !s;;

let print_parsing_trs (os:string -> unit) (s:parsing_trs) : unit = 
  os "(\n";
  List.iter (print_prule os) s;
  os ")\n";;       
