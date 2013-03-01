open Grammar;;
open Trs;;
open Trie;;
open Util;;
open Term;;

let dbg_cps = ref false;;
let dbg_rules = ref false;;
let dbg_pruning = ref false;;
let dbg_pruning_micro = ref false;;
let dbg_cps_details = ref false;;
let dbg_cps_micro = ref false;;
let dbg_completion = ref false;;
let dbg_rewriting = ref false;;
let add_unorientable_rules = ref false;;
let dbg_aut = ref false;;
let prune_cps_with_after = ref false;;
let continue_on_unorientable = ref false;;
let stop_on_new_rule = ref false;;

type cp = int * term * term * term * bool * rule * rule;; (* (maxvar,reduct1,reduct2,peak,toplevel,rule1,rule2) *)

let compare_cps (_,reduct1,reduct2,_,_,_,_) (_,reduct1',reduct2',_,_,_,_) : int =
  if eq_term nodbg reduct1 reduct1' then
    if eq_term nodbg reduct2 reduct2' then
      0
    else
      compare reduct2 reduct2'
  else
    compare reduct1 reduct1';;

let rename (minv:int) (r:rule) : rule =
  let rec rename_term (t:term) : term =
    match t with
	Normal(t') -> Normal(rename_term t')
      | Var(x) -> Var(x+minv)
      | App(f,args) -> App(f,List.map rename_term args) in
  let Rule((oname,maxv,q),lhs,rhs) = r in 
    Rule((oname,maxv+minv,q),rename_term lhs, rename_term rhs);;

let rec unify (subst:term option array) (t1:term) (t2:term) : bool =
  match t1 with
      Var(x) ->
	(match subst.(x) with
	     None -> subst.(x) <- Some(t2); true
	   | Some(t1') -> unify subst t1' t2)
    | Normal(t1') -> unify subst t1' t2
    | App(f1,args1) ->
	match t2 with
	    Var(x) -> 
	      (* let the case above handle this one *)
	      unify subst t2 t1
	  | Normal(t2') -> unify subst t1 t2'
	  | App(f2,args2) ->
	      if f1 <> f2 then
		false
	      else
		unify_args subst args1 args2
and unify_args (subst:term option array) (args1:term list) (args2:term list) : bool =
  match args1,args2 with
      t1::args1',t2::args2' ->
	if unify subst t1 t2 then
	  unify_args subst args1' args2'
	else
	  false
    | [],[] -> true
    | _,_ -> false (* we will treat different arity uses of the same function as uses
		      of different functions *);;

let unify (maxv:int) (t1:term) (t2:term) : term option array option =
  let subst = Array.make (maxv+1) None in
    if (unify subst t1 t2) then
      Some(subst)
    else
      None;;

let rec do_match (subst:term option array) (t1:term) (t2:term) : bool =
  match t1 with
      Var(x) ->
	(match subst.(x) with
	     None -> subst.(x) <- Some(t2); true
	   | Some(t1') -> do_match subst t1' t2)
    | Normal(t1') -> do_match subst t1' t2
    | App(f1,args1) ->
	let t2 = strip_normal t2 in
	match t2 with
	    Var(_) | Normal(_) (* should not happen *) -> false
	  | App(f2,args2) ->
	      if f1 <> f2 then
		false
	      else
		match_args subst args1 args2
and match_args (subst:term option array)  (args1:term list) (args2:term list) : bool =
  match args1,args2 with
      t1::args1',t2::args2' ->
	if do_match subst t1 t2 then
	  match_args subst args1' args2'
	else
	  false
    | [],[] -> true
    | _,_ -> false (* we will treat different arity uses of the same function as uses
		      of different functions *);;

(* match t1 as pattern against t2 as target.
   We assume t1's vars are renamed away from t2's.  maxv should be an upper bound on vars in t1.  *)
let do_match (dbg:string -> unit) (maxv:int) (t1:term) (t2:term) : term option array option =
  let subst = Array.make (maxv+1) None in
    dbg "(do_match ";
    print_term dbg t1;
    dbg " and ";
    print_term dbg t2;
    dbg "\n";
    if (do_match subst t1 t2) then
      (dbg "found match.)\n";
       (*print_trie (print_term dbg) subst;
       dbg "\n)\n"; *)
       Some(subst))
    else
      (dbg "no match.)\n";
       None);;

let rec apply_subst (subst:term option array) (t:term) : term =
  match t with
      Var(x) -> 
	(match subst.(x) with
	     None -> t
	   | Some(t') -> t')
    | Normal(t') -> apply_subst subst t'
    | App(f,args) ->
	App(f,List.map (apply_subst subst) args);;

(* t should be a subterm of lhs1, and we should have renamed r2 away from r1. 
   The int in the cp is an upper bound on its max var. 

   If eqlhs is true, then t equals lhs1.
*)
let rec cps dbg r1 r2 (c:term -> term) (t:term) (eqlhs1:bool) : cp list =
  let Rule((oname1,maxv1,sens1),lhs1,rhs1) = r1 in
  let Rule((oname2,maxv2,sens2),lhs2,rhs2) = r2 in
  let maxv = max maxv1 maxv2 in

    match sens1,sens2 with
	Syntactic,Lexical(_) | Lexical(_),Syntactic -> 
	  (* we do not consider overlaps between syntactic and lexical rules,
	     because we will rewrite in two phases *)
	  []
      | _,_ ->

	  (* compute cps for the args in rest_args, extending
	     the context c to account for the fact that the term
	     we are considering is c(f(pre_args,rest_args)) *)
	  let rec cps_args (f:string) (pre_args:term list) (rest_args : term list) : cp list =
	    match rest_args with 
		[] -> []
	      | arg::rest_args' ->
		  (cps dbg r1 r2 (fun x -> c (App(f,pre_args @ x::rest_args'))) arg false) 
		  @ (cps_args f (pre_args @ [arg]) rest_args')
	  in
	    match t with
		Var(x) -> [] (* we do not use unification with a variable in lhs1 to generate a cp *)
	      | Normal(t') -> cps dbg r1 r2 c t' eqlhs1
	      | App(f,args) ->
		  let rest = cps_args f [] args in
		    if (compare_rules r1 r2) = 0 && eqlhs1 then
		      (dbg "Computing cps: skipping the overlap of a rule with itself at the top level.\n";
		       rest)
		    else 
		      (dbg "Computing cps between rules:\n";
		       dbg "  ";
		       print_rule dbg r1;
		       dbg "\n  ";
		       print_rule dbg r2;
		       dbg "\nAt term\n  ";
		       print_term dbg t;
		       dbg "\n";
		       match unify maxv t lhs2 with
			   None -> 
			     dbg "No cp.\n";
			     rest
			 | Some(u) -> 
			     let new_cp1 = apply_subst u rhs1 in
			     let new_cp2 = c (apply_subst u rhs2) in
			     let peak = (c (apply_subst u t)) in
			       dbg "Cp found with peak\n  ";
			       print_term dbg peak;
			       dbg "\nThe cp is:\n  a. ";
			       print_term dbg new_cp1;
			       dbg "\n  b. ";
			       print_term dbg new_cp2;
			       dbg "\n\n";
			       (maxv,new_cp1,new_cp2,peak,eqlhs1,r1,r2)::rest) 
;;

(* we look for overlaps with the second rule in the first *)
let cps (dbg:string -> unit)  (r : rule * rule) : cp list =
  let (r1,r2) = r in
  let Rule((_,maxv2,syn2),_,_) = r2 in
  let r1' = rename (maxv2+1) r1 in
  let Rule(_,lhs,rhs) = r1' in
    cps dbg r1' r2 (fun x -> x) lhs true;;

let cps  (symmap:rule list trie) (headmap:rule list trie) (new_rules:rule list) : cp list =
  let dbg = debugger dbg_cps_micro in
  let consult_symmap (r:rule) : rule list =
    let Rule(rname,lhs,rhs) = r in
      match get_head_symbol lhs with
	  None -> [] (* should not happen *)
	| Some(f) ->
	    match trie_lookup symmap f with
		None -> []
	      | Some(rs) -> rs
  in
  let consult_headmap (r:rule) : rule list =
    let Rule(rname,lhs,rhs) = r in
    let syms = collect_fun_syms lhs in
      List.concat
	(List.map (fun f ->
		     match trie_lookup headmap f with
			 None -> []
		       | Some(rs) -> rs) 
	   syms)
  in
    
    dbg "Beginning computation of cps.\n";

    (* for each new rule r:
       
       1. collect the rules which contain the leading symbol of r,
       and look for unifiers with r's lhs in those rules.

       2. collect the rules which contain any symbol of r,
       and look for unifiers with the lhs's of those rules in r.
    *)
    
    List.concat
      (List.map 
	 (fun r ->
	    let ss = consult_symmap r in
	    let cs = consult_headmap r in 
	    let prrs = List.iter (fun r2 -> dbg "  "; print_rule dbg r2) in
	      dbg "(Computing cps with this rule:\n  ";
	      print_rule dbg r;
	      dbg "overlapping into these rules:\n";
	      prrs ss;
	      dbg "and being overlapped by these rules:\n";
	      prrs cs;
	      
	      let ret = 
		List.concat 
		  ((List.map (fun r2 -> cps dbg (r2,r)) ss)
		   @ (List.map (fun r2 -> cps dbg (r,r2)) cs)) in
		dbg "\n)\n";
		ret)
	 new_rules) 
      
;;

(* the symmap maps strings for functions symbols to
   rules where they appear. 
*)
let update_symmap (symmap:rule list trie) (rs : rule list) : unit =
  let rec add_term (r:rule) (t:term) : unit =
    match t with
	App(f,ts) -> 
	  if f <> "dot" then 
	    trie_cons symmap f r;
	  List.iter (add_term r) ts
      | Normal(t') -> add_term r t'
      | Var(x) -> ()
  in
    List.iter 
      (fun r ->
	 let Rule(_,lhs,rhs) = r in
	   add_term r lhs)
      rs;
    List.iter
      (fun s ->
	 match trie_lookup symmap s with
	     None -> () (* should not happen *)
	   | Some(rs) -> trie_insert symmap s (uniq compare_rules rs))
      (trie_strings symmap)
;;

(* the headmap maps strings for function symbols to the rules where
   they are the head, as defined by Grammar.get_head_symbol *)
let update_headmap_rule (headmap : rule list trie) (r:rule) : unit =
  let Rule(_,lhs,rhs) = r in
    match get_head_symbol lhs with
	None -> () (* should not happen *)
      | Some(f) ->
	  trie_cons headmap f r;;

let update_headmap (headmap:rule list trie) (rs : rule list) : unit =
  List.iter (update_headmap_rule headmap) rs
;;

let print_symmap (os:string -> unit) (symmap:rule list trie) : unit =
  print_trie
    os
    (fun rs ->
       List.iter (fun r -> os "\n  "; print_rule os r) rs;
       os "\n")
    symmap;;

(* if grammarsyms is supplied, we will not prune terms where f follows g in violation
   of after, but either f or g is not a grammarsym.  Otherwise, we will strictly
   enforce that if g follows f, then g is in the after-set of f. *)
let can_prune_term_with_after (dbgp:string->unit) (after:string_relation) 
    (grammarsyms:stringset option) (t:term) : bool =
  let dbgm = debugger dbg_pruning_micro in
  let (check_gsyms,gsyms) = match grammarsyms with None -> (false,trie_new()) | Some(sset) -> (true,sset) in

    (* we assume t has no toplevel Normal *)
  let rec helper t =
    dbgm "(Trying to prune term ";
    print_term dbgm t;
    dbgm "\n";
    let ret = 
      match t with
	  App("dot",[arg1a;arg1b]) ->
	    let arg1a = strip_normal arg1a in
	    let arg1b = strip_normal arg1b in
	    let arg1b' = dot_term_first arg1b in
	      (match arg1a, arg1b' with
		   App(f,_) , App(g,_) ->
		     (* we have a g following an f in the string *)
		     let sset = string_relation_image after f in
		       if trie_contains sset g || 
			 (if check_gsyms then not (trie_contains gsyms f) || not (trie_contains gsyms g) else false) 
		       then
			 (* either the after-set allows g to follow f, or else we
			    are checking the grammar symbols and f or g is not a grammar symbol (so we
			    do not count a conflict as blocking this term) *)
			 (dbgp "It is allowed for ";
			  dbgp f;
			  dbgp " to be followed by ";
			  dbgp g;
			  dbgp "\n";
			  helper arg1b)
		       else
			 (dbgp f;
			  dbgp " cannot be followed by ";
			  dbgp g;
			  dbgp "\n";
			  true (* can prune, because g cannot follow f *))
		 | _ -> 
		     dbgp "Cannot compare terms for pruning: ";
		     print_term dbgp arg1a;
		     dbgp " , ";
		     print_term dbgp arg1b';
		     dbgp "\n";
		     helper arg1b)
	| _ -> false
    in
      dbgm "Returning ";
      dbgm (if ret then "true" else "false");
      dbgm ")\n";
      ret
  in
    dbgp "(can_prune_term_with_after ";
    print_term dbgp t;
    dbgp "\n";
    let ret = helper (strip_normal t) in
      dbgp "returning ";
      dbgp (if ret then "true)\n" else "false)\n");
      ret
;;

(* return true iff t1 and t2 have disjoint after sets or disjoint before sets.
*) 
let disjoint_before_after (dbgp:string -> unit) (after:string_relation) (t1:term) (t2:term) : bool =
  let disjoint_syms(verb:string)(adj:string)(forw:bool)(f:string)(g:string) : bool =
    let h = if forw then string_relation_image else string_relation_preimage in
    let i = (trie_strings (stringset_intersect (h after f) (h after g))) in
      dbgp "(";
      dbgp f;
      dbgp " and ";
      dbgp g;
      if nonempty i then
	(dbgp " can be ";
	 dbgp verb;
	 dbgp " by these strings: ";
	 print_strings dbgp " " i;
	 dbgp "\n";
	 false)
      else
	(dbgp " have disjoint ";
	 dbgp adj;
	 dbgp "-sets.\n";
	 true)
  in
    dbgp "(Checking the before and after-sets of the lhs and rhs.\n";
    let ret = 
      match dot_term_last_str t1 , dot_term_last_str t2 with
	  Some(f), Some(g) ->
	    if disjoint_syms "followed" "after" true f g then
	      true
	    else
	      (match dot_term_first_str t1, dot_term_first_str t2 with
		   Some(f), Some(g) ->
		     disjoint_syms "preceded" "before" false f g
		 | _,_ -> false)
	| _,_ -> false
    in 
      dbgp "returning ";
      if ret then
	dbgp "true.)\n"
      else
	dbgp "false.)\n";
      ret
;;

(* If leftcont is Some(s), then s is the symbol occurring
   just before t in a dot term.

   the returned bool is for whether or not we rewrote the term 
   
   If preserve_after is true, we will not allow rewrite steps
   from t to t' where after(t) is not a subset of after(t').

*)
let rec rewrite_top (dbg:string -> unit) (after:string_relation) (preserve_after:bool)
    (grammarsyms:stringset option) (leftcont:string option)
    (headmap:rule list trie) (t:term) : bool * term =
  let t = 
    match strip_normal t with
	App("odot",args) -> dbg "Flattening dot expression.\n"; dot_flatten t
      | _ -> t
  in
		  
  let rec try_rules (rs:rule list) : bool * term =
    match rs with
	[] -> (false, t)
      | r::rs' ->
	  let Rule((_,maxv2,_),lhs,rhs) = r in
	    dbg "trying rule\n  ";
	    print_rule dbg r;

	    match do_match nodbg maxv2 lhs t with
		None -> try_rules rs'
	      | Some(u) -> 
		  let newt = apply_subst u rhs in
		  let testt = 
		    match leftcont with
			None -> newt
		      | Some(s) -> dot (const s) newt
		  in
		  let report what s1 s2 = 
		    dbg "(This rewrite step does not preserve ";
		    dbg what;
		    dbg "-constraints:\n  ";
		    print_term dbg t;
		    dbg " -> ";
		    print_term dbg newt;
		    dbg "\nThe ";
		    dbg what;
		    dbg "-set of the first term: ";
		    print_stringset dbg s1;
		    dbg "\nThe ";
		    dbg what;
		    dbg "-set of the second term: ";
		    print_stringset dbg s2;
		    dbg "\n"
		  in
		  let preserve_after_violated = 
		    if preserve_after then
		      match dot_term_last_str t, dot_term_last_str newt with
			  Some(f), Some(g) ->
			    let af = string_relation_image after f in
			    let ag = string_relation_image after g in
			      if (stringset_subset af ag) then
				match leftcont with
				    Some(_) -> 
				      (* we will check the constraints on newt when we
					 check testt below*)
				      false
				  | None ->
				      match dot_term_first_str t, dot_term_first_str newt with
					  Some(f), Some(g) ->
					    let af = string_relation_preimage after f in
					    let ag = string_relation_preimage after g in
					      if (stringset_subset af ag) then
						false
					      else
						(report "before" af ag;
						 true)
					| _,_ -> false
			      else
				(report "after" af ag;
				 true)
			| _ , _ -> false
		    else
		      false
		  in
		    if preserve_after_violated then
		       try_rules rs'
		    else
		      if can_prune_term_with_after dbg after grammarsyms testt then
			(* we will not actually perform this rewrite, as it
			   leads to a term that is not allowed by the 'after' constraints. *)
			(dbg "This term violates the after-constraints: ";
			 print_term dbg testt;
			 dbg "\n";
			 try_rules rs')
		      else
			let (_,ret) = rewrite_top dbg after preserve_after grammarsyms leftcont headmap newt in
			  (true,ret)
  in
    dbg "(rewrite_top ";
    print_term dbg t;
    dbg "\n";
    (match leftcont with
	 None -> dbg "  No left context.\n"
       | Some(l) -> dbg "  Left context is "; dbg l; dbg ".\n");
    
    let (rewritten,ret) = 
      match get_head_symbol t with
	  None -> (false, t)
	| Some(f) ->
	    match trie_lookup headmap f with
		None -> (false,t)
	      | Some(rs) ->
		  try_rules rs
    in
      dbg " => (";
      dbg (if rewritten then "true" else "false");
      dbg ", ";
      print_term dbg ret;
      dbg "))\n";
      (rewritten,ret)
;;

(* maxv should be an upper bound on the max var in t 

   if t is a dot term, then we will check after-constraints between the head symbol of
   its first argument and the string given by leftcont (if leftcont is not None).
*)
let rec rewrite_inner (dbg:string -> unit) (after:string_relation) (preserve_after:bool)
    (grammarsyms:stringset option) (leftcont:string option) 
    (mark_normal:bool) (headmap:rule list trie) (t:term) : term =
  dbg "(rewrite_inner ";
  print_term dbg t;
  dbg "\n";
  (match leftcont with
       None -> dbg "  No left context.\n"
     | Some(l) -> dbg "  Left context is "; dbg l; dbg ".\n");
  
  let rewrite_top_cont t =
    let (rewritten,t') = rewrite_top dbg after preserve_after grammarsyms leftcont headmap t in
      if rewritten then
	rewrite_inner dbg after preserve_after grammarsyms leftcont mark_normal headmap t'
      else
	t'
  in
  let ret = 
    match t with
	Var(x) -> t
      | Normal(t') -> t'
      | App("dot",[a1;a2]) ->
	  let preserve_after_a1 = match strip_normal a2 with Var(_) -> preserve_after | _ -> false in
	  let a1' = rewrite_inner dbg after preserve_after_a1 grammarsyms leftcont mark_normal headmap a1 in
	  let leftcont' = 
	    match strip_normal a1' with
		App(f,_) -> Some(f)
	      | _ -> None
	  in
	  let a2' = rewrite_inner dbg after preserve_after grammarsyms leftcont' mark_normal headmap a2 in
	    rewrite_top_cont (App("dot",[a1';a2']))
      | App(f,args) ->
	  let t' = App(f,List.map (rewrite_inner dbg after false grammarsyms None mark_normal headmap) args) in
	    rewrite_top_cont t'
  in
  let ret = if mark_normal then Normal(ret) else ret in
    dbg "=> ";
    print_term dbg ret;
    dbg ")\n";
    ret
;;

let rewrite_inner (dbg:string -> unit) (after:string_relation) 
    (grammarsyms:stringset option) (leftcont:string option) 
    (mark_normal:bool) (headmap:rule list trie) (t:term) : term =
  rewrite_inner dbg after true grammarsyms leftcont mark_normal headmap t;;

let rewrite_inner_rules (dbg:string -> unit) (after:string_relation) (grammarsyms:stringset option)
    (mark_normal:bool) (rs:rule list) (t:term) : term =
  let headmap = trie_new() in
    update_headmap headmap rs;
    rewrite_inner dbg after grammarsyms None mark_normal headmap t;;

let rules_compatible (Rule((_,_,syn1),_,_)) (Rule((_,_,syn2),_,_)) : bool = (syn1 = syn2);;

let gen_rules (after:string_relation) (symmap:rule list trie) (headmap:rule list trie) 
    (prev_rules:rule list) (new_rules:rule list) 
    : rule list =
  let dbgr = debugger dbg_rewriting in
  let dbg = debugger dbg_cps in
  let dbgu = debugger dbg_rules (* !dbg_cps implies !dbg_rules *) in
  let dbgd = debugger dbg_cps_details in
  let dbgm = debugger dbg_cps_micro in
  let dbgp = debugger dbg_pruning in
  let dot_size_term = count_sym_term "dot" in
  let rec rules_from_cps (cs: cp list) : rule list =
    match cs with
	[] -> []
      | (n,x,y,peak,toplevel,r1,r2)::cs' -> 
	  let Rule((_,_,syn1),_,_) = r1 in
	  let pr_rl (dbg_summary:string->unit)(dbg:string->unit) (newr:rule) (str:string) : unit = 
	    dbg "(";
	    dbg_summary str;
	    dbg_summary " rule: ";
	    print_rule dbg_summary newr;
	    dbg_summary "\n";
	    dbg "generated from peak term:\n  ";
	    print_term dbg peak;
	    dbg "\ncritical pair\n  a.";
	    print_term dbg x;
	    dbg "\n  b.";
	    print_term dbg y;
	    dbg "\nby rules:\n  1.";
	    print_rule dbg r1;
	    dbg "\n  2.";
	    print_rule dbg r2;
	    dbg ")\n" in
	  let add_rl (r:rule) : rule =
	    if !stop_on_new_rule then
	      (pr_rl print_string print_string r "Stopping on new";
	       exit 1);
	    pr_rl dbgu dbg r "New";
	    update_headmap_rule headmap r;
	    r
	  in
	    (* if the rule simplifies away (by rewriting, then return None; 
	       otherwise return the simplified rule.) *)
	  let simplify_rule (r:rule) : rule option =
	    let Rule((o,n,q),x,y) = r in
	      
	    dbgr "(Rewriting rule\n  ";
	    print_rule dbgr r;
	    dbgr ")\n(Rewriting lhs:\n";
	    
	    let nx = rewrite_inner dbgr after None None true headmap (rewrite_inner_rules dbgr after None false [r2] x) in
	      dbgr ")\n(Rewriting rhs:\n";
	      let ny = rewrite_inner dbgr after None None true headmap (rewrite_inner_rules dbgr after None false [r1] y) in
		dbgr ")\n";
		if (eq_term nodbg nx ny) then 
		  (dbgu "Both sides of the following rule rewrite to ";
		   print_term dbgu nx;
		   dbgu ":\n";
		   pr_rl dbgu dbgd (Rule((o,n,q),x,y)) "  Trivial";
		   None)
		else
		  Some(Rule((o,n,q),nx,ny))
	  in

	  let orient_rule (r:rule) : rule option = 
	    let Rule(o,x,y) = r in
	    let dsx = dot_size_term x in
	    let dsy = dot_size_term y in
	      
	      if (dsx > dsy (*&& dsy = 1*)) then Some(r)
	      else if (dsy > dsx (*&& dsx = 1*)) then Some(Rule(o, y, x))
	      else None
	  in
	    (* report that nr is unorientable, and either exit
	       or continue, adding or not adding the rule to rcs to
	       generate the return value of the function, depending
	       on various global flags. *)
	  let handle_unorientable (nr:rule) (rcs:rule list): rule list =
	    let rec extract_nondot t =
	      match t with
		  App(_ (* dot *),[a1;a2]) -> a1
		| Normal(t') -> extract_nondot t'
		| _ -> 
		    print_string "Internal error: could not extract non-dot part of a dot-term:\n";
		    print_term print_string t;
		    print_string "\n";
		    exit 1 
	    in	    
	    let Rule(o,x,y) = nr in
	      pr_rl dbgu dbg nr "Unorientable";
	      let dsx = dot_size_term x in
	      let dsy = dot_size_term y in
		print_string_flush "Unorientable: ";
		if (dsx = 1 && dsy = 1) then
		  (let (x,y) = if (size_term x) < (size_term y) then (y,x) else (x,y) in
		   let x = if dsx = 1 then extract_nondot x else x in
		   let y = if dsx = 1 then extract_nondot y else y in
		   let nr = Rule(o,x,y) in
		     print_rule print_string_flush nr)
		else
		  print_rule print_string_flush nr;
		if not !continue_on_unorientable then
		  exit 0;
		if !add_unorientable_rules then nr::rcs else rcs
	  in

	    let rcs = rules_from_cps cs' in
	      
	    let nr = Rule((None,n,syn1 (* we check later that syn1=syn2 *)),x,y) in
	      (* try to prune the cp before we simplify, since
		 simplification may expand the after set for the whole
		 term *)
	      pr_rl dbgm dbgm nr "Testing";
	      if (if !prune_cps_with_after then
		    (dbgp "Trying to prune: ";
		     print_rule dbgp nr;
		     if (can_prune_term_with_after dbgp after None x) then
		       (dbgp "The lhs violates the after constraints.\n";
			true)
		     else if (can_prune_term_with_after dbgp after None y) then
		       (dbgp "The rhs violates the after constraints.\n";
			true)
		     else 
		       disjoint_before_after dbgp after x y)
		  else
		    false)
	      then
		(pr_rl dbgu dbgd nr "Pruned";
		 rcs)
	      else
		(* try to simplify the rule away.  If that is not
		   possible, try to orient the rule.  *)
		(match simplify_rule nr with 
		     None -> rcs
		   | Some(nr) -> 
		       match orient_rule nr with
			   None -> 
			     handle_unorientable nr rcs
			 | Some(nr) ->
			     if not (rules_compatible r1 r2) then
			       (print_string "An overlap was found between a lexical and a syntactic rule (this is not allowed):\n  ";
				print_rule print_string r1;
				print_string "\n  ";
				print_rule print_string r2;
				print_string "\n";
				exit 1);
			     
			     (add_rl nr)::rcs)
  in 
  let the_cps = (cps symmap headmap new_rules) in
    dbg "(Computed ";
    dbg (string_of_int (List.length the_cps));
    dbg " critical pairs.)\n";
  let uniq_cps = uniq compare_cps the_cps in
    dbg "(Of the computed critical pairs, ";
    dbg (string_of_int (List.length uniq_cps));
    dbg " are unique.)\n";
    uniq compare_rules (rules_from_cps uniq_cps)
;;

(* we generate all cps where at least one rule is in new_rules.
   prev_rules are the rules indexed by symmap. 

   after and grammarsyms are from the grammar.
*)
let rec add_rules (after:string_relation) 
    (symmap:rule list trie) (headmap:rule list trie) 
    (prev_rules:rule list) (new_rules:rule list) : trs =
  let dbg = debugger dbg_completion in
    dbg "--------------------------\n";
    dbg "Starting a round of completion with these new rules:";
    List.iter (fun r -> dbg "\n  "; print_rule dbg r) new_rules;
    dbg "\n";
    (*dbg "And this symmap:\n";
    print_symmap dbg symmap; *)
    let new_rules2 = gen_rules after symmap headmap prev_rules new_rules   in
      if nonempty new_rules2 then
	(update_symmap symmap new_rules2;
	 (* we don't update the headmap here, because we update it where
	    we do rewriting, in gen_rules *)
	 add_rules after symmap headmap (prev_rules @ new_rules2) new_rules2  )
      else
	Trs(prev_rules)
;;

(* 
   The rule list trie returned is a headmap
 *)

let complete (after:string_relation) (Trs(rs)) : (trs * (rule list trie)) =
  let dbg = debugger dbg_completion in
    dbg "(Beginning completion.\n\n";
    let symmap = trie_new() in
    let headmap = trie_new() in

      dbg_rules := !dbg_rules || !dbg_cps;
      
      update_symmap symmap rs;
      update_headmap headmap rs;
      
      if !dbg_cps_micro then
	(print_string "The symmap is:\n(";
	 print_symmap print_string symmap;
	 print_string ")\n\nThe headmap is:\n(";
	 print_symmap print_string headmap;
	 print_string ")\n");
      
      let ret = (add_rules after symmap headmap rs rs, headmap) in
	dbg "Completion ends.)\n";
	ret
;;
