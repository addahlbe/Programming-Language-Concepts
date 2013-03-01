open Aut;;
open Trie;;
open Util;;
open Term;;
open Trs;;
open Grammar;;
open Parsing_trs;;
open Rewriting;;

let dbg_run_rewriting = ref false;;
let dbg_run_rewriting_micro = ref false;;

type 'a run = StateDot of state_t * 'a (* val *) * 'a run | End of bool option (* accepting *) * state_t
	      | NoTransition of state_t * string list;;

let rec print_run (os:string -> unit) (os_val:'a -> unit) (r:'a run) : unit =
  match r with
      StateDot(s,x,r') ->
	os (string_of_int s);
	os " ";
	os_val x;
	os " ";
	print_run os os_val r'
    | End(accepting,s) ->
	os (string_of_int s);
	(match accepting with
	     None -> ()
	   | Some(accepting) ->
	       if accepting then
		 os " (accepting)"
	       else
		 os " (not accepting)")
    | NoTransition(s,ss) ->
	os (string_of_int s);
	os " ";
	os "[no transition: ";
	print_strings os " " ss;
	os "]"
;;

let rec stringlist_of_string_run (r:string run) : string list option =
  match r with
      StateDot(s,x,r') ->
	(match stringlist_of_string_run r' with
	     None -> None
	   | Some(ss) -> Some((string_of_int s)::x::ss))
    | End(accepting, s) ->
	Some([string_of_int s])
    | NoTransition(s,ss) ->
	None;;

(* we assume there is an End in r. *)
let rec get_last_state (r:'a run) : state_t =
  match r with
      StateDot(_,_,r') -> get_last_state r'
    | End(_,s) -> s
    | NoTransition(_,_) -> err "Internal error in get_last_state.";;

let get_first_state (r:'a run) : state_t =
  match r with
      StateDot(st,_,_) -> st
    | End(_,st) -> st
    | NoTransition(_,_) -> err "Internal error in get_first_state.";;

let rec run_aut (dbg:string -> unit) (st:state_t) (trans:transrel) (finals:bool array) (ss:string list)  : string run =
  dbg "(run_aut with state = ";
  dbg (string_of_int st);
  dbg ", outgoing edges with labels ";
  print_strings dbg " " (edge_labels trans st);
  dbg "\n";
  let ret = 
    match ss with
	[] -> End(Some(finals.(st)),st)
      | e::ss' ->
	  dbg "(Following edge with label ";
	  dbg e;
	  dbg ")\n";
	  let sts' = next_states trans st e in
	    if empty sts' then
	      (dbg "(empty set of next states)\n";
	       NoTransition(st,ss))
	    else
	      let r = run_aut dbg (singleton_expected sts') trans finals ss' in
		StateDot(st,e,r)
  in
    dbg "returning \n";
    print_run dbg dbg ret;
    dbg ")\n";
    ret
;;

let long_edge_to_string e back_st e' = e ^ " ; " ^ back_st ^ " ; " ^ e';;

(* We assume we are starting in a state st whose out-edges are labeled
   with grammar symbols, not backward-automaton states.

   The edge labels for the runs we find will alternate between grammar
   symbols and back-automaton states, starting and ending in symbols.

   def is the 'a we will use when our run follows an edge corresponding
   to a state in the reverse automaton.

   
*)
let rec alt_runs (dbg:string -> unit) (dbg_as:('a * string) -> unit) (st:state_t) (trans:transrel) 
    (ss:('a * string) list)  : ('a * string) run list =
  dbg "(alt_runs with state = ";
  dbg (string_of_int st);
  dbg ", outgoing edges with labels ";
  print_strings dbg " " (edge_labels trans st);
  dbg "\n";
  let ret = 
    match ss with
	[] -> [End(None,st)]
      | (b,e)::ss' ->
	  dbg "(Trying to follow a path for symbol ";
	  dbg e;
	  dbg "\n";
	  let sts' = next_states trans st e in
	  let ret = 
	    List.concat
	      (List.map
		 (fun st' ->
		    let es = edge_labels trans st' in
		      if empty ss' then
			(* we want to end with an edge labeled by a grammar symbol, not a back-automaton state *)
			[StateDot(st,(b,e),End(None,st'))]
		      else
			List.concat
			  (List.map 
			     (fun back_st ->
				dbg "(Following edge corresponding to back-automaton state ";
				dbg back_st;
				dbg ", from state ";
				dbg (string_of_int st');
				dbg ")\n";
				let st'' = next_state trans st' back_st in
				  List.map
				    (fun r -> StateDot(st,(b,e),StateDot(st',(NotInAst,back_st),r)))
				    (alt_runs dbg dbg_as st'' trans ss'))
			     es)
		 )
		 sts')
	  in
	    dbg ")\n";
	    ret
  in
    dbg "alt_runs returning (\n";
    List.iter (fun r -> print_run dbg dbg_as r; dbg "\n") ret;
    dbg "))\n";
    ret
;;

(* convert the sequence of characters in i to a list of strings. *)
let rec stringlist_from_file(i:in_channel) : string list =
  try
    let c = input_char i in
      (quote (Char.escaped c))::(stringlist_from_file i)
  with End_of_file -> 
    if !Grammar.no_eos then
      []
    else
      ["_eos"]
;;

let stringlist_from_file(i:in_channel) : string list =
  (if !Grammar.no_eos then
     []
   else
     ["_sos"])
  @ (stringlist_from_file i);;

let run_aut (au:aut) (ss:string list) : string run =
  let dbg = debugger dbg_run_rewriting in
  let (StartState(start),FinalStates(finals),_,(trans,_)) = au in
    run_aut dbg start trans finals ss 
;;

type lside = 
    LsideNext of state_t * ast_type * string * lside
  | LsideEnd of state_t * ((bool (* reading *) * string (* lookahead grammar-symbol *)) option);;
type rside = 
    Rside of
      state_t
      * string (* rhs nonterminal *)
      * state_t 
      * ((string (* back-aut state *) * state_t * bool (* reading *) * string) option)
      * (term option);;

type rrule = Rrule of lside * rside;;

let rec print_lside (os : string -> unit) (r: lside) : unit =
  match r with
      LsideNext(st,tp,e,r') ->
	os (string_of_int st);
	os " ";
	print_prule_sym os tp e;
	os " ";
	print_lside os r'
    | LsideEnd(st,o) ->
	os (string_of_int st);
	match o with
	    None -> ()
	  | Some(r,e) -> os " "; if not r then os "#"; os e
;;

(* oe is an optional following edge *)
let print_rrule (os:string -> unit) (u:rrule) : unit = 
  let os_state st = os (string_of_int st) in
  let Rrule(lhs,rhs) = u in
  let os_edge_state e st = 
    os " ";
    os e;
    os " ";
    os_state st
  in
    print_lside os lhs;
    os " -> ";
    (match rhs with
	 Rside(st,e,st',look,ot) ->
	   os_state st;
	   os " ";
	   os e;
	   (match ot with
		None -> ()
	      | Some(t) -> 
		  os "(";
		  print_term os t;
		  os ")");
	   os " ";
	   os_state st';
	   match look with
	       None -> ()
	     | Some(b,st'',r,e') ->
		 os_edge_state b st'';
		 os " "; 
		 if not r then os "#";
		 os e');
    os "\n";;

let rec run_to_lside (r:(ast_type * string) run) (back:string) (st':state_t) (reading:bool) (look:string) : lside = 
  match r with
      StateDot(st,(tp,e),r') -> LsideNext(st,tp,e,run_to_lside r' back st' reading look)
    | End(b,st) -> LsideNext(st,NotInAst,back,LsideEnd(st',Some(reading,look)))
    | NoTransition(_,_) -> err "Internal error in run_to_lside."
;;

(* get the rrules corresponding to using the given prule in the given
   state.  We are assuming this will succeed.  We are assuming au recognizes
   runs of another automaton, so its transitions alternate between state of
   that other automaton and symbols.  The transitions leaving st should be labeled
   with symbols (so the alternation is symbol-state-symbol-state-...). 
*)
let get_new_rrules (gname:string) (au:aut) (reading_sym:string -> bool) (added:bool ref) (st:state_t) (p:prule) : rrule list = 
  let dbg = debugger dbg_run_rewriting in
  let dbgm = debugger dbg_run_rewriting_micro in
  let (StartState(start_state),_,_,(trans,trans_rev)) = au in
  let (lhs,rhs,ot) = p in
    dbg "(get_new_rrules with st = ";
    dbg (string_of_int st);
    dbg ", ";
    print_prule dbg p;
    dbg "\n";

    let ret = 
      let dbglhs d = (fun (tp,e) -> print_prule_sym d tp e) in
      let lhs'_runs = alt_runs dbgm (dbglhs dbgm) st trans lhs in
	List.concat
	  (List.map
	     (fun r ->
		(* for each lhs run *)
		let startst = get_first_state r in
		let rhs_endst = 
		  get_last_state r in
		let pr_edge () =
		  dbg (string_of_int startst);
		  dbg " -- ";
		  dbg rhs;
		  dbg " --> ";
		  dbg (string_of_int rhs_endst);
		  dbg ")\n"
		in
		  if not (edge_exists trans startst rhs rhs_endst) then
		    (add_edge trans trans_rev startst rhs rhs_endst;
		     added := true;
		     dbg "(adding edge ";
		     pr_edge());
		  List.concat
		    (List.map
		       (fun back_st ->
			  let st' = next_state trans rhs_endst back_st in
			    List.map 
			      (fun e ->
				 let rd = reading_sym e in
				   if rd then
				     dbg "(reading sym: "
				   else
				     dbg "(not a reading sym: ";
				   dbg e;
				   dbg ")\n";
				   let rside = 
				     Rside(startst,rhs,rhs_endst,Some(back_st,st',rd,e),ot)
				   in
				     Rrule(run_to_lside r back_st st' rd e, rside))
			      (edge_labels trans st'))
		       (edge_labels trans rhs_endst))
	     )
	     lhs'_runs)
    in
      dbg "get_new_rrules returning:(\n";
      List.iter (print_rrule dbg) ret;
      dbg "))\n";
      ret
;;

(* the string for the name of a state *)
let state_name st = string_of_int st;;

(* convert a run-rewriting rule to a term-rewriting rule.
*)
let convert_rrule (u:rrule) : rule =
  let Rrule(lhs,rhs) = u in
  let ending = ref (Var(0),Var(0)) in
  let rec helper (prev_var:int) (lhs:lside) : term =
    match lhs with
	LsideNext(st,tp,e,lhs') ->
	  let f = state_name st in
	    (match tp with
		 NotInAst ->
		   App(f,[const e;helper prev_var lhs'])
	       | SymOnly ->
		   let arg = const e in
	      	     App(f,[arg ; helper prev_var lhs'])
	       | SubAst(i) ->
		   let arg = Var(i) in
		     App(f,[App(e,[arg]); helper i lhs'])) 
      | LsideEnd(st,o) ->
	  let t = 
	    match o with
		Some(r,e') -> if r then App(e',[Var(prev_var+1)]) else const e'
	      | None -> Var(prev_var+1)
	  in
	  let v = Var(prev_var+2) in
	    ending := (t,v);
	    App(state_name st, [t; v])
  in
  let tlhs = helper 0 lhs in
  let (t,v) = !ending in
  let max_var = match v with Var(i) -> i | _ -> err "Internal error in convert_rrule" in
  let trhs = 
    match rhs with
	Rside(st,e,st',look,ot) ->
	  App(state_name st,
	      [(match ot with
		    None -> const e
		  | Some(t) -> app1 e t);
	       App(state_name st',
		   match look with
		       None -> [t;v]
		     | Some(b,st'',_,_) -> [const b; App(state_name st'',[t;v])])])
  in
    Rule((None,max_var),tlhs,trhs)
;;

(* get run-rewriting rules as Trs.rules from an rtn_aut.  These
   rules include pull rules and rules corresponding to productions.

   reading_sym will be used to tell if we should expect an argument
   or not for symbols we encounter while trying to generate pull rules. *)
let get_rr_trs (gname:string) (start_symbol:string) (reading_sym:string -> bool) (rau:rtn_aut) : trs =
  let dbg = debugger dbg_run_rewriting in
  let (prlab,au) = rau in
  let (StartState(start_state),_,_,(trans,_)) = au in
  let added = ref false in
  let num_states = aut_num_states au in
  let rec helper () = 
    let rs = 
      List.concat
	(List.map 
	   (fun i -> 
	      List.concat (List.map (get_new_rrules gname au reading_sym added i) prlab.(i))
	   )
	   (list_array_domain prlab))
    in
      write_aut_dot (gname^"_rewr") string_of_int au;
      if !added then
	(added := false;
	 rs @ (helper()))
      else
	rs
  in
  let rs = uniq compare (helper()) in

  let get_le_trie tr st =
    match tr.(st) with
	None -> let t = trie_new() in tr.(st) <- Some(t); t
      | Some(t) -> t
  in

  (* construct an index mapping long edges for rhs's to the lhs's of the rrules *)
  let index = 
    let index = Array.make num_states None in
      List.iter
	(fun rr ->
	   let Rrule(lhs,Rside(st,e,st',look,ot)) = rr in
	     match look with
		 None -> (* should not happen, since we add all lookahead up front *) ()
	       | Some(b,_,_,e') ->
		   let le = long_edge_to_string e b e' in
		     trie_cons (get_le_trie index st) le lhs)
	rs;
      index
  in

  (* with the help of index, construct a data structure called
     'relevant', telling which long edges can contribute to reaching the
     start state *)
  let relevant = 
    dbg "(Identifying relevant long edges.\n";
    let relevant = Array.make num_states None in
    let rec process_long_edge st e b e' =
      let rel = get_le_trie relevant st in
      let le = long_edge_to_string e b e' in
	dbg "(From state ";
	dbg (string_of_int st);
	dbg ", considering long edge ";
	dbg le;
	dbg ")\n";
	if (trie_contains rel le) then
	  dbg "(processed already)\n"
	else
	  (* we have not processed this long edge yet *)
	  (dbg "(not processed before)\n";
	   stringset_add rel le;

	   let i = get_le_trie index st in
	     match trie_lookup i le with
		 None -> () (* e should be a terminal in this case *)
	       | Some(lhss) ->
		   List.iter 
		     (fun lhs ->
			dbg "(Considering this lside of an rrule: ";
			print_lside dbg lhs;
			dbg ".\n";
			lside_add_relevant lhs;
			dbg ")\n")
		     lhss
	  )
    and lside_add_relevant (l:lside) =
      match l with
	  LsideNext(st,_,e,LsideNext(st',_,back_st,l')) ->
	    (match l' with
		 LsideNext(_,_,e',_) | LsideEnd(_,Some(_,e')) -> 
		   process_long_edge st e back_st e';
		   lside_add_relevant l'
	       | _ -> err "Internal error in lside_add_relevant.")
	| _ -> ()
    in
    let pr_edge e st' = 
      dbg " -- ";
      dbg e;
      dbg " -->\n";
      dbg (string_of_int st');
      dbg "\n";
    in
      List.iter
	(fun (_,st) ->
	   let st' = next_state trans st start_symbol in
	     dbg "(";
	     dbg (string_of_int st);
	     dbg "\n";
	     pr_edge start_symbol st';
	     List.iter
	       (fun back_st ->
		  let st'' = next_state trans st' back_st in
		    pr_edge back_st st'';
		    List.iter
		      (fun e ->

			 dbg e;
			 dbg "\n";
			 (* start_state
                            -- [don't care] --> 
                            st
                            -- start_symbol -->
                            st'
                            -- back_st -->
                            st''
                            -- e --> *)

			 process_long_edge st start_symbol back_st e)
		      (edge_labels trans st''))
	       (edge_labels trans st');
	     dbg ")\n")
	(all_next_states trans start_state);
      dbg "Relevant long edges identified).\n";
      relevant
  in

  let filtered_out = Array.make num_states [] in
  let rs = 
    dbg "(Filtering the generated run-rewriting rules based on use.\n";
    List.filter (fun rr -> 
		   let Rrule(lhs,Rside(st,e,st',look,ot)) = rr in
		   let ret =
		     match look with
			 None -> true
		       | Some(b,_,_,e') ->
			   if e = start_symbol then
			     true
			   else
			     match relevant.(st) with
				 None -> false
			       | Some(t) ->
				   trie_contains t (long_edge_to_string e b e')
		   in 
		     if ret then
		       dbg "Keeping run-rewriting rule: "
		     else
		       dbg "Filtering out run-rewriting rule: ";
		     print_rrule dbg rr;
		     if not ret then
		       filtered_out.(st) <- (e,st')::filtered_out.(st);
		     ret)
      rs in
  let drop_lookahead (rr:rrule) : rrule =
    let Rrule(lhs,rhs) = rr in
    let rec drop_lookahead_lside l =
      match l with
	  LsideNext(st,_,back,LsideEnd(st',_)) -> LsideEnd(st,None)
	| LsideNext(st,tp,e,l') -> LsideNext(st,tp,e,drop_lookahead_lside l')
	| LsideEnd(_,_) -> l (* should not happen *)
    in
    let lhs' = drop_lookahead_lside lhs in
    let rhs' = 
      match rhs with
	  Rside(st,e,st',_,ot) -> Rside(st,e,st',None,ot)
    in
      Rrule(lhs',rhs')
  in

  let rs = 
    (* make the list of filtered_out edge-state pairs unique *)
    List.iter (fun st -> filtered_out.(st) <- (uniq compare filtered_out.(st))) (list_array_domain filtered_out);
    List.map
      (fun rr -> 
	 let Rrule(lhs,Rside(st,e,st',_,_)) = rr in
	   if List.mem (e,st') filtered_out.(st) then
	     rr
	   else
	     drop_lookahead rr)
      rs in
  let rs = uniq compare rs in
  dbg ")\n";
    let rs = List.map convert_rrule rs in
      Trs(rs)
;;

(* we assume that NoTransition does not occur *)
let rec term_of_string_run (r:string run) : term =
  match r with
      StateDot(s,x,r') ->
	App(state_name s, [const x; term_of_string_run r'])
    | End(accepting, s) ->
	App(state_name s, [var 0; var 1])
    | NoTransition(s,ss) ->
	print_string "Internal error in term_of_string_run.";
	exit 1
;;

let rec print_run_term (os:string -> unit) (t:term) : unit =
  (* we do not print top-level variables *)
  match strip_normal t with
      App(f,[arg1;arg2]) ->
	os f;
	(match strip_normal arg1 with
	     Var(_) -> ()
	   | _ -> os " "; print_term_compact_lits os arg1);
	(match strip_normal arg2 with
	     Var(_) -> ()
	   | _ -> os " "; print_run_term os arg2);
    | App(f,[arg]) ->
	os f; os " "; print_run_term os arg
    | _ -> () 
;;

let print_run_red_seq (os:string -> unit) (ts:term list) : unit =
  os "(\n";
  List.iter (fun t -> os "  "; print_run_term os t; os "\n") ts;
  os ")\n";;

let print_run_rule (os:string -> unit) (r:rule) : unit = 
  let (Rule(_,lhs,rhs)) = r in
    print_run_term os lhs;
    os " -> ";
    print_run_term os rhs;
    os "\n";;

let print_run_trs (os:string -> unit) (t:trs) : unit = 
  let (Trs(rs)) = t in
    os "(The ";
    os (string_of_int (List.length rs));
    os " run-rewriting rules:\n";
    List.iter (print_run_rule os) rs;
    os ")\n";;

let print_run_cp (os:string -> unit) (c:Localconf.cp) =
  let (maxvar,x,y,peak,toplevel,r1,r2) = c in
    os "(We have two ways to rewrite the following partial run:\n  ";
    print_run_term os peak;
    os "\nWe could have this rewriting sequence\n";
    print_run_red_seq os x;
    os "or this one:\n";
    print_run_red_seq os y;
    os "\nThe overlapping rules are:\n";
    os "  ";
    print_run_rule os r1;
    os "  ";
    print_run_rule os r2;
    os ")\n";;

(* test confluence of prs, which is assumed to come from
   a set of rrules, modulo the first together with the second trs *)
let locally_confluent (Trs(prs)) (Trs(rs)) : Localconf.cp list =
  let index = trie_new() in
  let dbg = debugger Localconf.dbg_local_conf in
  let dbgm = debugger Localconf.dbg_local_conf_micro in
  let dbgc = debugger Localconf.dbg_cps in
  let rec list_suffixes2 (l:'a list) : 'a list list =
    match l with
	x::y::l' -> l::(list_suffixes2 l')
      | [] -> []
      | _ -> [l]
  in

    (* return prefixes in order from longest to shortest *)
  let list_prefixes2 (l:'a list) : 'a list list =
    List.map List.rev (list_suffixes2 (List.rev l))
  in
  let index_suffixes (r:rule) : unit =
    let (Rule(_,lhs,rhs)) = r in
    let lhs_strs = right_strs lhs in
    let ls = list_suffixes2 lhs_strs in
      (* modify the index to map each suffix, as a single string, to r *)
      List.iter (fun suf -> trie_cons index (String.concat " " suf) r) ls;
  in

  (* first check that no two rules have exactly the same lhs *)

  let prs = (List.sort (fun (Rule(_,lhs1,_)) (Rule(_,lhs2,_)) ->
			  if eq_term nodbg lhs1 lhs2 then 0
			  else compare lhs1 lhs2)
	       (List.map canonize_rule prs)) in
   
    (* index the rules we will use to rewrite critical pairs *)
    let rewritemap = Rewriting.compute_rewrite_map (prs @ rs) in

      dbg "(Analyzing run-rewriting rules for local confluence begins.\n";

      dbgm "(The rewrite map is:\n(";
      print_rewrite_map dbgm rewritemap;
      dbgm ")\n";

      dbg "(Indexing suffixes.\n";
      (* index all the rules which we are searching for critical pairs *)
      List.iter index_suffixes prs;
      dbg "done.\n";
      dbgm "The index is\n(\n";
      print_trie dbgm (List.iter (fun r -> print_rule dbgm r)) index;
      dbgm ")\n";
      dbg ")\n(Searching for overlaps between rules with the same lhs.\n";

      let rec split_into_eq prs =
	match prs with
	    [] -> ([],[])
	  | [r] -> ([r],[])
	  | r1::r2::prs' ->
	      let (Rule(_,lhs1,_)) = r1 in
	      let (Rule(_,lhs2,_)) = r2 in
		if eq_term nodbg lhs1 lhs2 then
		  let (h,l') = split_into_eq (r2::prs') in
		    ((r1::h),l')
		else
		  ([r1],(r2::prs'))
      in
	
      let rec cps_same_lhs prs =
	if empty prs then
	  []
	else
	  let (h,prs') = split_into_eq prs in
	    if singleton h then
	      cps_same_lhs prs'
	    else
	      (dbg "(Considering overlaps between the following rules with the same lhs:\n";
	       List.iter (print_rule dbg) h;
	       
	       let ret = List.concat (List.map (Localconf.cps_r dbgc rewritemap true) (all_pairs h h)) in
	       let ret = ret @ (cps_same_lhs prs') in
		 dbg ")\n";
		 ret)
      in

      let ret = cps_same_lhs prs in
	if nonempty ret then
	  ret
	else
	  (dbg "done searching for overlaps between rules with exactly the same lhs.)\n\n";
	   dbg "(Searching for overlaps between rules and proper suffixes of rules.\n";

	   (* check for critical pairs whenever there is overlap of
	      prefixes with suffixes (of run-rewriting rules) *)
	   
	   let rec suff_cps prs =
	     match prs with
		 [] -> []
	       | r::prs' ->
		   dbg "(Considering rule r=\n  ";
		   print_rule dbg r;
		   
		   (* for each rule, search the index for overlapping rules *)

		   let (Rule(_,lhs,_)) = r in

		   (* we take the tail to skip the entire string itself as a prefix *)
		   let pref = List.tl (list_prefixes2 (right_strs lhs)) in
		     
		     dbg "(Searching index for the prefixes of rule\n  ";
		     print_rule dbg r;
		     dbg "The prefixes are";
		     List.iter (fun s -> dbg "\n"; print_strings dbg " " s) pref;
		     dbg "\n)\n";
		     
		     let overlapping = List.concat (take_some (List.map (fun s -> trie_lookup index (String.concat " " s)) pref)) in
		       
		       dbg "\nThe rules found are:\n(\n";
		       List.iter (fun r -> dbg "  "; print_rule dbg r) overlapping;
		       dbg ")\n";
		       let ret = List.concat (List.map (fun r' -> Localconf.cps_r dbgc rewritemap false (r',r)) overlapping) in
			 dbg ")\n";

			 ret @ (suff_cps prs')
	   in
	   let ret = suff_cps prs in
	     dbg "done searching for overlaps between rules and proper suffixes of rules.)\n";
	     dbg "Analyzing run-rewriting rules for local confluence ends).\n";
	     ret)
;;
