open Aut;;
open Trie;;
open Util;;
open Term;;
open Trs;;
open Grammar;;
open Parsing_trs;;
open Rewriting;;

let dbg_run_rewriting = ref false;;

type 'a run = StateDot of state_t * 'a (* val *) * 'a run | End of bool (* accepting *) * state_t | NoTransition of state_t * string list;;

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
	if accepting then
	  os " (accepting)"
	else
	  os " (not accepting)"
    | NoTransition(s,ss) ->
	os (string_of_int s);
	os " ";
	os "[no transition: ";
	print_strings os " " ss;
	os "]"
;;

(* we assume there is an End in r. *)
let rec get_last_state (r:'a run) : state_t =
  match r with
      StateDot(_,_,r') -> get_last_state r'
    | End(_,s) -> s
    | NoTransition(_,_) -> err "Internal error in get_last_state.";;

(* the function f should compute the val field of StateDots in the run we produce. The list ss 
   gives the edges we should follow in trans, as well as some extra data to give to f. 
*)
let rec get_run (dbg:string -> unit) (dbg_a:'a -> unit) 
    (st:state_t) (trans:transrel) (finals:bool array) (f:state_t -> string -> 'b -> 'a)
    (ss:('b * string) list)  : 'a run =
    dbg "(get_run with state = ";
    dbg (string_of_int st);
    dbg ", outgoing edges with labels ";
    print_strings dbg " " (edge_labels trans st);
    dbg "\n";
    let ret = 
      match ss with
	  [] -> End(finals.(st),st)
	| (b,e)::ss' ->
	    dbg "(next string is ";
	    dbg e;
	    dbg ")\n";
	    let sts = get_next_states trans st e in
	      if empty sts then
		NoTransition(st,List.map snd ss)
	      else
		match sts with
		    [st'] -> StateDot(st,f st e b,get_run dbg dbg_a st' trans finals f ss')
		  | _ -> 
		      (print_string "Internal error in get_run: encountered multiple out-edges labeled ";
		       print_string e;
		       print_string ".\n";
		       print_string "The state with the multiple out-edges is ";
		       print_string (string_of_int st);
		       print_string "\n";
		       exit 1)
    in
      dbg "returning ";
      print_run dbg dbg_a ret;
      dbg ")\n";
      ret
;;
  
(* convert the sequence of characters in i to a list of strings. *)
let rec stringlist_from_file(i:in_channel) : string list =
  try
    let c = input_char i in
      (quote (Char.escaped c))::(stringlist_from_file i)
  with End_of_file -> [];;

let run_aut (au:aut) (i:in_channel) : term run =
  let dbg = debugger dbg_run_rewriting in
  let ss = List.map (fun x -> ((),x)) (stringlist_from_file i) in
  let (StartState(start),FinalStates(finals),_,(trans,_)) = au in
    get_run dbg (print_term dbg) start trans finals (fun st e () -> const e) ss
;;

type lside = LsideNext of state_t * string * ast_type * lside | LsideEnd of state_t | LsideEndLook of state_t * string;;
type rside = Rside of state_t * string * role * state_t * string option (* optional lookahead *);;

(* (name,lhs,rhs, r) is like Trs.prule, but incorporating states.  For
   some state s, lhs and rhs must both end in LsideEnd(s), or else
   both end in LsideEndLook. *)
type rrule = string * lside * rside;;

let rec print_lside (os : string -> unit) (os_edge_val : string -> 'a -> unit) (os_lookahead:string -> unit) (r: lside) : unit =
  match r with
      LsideNext(st,e,v,r') ->
	os (string_of_int st);
	os " ";
	os_edge_val e v;
	os " ";
	print_lside os os_edge_val os_lookahead r'
    | LsideEnd(st) ->
	os (string_of_int st)
    | LsideEndLook(st,e) ->
	os (string_of_int st);
	os " ";
	os_lookahead e;;

let print_rrule (os:string -> unit) (u:rrule) : unit = 
  let (name,lhs,rhs) = u in
  let os_lookahead x = os "#"; os x in
    os name;
    os " : ";
    print_lside os (fun e tp -> print_prule_sym os tp e) os_lookahead lhs;
    os " -> ";
    (match rhs with
	 Rside(st,e,r,st',olook) ->
	   os (string_of_int st);
	   os " ";
	   (match r with Reading -> ()
	      | _ -> os "#");
	   os e;
	   os " ";
	   os (string_of_int st');
	   (match olook with
		None -> ()
	      | Some(l) -> os " #"; os l));
    os "\n";;

(* get the rrules corresponding to using the given prule in the given
   state.  We are assuming this will succeed. *)
let get_rrule (au:aut) (st:state_t) (p:prule) : rrule list = 
  let dbg = debugger dbg_run_rewriting in
  let (_,FinalStates(finals),_,(trans,_)) = au in
  let (name,lhs,rhs,r) = p in
  let lhs' = get_run dbg (fun (e,tp) -> print_prule_sym dbg tp e) st trans finals (fun st e tp -> (e,tp)) lhs in
  let tmp = get_next_states trans st rhs in
    dbg "(get_rrule with st = ";
    dbg (string_of_int st);
    dbg ", ";
    print_prule dbg p;
    dbg ")\n";
  let rhs'_endstate = singleton_expected tmp in
  let lhs'_endstate = get_last_state lhs' in
  let get_common_edges s1 s2 : string list =
    let e1 = stringset_of_strings (edge_labels trans s1) in
    let e2 = stringset_of_strings (edge_labels trans s2) in
      trie_strings (stringset_intersect e1 e2)
  in
  let rec run_to_lside (r:(string * ast_type) run) (addlook:string option) : lside = 
    match r with
	StateDot(st,(e,tp),r') ->
	  LsideNext(st,e,tp,run_to_lside r' addlook)
      | End(b,st) -> 
	  (match addlook with
	       None -> LsideEnd(st)
	     | Some(e) -> LsideEndLook(st,e))
      | NoTransition(_,_) -> err "Internal error in run_to_lside."
  in
    
    if rhs'_endstate = lhs'_endstate then
      [(name, run_to_lside lhs' None, Rside(st,rhs,r,rhs'_endstate,None))]
    else
      List.map (fun e -> (name,run_to_lside lhs' (Some(e)), Rside(st,rhs,r,rhs'_endstate,Some(e))))
	(get_common_edges rhs'_endstate lhs'_endstate)
;;

let get_rrules (rau:rtn_aut) : rrule list =
  let (_,prlab,au) = rau in
    List.concat
      (List.map 
	 (fun i -> 
	    let rs = prlab.(i) in

	    (* first check that rules enabled in the same state do not have the same lhs. 
	       Later code assumes we have done this check.  

	       The check is done by first sorting by lhs string and then looking for consecutive 
	       rules with the same string. *)
	    let str = List.map snd in
	    let cmp_lhs = (fun (name,lhs,rhs,r) (name',lhs',rhs',r') -> compare (str lhs) (str lhs')) in
	    let rs = List.sort cmp_lhs rs in
	      List.concat (List.map (get_rrule au i) rs)) 
	 (list_array_domain prlab))
;;

(* convert a run-rewriting rule to a term-rewriting rule.

   reading_sym will be used to tell if we should expect an argument
   or not for lookahead symbols from the input.
*)
let convert_rrule (reading_sym:string -> bool) (u:rrule) : rule =
  let (name,lhs,rhs) = u in
  let args = ref [] in
  let next_var = ref 0 in
  let new_var () = 
    let ret = Var(!next_var) in
      incr next_var;
      ret
  in
  let ending = ref (Var(0),Var(0)) in
  let state_name st = string_of_int st in
  let rec helper (lhs:lside) : term =
    match lhs with
	LsideNext(st,e,tp,lhs') ->
	  let f = state_name st in
	    (match tp with
		 NotInAst ->
		   App(f,[const e;helper lhs'])
	       | SymOnly ->
		   let arg = const e in
		     args := arg::!args;
	      	     App(f,[arg ; helper lhs'])
	       | SubAst ->
		   let arg = new_var() in
		     args := arg::!args;
		     App(f,[App(e,[arg]); helper lhs'])) 
      | LsideEnd(st) ->
	  let t = new_var() in
	  let v = new_var() in
	    ending := (t,v);
	    App(state_name st, [t; v])
      | LsideEndLook(st,e) ->
	  let t = if reading_sym e then App(e,[new_var()]) else const e in
	  let v = new_var() in
	    ending := (t,v);
	    App(state_name st, [t; v])
  in
  let tlhs = helper lhs in
  let trhs = 
    match rhs with
	Rside(st,e,r,st',olook) ->
	  let rt = 
	    match r with
		Reading -> 
		  app1 e (App(name,List.rev !args))
	      | _ -> const e
	  in
	  let (t,v) = !ending in
	    App(state_name st, [rt;App(state_name st',[t;v])])
  in
    Rule((Some(name),!next_var),tlhs,trhs)
;;

let rec print_run_term (os:string -> unit) (t:term) : unit =
  (* we do not print top-level variables *)
  match strip_normal t with
      App(f,[arg1;arg2]) ->
	os f;
	(match strip_normal arg1 with
	     Var(_) -> ()
	   | _ -> os " "; print_term os arg1);
	(match strip_normal arg2 with
	     Var(_) -> ()
	   | _ -> os " "; print_run_term os arg2);
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
	       let ret = 
		 if nonempty ret then
		   ret
		 else
		   cps_same_lhs prs' in
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
	   
	   let rec first_cps prs =
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
			 if empty ret then
			   first_cps prs'
			 else
			   ret
	   in
	   let ret = first_cps prs in
	     dbg "done searching for overlaps between rules and proper suffixes of rules.)\n";
	     dbg "Analyzing run-rewriting rules for local confluence ends).\n";
	     ret)
;;
