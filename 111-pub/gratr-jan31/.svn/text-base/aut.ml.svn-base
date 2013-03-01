open Term;;
open Trs;;
open Grammar;;
open Trie;;
open Util;;
open Parsing_trs;;

let dbg_construct_aut = ref false;;
let dbg_construct_aut_micro = ref false;;
let dbg_rewrite_aut = ref false;;
let dbg_determinization = ref false;;
let dbg_determinization_micro = ref false;;
let dbg_minimization = ref false;;

(* this definition is to accommodate the subset construction *)
type state_t = int;;

type startState = StartState of state_t;;
type finalStates = FinalStates of bool array;;
type allStates = AllStates of state_t list;;

(* map strings s (nonterminals or terminals) to lists of next states. *)
type edgemap = state_t list trie;;

(* transition relation. 

   The list of states is for epsilon transitions. *)
type transrel = (edgemap * (state_t list)) option array;;

(* The two transrel's are for forward (1st component) and reverse transition relations *)
type aut = startState * finalStates * allStates * (transrel * transrel);;

(* the string list array is the set of items for each state, and
   the prule list array is the set of prules for each state *)
type rtn_aut = (string list array) * (prule list array) * aut;;

let print_int_as_item (os:string -> unit) (im:string option array) (i:int) : unit = 
  match im.(i) with
      None -> ()
    | Some(itm) -> os (string_of_int i); os " : "; os itm
;;

let get_states (au:aut) : state_t list =
  let (_,_,AllStates(states),_) = au in
    states
;;

let edge_labels (trans:transrel) (s:state_t) : string list =
  match trans.(s) with
      None -> []
    | Some(emap,_) ->
	trie_strings emap
;;

let get_next_states (trans:transrel) (s:state_t) (e:string) : state_t list =
  match trans.(s) with
      None -> []
    | Some(emap,_) ->
	match trie_lookup emap e with
	    None -> [] 
	  | Some(li) -> li
;;

(* should be of the form [N] @ (List.rev ss) @ ["."] @ ss' *)
type item = (string list);;
let new_item (nt:string) (prev:string list) (next:string list) = 
  nt::"->"::((List.rev prev) @ ("."::next));;
let print_item (os:string -> unit) (i:item) = os "["; print_strings os " " i; os "]";;
let string_of_item (i:item) : string =
  let m = ref "" in
    print_item (fun s -> m:=!m^s) i;
    !m;;

let print_item_map (os:string -> unit) (im:string list array) : unit =
  let iend = (Array.length im) - 1 in
  for i = 0 to iend do
    if nonempty im.(i) then
      (os (string_of_int i);
       os " :(\n";
       print_strings os "\n" im.(i);
       os ")\n");
  done;;

let print_state (os:string -> unit) (s:state_t) : unit = os (string_of_int s);;

let add_edge_one_way (trans:transrel) (s:state_t) (e:string) (s':state_t) : unit = 
  let emap = (match trans.(s) with
		  None -> 
		    let emap = trie_new() in
		      trans.(s) <- Some(emap,[]);
		      emap
		| Some(emap,_) -> emap) in
  let li = (match trie_lookup emap e with
		None -> []
	      | Some(li) -> li) in
  let rec insert (s:state_t)(l:state_t list) : state_t list =
    match l with
	[] -> [s]
      | s'::l' ->
	  if s = s' then
	    l
	  else if s < s' then
	    s::l
	  else
	    s'::(insert s l')
  in
    trie_insert emap e (insert s' li);
;;

(* we will not add edges twice *)
let add_edge_c (trans:transrel) (trans_rev:transrel)
    (s:state_t) (e:string) (s':state_t) : unit = 
  add_edge_one_way trans s e s';
  add_edge_one_way trans_rev s' e s;
;;
let add_edge (trans:transrel) (trans_rev:transrel) (s:state_t) (e:string) (s':state_t) = 
  add_edge_c trans trans_rev s e s'
;;

let add_eps_edge_one_way (trans:transrel) (s:state_t) (s':state_t) : unit = 
  let (emap,eps) = (match trans.(s) with
			None -> 
			  let emap = trie_new() in
			    (emap,[])
		      | Some(emap,eps) -> (emap,eps)) in
    trans.(s) <- Some(emap,s'::eps)
;;

(* we do not check to see if there is already an epsilon edge from s to s' *)
let add_eps_edge (trans:transrel) (trans_rev:transrel) (s:state_t) (s':state_t) = 
  if s <> s' then
    (add_eps_edge_one_way trans s s';
     add_eps_edge_one_way trans_rev s' s);
;;

let print_aut (os:string -> unit) (os_state : state_t -> unit) (au : aut) : unit =
  let (StartState(start),FinalStates(finals),AllStates(states),(trans,trans_rel)) = au in
    os "(Automaton\n";
    os "(Start state: ";
    os_state start;
    os ")\n";
    os "(Final states:";
    List.iter (fun s -> os " "; os_state s) (bool_array_domain finals);
    os ")\n";
    os "(Number of states ";
    os (string_of_int (List.length states));
    os ")\n(Transitions:\n";
    List.iter 
      (fun s ->
	 match trans.(s) with
	     None -> () (* should not happen *)
	   | Some(emap,eps) ->
	       List.iter (fun s' -> os_state s; os " ----> "; os_state s'; os "\n") eps;
	       List.iter
		 (fun e ->
		    List.iter (fun s' ->
				 os_state s;
				 os " -- ";
				 os e;
				 os " --> ";
				 os_state s';
				 os "\n") (get_next_states trans s e))
		 (trie_strings emap))
      (opt_array_domain trans);
    os "))\n"
;;

let print_aut_dot (os:string -> unit) (state_label : int -> string) (name:string) (au : aut) : unit =
  let os_state s = os "s"; os (string_of_int s) in
  let os_state_decl s = os_state s; os " [label = \""; os (state_label s); os "\"];\n" in
  let (StartState(start),FinalStates(finals),AllStates(states),(trans,trans_rel)) = au in
    os "digraph ";
    os name;
    os " {\n";
    os "hidden [shape = plaintext, label = \"\"];\n";
    os "node [shape = doublecircle];\n";
    List.iter os_state_decl (bool_array_domain finals);
    os "node [shape = circle];\n";
    List.iter os_state_decl states;
    
    os "hidden -> ";
    os_state start;
    os "\n\n";
    List.iter 
      (fun s ->
	 match trans.(s) with
	     None -> () (* should not happen *)
	   | Some(emap,eps) ->
	       List.iter (fun s' -> os_state s; os " -> "; os_state s'; os ";\n") eps;
	       os "\n";
	       List.iter
		 (fun e ->
		    List.iter (fun s' ->
				 os_state s;
				 os " -> ";
				 os_state s';
				 os " [label = \"";
				 os (String.escaped e);
				 os "\"];\n")
		      (get_next_states trans s e))
		 (trie_strings emap))
      (opt_array_domain trans);
    os "}\n"
;;

let write_aut_dot (name:string) (state_label : int -> string) (au:aut) : unit =
  let o = open_out (name^".gv") in
  let os = output_string o in
    print_aut_dot os state_label name au;
    close_out o;;

let string_of_history (history:item list) : string = 
  "["^(String.concat " ; " (List.map (String.concat " ") (List.rev history)))^"]";;

let print_history (os:string -> unit) (history:item list) : unit =
  os (string_of_history history);;

(* This uses an algorithm from Cormen, Leiserson, and Rivest (CLR): do
   a depth-first search of the graph, recording vertices whenever
   exploration of their out-edges finishes; then do a second DFS on
   the inverse of the original graph, starting with the vertices that
   finished last in the first DFS search.  The resulting forest is
   proved in CLR to consist of SCCs. *)
let find_sccs (is_nt:string -> bool) (ptrs:parsing_trs) : string list list =
  (* edge(x,y) holds iff there is a production x -> ... y ..., with y a nonterminal, 
     represented in ptrs. *)

  (* compute the graph and its inverse *)
  let edge = trie_new() in
  let rev_edge = trie_new() in
    List.iter (fun (name,lhs,rhs,r) -> 
		 let lhs_nts = (List.filter is_nt (List.map snd lhs)) in
		   trie_append edge rhs lhs_nts;
		   List.iter (fun s -> trie_cons rev_edge s rhs) lhs_nts) ptrs;
    
    let mark = trie_new() in
    let finished = ref [] in

    let rec dfs (r:string list trie) (s:string) : unit =
      if not (trie_contains mark s) then
	(stringset_add mark s;
	 List.iter (dfs r) (list_trie_lookup r s);
	 finished := s::!finished)
    in

    let nodes = trie_strings edge in
      List.iter (dfs edge) nodes;
      let search_nodes = !finished in 
      let sccs = ref [] in
	trie_clear mark;
	List.iter 
	  (fun n ->
	     finished := [];
	     dfs rev_edge n;
	     if nonempty !finished then
	       sccs := !finished::!sccs)
	  search_nodes;

	!sccs
;;

(* we return (imap,au), where au is an automaton with some states
   labeled by prules to apply (in those states), and imap associates
   states with strings representing the history plus either nonterminals 
   or items (just for giving feedback to the user).
*)
let rec construct_rtn_aut (start:string) (ptrs:parsing_trs) : rtn_aut =
  let dbg = debugger dbg_construct_aut in 
  let dbgm = debugger dbg_construct_aut_micro in 

  (* build an index for ptrs *)
  let pmap = 
    let pmap = trie_new () in 
      List.iter (fun (name,lhs,rhs,r) -> trie_cons pmap rhs (name,lhs,r)) ptrs;
      pmap
  in

  let scc_nums =
    let sccs = find_sccs (trie_contains pmap) ptrs in
    let scc_nums = trie_new() in
    let next_scc = ref 0 in
      List.iter
	(fun scc -> 
	   let sccnum = !next_scc in
	     incr next_scc;
	     List.iter (fun s -> trie_insert scc_nums s sccnum) scc
	)
	sccs;
      scc_nums
  in
    
  (* precomputing the automaton.

     We will precompute the states and edges that need to be added,
     so that we do not have to overestimate the size of the
     automaton.

     About rev_im: im will be defined below to map states to strings
     representing the history and then either the nonterminal or the
     item.  rev_im does the reverse. *)
  let rev_im : state_t trie = trie_new() in
  let edges = ref [] in
  let eps_edges = ref [] in
  let labels = ref [] in

  let add_edge_deferred s nt s' =
    edges := (s,nt,s')::!edges
  in

  let add_eps_edge_deferred s s' =
    eps_edges := (s,s')::!eps_edges
  in

  let add_label_deferred l s =
    dbgm "(add_label_deferred (";
    Parsing_trs.print_prule dbgm l;
    dbgm ", ";
    dbgm (string_of_int s);
    dbgm "))\n";
    labels := (l,s)::!labels
  in

  let next_state = ref 0 in
  let nt_str (history:item list) (n:string list) : string = 
    string_of_history (n::history)
  in
  let state_exists (history:item list) (n:string list) : state_t option = 
    let n_str = nt_str history n in
      trie_lookup rev_im n_str
  in
    (* add a state if it does not exist *)
  let add_state (history:item list) (n:string list) : state_t = 
    match state_exists history n with
	None ->
	  let n_str = nt_str history n in
	  let s = !next_state in
	    incr next_state;
	    trie_insert rev_im n_str s;
	    s
      | Some(s) -> s
  in

  let nt_start (history:item list) (nt:string):state_t =
    add_state history [nt]
  in
  let nt_end (history:item list) (nt:string):state_t =
    add_state history [nt^"'end"]
  in

  let item_state (history : string list list) (i:item) : state_t = 
    add_state history i
  in

  (* return the start state for the given nonterminal *)
  let rec process_nt (history:item list) (nt:string) : state_t =
    dbg "(process_nt begins with history = ";
    print_history dbgm history;
    dbg ", nonterminal = ";
    dbg nt;
    dbg "\n";
    let oscc_nt = trie_lookup scc_nums nt in
    let ret = 
      match state_exists history [nt] with
	  None ->
	    let sides = (match trie_lookup pmap nt with None -> [] | Some(ss) -> ss) in
	    let s = nt_start history nt in
	    let s' = nt_end history nt in

	      (* add an edge labeled by the nonterminal from s to s' *)
	      if not !Grammar.approx_lang_only then
		(dbgm "(Adding edge ";
		 print_state dbgm s;
		 dbgm " -- ";
		 dbgm nt;
		 dbgm " --> ";
		 print_state dbgm s';
		 dbgm ")\n";
		 add_edge_deferred s nt s');

		(* now add edges for items *)
		List.iter 
		  (fun (name,lhs,r) ->
		     (* return a pair of the states corresponding to the items 
			with the dot before next, and the dot at the end of next. *)
		     let rec items prev_state prev next =
		       let i = new_item nt prev (List.map snd next) in
			 dbgm "(items with nt = ";
			 dbgm nt;
			 dbgm ", prev_state = ";
			 print_state dbgm prev_state;
			 dbgm ", current item = ";
			 print_item dbgm i;
			 dbgm "\n";
			 let ret = 
			   match next with
			       [] -> prev_state
			     | (tp,sym)::next' ->
				 let next_st = 
				   if trie_contains pmap sym then
				     (* this is a nonterminal *)
				     let history' = 
				       match oscc_nt, trie_lookup scc_nums sym with
					   Some(j), Some(k) -> 
					     if j = k then
					       history
					     else
					       (i::history)
					 | _,_ -> err "Internal error in items."
				     in
				     let sn = process_nt history' sym in
				     let sn' = nt_end history' sym in
				       dbgm "(Adding glue edge for invocation of nonterminal:\n";
				       print_state dbgm prev_state;
				       dbgm " ----> ";
				       print_state dbgm sn;
				       dbgm ")\n";
				       add_eps_edge_deferred prev_state sn;
				       sn'
				   else
				     let next_i = new_item nt (sym::prev) (List.map snd next') in
				     let next_st = item_state history next_i in
				       dbgm "(Adding glue edge for terminal:\n";
				       print_state dbgm prev_state;
				       dbgm " -- ";
				       dbgm sym;
				       dbgm " --> ";
				       print_state dbgm next_st;
				       dbgm ")\n";
				       add_edge_deferred prev_state sym next_st;
				       next_st
				 in
				   items next_st (sym::prev) next'
			 in
			   dbgm "items returning)\n";
			   ret
		     in
		       add_label_deferred (name,lhs,nt,r) s;
		       let is' = items s [] lhs in
			 add_eps_edge_deferred is' s')
		  sides;
		s
	  | Some(s) -> dbgm "(cache hit "; dbgm nt; dbgm ")\n"; s
      in
	dbgm "process_nt ends with ";
	print_state dbgm ret;
	dbgm ")\n";
	ret
    in

      let start_state = process_nt [] start in
      let numstates = !next_state in
      let im : string list array = Array.make numstates [] in
      let finals = Array.make numstates false in
      let trans = Array.make numstates None in
      let trans_rev = Array.make numstates None in
      let prlab = Array.make numstates [] in
      let rec enumerate cur bnd =
	if cur >= bnd then []
	else cur :: (enumerate (cur+1) bnd)
      in
      let states = enumerate 0 numstates in
	
	dbgm "(Deferred creation of the automaton finishes.  Now processing the instructions to build the actual automaton.)\n";

	(* now process all the accumulated information *)

	(* trans and trans_rev *)
	List.iter (fun (s,nt,s') -> add_edge trans trans_rev s nt s') !edges;
	List.iter (fun (s,s') -> add_eps_edge trans trans_rev s s') !eps_edges;

	dbgm "(Constructed the transition relation.)\n";

	(* prlab *)
	List.iter (fun (l,s) -> prlab.(s) <- l::prlab.(s)) !labels;
        (* uniquify, because we can get multiple labels *)
	List.iter (fun i -> prlab.(i) <- uniq compare prlab.(i)) (list_array_domain prlab);

	dbgm "(Computed the rule labeling.)\n";

	(* im *)
	List.iter (fun str -> 
		     match trie_lookup rev_im str with
			 None -> err "Internal error in construct_rtn_aut." (* should not happen *)
		       | Some(s) -> im.(s) <- [str])
	  (trie_strings rev_im);
	
	dbgm "(Computed the item labeling.)\n";

	let start' = nt_end [] start in
	  
	  dbgm "\n";
	  
	  finals.(start') <- true;
	  let au = (StartState(start_state), FinalStates(finals), AllStates(states), (trans,trans_rev)) in
	    (im, prlab,au)
;;

let aut_num_states (au:aut) : int = 
  let (_,FinalStates(finals), _, _) = au in
    Array.length finals 
;;

(* we assume rau has a unique final state *)
let reverse (rau:rtn_aut) : rtn_aut =
  let (im,prlab,au) = rau in
  let (StartState(start_state), FinalStates(finals), AllStates(states), (trans,trans_rev)) = au in
  let numstates = aut_num_states au in
  let finals' = Array.make numstates false in
    finals'.(start_state) <- true;
    (im,prlab,(StartState(singleton_expected (bool_array_domain finals)), FinalStates(finals'), AllStates(states), (trans_rev,trans)))
;;

let canonize_prlab_im states prlab im =
  (* canonize the lists in im and prlab *)
  List.iter (fun d -> 
	       prlab.(d) <- uniq compare prlab.(d);
	       im.(d) <- uniq compare im.(d))
    states;;

let determinize_aut (rau:rtn_aut) : rtn_aut * (int inttrie) =
  let (im,prlab,au) = rau in
  let dbg = debugger dbg_determinization in
  let dbgm = debugger dbg_determinization_micro in
  let (StartState(start_state), FinalStates(finals), AllStates(states), (trans,trans_rev)) = au in
  let bound = aut_num_states au in

  let edges = ref [] in
  let add_edge_deferred s nt s' =
    edges := (s,nt,s')::!edges
  in

    (* take a list of NFA states and turn it into a DFA state,
       setting finals' as we go *)
  let eps_closure_cache : state_t list option array = Array.make bound None in
  let mark : bool array = Array.make bound false in
  let eps_closure (s:state_t list) : state_t list =
    let rec helper (s:int) : state_t list =
      let ret = 
	dbgm "(helper  ";
	dbgm (string_of_int s);
	dbgm "\n";
	if mark.(s) then
	  (* we already saw this state in our current set of recursive calls to helper *)
	  []
	else
	  (mark.(s) <- true;
	   match trans.(s) with
	       None -> [s]
	     | Some(_,eps) ->
		 let e = s::(List.concat (List.map helper eps)) in
		   uniq compare e)
      in
	dbgm "returning \n";
	print_ints dbgm " " ret;
	dbgm ")\n";
	ret
    in
      (* we are processing each NFA state in s *)
      dbgm "(eps_closure ";
      print_ints dbgm " " s;
      dbgm "\n";
      (* first check our cache for the state s0, then
	 call helper if we have a cache miss *)
      let helper_if (s0:state_t) =
	match eps_closure_cache.(s0) with
	    Some(ue) ->
	      dbgm "(cache hit)\n";
	      ue
	  | None -> 
	      let ue = helper s0 in

		(* clear our marks *)
		List.iter (fun s0 -> mark.(s0) <- false) ue;

		eps_closure_cache.(s0) <- Some(ue);
		ue
      in
      let ret =
	uniq compare (List.concat (List.map helper_if s))
      in
	dbgm "returning ";
	print_ints dbgm " " ret;
	dbgm ")\n";
	ret
  in
  let start_state' = eps_closure [start_state] in
  let next_st = ref 0 in

  (* fill out trans' and trans_rev' by exploring depth-first from the given DFA state. *)
  let st_map = inttrie_new bound in
  let rec dfa_state (s:state_t list) : int =
    dbg "(dfa_state";
    List.iter (fun s -> dbg " "; dbg (string_of_int s)) s;
    dbg "\n";
    let ret = 
      match inttrie_lookup st_map s with
	  None ->
	    let d = !next_st in
	      inttrie_insert st_map s d;
	      incr next_st;
	      (* get all the edge labels for edges leaving s *)
	      let es = uniq compare (List.concat (List.map (fun x -> edge_labels trans x) s)) in
		dbg "(out-edges: ";
		print_strings dbg " " es;
		dbg ")\n";
		List.iter
		  (fun e ->
		     (* for each edge label leaving s, form s' as the set of
			new states reachable from s.  *)
		     let s' = List.concat (List.map (fun x -> get_next_states trans x e) s) in
		       if empty s' then
			 err "Internal error2 in determinize_aut";
		       let s' = eps_closure s' in
		       let d' = dfa_state s' in
			 add_edge_deferred d e d'
		  ) es;
		d
	| Some(d) -> d
    in
      dbg "dfa_state returning ";
      dbg (string_of_int ret);
      dbg ")\n";
      ret
  in
    
    dbg "(Determinization begins\n";
    let start_state' = dfa_state start_state' in
      dbg "determinization ends.)\n";


      (* now build the new automaton *)
      
      (* bound is the number of states *)
      let state_sets = inttrie_domain st_map in
      let bound = List.length state_sets in
      let finals' = Array.make bound false in
      let trans' = Array.make bound None in
      let trans_rev' = Array.make bound None in
      let im' = Array.make bound [] in
      let prlab' = Array.make bound [] in
      let states' = List.map dfa_state state_sets in

	(* set finals', im', and prlab' *)
	List.iter (fun st -> 
		     let d = dfa_state st in
		       List.iter
			 (fun s -> 
			    if finals.(s) then
			      finals'.(d) <- true;
			    im'.(d) <- im.(s) @ im'.(d);
			    prlab'.(d) <- prlab.(s) @ prlab'.(d))
			 st)
	  state_sets;
	
	canonize_prlab_im states' prlab' im';

	(* set trans' and trans_rev' *)
	List.iter (fun (d,nt,d') -> add_edge trans' trans_rev' d nt d') !edges;
	
	((im',prlab',(StartState(start_state'), FinalStates(finals'), AllStates(states'), (trans',trans_rev'))),
	 st_map)
;;

(* return a mapping from old states to new states, as well as the new automaton *)
let minimize_aut (rau:rtn_aut) : rtn_aut * (int inttrie) =
  let dbg = debugger dbg_minimization in
  let dbg_state (s:state_t) : unit =
    dbg (string_of_int s) 
  in
  let (im,prlab,au) = rau in
  let (StartState(start_state), FinalStates(finals), AllStates(states), (trans,trans_rev)) = au in
  let bound = aut_num_states au in
    (* diff will map states to inttries of states which are known to be different *)
  let diff = Array.make bound None in
  let finals_l = bool_array_domain finals in
    
  (* a list of all the nonfinal states *)
  let nonfinals = 
    let nonfinals = Array.make bound false in
      (* add all states which are not final to nonfinals *)
      List.iter (fun s -> nonfinals.(s) <- (not finals.(s))) states;
      bool_array_domain nonfinals
  in
    dbg "(non-final states are:";
    List.iter (fun s -> dbg "\n"; dbg_state s) nonfinals;
    dbg "\n)\n";

    let get_diff_trie x = 
      match diff.(x) with
	  None -> 
	    let t = Array.make bound false in
	      diff.(x) <- Some(t);
	      t
	| Some(u) -> u
    in

    (* return true iff we added a pair to the table *)
  let set_diff (x:state_t) (y:state_t) : bool =
    let dx = get_diff_trie x in
      if dx.(y) then
	(* we must have already added this pair *)
	false
      else 
	(dbg "(set_diff ";
	 dbg_state x;
	 dbg " ";
	 dbg_state y;
	 dbg ")\n";
	 dx.(y) <- true;
	 (get_diff_trie y).(x) <- true;
	 true)
  in
  let set_diff_r s s' = 
    let _ = set_diff s s' in () 
  in
  let dbg_states (ss:state_t list) : unit =
    List.iter (fun s -> dbg " "; dbg_state s) ss
  in

    (* finals are different from nonfinals *)
    List.iter
      (fun s -> 
	 List.iter (set_diff_r s) nonfinals
      )
      finals_l;

    (* states which have different sets of out-edges are different. *)
    List.iter
      (fun st ->
	 List.iter
	   (fun st' ->
	      if st <> st' then
		(let es = List.sort compare (edge_labels trans st) in
		 let es' = List.sort compare (edge_labels trans st') in
		   dbg "(Out-edges from ";
		   dbg_state st;
		   dbg ":\n  ";
		   print_strings dbg " " es;
		   dbg "\nOut-edges from ";
		   dbg_state st';
		   dbg ":\n  ";
		   print_strings dbg " " es';
		   dbg ")\n";
		   if es <> es' then
		     set_diff_r st st'))
	   states)
      states;
	 

    let rec repeat() = 
      let mark = Array.make bound false in
      let added = ref false in
      let rec rev_traverse (s:state_t) : unit =
	dbg "(rev_traverse ";
	dbg_state s;
	dbg "\n";
	if not mark.(s) then
	  (mark.(s) <- true;
	   match diff.(s) with
	       None -> ()
	     | Some(u) ->
		 (* for each state s' which we know is inequivalent to s,
		    traverse backwards in the automaton and mark states as
		    inequivalent *)
		 List.iter
		   (fun s' ->
		      let es = edge_labels trans_rev s in
			List.iter
			  (fun e ->
			     (* get the predecessors of s and s' on edges labeled e *)
			     let ps = get_next_states trans_rev s e in
			     let ps' = get_next_states trans_rev s' e in
			     let pp = all_pairs ps ps' in
			     let predp s ps =
			       dbg "(predecessors of ";
			       dbg_state s;
			       dbg " on ";
			       dbg e;
			       dbg ": ";
			       dbg_states ps;
			       dbg ")\n"
			     in
			       predp s ps;
			       predp s' ps';
			       List.iter (fun (s,s') -> let b = set_diff s s' in added := b || !added) pp;
			       List.iter rev_traverse ps;
			       List.iter rev_traverse ps')
			  es)
		   (bool_array_domain u));
	dbg ")\n";
      in
	List.iter rev_traverse finals_l;
	if !added then repeat()
    in
      
      repeat();
      dbg "(The diff trie (map states to different states):\n";
      (let iend = bound-1 in
	 for i = 0 to iend do
	   match diff.(i) with
	       None -> ()
	     | Some(u) ->
		 dbg_state i;
		 dbg " -> ";
		 print_ints dbg " " (bool_array_domain u);
		 dbg "\n"
	 done);
      dbg ")\n";


      (* now map each state to the quotient state, which combines all
	 the states which that state equals. *)
      
      dbg "(The quotient trie (map states to equivalent states):\n";
      let quot_map = inttrie_new bound in
      let next_quot_state = ref 0 in
      let map_quot_state (s:state_t list) =
	match inttrie_lookup quot_map s with
	    None ->
	      let q = !next_quot_state in
		inttrie_insert quot_map s q;
		incr next_quot_state;
		q
	  | Some(q) -> q
      in
      let quot = Array.make bound [] in
	List.iter 
	  (fun st ->
	     let d = get_diff_trie st in
	     let same = List.filter (fun s -> not d.(s)) states in
	     let same = uniq compare same in
	     let d = map_quot_state same in 
	       dbg_state st;
	       dbg " -> ";
	       dbg (string_of_int d);
	       dbg "[";
	       print_ints dbg " " same;
	       dbg "]\n";
	       quot.(st) <- same
	  )
	  states;
	dbg ")\n";

	let finals' = Array.make bound false in
	let states' = ref [] in
	let trans' = Array.make bound None in
	let trans_rev' = Array.make bound None in
	let im' = Array.make bound [] in
	let prlab' = Array.make bound [] in
	
	let mark = Array.make bound false in
	  (* return the state_t for the quotient state of s in the
	     new automaton. *)
	let get_quot (s:state_t) : state_t = map_quot_state quot.(s) in
	let rec explore (s:state_t) : unit =
	  if not mark.(s) then
	    let q = get_quot s in
	      mark.(s) <- true;
	      states' := q::!states';
	      if finals.(s) then
		finals'.(q) <- true;
	      im'.(q) <- im.(s) @ im'.(q);
	      prlab'.(q) <- prlab.(s) @ prlab'.(q);
	      List.iter
		(fun e ->
		   match get_next_states trans s e with
		       [s'] ->
			 let q' = get_quot s' in
			   add_edge trans' trans_rev' q e q'
		     | _ -> err "Internal error: a deterministic automaton has multiple out-edges from a state.")
		(edge_labels trans s)
	in

	  List.iter explore states;

	  canonize_prlab_im !states' prlab' im';

	  ((im',prlab',(StartState(get_quot start_state),FinalStates(finals'),AllStates(uniq compare !states'), (trans',trans_rev'))),
	   quot_map)
;;


