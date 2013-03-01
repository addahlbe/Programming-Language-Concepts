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
let dbg_intermed_aut = ref true;;
let dbg_refine = ref false;;
let stop_before_determinization = ref false;;
let starting_stackdepth = ref 0;;
let crude_aut = ref false;;

let empty_nt = "empty";;

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

type prlab_t = prule list array;;

(* the string list array is the set of items for each state, and
   the prule list array is the set of prules for each state *)
type rtn_aut = prlab_t * aut;;

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

let edge_exists (trans:transrel) (s:state_t) (e:string) (s':state_t) : bool =
  match trans.(s) with
      None -> false
    | Some(emap,_) ->
	match trie_lookup emap e with
	    None -> false
	  | Some(sts) -> List.mem s' sts
;;

let next_states (trans:transrel) (s:state_t) (e:string) : state_t list =
  match trans.(s) with
      None -> []
    | Some(emap,_) ->
	match trie_lookup emap e with
	    None -> [] 
	  | Some(li) -> li
;;

let get_common_edges (trans:transrel) (s1:state_t) (s2:state_t) : string list =
  let e1 = stringset_of_strings (edge_labels trans s1) in
  let e2 = stringset_of_strings (edge_labels trans s2) in
    trie_strings (stringset_intersect e1 e2);;

(* return the list of pairs (e,s') such that there is an edge labeled e from s to s' *)
let all_next_states (trans:transrel) (s:state_t) : (string * state_t) list =
  List.concat 
    (List.map
       (fun e -> 
	  (* build pairs of edge and each next state *)
	  List.map (fun s -> (e,s)) (next_states trans s e))
       (edge_labels trans s));;

(* call only if you know there is exactly one next state following s on e *)
let next_state (trans:transrel) (s:state_t) (e:string) : state_t = singleton_expected (next_states trans s e);;

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

let add_edge (trans:transrel) (trans_rev:transrel) (s:state_t) (e:string) (s':state_t) : unit = 
  add_edge_one_way trans s e s';
  add_edge_one_way trans_rev s' e s;
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
				 os "\n") (next_states trans s e))
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
		      (next_states trans s e))
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
    List.iter (fun (lhs,rhs,ot) -> 
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

let change_top (history:item list) (i:item) : item list = 
  match history with
      [] -> [i]
    | i'::history' -> i::history'
;;

(* we return (imap,au), where au is an automaton with some states
   labeled by prules to apply (in those states), and imap associates
   states with strings representing the history plus either nonterminals 
   or items (just for giving feedback to the user).

*)
let construct_rtn_aut (start:string) (sentential:bool) (ptrs:parsing_trs) : (string list array) * rtn_aut =
  let dbg = debugger dbg_construct_aut in 
  let dbgm = debugger dbg_construct_aut_micro in 

  (* build an index for ptrs *)
  let pmap = 
    let pmap = trie_new () in 
      List.iter (fun (lhs,rhs,ot) -> trie_cons pmap rhs (lhs,ot)) ptrs;
      pmap
  in

  let (regular,scc_nums) =
    let generating (left:bool) (scc:string list) : bool =
      let scc_set = stringset_of_strings scc in
      let helper (lhs,ot) : bool = 
	match lhs with
	    [] -> false
	  | x::lhs' ->
	      let lhs' = 
		if left then
		  lhs'
		else
		  let (lhs',_) = split_list_last lhs in
		    lhs'
	      in
		List.exists (fun (_,s) -> trie_contains scc_set s) lhs'
      in
	(* look for a side of a rule with rhs in scc which satisfies the helper *)
	List.exists helper (List.concat (List.map (list_trie_lookup pmap) scc))
    in
    let sccs = find_sccs (trie_contains pmap) ptrs in
    let scc_nums = trie_new() in
    let regular = trie_new() in 
    let next_scc = ref 0 in
      dbg "(The SCCs of the grammar:\n";
      List.iter
	(fun scc -> 
	   let sccnum = !next_scc in
	     dbg "  ("; print_strings dbg " " scc; dbg "): ";
	     incr next_scc;
	     List.iter (fun s -> trie_insert scc_nums s sccnum) scc;
	     let leftgen = generating true scc in
	     let rightgen = generating false scc in
	     let p b s = 
	       dbg (if b then s else "not "^s);
	       dbg "Generating "
	     in
	       p leftgen "Left";
	       p rightgen "Right";
	       dbg "\n";
	       if not leftgen || not rightgen then
		 List.iter (stringset_add regular) scc;
	)
	sccs;
      dbg ")\n";
      (regular,scc_nums)
  in

    (* return -1 if we do not have an scc number -- this should only happen if sym is a terminal. *)
  let get_scc_num sym = 
    match trie_lookup scc_nums sym with None -> -1 | Some(i) -> i 
  in

  let is_regular sym =
    trie_contains regular sym
  in

  (* find nonterminals with a looping rule *)
  let _ = 
    let unit_rules = List.filter (fun (lhs,_,_) -> List.length lhs = 1) ptrs in
    let unit_index = trie_new() in
      List.iter (fun (lhs,rhs,_) -> trie_cons unit_index rhs (snd (List.hd lhs))) unit_rules ;
      let seen = trie_new() in
      let rec traverse_unit c n = 
	if trie_contains seen n then
	  let c = List.rev c in
	    print_string "The grammar contains cyclic unit productions:\n  ";
	    print_strings print_string " ->* " c;
	    print_string " ->* ";
	    print_string (List.hd c);
	    print_string "\nThis makes the grammar ambiguous.\n";
	    exit 1
	else
	  (stringset_add seen n;
	   List.iter (traverse_unit (n::c)) (list_trie_lookup unit_index n);
	   trie_remove seen n) 
      in
	List.iter (traverse_unit []) (trie_strings unit_index)
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

  let nextst = ref 0 in
  let nt_str (history:item list) (n:string list) : string = 
    string_of_history (n::history)
  in
  let state_exists (history:item list) (n:string list) : state_t option = 
    let n_str = nt_str history n in
    let ret = trie_lookup rev_im n_str in
      ret
  in
    (* add a state if it does not exist *)
  let add_state (history:item list) (n:string list) : state_t = 
    match state_exists history n with
	None ->
	  let n_str = nt_str history n in
	  let s = !nextst in
	    incr nextst;
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
    print_history dbg history;
    dbg ", nonterminal = ";
    dbg nt;
    dbg "\n";
    let scc_nt = get_scc_num nt in
    let regular_nt = is_regular nt in
    let ret = 
      match state_exists history [nt] with
	  None ->
	    let s = nt_start history nt in
	    let s' = nt_end history nt in
	    let sides = (match trie_lookup pmap nt with None -> [] | Some(ss) -> ss) in

	      (* add an edge labeled by the nonterminal from s to s' *)
	      if sentential then
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
		  (fun (lhs,ot) ->
		     (* return a pair of the states corresponding to the items 
			with the dot before next, and the dot at the end of next. *)
		     let rec items prev_state prev next =
		       let cur_i = new_item nt prev next in
			 dbgm "(items with nt = ";
			 dbgm nt;
			 dbgm ", prev_state = ";
			 print_state dbgm prev_state;
			 dbgm ", current item = ";
			 print_item dbgm cur_i;
			 dbgm "\n";
			 let ret = 
			   match next with
			       [] -> prev_state
			     | sym::next' ->
				 let next_st = 
				   if trie_contains pmap sym then
				     (* this is a nonterminal *)
				     let history' = 
				       if !crude_aut then
					 history
				       else
					 let scc_sym = get_scc_num sym in
					   if scc_sym = scc_nt then
					     if regular_nt then
					       (dbgm "(nt and sym are both regular).\n";
						history)
					     else
					       (dbgm "(nt and sym are in the same scc).\n";
						change_top history cur_i) 
					   else
					     (dbgm "(nt and sym are not in the same scc).\n";
					      cur_i::history)
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
				     let next_i = new_item nt (sym::prev) next' in
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
		       add_label_deferred (lhs,nt,ot) s;
		       let is' = items s [] (List.map snd lhs) in
			 add_eps_edge_deferred is' s';
		  )
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
      let numstates = !nextst in
      let im : string list array = Array.make numstates [] in
      let finals = Array.make numstates false in
      let trans = Array.make numstates None in
      let trans_rev = Array.make numstates None in
      let prlab = Array.make numstates [] in
      let states = enumerate 0 numstates in
	
	dbgm "(Deferred creation of the automaton finishes.  Now processing the instructions to build the actual automaton.)\n";

	(* now process all the accumulated information *)

	(* trans and trans_rev *)
	List.iter (fun (s,nt,s') -> add_edge trans trans_rev s nt s') !edges;
	List.iter (fun (s,s') -> add_eps_edge trans trans_rev s s') (uniq compare !eps_edges);

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
	    (im, (prlab,au))
;;

let aut_num_states (au:aut) : int = 
  let (_,FinalStates(finals), _, _) = au in
    Array.length finals 
;;

(* we assume rau has a unique final state *)
let reverse (rau:rtn_aut) : rtn_aut =
  let (prlab,au) = rau in
  let (StartState(start_state), FinalStates(finals), AllStates(states), (trans,trans_rev)) = au in
  let numstates = aut_num_states au in
  let finals' = Array.make numstates false in
    finals'.(start_state) <- true;
    (prlab,(StartState(singleton_expected (bool_array_domain finals)), FinalStates(finals'), AllStates(states), (trans_rev,trans)))
;;

let canonize_prlab states prlab =
  (* canonize the lists in im and prlab *)
  List.iter (fun d -> prlab.(d) <- uniq compare prlab.(d)) states;;

let determinize_aut (rau:rtn_aut) : rtn_aut * (int inttrie) =
  let (prlab,au) = rau in
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
		     let s' = List.concat (List.map (fun x -> next_states trans x e) s) in
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
      let prlab' = Array.make bound [] in
      let states' = List.map dfa_state state_sets in

	(* set finals', im', and prlab' *)
	List.iter (fun st -> 
		     let d = dfa_state st in
		       List.iter
			 (fun s -> 
			    if finals.(s) then
			      finals'.(d) <- true;
			    prlab'.(d) <- prlab.(s) @ prlab'.(d))
			 st)
	  state_sets;
	
	canonize_prlab states' prlab';

	(* set trans' and trans_rev' *)
	List.iter (fun (d,nt,d') -> add_edge trans' trans_rev' d nt d') !edges;
	
	((prlab',(StartState(start_state'), FinalStates(finals'), AllStates(states'), (trans',trans_rev'))),
	 st_map)
;;

let same_prlabels (prlab:prlab_t) (st1:state_t) (st2:state_t) : bool =
  let ls1 = List.map prule_to_string prlab.(st1) in
  let ls2 = List.map prule_to_string prlab.(st2) in
  let len = List.length ls1 in
    if len <> List.length ls2 then
      false
    else
      let ss1 = stringset_of_strings ls1 in
      let ss2 = stringset_of_strings ls2 in
	(List.length (trie_strings (stringset_intersect ss1 ss2)) = len)
;;

(* return a mapping from old states to new states, as well as the new automaton *)
let minimize_aut (rau:rtn_aut) : rtn_aut * (int inttrie) =
  let dbg = debugger dbg_minimization in
  let dbg_state (s:state_t) : unit =
    dbg (string_of_int s) 
  in
  let (prlab,au) = rau in
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

    let get_diff_array x = 
      match diff.(x) with
	  None -> 
	    let t = Array.make bound false in
	      diff.(x) <- Some([],t);
	      t
	| Some(_,u) -> u
    in

    let update_diff_info x y =
      let _ = get_diff_array x in
      let _ = get_diff_array y in
	(* make sure the diff info exists *)
	match diff.(x), diff.(y) with
	    Some(lx,dx), Some(ly,dy) ->
	      dbg "(set_diff ";
	      dbg_state x;
	      dbg " ";
	      dbg_state y;
	      dbg ")\n";
	      dx.(y) <- true;
	      dy.(x) <- true;
	      
	      diff.(x) <- Some(y::lx,dx);
	      diff.(y) <- Some(x::ly,dy)
	  | _,_ -> err "Internal error in update_diff_info"
    in

    (* return true iff we added a pair to the table *)
  let set_diff (x:state_t) (y:state_t) : bool =
    let dx = get_diff_array x in
      if dx.(y) then
	(* we must have already added this pair *)
	false
      else 
	(update_diff_info x y;
	 true)
  in
  let dbg_states (ss:state_t list) : unit =
    List.iter (fun s -> dbg " "; dbg_state s) ss
  in

  (* compute the starting points for our reverse traversal *)
  let starting_pairs = 
    (all_pairs finals_l nonfinals) (* finals are different from nonfinals *)
    @ (List.filter
	 (fun (st,st') ->
	    if st = st' then
	      false
	    else
	      (* states which have different sets of out-edges or
		 different prlabs are different. *)
	      (let es = List.sort compare (edge_labels trans st) in
	       let es' = List.sort compare (edge_labels trans st') in
		 if es <> es' then
		   (dbg "(different sets of out-edges for ";
		    dbg_state st;
		    dbg " and ";
		    dbg_state st';
		    dbg ")\n";
		    true)
		 else if not (same_prlabels prlab st st') then
		   (dbg "(different prlabs for ";
		    dbg_state st;
		    dbg " and ";
		    dbg_state st';
		    dbg ")\n";
		    true)
		 else 
		   false
	      ))
	 (all_pairs states states))
  in
	 

    let process() = 
      let rec rev_traverse (p:state_t * state_t) : unit =
	let (s1,s2) = p in
	  dbg "(rev_traverse ";
	  dbg_state s1;
	  dbg " ";
	  dbg_state s2;
	  dbg "\n";
	  if set_diff s1 s2 then
	    ( (* we haven't explored backwards from this pair of states before *)
	      let es = edge_labels trans_rev s1 in
		List.iter
		  (fun e ->
		     (* get the predecessors of s and s' on edges labeled e *)
		     let ps1 = next_states trans_rev s1 e in
		     let ps2 = next_states trans_rev s2 e in
		     let pp = all_pairs ps1 ps2 in
		     let predp s ps =
		       dbg "(predecessors of ";
		       dbg_state s;
		       dbg " on ";
		       dbg e;
		       dbg ": ";
		       dbg_states ps;
		       dbg ")\n"
		     in
		       predp s1 ps1;
		       predp s2 ps2;
		       List.iter rev_traverse pp)
		  es);
	  dbg ")\n";
      in
	List.iter rev_traverse starting_pairs
    in
      
      process();
      dbg "(The diff trie (map states to different states):\n";
      (let iend = bound-1 in
	 for i = 0 to iend do
	   match diff.(i) with
	       None -> ()
	     | Some(l,u) ->
		 dbg_state i;
		 dbg " -> ";
		 print_ints dbg " " l;
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
	     let d = get_diff_array st in
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
	      prlab'.(q) <- prlab.(s) @ prlab'.(q);
	      List.iter
		(fun e ->
		   match next_states trans s e with
		       [s'] ->
			 let q' = get_quot s' in
			   add_edge trans' trans_rev' q e q'
		     | _ -> err "Internal error: a deterministic automaton has multiple out-edges from a state.")
		(edge_labels trans s)
	in

	  List.iter explore states;

	  canonize_prlab !states' prlab';

	  ((prlab',(StartState(get_quot start_state),FinalStates(finals'),AllStates(uniq compare !states'), (trans',trans_rev'))),
	   quot_map)
;;

let extra_nt = "_extra";;

(* produce a new automaton by refining a forward automaton (forw) with its
   reverse (back). *)
let refine_with_rev (forw:rtn_aut) (back:rtn_aut) : rtn_aut = 
(*  let dbg = debugger dbg_refine in*)
  let edges_def = ref [] in
  let labels_def = ref [] in
  let finals_def = ref [] in
  let make_final_deferred s =
    finals_def := s::!finals_def
  in
  let add_edge_deferred s nt s' =
    edges_def := (s,nt,s')::!edges_def
  in

  let add_label_deferred s l =
    labels_def := (l,s)::!labels_def
  in
  
  let (fprlab,fau) = forw in
  let (bprlab,bau) = back in
  let (StartState(fstart_state), FinalStates(ffinals), AllStates(fstates), (ftrans,ftrans_rev)) = fau in
  let (StartState(bstart_state), FinalStates(bfinals), AllStates(bstates), (btrans,btrans_rev)) = bau in

  (* we have to map sequences consisting of a state in the forward
     automaton and an ordered list of states in the backward
     automaton, to states in the new refined automaton *)
  let bound = max (aut_num_states fau) (aut_num_states bau) in
  let st_map = inttrie_new bound in
  let next_st = ref 0 in
  let new_state () = 
    let s = !next_st in
      incr next_st;
      s
  in
  let common_edges (f:state_t) (b:state_t) : string list =
    match btrans_rev.(b) with
	None -> []
      | Some(bem,_) ->
	  let es = edge_labels ftrans f in
	    List.filter (trie_contains bem) es
  in
  let common_labels (f:state_t) (b:state_t) : prule list =
    let t = trie_new() in
      List.iter (fun p -> trie_insert t (prule_to_string p) p) fprlab.(f);
      List.filter (fun p -> trie_contains t (prule_to_string p)) bprlab.(b) 
  in

  let rec refine_state (f:state_t) (bs:state_t list) : state_t =
    let bs = List.sort compare bs in
      match inttrie_lookup st_map (f::bs) with
	  Some(s) -> s
	| None ->
	    let s = new_state() in 
	      inttrie_insert st_map (f::bs) s;
	      if ffinals.(f) then
		make_final_deferred s;
	      List.iter 
		(fun b -> 
		   let es = common_edges f b in
		   let ls = common_labels f b in
		   let s' = new_state() in 
		     List.iter (add_label_deferred s') ls;
		     add_edge_deferred s (string_of_int b) s';
		     if b = bstart_state then
		       make_final_deferred s';

		     List.iter
		       (fun e ->
			  let fs = next_states ftrans f e in
			    if nonempty fs then
			      let f' = singleton_expected fs in
			      let bs' = next_states btrans_rev b e in
				add_edge_deferred s' e (refine_state f' bs'))
		       es) bs;
	      s
  in
  let new_start = refine_state fstart_state (bool_array_domain bfinals) in
  let extra = new_state() in
  let numstates = !next_st in
  let would_be_finals = Array.make numstates false in
  let finals = Array.make numstates false in
  let trans = Array.make numstates None in
  let trans_rev = Array.make numstates None in
  let prlab = Array.make numstates [] in
  let states = enumerate 0 numstates in
	
    (* now process all the accumulated information *)
    
    (* trans and trans_rev *)
    List.iter (fun (s,nt,s') -> add_edge trans trans_rev s nt s') !edges_def;
    
    (* finals *)
    List.iter (fun s -> would_be_finals.(s) <- true) !finals_def;

    (* prlab *)
    List.iter (fun (l,s) -> prlab.(s) <- l::prlab.(s)) !labels_def;
    canonize_prlab states prlab;
    
    (* add edges from all the final states to the extra state *)
    List.iter (fun s -> add_edge trans trans_rev s extra_nt extra) (bool_array_domain would_be_finals);
    
    finals.(extra) <- true;

    let au = (StartState(new_start), FinalStates(finals), AllStates(states), (trans,trans_rev)) in
      (prlab,au)
;;


let construct_parsing_aut (dbg:string -> unit) (gname:string) (start:string) (trs:parsing_trs) : rtn_aut * rtn_aut * rtn_aut =
  let dbgm = debugger dbg_intermed_aut in
    
  let dbgm_prlab what prlab states =
    dbgm "(Prules associated with ";
    dbgm what;
    dbgm " states:\n";
    List.iter (fun st -> 
		 let ps = prlab.(st) in
		   if nonempty ps then
		     (dbgm "(";
		      dbgm (string_of_int st);
		      dbgm " :\n";
		      List.iter (fun p ->  dbgm " "; Parsing_trs.print_prule dbgm p) ps;
		      dbgm ")\n"))
      states;
    dbgm ")"
  in
  let show_aut long_name short_name file_name dbg_state rau =
    let (prlab, au) = rau in
      dbgm "(The ";
      dbgm long_name;
      dbgm " automaton:\n";
      print_aut dbgm dbg_state au;
      dbgm "\n";
      dbgm_prlab short_name prlab (get_states au);
      write_aut_dot (gname^"_"^file_name) string_of_int au;
      dbgm ")\n"
  in
    
  let (im,rau) = construct_rtn_aut start false (* sentential *) trs in

  let item_from_nfa_state s =
    match im.(s) with
	[i] -> i
      | _ -> err "Internal error getting sole item for nfa state."
  in
  let dbgm_state st = 
    dbgm (string_of_int st)
  in
  let dbgm_nfa_state st = 
    dbgm_state st;
    dbgm " : ";
    dbgm (item_from_nfa_state st)
  in

    show_aut "nondeterministic" "NFA" "nfa" dbgm_nfa_state rau;

    if !stop_before_determinization then
      (dbgm "(Stopping as requested, before determinization.)\n";
       exit 0);

    let (rau',st_map) = determinize_aut rau in

    show_aut "deterministic" "DFA" "dfa" dbgm_state rau';

      let dbgm_state_list (ss:state_t list) : unit = 
	dbgm "["; List.iter (fun s -> dbgm " "; print_state dbgm s) ss; dbgm " ]" 
      in
      let dbgm_state_map st_map =
	dbgm "(The state map is:";
	List.iter (fun st -> 
		     dbgm "\n"; 
		     dbgm_state_list st; 
		     dbgm " -> "; 
		     match inttrie_lookup st_map st with
			 None -> err "Internal error printing state map.\n"
		       | Some(s) -> dbgm (string_of_int s))
	  (inttrie_domain st_map);
	dbgm ")\n"
      in
	dbgm_state_map st_map;
	
	let (rau'',quot_map) = minimize_aut rau' in

	  show_aut "minimized deterministic" "Min DFA" "min" dbgm_state rau'';

	  dbgm_state_map quot_map;

	  let rev_nfa_rau = (reverse rau'') in

	  show_aut "nondeterministic reversed" "Reverse NFA" "rev_nfa" dbgm_state rev_nfa_rau;

	  let rev_dfa_rau = fst (determinize_aut rev_nfa_rau) in

	    show_aut "determinized reversed" "Reverse DFA" "rev_dfa" dbgm_state rev_dfa_rau;

	    let rev_min_rau = fst (minimize_aut rev_dfa_rau) in
	      
	      show_aut "minimized reversed" "Reverse Min DFA" "rev_min" dbgm_state rev_min_rau;
	      
	      let ref_rau = fst (minimize_aut (refine_with_rev rau'' rev_min_rau)) in
		
		show_aut "minimized refined" "Refined" "ref" dbgm_state ref_rau;
		
		(rau'',rev_min_rau,ref_rau)
;;
