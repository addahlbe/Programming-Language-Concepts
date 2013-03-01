open Trie;;
open Util;;
open Srs;;

let dbg_rewrite_aut = ref false;;

(* a simplified structure for automata:
   state 0 is the sole start state, and the last state in the array is the sole final state. *)
type state = int;;
type stateset = bool array * state list (* we maintain the set of states in both array and list form for efficiency *)
type statemap = stateset trie * state list;; (* the state list is for universal transitions *)
type aut = Aut of statemap array;;
    
let start_state(a:aut) : state = 0;;
let last_state(Aut(s)) : state = (Array.length s) - 1;;
let final_state(a:aut)(x:state) = (x = last_state a);;

let new_stateset (Aut(states)) =
  (Array.create (Array.length states) false, []);;

let print_stateset (os:string -> unit) (arr,li) : unit =
  os "array: ";
  Array.iteri (fun i v -> os "("; print_int i; os (if v then " , true)" else " , false)")) arr;
  os "\nlist:";
  List.iter (fun x -> os " "; print_int x) li;
  os "\n";;

(* we return true if a new transition was added *)
let add_transition (a:aut) (n:state) (m:state) (s:string) : bool = 
  let Aut(states) = a in
  let (st,u) = states.(n) in
    if List.mem m u then
      false
    else
      (* we are not already mapping n to m by a universal transition *)
      match trie_lookup st s with
	  None ->
	    let se = new_stateset a in
	    let se = (fst se, [m]) in
	      (fst se).(m) <- true;
	      trie_insert st s se; 
	      (* print_stateset print_string se; *)
	      true
	| Some((arr,li)) ->
	    if arr.(m) then
	      false
	    else
	      (arr.(m) <- true;
	       let se = (arr, (m::li)) in
		 trie_insert st s se;
		 (* print_stateset print_string se; *)
		 true)
;;

(* add a universal transition from n to m -- we assume such
   is not present already. *)
let add_universal (a:aut) (n:state) (m:state) : unit =
  let Aut(states) = a in
  let (st,u) = states.(n) in
    states.(n) <- (st,m::u);;

(* Build an automaton that recognizes the set of strings which start
   with terminal symbols, then contain a string as described by ss,
   and then end with terminal symbols.

   Terminals(ss) -- the set of strings ss.
   Nonterm(c,f,Some(m),l) -- the set described by "c | f m* l"
   Nonterm(c,f,None,l) -> the set described by "c | f T* l", where T is the set of all terminals

   We assume ss is non-empty. *)
type peak_word = 
    Terminals of string list | Nonterm of string list * string list * string list option * string list;;
let build_aut (ss:peak_word list) : aut =
  let rec compute_max_state ss =
    match ss with
	[] -> 0
      | s::ss' ->
	  match s with
	      Terminals(_) -> 1+(compute_max_state ss')
	    | Nonterm(_,_,_,_) -> 2+(compute_max_state ss')
  in
  let max_state = compute_max_state ss in
  let states = Array.init (max_state+1) (fun x -> (trie_new(),[])) in
  let a = Aut(states) in

  (* add transitions from n to m for all symbols in ter *)
  let add_all n m ts = List.iter (fun x -> let _ = add_transition a n m x in ()) ts in

  (* we assume ss has at least one string *)
  let rec chain cur ss =
    match ss with
	w::ss' ->
	  (match w with
	       Nonterm(c,f,om,l) -> 
		 add_all cur (cur+2) c;

		 add_all cur (cur+1) f;

		 (match om with
		      None -> 
			add_universal a (cur+1) (cur+1)
		    | Some(m) ->
			add_all (cur+1) (cur+1) m);
		 
		 add_all (cur+1) (cur+2) l;

		 chain (cur+2) ss'

	      | Terminals(ts) -> 
		  add_all cur (cur+1) ts;
		  chain (cur+1) ss')
	| _ -> ()
  in

    add_universal a 0 0;
    add_universal a max_state max_state;
    chain 0 ss;
    a
;;



let print_aut (os:string -> unit) (Aut(s)) : unit =
  let len = Array.length s in
    os "(\n";
    for n = 0 to (len-1) do
      os "(State ";
      os (string_of_int n);
      os " :\n";
      let (st,u) = s.(n) in
	if nonempty u then
	  (os "* -> ";
	   List.iter (fun x -> os " "; os (string_of_int x)) u;
	   os "\n");
	print_trie os (fun (x,y) -> List.iter (fun x -> os " "; os (string_of_int x)) y) st;
	os ")\n"
    done;
    os ")\n";;

let print_aut_gviz (os:string -> unit) (Aut(s)) : unit =
  let len = Array.length s in
    os "digraph aut {\nrankdir=LR;\n";
    for n = 0 to (len-1) do
      let nstr = string_of_int n in
      let (st,u) = s.(n) in
	if nonempty u then
	  List.iter (fun x -> os nstr; os " -> "; os (string_of_int x); os " [label = \"*\"];\n") u;
	List.iter
	  (fun e ->
	     match trie_lookup st e with
		 None -> () (* should not happen *)
	       | Some((_,ss)) -> List.iter (fun x -> os nstr; os " -> "; os (string_of_int x); os " [label = \""; os e; os "\"];\n") ss)
	  (trie_strings st);
    done;
    os "}\n";;
    
let successors (Aut(states)) (x:state) (s:string) : state list =
  let (st,u) = states.(x) in
    match trie_lookup st s with
	None -> u
      | Some(sts) -> u @ snd sts;;

let rec descendants (a:aut) (x:state) (ss:string list) : state list = 
  match ss with
      [] -> [x]
    | s::ss' ->
      List.concat (List.map (fun st -> (descendants a st ss')) (successors a x s));;

(* destructively modify the given automaton by rewriting it
   using the given srs *)
let rec rewrite_aut (sr:srs) (a:aut) : unit = 
  let dbg = debugger dbg_rewrite_aut in
  let Srs(rs) = sr in
  let last = last_state a in
  let added = ref false in
  let add_one (x:state) (y:state) (s:string) (reason:string list) =
    let added_this = add_transition a x y s in
      if added_this then
	(dbg "adding transition ";
	 dbg (string_of_int x);
	 dbg " -> ";
	 dbg (string_of_int y);
	 dbg " on ";
	 dbg s;
	 dbg " because of ";
	 print_strings dbg reason;
	 dbg "\n");
    added := !added || added_this
  in
  
    dbg "(Starting a round of automaton rewriting.\n";

    List.iter
      (* for each rule *)
      (fun (Rule(_,ss,s)) ->
	 for st = 0 to last do
	   (* for each state *)
	   List.iter
	     (* for each descendant state (st2) in the automaton
		reachable from state st by following the path ss *)
	     (fun st2 ->
		add_one st st2 s ss)
	     (descendants a st ss)
	 done)
      rs;
    if !added then
      rewrite_aut sr a;
    dbg ")\n"
;;
      
	     
let accepted (a:aut) (ss:string list) : bool =
  List.mem (last_state a) (descendants a (start_state a) ss);;
