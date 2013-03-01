module OrderedInt =
struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end;;

module IntMap = Map.Make(OrderedInt);;

open Char;;

(***************************************************)
(* inttries                                        *)
(*                                                 *)
(* These map lists of ints to values.              *)
(***************************************************)

type 'a inttrieh = 
    Tnone 
  | Texact of int list * 'a
  | TnextMap of 'a option * ('a inttrieh IntMap.t)
  | TnextArray of 'a option * ('a inttrieh array)

(* to avoid dependence on OCaml 3.12: *)
let bindings (m:'a inttrieh IntMap.t) : (int * 'a inttrieh) list =
  let li = ref [] in
    IntMap.iter (fun k v -> li := (k,v)::!li) m;
    List.rev !li;;

(* if an int has value more than this, we will switch to Maps instead of arrays *)
let val_cutoff = 128;;

type 'a inttrie = ('a inttrieh * int (* size of arrays *)) ref;;

let inttrie_update (t:'a inttrie) (s:int list) (a:'a option) : unit = 
  let (h,sz) = !t in
  let rec inttrieh_update (t:'a inttrieh) (s:int list) (a:'a option) : 'a inttrieh = 
    match t with 
	Tnone -> 
	  (match a with
	       None -> t
	     | Some(v) -> Texact(s,v))
      | Texact(s',v') ->
	  (match a with
	      None ->
		(* check if we are removing exactly s *)
		if s = s' then
		  Tnone
		else
		  t
	     | Some(v) ->
		 if s = s' then
		   Texact(s',v)
		 else
		   let mk_map = 
		     match s,s' with
			 x::_,_ | _,x::_ -> x > val_cutoff
		       | _,_ -> true (* should not happen *)
		   in
		   let newt = 
		     (if mk_map
		      then TnextArray(None,(Array.make sz Tnone))
		      else TnextMap(None,IntMap.empty)) in
		     (* insert both value into the new trie *)
		     inttrieh_update (inttrieh_update newt s' (Some(v'))) s a)
      | TnextArray(o,v) ->
	  (match s with
               [] -> TnextArray(a,v)
	     | c::s' -> 
		 Array.set v c (inttrieh_update (Array.get v c) s' a);
		 TnextArray(o,v))
      | TnextMap(o,m) ->
	  match s with
	      [] -> TnextMap(a,m)
	    | c::s' ->
		let h' = 
		  try 
		    (IntMap.find c m)
		  with
		      _ -> Tnone
		in
		  TnextMap(o, IntMap.add c (inttrieh_update h' s' a) m)
  in
    t := (inttrieh_update h s a,sz);;

let inttrie_lookup (t:'a inttrie) (s:int list) = 
  let rec inttrieh_lookup t (s:int list) = 
    match t with
	Tnone -> None
      | Texact(s',v) ->
	  if s = s' then Some(v) else None
      | TnextArray(o,v) -> 
	  (match s with
              [] -> o
	    | c::s' -> inttrieh_lookup (Array.get v c) s')
      | TnextMap(o,m) ->
	  (match s with
	       [] -> o
	     | c::s' -> 
		 try
		   inttrieh_lookup (IntMap.find c m) s'
		 with 
		     _ -> None)
  in
  let (h,_) = !t in
    inttrieh_lookup h s;;

let rec is_prefix (l1:'a list) (l2:'a list) : bool =
  match l1,l2 with
      x::l1',y::l2' -> if x = y then is_prefix l1' l2' else false
    | [],_ -> true
    | _,_ -> false;;

(* we return the list of values to which the trie maps some prefix of s. *)
let inttrie_lookup_prefix (t:'a inttrie) (s:int list) : 'a list = 
  let rec inttrieh_lookup t (s:int list) = 
    match t with
	Tnone -> []
      | Texact(s',v) ->
	  if is_prefix s' s then [v] else []
      | TnextArray(o,v) -> 
	  let l1 = 
	    match o with
		None -> []
	      | Some(v) -> [v]
	  in
	  (match s with
              [] -> l1
	    | c::s' -> l1@(inttrieh_lookup (Array.get v c) s'))
      | TnextMap(o,m) ->
	  let l1 = 
	    match o with
		None -> []
	      | Some(v) -> [v]
	  in
	  (match s with
	       [] -> l1
	     | c::s' -> 
		 l1 @
		   (try
		      (inttrieh_lookup (IntMap.find c m) s')
		    with 
			_ -> []))
  in
  let (h,_) = !t in
    inttrieh_lookup h s;;

let inttrie_domain (t:'a inttrie) : int list list = 
  let (h,sz) = !t in
  let rec helper (t : 'a inttrieh) (sofar : int list) (strs : int list list) : int list list =
    match t with 
	Tnone -> strs
      | Texact(l,v) -> ((List.rev sofar) @ l)::strs
      | TnextArray(o,v) -> 
	  (match o with
              None -> helper_arr v 0 sofar strs
            | Some(trm) -> helper_arr v 0 sofar ((List.rev sofar)::strs))
      | TnextMap(o,m) -> 
	  match o with
              None -> helper_map (bindings m) sofar strs
            | Some(trm) -> helper_map (bindings m) sofar ((List.rev sofar)::strs)
  and helper_arr (arr : 'a inttrieh array) (next_index:int) (sofar : int list) (strs : int list list) : int list list =
    if (next_index = sz) then
      strs
    else
      let elem_strings = helper arr.(next_index) (next_index::sofar) strs in
	helper_arr arr (next_index+1) sofar elem_strings
  and helper_map (m : (int * 'a inttrieh) list) (sofar : int list) (strs : int list list) : int list list =
    match m with
	[] -> strs
      | (k,v)::m' ->
	  let elem_strings = helper v (k::sofar) strs in
	    helper_map m' sofar elem_strings
  in
    helper h [] [];;

let inttrie_size (t:'a inttrie) : int = 
  let (_,sz) = !t in sz;;

let inttrie_new (max_int:int) : 'a inttrie = ref (Tnone,max_int+1);;
let inttrie_insert (t:'a inttrie) (s:int list) (a:'a) : unit = inttrie_update t s (Some(a));;
let inttrie_remove (t:'a inttrie) (s:int list) : unit = inttrie_update t s None;;
let inttrie_update (t:'a inttrie) (s:int list) (a:'a option) : unit = inttrie_update t s a;;
let inttrie_contains (t:'a inttrie) (s:int list) : bool =
  match (inttrie_lookup t s) with
      Some(_) -> true
    | _ -> false;;

let inttrie_clear (t:'a inttrie) : unit = 
  let (h,sz) = !t in
    t := (Tnone,sz);;
let inttrie_clone (t:'a inttrie) : 'a inttrie =
  let t2 = inttrie_new (inttrie_size t) in
    List.iter (fun s -> inttrie_update t2 s (inttrie_lookup t s)) (inttrie_domain t);
    t2;;

let print_inttrie (os:string -> unit) (print_intlist : int list -> unit) (print_value : 'a -> unit) (t:'a inttrie) : unit = 
  os "(";
  List.iter (fun x -> 
	       print_intlist x; 
	       os " -> ";
	       (match (inttrie_lookup t x) with
		    None -> os "[internal error, missing string]" (* should never happen *)
		  | Some(d) -> print_value d);
	       os "\n")
    (inttrie_domain t);
  os ")";;

type intlist_set = unit inttrie;;
let intlist_set_new (sz:int) = inttrie_new sz;;
let intlist_set_add (t: intlist_set) (s:int list) : unit = inttrie_update t s (Some());;
let intlist_set_remove (t: intlist_set) (s:int list) : unit = inttrie_update t s None;;
let intlist_set_contains (t: intlist_set) (s:int list) : bool = inttrie_contains t s;;
let intlist_set_ints (t: intlist_set) : int list list = inttrie_domain t;;
let intlist_set_clear (t: intlist_set) : unit = inttrie_clear t;;
let intlist_set_clone (t: intlist_set) : intlist_set = inttrie_clone t;;
let intlist_set_size (t:'a inttrie) : int = inttrie_size t;;
let print_intlist_set (os:string -> unit) (os_intlist : int list -> unit) (t: intlist_set) : unit = 
  let first = ref true in
  List.iter (fun s -> if !first then first := false else os " "; os_intlist s) (intlist_set_ints t);;

let inttrie_cons (t:'a list inttrie) (s:int list) (a:'a) = 
  match inttrie_lookup t s with
      None -> inttrie_insert t s [a]
    | Some(l) -> inttrie_insert t s (a::l);;

let intlist_set_of_intlists (bound:int)(ss : int list list) : intlist_set =
  let t = inttrie_new bound in
    List.iter (intlist_set_add t) ss;
    t
;;


(***************************************************)
(* tries                                           *)
(***************************************************)

let rec intlist_of_string s i =
  if (i = String.length s) then
    []
  else
    (Char.code s.[i])::(intlist_of_string s (i+1));;

let intlist_of_string s = intlist_of_string s 0;;

let rec string_of_intlist l i iend s =
  if i = iend then s
  else
    (String.set s i (Char.chr (List.hd l));
     string_of_intlist (List.tl l) (i+1) iend s);;

let string_of_intlist l = 
  let len = (List.length l) in
    string_of_intlist l 0 len (String.create len);;

type 'a trie = 'a inttrie;;
let max_char = 127;;
let trie_new () = inttrie_new max_char;;
let trie_insert (t:'a trie) (s:string) (a:'a) : unit = inttrie_update t (intlist_of_string s) (Some(a));;
let trie_remove (t:'a trie) (s:string) : unit = inttrie_update t (intlist_of_string s) None;;
let trie_lookup (t:'a trie) (s:string) = inttrie_lookup t (intlist_of_string s);;
let trie_lookup_prefix (t:'a trie) (s:string) = inttrie_lookup_prefix t (intlist_of_string s);;
let trie_update (t:'a trie) (s:string) (a:'a option) = inttrie_update t (intlist_of_string s) a;;
let trie_contains (t:'a trie) (s:string) : bool = inttrie_contains t (intlist_of_string s);;
let trie_strings (t:'a trie) : string list = 
  List.map string_of_intlist (inttrie_domain t);;
let trie_clear (t:'a trie) : unit = inttrie_clear t;;
let trie_clone (t:'a trie) : 'a trie = inttrie_clone t;;
let print_trie (os:string -> unit) (print_value : 'a -> unit) (t:'a trie) : unit = 
  print_inttrie os (fun l -> os (string_of_intlist l)) print_value t;;

let trie_cons (t:'a list trie) (s:string) (a:'a) = 
  match trie_lookup t s with
      None -> trie_insert t s [a]
    | Some(l) -> trie_insert t s (a::l);;

let trie_append (t:'a list trie) (s:string) (l:'a list) = 
  match trie_lookup t s with
      None -> trie_insert t s l
    | Some(l') -> trie_insert t s (l @ l');;
  
let list_trie_lookup (t:'a list trie) (s:string) : 'a list =
  match trie_lookup t s with
      None -> []
    | Some(l) -> l;;

let uniq (cmp : 'a -> 'a -> int) (l : 'a list) : 'a list = 
  let rec drop_dups (l:'a list) : 'a list =
    match l with
	[] -> []
      | [x] -> [x]
      | x::y::l' -> 
	  let r = drop_dups (y::l') in
	    if (cmp x y = 0) then r else x::r 
  in
  drop_dups (List.sort cmp l);;

let list_trie_uniq (t:'a list trie) (cmp:'a -> 'a -> int) : unit =
  List.iter
    (fun s ->
       match trie_lookup t s with
	   None -> () (* should not happen *)
	 | Some(rs) -> trie_insert t s (uniq cmp rs))
    (trie_strings t);;    

(**************************************************)
(* stringsets                                     *)
(**************************************************)

type stringset = unit trie

let stringset_add_b (t:stringset) (s:string) : bool =
  if trie_contains t s then
    false
  else
    (trie_insert t s ();
     true);;
let stringset_add (t:stringset) (s:string) : unit =
  let _ = stringset_add_b t s in
    ();;

let stringset_disjoint (s1:stringset) (s2:stringset) : bool = 
  List.for_all (fun s -> not (trie_contains s1 s)) (trie_strings s2)
;;

let stringset_intersect (s1:stringset) (s2:stringset) : stringset = 
  let sset = trie_new() in
    List.iter (fun s -> let _ = stringset_add sset s in ())
      (List.filter (trie_contains s1) (trie_strings s2));
    sset
;;

let stringset_union (s1:stringset) (s2:stringset) : stringset = 
  let sset = trie_new() in
    List.iter (stringset_add sset) (trie_strings s1);
    List.iter (stringset_add sset) (trie_strings s2);
    sset
;;

let stringset_trie_lookup (t:stringset trie) (s:string) : stringset =
  match trie_lookup t s with
      None -> 
	let sset = trie_new() in
	  trie_insert t s sset;
	  sset
    | Some(sset) -> sset;;

(* add v to the stringset associated by t1 with s.  Return false
   if v was already there, and true otherwise (i.e., we truly added v). *)
let stringset_trie_add_b (t1:stringset trie) (s:string) (v:string) : bool =
  let sset = stringset_trie_lookup t1 s in
    if trie_contains sset v then
      false
    else
      (trie_insert sset v ();
       true)
;;
let stringset_trie_add (t1:stringset trie) (s:string) (v:string) : unit =
  let _ = stringset_trie_add_b t1 s v in ();;

let stringset_of_strings (ss : string list) : stringset =
  let t = trie_new() in
    List.iter (stringset_add t) ss;
    t
;;

(* add all strings from ss to s1, returning true iff we actually added something *)
let stringset_include_strings_b(s1:stringset) (ss:string list) : bool=
  let added = ref false in
    List.iter (fun s -> 
		 if not (trie_contains s1 s) then
		   (added := true;
		    trie_insert s1 s ()))
      ss;
    !added
;;
let stringset_include_strings(s1:stringset) (ss:string list) : unit =
  let _ = stringset_include_strings_b s1 ss in ();;

let stringset_include_b(s1:stringset) (s2:stringset) : bool=
  stringset_include_strings_b s1 (trie_strings s2)
;;

let stringset_subset (s1:stringset) (s2:stringset) : bool = 
  let rec helper ss =
    match ss with
	[] -> true
      | s::ss' ->
	  if not (trie_contains s2 s) then
	    false
	  else
	    helper ss'
  in
    helper (trie_strings s1);;

(* add the stringset sset to the stringset associated by t1 with s, returning
   true iff we actually added something. *)
let stringset_trie_include_b (t1:stringset trie) (s:string) (sset:stringset) : bool =
  match trie_lookup t1 s with
      None -> 
	 (match (trie_strings sset) with
	      [] -> false
	    | _ -> (* sset is non-empty *)
		trie_insert t1 s (trie_clone sset);
		true
	 )
    | Some(sset2) -> stringset_include_b sset2 sset;;
let stringset_trie_include (t1:stringset trie) (s:string) (sset:stringset) : unit =
  let _ = stringset_trie_include_b t1 s sset in ();;

let stringset_trie_include_strings_b (t1:stringset trie) (s:string) (ss:string list) : bool =
  match trie_lookup t1 s with
      None -> 
	(match ss with
	     [] -> false
	   | _ -> (* sset is non-empty *)
	       trie_insert t1 s (stringset_of_strings ss);
	       true
	)
    | Some(sset2) -> stringset_include_strings_b sset2 ss;;
let stringset_trie_include_strings (t1:stringset trie) (s:string) (ss:string list) : unit =
  let _ = stringset_trie_include_strings_b t1 s ss in ();;

(* copy the stringset for s2 into s1, returning true iff we actually added something *)
let stringset_trie_pull_b (t:stringset trie) (s1:string) (s2:string) : bool =
  stringset_trie_include_b t s1 (stringset_trie_lookup t s2) 
let stringset_trie_pull (t:stringset trie) (s1:string) (s2:string) : unit =
  let _ = stringset_trie_pull_b t s1 s2 in ();;

let print_stringset(os:string -> unit)(s:stringset) : unit =
  List.iter (fun s -> os s; os " ") (trie_strings s);;

let print_stringset_trie(os:string -> unit)(s:stringset trie) : unit =
  print_trie os (print_stringset os) s;;  

(**************************************************)
(* string_relations                               *)
(**************************************************)

type string_relation = stringset trie * stringset trie;;

let string_relation_new () = (trie_new(),trie_new());;

let string_relation_add (r:string_relation) (s1:string) (s2:string) : unit =
  let (fw,bk) = r in
    stringset_trie_add fw s1 s2;
    stringset_trie_add bk s2 s1
;;

let string_relation_include (r:string_relation) (s1:string) (s2:stringset) : unit =
  List.iter (fun s -> string_relation_add r s1 s) (trie_strings s2);;

let string_relation_image (r:string_relation) (s:string) : stringset =
  let (fw,bk) = r in
    stringset_trie_lookup fw s
;;

let string_relation_preimage (r:string_relation) (s:string) : stringset =
  let (fw,bk) = r in
    stringset_trie_lookup bk s
;;

let print_string_relation (os:string->unit) (r:string_relation) : unit =
  let (fw,bk) = r in
    os "((Forward mapping:\n";
    print_stringset_trie os fw;
    os ")\n(Backward mapping:\n";
    print_stringset_trie os bk;
    os "))\n"
;;
