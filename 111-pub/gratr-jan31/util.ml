let sym_print = ref false;;

let err (s:string) =
  print_string s;
  print_string "\n";
  exit 1;;

let rec map_end (f : 'a -> 'b) (l : 'a list) (l2:'b list) : 'b list =
  match l with
      [] -> l2
    | a::l' -> (f a)::(map_end f l' l2);;

let rec all_pairs (l1:'a list) (l2:'b list) (accum:('a * 'b) list) : ('a * 'b) list =
  match l2 with
      [] -> accum
    | b::l2' ->
	all_pairs l1 l2' (map_end (fun a -> (a,b)) l1 accum);;

let all_pairs (l1:'a list) (l2:'b list) : ('a * 'b) list = all_pairs l1 l2 [];;

let singleton_expected (l:'a list) : 'a =
  match l with
      [x] -> x
    | _ -> err "Internal error in singleton_expected.";;

let rec max_elt (x:'a) (l:'a list) : 'a =
  match l with
      [] -> x
    | a::l' ->
	let c = compare x a in
	  if c < 0 then
	    max_elt a l'
	  else
	    max_elt x l';;
	  
let rec add_list (l:int list) : int =
  match l with
      [] -> 0
    | x::l' -> x+(add_list l');;

let rec pow (x:int) (y:int) : int =
  if y <= 0 then 1
  else x * (pow x (y-1));;

let rec numlist (i:int) : int list =
  if (i < 0) then []
  else
    i::(numlist (i-1));;

let print_string_flush x = print_string x; flush stdout;;

let nodbg (x:string) : unit = ();;

let debugger_out = ref stdout;;
let set_debugger_out (o:out_channel) : unit = 
  debugger_out := o;;

let debugger (b:bool ref) =
  let outfile = !debugger_out in
  if !b then (fun s -> output_string outfile s; flush outfile) else nodbg;;

let dbgif (b:bool ref) (f:unit -> unit) : unit =
    if !b then f();;

let nonempty (x:'a list) : bool =
  match x with
      [] -> false
    | _ -> true;;

let empty (x:'a list) : bool =
  match x with
      [] -> true
    | _ -> false;;

let singleton (x:'a list) : bool =
  match x with
      [y] -> true
    | _ -> false;;


(* remapping strings which we cannot print as TRS variables *)

let sym_num = ref 0;;
let sym() = incr sym_num; "sym"^(string_of_int !sym_num);;

let xlate_tbl = Trie.trie_new();;
let idregexp = Str.regexp ("[0-9 a-z A-Z _]+");;

let dump_sym_table (os:string -> unit) : unit =
  Trie.print_trie os os xlate_tbl;
  os "\n"
;;

let safe_string (s:string) : string =
  if not !sym_print then
    s
  else
    let ok = 
      if Str.string_match idregexp s 0 then
	(Str.match_end() >= String.length s)
      else false in
      if not ok then
	match Trie.trie_lookup xlate_tbl s with
	    None ->
	      let s2 = sym() in
		Trie.trie_insert xlate_tbl s s2;
		s2
	  | Some(x) -> x
      else
	s
;;

let rec append_all_to_all (l1:'a list list) (l2:'a list list) (accum : 'a list list list) : 'a list list =
  match l1 with
      [] -> List.concat accum
    | l1e::l1' ->
	append_all_to_all l1' l2 ((List.map (List.append l1e) l2)::accum);;

let append_all_to_all(l1:'a list list) (l2:'a list list) : 'a list list = append_all_to_all l1 l2 [];;

let cons_to_all (a:'a) (ls : 'a list list) : 'a list list = List.map (fun l -> a::l) ls;;

let rec prefix (l1:'a list) (l2:'a list) : bool =
  match l1,l2 with
      a::l1',b::l2' ->
	if a <> b then
	  false
	else
	  prefix l1' l2'
    | [],_ -> true
    | _,_ -> false;;

let rec contains_prefix (ss : 'a list list) : bool =
  match ss with
      s::ss' ->
	if List.exists (fun s' -> prefix s s' || prefix s' s) ss' then
	  true
	else
	  contains_prefix ss'
    | [] -> false
;;

let print_strings (os:string -> unit) (sep:string) (ss:string list) : unit =
  match ss with
      [] -> ()
    | s::ss' ->
	os s;
	List.iter (fun s -> os sep; os s) ss';;

let print_ints (os:string -> unit) (sep:string) (ss:int list) : unit =
  print_strings os sep (List.map string_of_int ss);;

let rec list_eq (cmp:'a -> 'a -> int) (l1:'a list) (l2:'a list) : bool =
  match l1,l2 with
      a1::l1', a2::l2' ->
	if cmp a1 a2 = 0 then
	  list_eq cmp l1' l2'
	else
	  false
    | [],[] -> true
    | _,_ -> false;;

(* we assume l is non-empty *)
let rec split_list_last (l:'a list) : 'a list * 'a =
  match l with
      [a] -> ([],a)
    | x::l' -> 
	let (l'',y) = split_list_last l' in 
	  (x::l'',y)
    | _ -> raise (Failure("split_list_last"))
;;

let rec list_last (l:'a list) : 'a =
  let (_,x) = split_list_last l in x
;;

let list_first (l:'a list) : 'a =
  match l with 
      [] -> raise (Failure("list_first")) 
    | s::_ -> s 
;;

let rec list_range (l:'a list) (first :int)(len:int) : 'a list =
  if len = 0 then
    []
  else
    match l with
	[] -> []
      | a::l' ->
	  if first = 0 then
	    a::(list_range l' first (len-1))
	  else
	    list_range l' (first-1) len;;

let rec lift_option (l : 'a option list) : 'a list option =
  match l with
      [] -> Some([])
    | a::l' ->
	match a, lift_option l' with
	    None,_ | _, None -> None
	  | Some(x),Some(l2) -> Some(x::l2);;

let quote (s:string) : string =
  "\'"^s^"\'";;

(* we assume s begins and ends with a single quote.  We will
   turn this into a list of its characters, counting escape sequences as
   single characters. *)
let explode_quoted (s:string) : string list =
  let rec explode_quoted (s:string) : string list =
    let n = String.length s in
      if n = 0 then
	[s]
      else
	if s.[0] = '\'' then
	  helper s 1 n
	else
	  [s]
  and helper s i n =
    if i >= (n-1) then
      []
    else
      let c = s.[i] in
      let quote_char escape d =
	quote ((if escape then "\\" else "")^(String.make 1 d)) 
      in
	if c = '\\' then
	  (quote_char true s.[i+1])::(helper s (i+2) n)
	else
	  (quote_char false c)::(helper s (i+1) n)
  in
    explode_quoted s
;;

let strip_quotes (s:string) : string option =
  let len = String.length s in
  if len < 2 then
    None
  else
    if s.[0] = '\'' && s.[len-1] = '\'' then
      Some(String.sub s 1 (len-2))
    else
      None;;

let is_quoted (s:string) : bool =
  match strip_quotes s with
      None -> false
    | _ -> true;;

let rec and_list l =
  match l with
      [] -> true 
    | x::l' -> 
	if x then
	  and_list l'
	else
	  false
;;

let rec or_list l =
  match l with
      [] -> false
    | x::l' -> 
	if x then
	  true
	else
	  or_list l'
;;

(* we assume s is nonempty *)
let is_capitalized (s:string) : bool = 
  Char.uppercase (s.[0]) = s.[0];;

  (* return a list of all the lists resulting from concatenating
     a list in l1 with a list in l2 *)
let mix (l1:'a list list) (l2:'a list list) : 'a list list =
  List.map (fun (x,y) -> x @ y) (all_pairs l1 l2)
;;

let loop() = 
  print_string_flush "Looping...\n";
  let rec loop() = loop()
  in loop();;

let rec nums cur max =
  if cur > max then
    []
  else
    cur::(nums (cur+1) max);;

let printable_ascii = [9; 10] @ (nums 32 126);;

(* we assume s is three or four characters long; e.g. "'a'" or "'\n'" *)
let map_escaped s =
  if s = "'\\n'" then '\n'
  else if s = "'\\t'" then '\t'
  else if s = "'\\\\'" then '\\'
  else s.[1];;

(* return a list of positions i where f returns true for arr.(i) *)
let filter_array (f:'a -> bool) (arr : 'a array) : int list =
  let iend = (Array.length arr) - 1 in
  let l = ref [] in
    for i = 0 to iend do
      if f arr.(i) then
	l := i::!l
    done;
    !l
;;

let opt_array_domain (arr : 'a option array) : int list =
  filter_array (fun x -> match x with None -> false | _ -> true) arr;;

let bool_array_domain (arr : bool array) : int list =
  filter_array (fun x -> x) arr;;

let list_array_domain (arr : 'a list array) : int list =
  filter_array nonempty arr;;

let rec take_some (l:'a option list) : 'a list =
  match l with
      [] -> []
    | None::l' -> take_some l'
    | Some(x)::l' -> x::(take_some l')
;;

let rec list_suffixes (l:'a list) : 'a list list =
  match l with
      [] -> [[]]
    | x::l' -> l::(list_suffixes l')
;;

