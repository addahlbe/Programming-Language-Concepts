open Util;;

let print_raw = ref false;;

type term = App of string * term list | Var of int | Normal of term (* to mark terms as normalized *)
(*	    | StateDot of int (* state of an automaton *) * term*)

let const (s:string) : term = App(s,[]);;
let var (i:int) : term = Var(i);;

let app1 (f:string) (t:term) = App(f,[t]);;
let app2 (f:string) (t1:term) (t2:term) = App(f,[t1;t2]);;
let dot (t1:term) (t2:term) : term = App("dot",[t1;t2]);;

let rec strip_normal(t:term):term =
  match t with
      Normal(t') -> strip_normal t'
    | _ -> t;;

(* if t is a string literal, return the string *)
let string_lit_if (t:term) : string option =
  match strip_normal t with
      App(f,[]) -> strip_quotes f
    | _ -> None
;;

(* we assume every "dot" term has at least one argument.  
   dot -- if true, flatten with "dot"; else, flatten with "odot".
*)
let rec dot_flatten (t:term) (h:term option) (dot:bool) : term =
  match t with
      Normal(t') -> Normal(dot_flatten t' h dot)
    | App("dot",args) ->
	if empty args then
	  const (quote "")
	else
	  dot_flatten_args args h true
    | App("odot",args) ->
	if empty args then
	  const (quote "")
	else
	  dot_flatten_args args h false
    | _ -> 
	match h with
	    None -> t
	  | Some(t') -> App((if dot then "dot" else "odot"),[t;t'])
and dot_flatten_args (args:term list) (h:term option) (dot:bool) : term =
  match args with
      [] -> err "Internal error: dot_flatten_args."
    | [a] -> dot_flatten a h dot
    | a::args' ->
	dot_flatten a (Some(dot_flatten_args args' h dot)) dot
;;

(* see spec for dot_flatten above *)
let dot_flatten (t:term) : term =
  dot_flatten t None true;;

let rec dump_term (os:string -> unit) (t:term) : unit =
  match t with
      Var(x) -> os "x"; os (string_of_int x)
    | Normal(t) -> 
	os "[";
	dump_term os t;
	os "]";
    | App(f,ts) -> 
	if ts = [] then
	  os (Util.safe_string f)
	else
	  (os (Util.safe_string f); os "("; print_args os ts; os ")")
(*    | StateDot(i,t) ->
	os (string_of_int i);
	os " ";
	dump_term os t*)
and print_args (os:string -> unit) (ts:term list) : unit =
  match ts with
      [] -> ()
    | [t] -> dump_term os t
    | t::ts -> dump_term os t; os ", "; print_args os ts;;	

let get_head_symbol (t:term) : string option =
  match strip_normal t with
      App(f,_) -> Some(f)
    | _ -> None;;

(* return the first argument in t if t is a dot term, or just t
   otherwise.  In all cases, we will strip normal off the top of the
   returned term. *)
let dot_term_first (t:term) : term =
  let t = strip_normal t in
    match t with
	App("dot",[a1;a2]) -> strip_normal a1
      | _ -> t
;;

let dot_term_first_str (t:term) : string option =
  match dot_term_first t with
      App(f,args) -> Some(f)
    | _ -> None
;;

(* if t is a dot term, return its last non-variable symbol *)
let rec dot_term_last (t:term) : term =
  let t = strip_normal t in
    match strip_normal t with
	App("dot",[a1;a2]) -> 
	  (match strip_normal a1, strip_normal a2 with 
	       a1,Var(_) -> a1
	     | a1,a2 -> dot_term_last a2)
      | _  -> t
;;
let dot_term_last_str (t:term) : string option =
  match dot_term_last t with
      App(f,args) -> Some(f)
    | _ -> None
;;

(* assuming t is a dot-term, try to concatenate all the string
   literals encountered along a right spine in t.  Return the
   components of the resulting dot-term: the second component 
   will be omitted if the right-spine of t ends in a string
   literal.
*)
let rec compact_literals (t:term) : term * (term option) = 
  match strip_normal t with
      App("dot",[a1;a2]) | App("odot",[a1;a2]) ->
	(match string_lit_if a1 with
	     None -> (a1,Some(a2))
	   | Some(f) ->
	       let a2 = strip_normal a2 in 
		 match a2 with
		     App("dot",_) | App("odot",_) ->
		       let (t1,ot2) = compact_literals a2 in
			 (match string_lit_if t1 with
			      None -> (a1,Some(a2))
			    | Some(g) ->
				(App("\'"^f^g^"\'",[]),ot2))
		   | _ -> 
		       match string_lit_if a2 with
			   None -> (a1,Some(a2))
			 | Some(g) -> (App("\'"^f^g^"\'",[]),None))
    | r -> 
	print_string "Internal error: compact_literals called with a term which is not a dot term:";
	dump_term print_string r;
	print_string "\n";
	exit 1
;;

(* similar to compact_literals above, but we return a term, which is
   guaranteed to have normal terms stripped off already.  Also, it is
   not required that t be a dot term. *)
let compact_literals_term (t:term) : term =
  let t = strip_normal t in
  let ret = 
    match t with
	App("dot",_) | App("odot",_) ->
	  let (t1,ot2) = compact_literals t in
	    (match ot2 with
		 None -> t1
	       | Some(t2) -> App("dot",[t1;t2]))
      | _ -> t
  in
    match ret with
	Normal(_) -> err "Internal error: compact_literals_term did not strip off Normal."
      | _ -> ret
;;

let rec collect_fun_syms(t:term) : string list =
  match t with
      Var(_) -> []
    | Normal(t') -> collect_fun_syms t'
    | App(f,ts) -> f::(List.concat (List.map collect_fun_syms ts));;

let rec print_term_c (compact_lits:bool) (os:string -> unit) (t:term) : unit =
  let t = (if !print_raw then t 
	   else 
	     let t = dot_flatten t in
	       if compact_lits then compact_literals_term t else t) in
  match t with
      Var(x) -> os "x"; os (string_of_int x)
    | Normal(t) -> 
	if !print_raw then os "[";
	print_term_c compact_lits os t;
	if !print_raw then os "]";
    | App(f,ts) -> 
	let defpr () = os (Util.safe_string f); os "("; print_args compact_lits os ts; os ")" in
	if ((f = "dot" || f = "odot") && (List.length ts = 2) && not !print_raw) then
	  (match ts with
	       [t1;t2] ->
		 print_term_c compact_lits os t1; os " . "; print_term_c compact_lits os t2
	     | _ -> defpr())
	else if ts = [] then
	  os (Util.safe_string f)
	else
	  defpr()
and print_args (compact_lits:bool) (os:string -> unit) (ts:term list) : unit =
  match ts with
      [] -> ()
    | [t] -> print_term_c compact_lits os t
    | t::ts -> print_term_c compact_lits os t; os ", "; print_args compact_lits os ts;;	

let print_term (os:string->unit) (t:term) : unit =
  print_term_c false os t;;

let print_term_compact_lits (os:string->unit) (t:term) : unit =
  print_term_c true os t;;

let rec eq_term (dbg:string -> unit) (t1:term) (t2:term) : bool =
  dbg "(eq term ";
  print_term dbg t1;
  dbg " ";
  print_term dbg t2;
  dbg "\n";
  let ret = 
    match t1,t2 with
	Var(x),Var(y) -> x = y
      | Normal(t1'),t2' | t1',Normal(t2')  -> eq_term dbg t1' t2'
      | App(f,args), App(g,args') ->
	  if f = g then
	    eq_term_args dbg args args'
	  else
	    false
      | _,_ -> false in
    dbg " => ";
    dbg (if ret then "true" else "false");
    dbg ")\n";
    ret
and eq_term_args (dbg:string -> unit) (args1:term list) (args2:term list) : bool =
  match args1,args2 with
      a::args1', a'::args2' ->
	if eq_term dbg a a' then
	  eq_term_args dbg args1' args2'
	else
	  false
    | [],[] -> true
    | _,_ -> false;;
