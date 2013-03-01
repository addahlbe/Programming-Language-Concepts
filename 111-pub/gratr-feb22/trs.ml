open Util;;
open Term;;

type rule = 
    Rule of 
      (string option (* Some(name) means this rule comes from the production with the given name *)
       * int (* the max var used *))
      * term (* lhs *)
      * term (* rhs *)
type trs = Trs of rule list

let canonize_rule (Rule((oname,max),lhs,rhs)) : rule =
  let a = Array.make (max+1) (-1) in
  let nextv = ref 0 in
  let newvar() = 
    let x = !nextv in
      incr nextv; 
      x 
  in
  let rec canonize_term (t:term) : term =
    match t with
	Var(i) -> 
	  if a.(i) = -1 then
	    let x = newvar() in
	      a.(i) <- x;
	      Var(x)
	  else
	    Var(a.(i))
      | Normal(t) -> Normal(canonize_term t)
      | App(f,args) -> App(f,List.map canonize_term args)
  in
  let nlhs = canonize_term lhs in
  let nrhs = canonize_term rhs in
    Rule((oname,!nextv-1),nlhs,nrhs);;

let compare_rules (r1:rule) (r2:rule) : int =
  let Rule(_,lhs1,rhs1) = (canonize_rule r1) in
  let Rule(_,lhs2,rhs2) = (canonize_rule r2) in
    if eq_term nodbg lhs1 lhs2 && eq_term nodbg rhs1 rhs2 then
      0
    else
      compare r1 r2;;


let print_rule (os:string -> unit) (Rule((oname,_),lhs,rhs)) : unit =
  (match oname with
       Some(name) -> os "["; os name; os "] "
     | None -> ());
  print_term os lhs;
  os " -> ";
  print_term os rhs;
  os "\n";;

let rename_rule (minv:int) (r:rule) : rule =
  let rec rename_term (t:term) : term =
    match t with
	Normal(t') -> Normal(rename_term t')
      | Var(x) -> Var(x+minv)
      | App(f,args) -> App(f,List.map rename_term args) in
  let Rule((oname,maxv),lhs,rhs) = r in 
    Rule((oname,maxv+minv),rename_term lhs, rename_term rhs);;


let print_trs (os:string -> unit) (Trs(rs)) : unit =
  List.iter (print_rule os) rs;;

let union_trs (Trs(s1)) (Trs(s2)) : trs =
  Trs(s1@s2);;

