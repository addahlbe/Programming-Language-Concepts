open Arg;;
open Util;;
open Trie;;

let infile = ref stdin;;
let do_print_grammar = ref false;;
let do_dump_grammar = ref false;;
let do_print_trs = ref false;;
let dbg_parsing = ref true;;
let stop_before_determinization = ref false;;

let file_to_parse = ref None;;
let set_file_to_parse(f:string):unit =
  file_to_parse := Some(f);;

let file_to_run = ref None;;
let set_file_to_run(f:string):unit =
  file_to_run := Some(f);;

let usage = "Usage: gra2srs [options] <file>\n";;

let options =
  align 
  ["--print-trs",      Set do_print_trs,     
   " print the parsing TRS";
   "--print-grammar",  Set do_print_grammar, 
   " print the converted grammar";
   "--dump-grammar",  Set do_dump_grammar, 
   " dump information on the converted grammar";
   "--run", String set_file_to_run, 
   " Run the automaton on the contents of the named file; the results will be written to run.txt."; 
   "--parse", String set_file_to_parse, 
   " Parse the contents of the named file; the results will be written to parsed.txt."; 
   "--stop-before-determinization", Set stop_before_determinization, 
   " Stop before determinizing the automaton.\n";
   "--print-raw",               Set Term.print_raw, 
   " Print terms in a raw form.";
   "--lang-only", Set Grammar.approx_lang_only, 
   " Construct an automaton approximating the language of the grammar, not its sentential language.";
   "--no-debug-parsing", Clear dbg_parsing, 
   " Do not write to the report file for the overall parsing process.";
   "--debug-grammar-to-ast",          Set Grammar.dbg_grammar_to_ast,
   " Debug the conversion of an EBNF grammar to a BNF grammar.";
   "--debug-convert-grammar", Set Parsing_trs.dbg_convert_grammar, 
   " Debug the conversion of a grammar to a TRS.";
   "--debug-construct-automaton", Set Aut.dbg_construct_aut, 
   " Debug the construction of the automaton.";
   "--debug-construct-automaton-micro", Set Aut.dbg_construct_aut_micro, 
   "";
   "--debug-determinization", Set Aut.dbg_determinization, 
   " Debug determinization of the automaton.";
   "--debug-determinization-micro", Set Aut.dbg_determinization_micro, 
   " Micro debugging of determinization of the automaton.";
   "--debug-minimization", Set Aut.dbg_minimization, 
   " Debug minimization of the automaton.";
   "--debug-rewriting", Set Localconf.dbg_rewriting,
   " Debug rewriting during local-confluence testing.";
   "--debug-local-confluence", Set Localconf.dbg_local_conf,
   " Debug local-confluence testing.";
   "--debug-local-confluence-micro", Set Localconf.dbg_local_conf_micro,
   " Micr-level debugging of local-confluence testing.";
   "--debug-cps", Set Localconf.dbg_cps,
   " Debug the computation of critical pairs in local-confluence testing.";
   "--debug-run-rewriting", Set Run_rewriting.dbg_run_rewriting,
   " Debug the generation and rewriting of runs of the automaton.";
  ];; 

Arg.parse options (fun a -> Gra2srs_util.fname := a; infile := open_in a) usage;;

let reportfile = 
  try
    open_out "report.txt"
  with
      _ ->
	print_string "There was a problem opening report.txt, which we will use to report on the analysis of the grammar.\n";
	exit 1
;;

set_debugger_out reportfile;;

let () =
  let parsed =
     let lexbuf = Lexing.from_channel !infile in
       Gra2srs_parse.main Gra2srs_lex.token lexbuf 
  in

  match parsed with
      None -> ()
    | Some(x) ->
	let dbg = debugger dbg_parsing in
	let g = Grammar.to_ast x in
	let (Grammar.Grammar(_,start,_,(Grammar.SyntacticNts(syn_nts),Grammar.ReadingNts(read_nts),_,_),_,_,reorganizing_trs)) = g in

	  (match !file_to_run, !Grammar.approx_lang_only with
	      Some(_), false ->
		print_string "If you give the --run command-line flag, you must also supply the --lang-only flag.\n";
		exit 1
	    | _, _ -> ());

	  if !do_print_grammar then
	    Grammar.print_grammar dbg g;
	  if !do_dump_grammar then
	    Grammar.dump_grammar dbg g;

          let sn = Termination.terminating reorganizing_trs in
	  dbg "(Termination of the reorganizing TRS: ";
	  dbg (string_of_bool sn);
	  dbg ")\n\n";

          let lc = Localconf.locally_confluent reorganizing_trs in
	    if nonempty lc then
	      (print_string "The term-rewriting system for parse trees is not locally confluent.\n";
	       print_string "See report.txt for details.\n";
	       dbg "(----------------------------------------------------\n";
	       dbg "The rules for rewriting parse trees are not locally confluent.\n";
	       dbg (string_of_int (List.length lc));
	       dbg " critical pairs found:(\n";
	       List.iter (Localconf.print_cp dbg) lc;
	       dbg ")\n";
	       exit 1);
	    dbg "(Local confluence of the reorganizing TRS: true)\n\n";
	  
	  let trs = Parsing_trs.convert_grammar g in
	    
	    if !do_print_trs then
	      (dbg "(The parsing TRS for the grammar is:\n";
	       Parsing_trs.print_parsing_trs dbg trs;
	       dbg ")\n");


	    let rau = Aut.construct_rtn_aut start trs in
	    let (im,prlab,au) = rau in

	    let dbg_im what im = 
	      dbg "(Items associated with ";
	      dbg what;
	      dbg " states:\n";
	      Aut.print_item_map dbg im ;
	      dbg ")"
	    in
	    let dbg_prlab what prlab states =
	      dbg "(Prules associated with ";
	      dbg what;
	      dbg " states:\n";
	      List.iter (fun st -> 
			   let ps = prlab.(st) in
			     if nonempty ps then
			       (dbg "(";
				dbg (string_of_int st);
				dbg " :\n";
				List.iter (fun p ->  dbg " "; Parsing_trs.print_prule dbg p) ps;
				dbg ")\n"))
		states;
	      dbg ")"
	    in
	    let item_from_nfa_state s =
	      match im.(s) with
		  [i] -> i
		| _ -> err "Internal error getting sole item for nfa state."
	    in
	    let dbg_nfa_state st = 
	      dbg (string_of_int st);
	      dbg " : ";
	      dbg (item_from_nfa_state st)
	    in
	      dbg "(The nondeterministic automaton:\n";
	      Aut.print_aut dbg dbg_nfa_state au;
	      dbg "\n";
	      dbg_im "NFA" im;
	      dbg "\n";
	      dbg_prlab "NFA" prlab (Aut.get_states au);
	      Aut.write_aut_dot "nfa" string_of_int au;
	      dbg ")\n";

	      if !stop_before_determinization then
		(dbg "Stopping as requested, before determinization.\n";
		 exit 0);

	      let (rau',st_map) = Aut.determinize_aut (im,prlab,au) in
	      let (im',prlab',au') = rau' in
		dbg "\n(The deterministic automaton:\n";
		Aut.print_aut dbg (fun x -> dbg (string_of_int x)) au';
		dbg "\n";
		dbg_im "DFA" im';
		dbg "\n";
		dbg_prlab "DFA" prlab' (Aut.get_states au');
		Aut.write_aut_dot "dfa" string_of_int au';
		dbg ")\n";

	      let dbg_state_list (ss:Aut.state_t list) : unit = 
		dbg "["; List.iter (fun s -> dbg " "; Aut.print_state dbg s) ss; dbg " ]" 
	      in
	      let dbg_state_map st_map =
		dbg "(The state map is:";
		List.iter (fun st -> 
			     dbg "\n"; 
			     dbg_state_list st; 
			     dbg " -> "; 
			     match inttrie_lookup st_map st with
				 None -> err "Internal error printing state map.\n"
			       | Some(s) -> dbg (string_of_int s))
		  (inttrie_domain st_map);
		dbg ")\n"
	      in
		dbg_state_map st_map;
		
		let (rau'',quot_map) = Aut.minimize_aut (im',prlab',au') in
		let (im'',prlab'',au'') = rau'' in

		dbg "\n(The minimized deterministic automaton:\n";
		Aut.print_aut dbg (fun x -> dbg (string_of_int x)) au'';
		dbg "\n";
		dbg_im "Min DFA" im'';
		dbg "\n";
		dbg_prlab "Min DFA" prlab'' (Aut.get_states au'');
		Aut.write_aut_dot "min" string_of_int au'';
		dbg ")\n";

		dbg_state_map quot_map;

		let rev_rau = fst (Aut.minimize_aut (fst (Aut.determinize_aut (Aut.reverse rau)))) in
		let (rev_im,rev_prlab,rev_au) = rev_rau in
		  
		dbg "\n(The minimized deterministic reverse automaton:\n";
		Aut.print_aut dbg (fun x -> dbg (string_of_int x)) rev_au;
		dbg "\n";
		dbg_im "Reverse Min DFA" rev_im;
		dbg "\n";
		dbg_prlab "Reverse Min DFA" rev_prlab (Aut.get_states rev_au);
		Aut.write_aut_dot "rev" string_of_int rev_au;
		dbg ")\n";

		(match !file_to_run with
		     Some(f) ->
		       let i = open_in f in
		       let o = open_out "run.txt" in
		       let r = Run_rewriting.run_aut au'' i in
			 dbg "(Run of the automaton on input from file \"";
			 dbg f;
			 dbg "\":\n\n  ";
			 Run_rewriting.print_run dbg (Term.print_term dbg) r;
			 dbg "\n\n)\n";
			 Run_rewriting.print_run (output_string o) (Term.print_term (output_string o)) r
		   | _ -> ());

		if !Grammar.approx_lang_only then
		  (dbg "(We are stopping after minimizing the DFA, because the --lang-only flag was given.)\n";
		   exit 0);

(*
		let rau'' = rau' in
		let (_,_,au'') = rau'' in
*)

		let rrs = Run_rewriting.get_rrules rau'' in
		  
		  dbg "(The ";
		  dbg (string_of_int (List.length rrs));
		  dbg " run-rewriting rules:\n";
		  List.iter (Run_rewriting.print_rrule dbg) rrs;
		  dbg ")\n";

		  let is_reading_sym s =
		    Trie.trie_contains syn_nts s || Trie.trie_contains read_nts s
		  in
		    
		  let rtrs = Trs.Trs(List.map (Run_rewriting.convert_rrule is_reading_sym) rrs) in
(*		    dbg "(The term-rewriting versions of the run rewriting rules:\n";
		    Trs.print_trs dbg rtrs;
		    dbg ")\n";
*)
		    let lc' = Run_rewriting.locally_confluent rtrs reorganizing_trs in		    

		      if nonempty lc' then
			(print_string "The run-rewriting rules are not locally confluent (so the grammar may be ambiguous).\n";
			 print_string "See report.txt for details.\n";
			 dbg "(----------------------------------------------------\n";
			 dbg "(The run-rewriting rules are not locally confluent.)\n";
			 let len = List.length lc' in
			   if len > 1 then
			     (dbg (string_of_int len);
			      dbg " critical pairs found in the first batch:(\n")
			   else
			     dbg "The first critical pair found:(\n";
			   List.iter (Run_rewriting.print_run_cp dbg) lc';
			   dbg ")\n";
			   exit 1)
		      else
			dbg "(The run-rewriting rules are locally confluent.  We can parse with this grammar.)\n";

;;

close_out reportfile;;
