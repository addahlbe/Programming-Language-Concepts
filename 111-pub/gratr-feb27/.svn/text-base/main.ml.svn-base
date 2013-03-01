open Arg;;
open Util;;
open Trie;;

let infile = ref stdin;;
let dbg_parsing = ref true;;
let print_rr_terms = ref false;;
let print_parse_seq = ref false;;
let rewrite_rules_only = ref false;;
let continue_with_nonterminating = ref false;;
let skip_analyses = ref false;;

let file_to_parse = ref None;;
let set_file_to_parse(f:string):unit =
  file_to_parse := Some(f);;

let file_to_run = ref None;;
let set_file_to_run(f:string):unit =
  file_to_run := Some(f);;

let file_to_parse = ref None;;
let set_file_to_parse(f:string):unit =
  file_to_parse := Some(f);;

(*let set_stackdepth d =
  Aut.lr_aut := Some(d);;*)

let usage = "Usage: gra2srs [options] <file>\n";;

let options =
  align 
    ["--run", String set_file_to_run, 
     " Run the automaton on the contents of the named file; the results will be written to run.txt."; 
     "--parse", String set_file_to_parse, 
     " Parse the contents of the named file; the results will be written to parsed.txt."; 
     "--print-parse-seq", Set print_parse_seq, 
     " When parsing (with --parse), print the step-by-step transformation of the run, to parsed.txt."; 
     "--rewrite-rules-only", Set rewrite_rules_only,
     " Stop after analyzing the rewriting rules (in the Rules) section for termination and local confluence.\n";
     "--crude-aut", Set Aut.crude_aut,
     " Construct a very crude approximating automaton (faster but greater risk of failing local confluence.)\n";
     "--skip-analyses", Set skip_analyses,
     " Skip all the analyses of the grammar and rewrite rules, to go straight to parsing (but still must construct automata).\n";
     "--continue-with-nonterminating", Set continue_with_nonterminating,
     " Continue even if we cannot confirm that the rewriting rules are terminating.\n";
     "--stop-before-determinization", Set Aut.stop_before_determinization, 
     " Stop before determinizing the automaton.\n";
     "--print-raw",               Set Term.print_raw, 
     " Print terms in a raw form.";
     "--no-eos", Set Grammar.no_eos, 
     " Do not add _sos and _eos symbols for the start and end of the input string (default is to add them).";
(*     "--lr-aut", Int set_stackdepth,
     " Use this flag with a nonnegative integer N to construct an LR(N)-style automaton (default is to construct an RTN-style aut.)";*)
     "--print-rr-terms", Set print_rr_terms,
     " Print run-rewriting rules and terms as first-order rules and terms";
     "--no-debug-parsing", Clear dbg_parsing, 
     " Do not write to the report file for the overall parsing process.";
     "--debug-grammar-to-ast",          Set Grammar.dbg_grammar_to_ast,
     " Debug the conversion of an EBNF grammar to a BNF grammar.";
     "--debug-convert-grammar", Set Parsing_trs.dbg_convert_grammar, 
     " Debug the conversion of a grammar to a TRS.";
     "--debug-construct-nfa", Set Aut.dbg_construct_aut, 
     " Debug the construction of the original non-deterministic automaton.";
     "--debug-construct-nfa-micro", Set Aut.dbg_construct_aut_micro, 
     " Micro-level debugging of the construction of the original non-deterministic automaton.";
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
     " Micro-level debugging of local-confluence testing.";
     "--debug-cps", Set Localconf.dbg_cps,
     " Debug the computation of critical pairs in local-confluence testing.";
     "--debug-run-rewriting", Set Run_rewriting.dbg_run_rewriting,
     " Debug the generation and rewriting of runs of the automaton.";
     "--debug-run-rewriting-micro", Set Run_rewriting.dbg_run_rewriting_micro,
     " Micro-level debugging of generation and rewriting of runs of the automaton.";
     "--debug-refine", Set Aut.dbg_refine,
     " Debug the refinement of the forward automaton by the reverse one.";
     "--hide-intermediate-automata", Clear Aut.dbg_intermed_aut,
     " Hide the intermediate automata generated."
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
	  let (Grammar.Grammar(gname,start,_,
			       (Grammar.SyntacticNts(syn_nts),Grammar.ReadingNts(read_nts),_,_,Grammar.Nullable(nullable)),
			       _,_,reorganizing_trs)) = g in

	    Grammar.dump_grammar dbg g;

	    if !skip_analyses then
	      dbg "(Skipping termination and local confluence checks for the reorganizing rewriting rules.)\n"
	    else
              (let sn = Termination.terminating reorganizing_trs in
		 if sn then
		   dbg "(The reorganizing TRS is terminating.)\n"
		 else
		   (dbg "(The reorganizing TRS might be non-terminating (cannot tell for sure).)\n";
		    if (not !continue_with_nonterminating) then
		      (print_string "The rewriting rules cannot be confirmed to be terminating.\n";
		       print_string "Run gratr with --continue-with-nonterminating to continue past this point.\n";
		       exit 1));

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
		   dbg "(Local confluence of the reorganizing TRS: true)\n\n");
	    
	      if !rewrite_rules_only then
		(dbg "(We are stopping early, since the --rewrite-rules-only flag was given.)\n";
		 exit 1);

	      let trs = Parsing_trs.convert_grammar g in
		
		(dbg "(The parsing TRS for the grammar is:\n";
		 Parsing_trs.print_parsing_trs dbg trs;
		 dbg ")\n");

		let (min_rau,rev_rau,ref_rau) = Aut.construct_parsing_aut dbg gname start trs in
		let (min_prlab,min_au) = min_rau in 
		let (rev_prlab,rev_au) = rev_rau in 
		let (ref_prlab,ref_au) = ref_rau in 

		let is_reading_sym s = Trie.trie_contains syn_nts s || Trie.trie_contains read_nts s in
		let rtrs = Run_rewriting.get_rr_trs gname start is_reading_sym ref_rau in
		  if !print_rr_terms then
		    Trs.print_trs dbg rtrs
		  else
		    Run_rewriting.print_run_trs dbg rtrs;
		  
		  if !skip_analyses then
		    dbg "(Skipping analysis of parsing rewrite rules for local confluence.)\n"
		  else
		    (let lc' = Run_rewriting.locally_confluent rtrs reorganizing_trs in		    
		       
		     let msg s = "The run-rewriting rules with the reorganizing rules are "^s^"locally confluent.\n" in
		       if nonempty lc' then
			 (print_string (msg "not ");
			  print_string "See report.txt for details.\n";
			  dbg "(----------------------------------------------------\n";
			  dbg (msg "not ");
			  let len = List.length lc' in
			  let lc' = take 10 lc' in 
			    dbg "Found ";
			    dbg (string_of_int len);
			    dbg " critical pairs.\n";
			    if len > 10 then
			      dbg "Here are the first 10:(\n"
			    else
			      dbg "They are:\n";

			    List.iter (if !print_rr_terms then Localconf.print_cp dbg else Run_rewriting.print_run_cp dbg) lc';
			    
			    dbg ")\n";
			    exit 1)
		       else
			 dbg (msg ""));
		    
		    (match !file_to_run with
			 Some(f) ->
			   let i = open_in f in
			   let o = open_out "run.txt" in
			   let ss = Run_rewriting.stringlist_from_file i in
			   let r = Run_rewriting.run_aut min_au ss in
			     close_in i;
			     dbg "(Run of the automaton on input from file \"";
			     dbg f;
			     dbg "\":\n\n  ";
			     Run_rewriting.print_run dbg dbg r;
			     dbg "\n\n)\n";
			     Run_rewriting.print_run (output_string o) (output_string o) r;
			     close_out o
		       | _ -> ());

		    (match !file_to_parse with
			 Some(f) ->
			   let i = open_in f in
			   let o = open_out "parsed.txt" in
			   let os = output_string o in
			   let ss = Run_rewriting.stringlist_from_file i in
			   let r = Run_rewriting.run_aut rev_au (List.rev ss) in
			     close_in i;
			     dbg "(Run of the backward automaton on the reverse of the input from file \"";
			     dbg f;
			     dbg "\":\n\n  ";
			     Run_rewriting.print_run dbg dbg r;
			     dbg "\n\n)\n";
			     (match Run_rewriting.stringlist_of_string_run r with
				  None -> 
				    os "The reversed input could not be recognized with the backward automaton.\n";
				    os "The failing run is:\n";
				    Run_rewriting.print_run os os r;
				| Some(ss) ->
				    (* reverse the run and the rewrite with the refined automaton *)
				    let r2 = Run_rewriting.run_aut ref_au (List.rev (Aut.extra_nt::ss)) in
				      close_in i;
				      dbg "(Run of the refined automaton on the reverse of the run just listed:\n\n  ";
				      Run_rewriting.print_run dbg dbg r2;
				      dbg "\n\n)\n";
				      let t = Run_rewriting.term_of_string_run r2 in
				      let dbgr = debugger Localconf.dbg_rewriting in
				      let rules = Trs.union_trs rtrs reorganizing_trs in
				      let ps = Rewriting.rewrite_inner_trs dbgr true rules t in
				      let p = List.hd ps in
					dbg "(The rewritten run:\n";
					Run_rewriting.print_run_term dbg p;
					dbg "\n)\n";
					if !print_parse_seq then
					  Run_rewriting.print_run_red_seq os (List.rev ps)
					else
					  Run_rewriting.print_run_term os p;
					os "\n"
			     );
			     close_out o
		       | _ -> ());
;;

close_out reportfile;;
1
