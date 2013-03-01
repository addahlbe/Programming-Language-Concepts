gratr: trie.cmx gra2srs_util.cmx gra2srs_syntax.cmx gra2srs_parse.cmx gra2srs_lex.cmx gra2srs_pp.cmx gra2srs_eq.cmx gra2srs_gviz.cmx gra2srs_ppast.cmx util.cmx term.cmx trs.cmx grammar.cmx parsing_trs.cmx termination.cmx aut.cmx rewriting.cmx localconf.cmx run_rewriting.cmx main.cmx 
	ocamlopt -o gratr str.cmxa trie.cmx gra2srs_util.cmx gra2srs_syntax.cmx gra2srs_parse.cmx gra2srs_lex.cmx gra2srs_pp.cmx gra2srs_ppast.cmx gra2srs_gviz.cmx gra2srs_eq.cmx util.cmx term.cmx trs.cmx grammar.cmx parsing_trs.cmx termination.cmx  aut.cmx rewriting.cmx localconf.cmx run_rewriting.cmx main.cmx 

main.cmx: main.ml gra2srs_ppast.cmx gra2srs_pp.cmx gra2srs_parse.cmx gra2srs_lex.cmx gra2srs_gviz.cmx util.cmx term.cmx grammar.cmx termination.cmx trs.cmx aut.cmx gra2srs_syntax.cmx localconf.cmx run_rewriting.cmx
	ocamlopt -c main.ml

completion.cmx: completion.ml gra2srs_ppast.cmx gra2srs_pp.cmx gra2srs_parse.cmx gra2srs_lex.cmx gra2srs_gviz.cmx util.cmx term.cmx grammar.cmx  trs.cmx 
	ocamlopt -c completion.ml

run_rewriting.cmx: run_rewriting.ml aut.cmx util.cmx term.cmx grammar.cmx trs.cmx localconf.cmx
	ocamlopt -c run_rewriting.ml

aut.cmx: aut.ml util.cmx term.cmx grammar.cmx  trs.cmx parsing_trs.cmx
	ocamlopt -c aut.ml

rewriting.cmx: rewriting.ml util.cmx term.cmx grammar.cmx trs.cmx 
	ocamlopt -c rewriting.ml

localconf.cmx: localconf.ml util.cmx term.cmx grammar.cmx trs.cmx rewriting.cmx
	ocamlopt -c localconf.ml

trie.cmx: trie.ml
	ocamlopt -c trie.ml

term.cmx: term.ml util.cmx
	ocamlopt -c term.ml

util.cmx: util.ml trie.cmx
	ocamlopt -c util.ml

trs.cmx: trs.ml util.cmx term.cmx
	ocamlopt -c trs.ml

parsing_trs.cmx: parsing_trs.ml util.cmx trs.cmx term.cmx grammar.cmx
	ocamlopt -c parsing_trs.ml

grammar.cmx: grammar.ml util.cmx term.cmx trs.cmx trie.cmx gra2srs_syntax.cmx
	ocamlopt -c grammar.ml

gra2srs_syntax.cmx: gra2srs_syntax.ml gra2srs_util.cmx 
	ocamlopt -c gra2srs_syntax.ml

gra2srs_pp.cmx: gra2srs_pp.ml gra2srs_syntax.cmx 
	ocamlopt -c gra2srs_pp.ml

gra2srs_ppast.cmx: gra2srs_ppast.ml gra2srs_syntax.cmx 
	ocamlopt -c gra2srs_ppast.ml

gra2srs_gviz.cmx: gra2srs_gviz.ml gra2srs_syntax.cmx 
	ocamlopt -c gra2srs_gviz.ml

gra2srs_eq.cmx: gra2srs_eq.ml gra2srs_syntax.cmx 
	ocamlopt -c gra2srs_eq.ml

gra2srs_util.cmx: gra2srs_util.ml 
	ocamlopt -c gra2srs_util.ml

gra2srs_lex.cmx: gra2srs_lex.ml gra2srs_util.cmx gra2srs_parse.cmi 
	ocamlopt -c gra2srs_lex.ml

gra2srs_parse.cmx: gra2srs_parse.ml gra2srs_util.cmx gra2srs_syntax.cmx gra2srs_parse.cmi 
	ocamlopt -c gra2srs_parse.ml

gra2srs_parse.cmi: gra2srs_parse.mli gra2srs_syntax.cmx 
	ocamlopt -c gra2srs_parse.mli

gra2srs_parse.mli gra2srs_parse.ml: gra2srs_parse.mly gra2srs_syntax.cmx
	ocamlyacc -v gra2srs_parse.mly

gra2srs_lex.ml: gra2srs_lex.mll gra2srs_parse.cmi 
	ocamllex gra2srs_lex.mll

termination.cmi: termination.mli grammar.cmx
	ocamlopt -c termination.mli

termination.cmx: termination.ml term.cmx grammar.cmx termination.cmi
	ocamlopt -c termination.ml

clean:
	rm -f gra2srs_lex.ml gra2srs_parse.mli gra2srs_parse.ml *.cmx *.cmo *.cmi *.o gra2srs

