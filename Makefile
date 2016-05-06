.PHONY: clean build install uninstall default doc

default:
	@echo "available targets:"
	@echo "  build        compile prop, first_order, and Ensembles"
	@echo "  test         compile and run tests"
	@echo "  test.debug   compile and run in debug mode test_formula_prop, a test suite"
	@echo "  coverage     compile and run tests with instrumented bisect_ppx coverage"
	@echo "  cov_report   create a coverage report from the latest coverage run"
	@echo "  clean        remove build directory"
	@echo "  install      install via ocamlfind"
	@echo "  uninstall    unintall via ocamlfind"
	@echo "  merlinize    create .merlin file"
	@echo "  doc          create documentation"

parser:
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop parser.native

build:
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop proof_prop.native
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order theory.native
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order -I Ensembles ensembles.native

test:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop_parser.native  && \
	rm test_formula_prop_parser.native && \
	mv _build/prop/test/test_formula_prop_parser.native test_formula_prop_parser && \
	./test_formula_prop_parser
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop.native  && \
	rm test_formula_prop.native && \
	mv _build/prop/test/test_formula_prop.native test_formula_prop && \
	./test_formula_prop
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_proof_prop.native  && \
	rm test_proof_prop.native && \
	mv _build/prop/test/test_proof_prop.native test_proof_prop && \
	./test_proof_prop
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_formula_first_order.native  && \
	rm test_formula_first_order.native && \
	mv _build/first_order/test/test_formula_first_order.native test_formula_first_order && \
	./test_formula_first_order

test.debug:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -I util -I prop -I prop/test test_formula_prop.d.byte  && \
	rm test_formula_prop.d.byte && \
	mv _build/prop/test/test_formula_prop.d.byte test_formula_prop && \
	ocamldebug -I _build/prop -I _build/prop/test -I _build/util  ./test_formula_prop

coverage:
	rm -f bisect*.out
	ocamlbuild -use-ocamlfind -pkgs oUnit,bisect_ppx.fast -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop.native
	rm test_formula_prop.native
	mv _build/prop/test/test_formula_prop.native test_formula_prop_coverage
	./test_formula_prop_coverage
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_proof_prop.native
	rm test_proof_prop.native
	mv _build/prop/test/test_proof_prop.native test_proof_prop
	./test_proof_prop
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_formula_first_order.native
	rm test_formula_first_order.native
	mv _build/first_order/test/test_formula_first_order.native test_formula_first_order
	./test_formula_first_order

clean:
	ocamlbuild -clean && \
	rm -f *.native && \
	rm -f test_formula_prop test_formula_prop_parser test_formula_prop_coverage test_proof_prop test_formula_first_order && \
	rm -f bisect*.out && \
	rm -rf report_dir

install:
	ocamlfind install prop META 

uninstall:
	ocamlfind remove prop

merlinize:
	echo 'S .' > .merlin
	echo 'S util/**' >> .merlin
	echo 'S prop/**' >> .merlin
	echo 'B _build' >> .merlin

doc:
	cp prop/prop.mlpack prop.odocl && \
	ocamlbuild -I prop/-docflags -charset,UTF-8,-keep-code,-colorize-code,-html,-short-functors prop.docdir/index.html && \
	rm prop.docdir && \
	ln -s _build/prop.docdir/ doc && \
	rm prop.odocl

cov_report: 
	cd _build && \
	bisect-ppx-report -html ../report_dir ../bisect*.out
