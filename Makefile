EXT=byte

.PHONY: clean build install uninstall default doc

default:
	@echo "available targets:"
	@echo "  build        compile prop, first_order, and Ensembles"
	@echo "  test         compile and run tests"
	@echo "  test_prop.debug   compile and run in debug mode test_formula_prop, a test suite"
	@echo "  test_first_order_formula.debug   compile and run in debug mode test_first_order_formula, a test suite"
	@echo "  test_first_order_schemas.debug   compile and run in debug mode test_first_order_schemas, a test suite"
	@echo "  coverage     compile and run tests with instrumented bisect_ppx coverage"
	@echo "  cov_report   create a coverage report from the latest coverage run"
	@echo "  clean        remove build directory"
	@echo "  install      install via ocamlfind"
	@echo "  uninstall    unintall via ocamlfind"
	@echo "  merlinize    create .merlin file"
	@echo "  doc          create documentation"

parser:
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order formula_prop.cmi formula.cmi signature.cmi
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop prop_parser.${EXT}
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order  first_order_parser.${EXT}

build: parser
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop proof_prop.${EXT}
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order theory.${EXT}
	ocamlbuild -use-ocamlfind -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order -I Ensembles ensembles.${EXT}

test: build
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop_parser.${EXT}  && \
		rm test_formula_prop_parser.${EXT} && \
		mv _build/prop/test/test_formula_prop_parser.${EXT} test_formula_prop_parser && \
		./test_formula_prop_parser
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop.${EXT}  && \
		rm test_formula_prop.${EXT} && \
		mv _build/prop/test/test_formula_prop.${EXT} test_formula_prop && \
		./test_formula_prop
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_proof_prop.${EXT}  && \
		rm test_proof_prop.${EXT} && \
		mv _build/prop/test/test_proof_prop.${EXT} test_proof_prop && \
		./test_proof_prop
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_formula_first_order.${EXT}  && \
		rm test_formula_first_order.${EXT} && \
		mv _build/first_order/test/test_formula_first_order.${EXT} test_formula_first_order && \
		./test_formula_first_order
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_schemas_first_order.${EXT}  && \
		rm test_schemas_first_order.${EXT} && \
		mv _build/first_order/test/test_schemas_first_order.${EXT} test_schemas_first_order && \
		./test_schemas_first_order
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I prop -I Ensembles -I Ensembles/test test_ensembles.${EXT}  && \
		rm test_ensembles.${EXT} && \
		mv _build/Ensembles/test/test_ensembles.${EXT} test_ensembles && \
		./test_ensembles

test_prop.debug:
		rm -f test_formula_prop.byte && \
	ocamlbuild -use-ocamlfind -tag 'debug' -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop.byte  && \
		mv _build/prop/test/test_formula_prop.byte test_formula_prop && \
		ocamldebug -I _build/prop -I _build/prop/test -I _build/util  ./test_formula_prop

test_first_order_formula.debug:
	rm -f test_formula_first_order && \
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test -tag 'debug' test_formula_first_order.byte  && \
		ocamldebug -cd _build/first_order/test  -I _build/first_order -I _build/first_order/test -I _build/util test_formula_first_order.byte

test_first_order_schemas.debug:
	rm -f test_schemas_first_order && \
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test -tag 'debug' test_schemas_first_order.byte  && \
		ocamldebug -cd _build/first_order/test  -I _build/first_order -I _build/first_order/test -I _build/util test_schemas_first_order.byte

test_schema.debug:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_schemas_first_order.d.byte  && \
		ocamldebug -cd _build/first_order/test  -I _build/first_order -I _build/first_order/test -I _build/util test_schemas_first_order.d.byte

coverage:
	rm -f bisect*.out
	ocamlbuild -use-ocamlfind -pkgs oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_formula_prop.${EXT}
	rm test_formula_prop.${EXT}
	mv _build/prop/test/test_formula_prop.${EXT} test_formula_prop_coverage
	./test_formula_prop_coverage
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I prop/test test_proof_prop.${EXT}
	rm test_proof_prop.${EXT}
	mv _build/prop/test/test_proof_prop.${EXT} test_proof_prop
	./test_proof_prop
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_formula_first_order.${EXT}
	rm test_formula_first_order.${EXT}
	mv _build/first_order/test/test_formula_first_order.${EXT} test_formula_first_order
	./test_formula_first_order
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I first_order -I first_order/test test_schemas_first_order.${EXT}
	rm test_schemas_first_order.${EXT}
	mv _build/first_order/test/test_schemas_first_order.${EXT} test_schemas_first_order
	./test_schemas_first_order
	ocamlbuild -use-ocamlfind  -package oUnit,bisect_ppx -cflag -safe-string -cflag -bin-annot -cflag -annot -pkg dyp -I util -I prop -I first_order -I Ensembles -I Ensembles/test test_ensembles.${EXT}
	rm test_ensembles.${EXT}
	mv _build/Ensembles/test/test_ensembles.${EXT} test_ensembles
	./test_ensembles

clean:
	ocamlbuild -clean && \
		rm -f *.${EXT} && \
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
	echo 'S first_order/**' >> .merlin
	echo 'B _build/**' >> .merlin

doc:
	cp prop/prop.mlpack prop.odocl && \
		ocamlbuild -I prop/-docflags -charset,UTF-8,-keep-code,-colorize-code,-html,-short-functors prop.docdir/index.html && \
		rm prop.docdir && \
		ln -s _build/prop.docdir/ doc && \
		rm prop.odocl

cov_report: 
	cd _build && \
		bisect-ppx-report -html ../report_dir ../bisect*.out
