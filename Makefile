.PHONY: clean build install uninstall default doc

default:
	@echo "available targets:"
	@echo "  build        compile prop, first_order, and Ensembles"
	@echo "  test         compile and run tests"
	@echo "  test.debug   compile and run in debug mode prop_test, a test suite"
	@echo "  coverage     compile and run tests with instrumented bisect_ppx coverage"
	@echo "  cov_report   create a coverage report from the latest coverage run"
	@echo "  clean        remove build directory"
	@echo "  install      install via ocamlfind"
	@echo "  uninstall    unintall via ocamlfind"
	@echo "  merlinize    create .merlin file"
	@echo "  doc          create documentation"

build:
	ocamlbuild -use-ocamlfind -cflag -safe-string -I util -I prop proof_prop.native
	ocamlbuild -use-ocamlfind -cflag -safe-string -I util -I prop -I first_order theory.native
	ocamlbuild -use-ocamlfind -cflag -safe-string -I util -I prop -I first_order -I Ensembles ensembles.native

test:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -I util -I prop -I prop/test test_formula_prop.native  && \
	rm test_formula_prop.native && \
	mv _build/prop/test/test_formula_prop.native test_formula_prop && \
	./test_formula_prop

test.debug:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -I util -I prop -I prop/test prop_test.d.byte  && \
	rm prop_test.d.byte && \
	mv _build/prop/test/prop_test.d.byte prop_test && \
	ocamldebug -I _build/prop -I _build/prop/test -I _build/util  ./prop_test

coverage:
	rm -f bisect*.out
	ocamlbuild -use-ocamlfind -pkgs oUnit,bisect_ppx.fast -cflag -safe-string -I util -I prop -I prop/test  prop_test.native
	rm prop_test.native
	mv _build/prop/test/prop_test.native prop_test_coverage
	prop_test_coverage

clean:
	ocamlbuild -clean && \
	rm -f *.native && \
	rm -f prop_test prop_test_coverage && \
	rm -f bisect*.out && \
	rm -rf report_dir

install:
	ocamlfind install prop META \
		_build/src/lib/prop.cmi \
		_build/src/lib/prop.cmo \
		_build/src/lib/prop.cmx \
		_build/src/lib/prop.a \
		_build/src/lib/prop.o \
		_build/src/lib/prop.cma \
		_build/src/lib/prop.cmxa \
		_build/src/lib/prop.cmxs

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
