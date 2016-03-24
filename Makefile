.PHONY: clean build install uninstall default doc

default:
	@echo "available targets:"
	@echo "  build        compile prop"
	@echo "  test         compile prop_tests, a test suite"
	@echo "  coverage     compile prop_test with instrumented bisect_ppx coverage"
	@echo "  cov_report   create a coverage report from the latest coverage run"
	@echo "  clean        remove build directory"
	@echo "  install      install via ocamlfind"
	@echo "  uninstall    unintall via ocamlfind"
	@echo "  merlinize    create .merlin file"
	@echo "  doc          create documentation"

build:
	ocamlbuild -use-ocamlfind -cflag -safe-string -I util -I prop  preuve_prop.native

test:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -I util -I prop -I prop/test prop_test.native  && \
	rm prop_test.native && \
	mv _build/prop/test/prop_test.native prop_test && \
	./prop_test

test.debug:
	ocamlbuild -use-ocamlfind  -package oUnit -cflag -safe-string -I util -I prop -I prop/test prop_test.d.byte  && \
	rm prop_test.d.byte && \
	mv _build/prop/test/prop_test.d.byte prop_test && \
	ocamldebug -I _build/prop -I _build/prop/test -I _build/util  ./prop_test

coverage:
	ocamlbuild -use-ocamlfind -pkgs oUnit,bisect_ppx.fast -cflag -safe-string -I util -I prop -I prop/test prop_test.native
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
	bisect-ppx-report -html ../report_dir ../$(shell ls -t bisect*.out | head -1)
