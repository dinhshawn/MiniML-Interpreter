all: miniml tests

miniml: miniml.ml
	ocamlbuild miniml.byte

tests: tests.ml
	ocamlbuild tests.byte

clean:
	rm -rf _build *.byte
