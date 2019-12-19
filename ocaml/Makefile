PROGS=enum_all count_all solve test
LIB=lib2less.ml


all: ${PROGS}


% : %.ml
	ocamlopt -o $@ ${LIB} $<


clean:
	rm -f *.cmi *.cmx *.o
	rm -f ${PROGS}


.PHONY: clean
