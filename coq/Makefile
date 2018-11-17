all: Makefile.coq
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
