# Makefile originally taken from coq-club

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf _CoqProject

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:
	@echo -Q src MSTPE > _CoqProject
	@echo src/*.v 		 >> _CoqProject

Makefile: ;

phony: ;

.PHONY: all clean phony