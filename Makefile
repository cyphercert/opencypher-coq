COQMODULE    := OpencypherCoq
COQTHEORIES  := src/*.v

.PHONY: all theories fmt lint docs tags clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=6

_CoqProject: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f src/.*.aux
	rm -f _CoqProject Makefile.coq Makefile.coq.conf

tags:
	ctags --options=coq.ctags -R -o .tags `echo $(COQTHEORIES)`

docs: Makefile.coq
	$(MAKE) -f Makefile.coq coqdoc

lint:
	opam lint .

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES) 
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)
	sed -i 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i 's/\^\*/＊/g' $(COQTHEORIES)
