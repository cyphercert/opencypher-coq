COQMODULE    := OpencypherCoq
COQTHEORIES  := src/*.v

.PHONY: all theories fmt lint docs clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=6

_CoqProject.dune: Makefile $(COQTHEORIES)
	(echo "-R _build/default/src $(COQMODULE)"; \
	echo _build/default/$(COQTHEORIES)) > _CoqProject.dune

_CoqProject: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject

Makefile.coq: _CoqProject
	opam exec -- coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	rm -f src/*.glob
	rm -f src/*.vo
	rm -f src/*.vok
	rm -f src/*.vos
	rm -f src/.*.aux
	rm -f _CoqProject.dune
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf

docs: Makefile.coq
	$(MAKE) -f Makefile.coq coqdoc

fmt:
	opam exec -- dune build @fmt --auto-promote

lint:
	opam exec -- dune build @fmt
	opam lint .

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES) 
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)
	sed -i 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i 's/\^\*/＊/g' $(COQTHEORIES)
