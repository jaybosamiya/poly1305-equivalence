update-all-existing-hints : $(wildcard *.fst.hints)

gen-all : Axioms.phony KeyEquivalence.phony MsgEquivalence.phony MapEquivalence.phony Poly1305.Equivalence.phony TagEquivalence.phony ThirdSpec.phony UsefulLemmas.phony

%.hints :
	fstar --use_hints --record_hints $(patsubst %.hints,%,$@)

%.phony :
	fstar --use_hints --record_hints $(patsubst %.phony,%.fst,$@)
