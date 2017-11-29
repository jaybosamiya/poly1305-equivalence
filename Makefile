update-all-existing-hints : $(patsubst %.fst.hints,%.phony,$(wildcard *.fst.hints))

gen-all : Axioms.phony KeyEquivalence.phony MsgEquivalence.phony Poly1305.Equivalence.phony TagEquivalence.phony ThirdSpec.phony UsefulLemmas.phony

%.phony :
	fstar --use_hints --record_hints $(patsubst %.phony,%.fst,$@)
