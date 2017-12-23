# Poly1305-Equivalence

Steps to machine-check the proofs:
```sh
# The clone might take a while since it pulls vale and hacl* as well
git clone --recursive https://github.com/jaybosamiya/poly1305-equivalence
cd poly1305-equivalence

# Apply minor patch to squash some trivial warnings and errors
git apply --directory=hacl-star hacl-star-0001-Squash-some-errors-warnings.patch

# Apply minor patch to de-anonymize a function, to make it possible to prove stuff
git apply --directory=hacl-star hacl-star-0002-de-anonymize-function.patch

# Run fstar on all fst files in current directory, using hints
find -maxdepth 1 -type f -name '*.fst' -exec fstar --use_hints {} \;
```

Expected output:
```
Verified module: Poly1305.Equivalence (253 milliseconds)
All verification conditions discharged successfully
Verified module: TagEquivalence (135 milliseconds)
All verification conditions discharged successfully
Verified module: MsgEquivalence (32622 milliseconds)
All verification conditions discharged successfully
Verified module: UsefulLemmas (1152 milliseconds)
All verification conditions discharged successfully
Verified module: Axioms (924 milliseconds)
All verification conditions discharged successfully
Verified module: KeyEquivalence (947 milliseconds)
All verification conditions discharged successfully
Verified module: ThirdSpec (3913 milliseconds)
All verification conditions discharged successfully
```

FStar Version:
```
F* 0.9.5.0
platform=Linux_x86_64
compiler=OCaml 4.05.0
date=2017-08-23T11:19:43-07:00
commit=fa9b1fd
```

HACL* Commit: `3b72903e` + [minor patch](hacl-star-0001-Squash-some-errors-warnings.patch) + [minor patch](hacl-star-0002-de-anonymize-function.patch)

Vale Commit: `5aab381`

Notes:
1. To simplify `fstar` finding everything, I have simply symlinked all
   relevant files from the Vale and HACL* directories into the root
   directory of this repository. I will hopefully clean that up at
   some point.
2. Imho, the proof should be read starting from
   [`Poly1305.Equivalence.fst`](Poly1305.Equivalence.fst), since it
   provides the overall goal of the proof, as well as links into
   lemmas that are used to achieve it.
3. A bunch of the `*_semantics` lemmas in `Axioms.fst` exist only
   because HACL* decides not to reveal the implementations for IntSeq
   and IntTypes. I've manually checked them a bunch of times to ensure
   that they match with the implementation, but it'd be nice to have a
   better way to have them be machine-checked against the
   implementation.
4. I am using `ocp-indent` for indentation, and overall, it works out
   great! However, for certain trivial edge cases, it leads to weird
   indentations (nothing unreadable, but it troubles me to see the
   aesthetics be spoilt). Either `fstar --indent` must be improved (it
   kills all my newlines, which I dislike), or `ocp-indent` must be
   modified to support fstar's differences from OCaml. Just felt like
   this should be written down somewhere :P
