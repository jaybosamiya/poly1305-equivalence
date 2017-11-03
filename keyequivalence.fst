module KeyEquivalence

(** Define split and merge primitives. This will let us combine
    arbitrary [nat]s losslessly. [merge_nat a b] merges [a] and [b]
    into a single [nat] which has [a] in the higher order digits, and
    [b] in the lower order digits. [split_nat_a] and [split_nat_b] are
    used to retrieve [a] and [b] from the merged [nat].

    [merge_split_inverses] tells us that the merge and split functions
    are inverses of each other. *)

type natlim (lim:pos) = x:nat{x<lim}

val split_nat : #lim:pos -> c:natlim (lim `op_Multiply` lim) ->
  a:natlim lim * b:natlim lim
let split_nat #lim c = c / lim, c % lim

val merge_nat : #lim:pos -> a:natlim lim -> b:natlim lim ->
  c:natlim (lim `op_Multiply` lim)
let merge_nat #lim a b =
  let k = (a `op_Multiply` lim) in
  assert (k <= lim `op_Multiply` (lim - 1));
  (* This assertion lets it prove that the output limit is correct *)
  let l = k + b in
  l

  (* Need to increase limits to prove divmod lemma below *)
  #set-options "--z3rlimit 20"


val divmod_lemma : #lim:pos -> a:natlim lim -> b:natlim lim ->
  Lemma ((((a `op_Multiply` lim) + b) / lim = a) /\
         (((a `op_Multiply` lim) + b) % lim = b))
let divmod_lemma #lim a b =
  Math.Lemmas.modulo_addition_lemma b lim a

val merge_split_inverses :
  #lim:pos -> a:natlim lim -> b:natlim lim ->
  c:natlim (lim `op_Multiply` lim) ->
  Lemma (
    (merge_nat a b = c) <==>
    (split_nat c = (a, b)))
let merge_split_inverses #lim a b c = divmod_lemma #lim a b

(** Prove equivalence b/w the key types used by the Vale and the HACL*
    specs. We do this by using the merging and splitting primitives
    defined above.

    Defines [key_vale_to_hacl] and [key_hacl_to_vale] to convert
    between the two keys, and [key_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

type nat128 = ValeSpec.nat128
type key = HaclSpec.key

open Spec.Lib.IntSeq
open Spec.Lib.IntTypes

val key_hacl_to_vale : k:key -> r:nat128 * s:nat128
let key_hacl_to_vale k =
  let c = nat_from_intseq_le k in
  Math.Lemmas.pow2_plus 128 128;
  let a, b = split_nat #(pow2 128) c in
  b, a

val key_vale_to_hacl :
  r:nat128 -> s:nat128 ->
  k:key
let key_vale_to_hacl r s =
  let c = merge_nat #(pow2 128) s r in
  Math.Lemmas.pow2_plus 128 128;
  nat_to_bytes_le 32 c

let equal_intseqs a b =
  nat_from_intseq_le a = nat_from_intseq_le b

val key_equivalence :
  r:nat128 ->
  s:nat128 ->
  k:key ->
  Lemma (
    (equal_intseqs (key_vale_to_hacl r s) k)
    <==>
    (key_hacl_to_vale k == (r, s))
  )

let key_equivalence r s k =
  Math.Lemmas.pow2_plus 128 128;
  let c = (merge_nat #(pow2 128) r s) in
  merge_split_inverses r s c

