module KeyEquivalence

(** Defines [key_vale_to_hacl] and [key_hacl_to_vale] to convert
    between the two keys, and [key_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

type nat128 = ValeSpec.nat128
type key = HaclSpec.key

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Axioms

val key_hacl_to_vale : k:key -> r:nat128 * s:nat128
let key_hacl_to_vale k =
  let r = slice_semantics k 0 16; slice k 0 16 in
  let s = slice_semantics k 16 32; slice k 16 32 in
  nat_from_intseq_le r, nat_from_intseq_le s

val key_vale_to_hacl :
  r:nat128 -> s:nat128 ->
  k:key
let key_vale_to_hacl r s =
  append
    (nat_to_bytes_le 16 r)
    (nat_to_bytes_le 16 s)

val part_inv_hacl :
  k:key ->
  Lemma (k ==
         key_vale_to_hacl
           (fst (key_hacl_to_vale k))
           (snd (key_hacl_to_vale k)))

let part_inv_hacl k =
  let r = slice_semantics k 0 16; slice k 0 16 in
  let s = slice_semantics k 16 32; slice k 16 32 in
  let r', s' = nat_from_intseq_le r, nat_from_intseq_le s in
  let k' = key_vale_to_hacl r' s' in
  let r0, s0 = sub k' 0 16, sub k' 16 16 in
  eq_nat_from_intseq r r0;
  eq_nat_from_intseq s s0;
  UsefulLemmas.subs_eq 16 k k'

val part_inv_vale :
  r:nat128 ->
  s:nat128 ->
  Lemma ((r,s) = key_hacl_to_vale (key_vale_to_hacl r s))

let part_inv_vale r s =
  let k = key_vale_to_hacl r s in
  slice_semantics k 0 16;
  slice_semantics k 16 32

val key_equivalence :
  r:nat128 ->
  s:nat128 ->
  k:key ->
  Lemma ((key_vale_to_hacl r s == k) <==>
         (key_hacl_to_vale k == (r, s)))

let key_equivalence r s k =
  part_inv_hacl k;
  part_inv_vale r s
