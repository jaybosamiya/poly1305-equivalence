module Poly1305.Equivalence

       (* Need to increase limits to have the proofs go through *)
       #set-options "--z3rlimit 100"

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

type nat128 = ValeSpec.nat128
type size_t = Spec.Lib.IntTypes.size_t   // from HaclSpec
type lbytes l = Spec.Lib.IntSeq.lbytes l // from HaclSpec
type key = HaclSpec.key
type tag = HaclSpec.tag

val spec_equal :
  key_r:nat128 ->
  key_s:nat128 ->
  inp:(int->nat128) ->
  len:nat ->
  t:int{t==ValeSpec.poly1305_hash key_r key_s inp len} ->
  len1:size_t ->
  msg:lbytes len1 ->
  k:key ->
  t1:tag{t1==HaclSpec.poly1305 len1 msg k} ->
  Lemma
    (requires (
        (len = len1) /\
        (k == KeyEquivalence.key_vale_to_hacl key_r key_s) /\
        (inp == MsgEquivalence.inp_hacl_to_vale #len1 msg)))
    (ensures (
        (t == TagEquivalence.tag_hacl_to_vale t1) /\
        (t1 == TagEquivalence.tag_vale_to_hacl t)))

let spec_equal
    key_r key_s inp len t
    len1 msg k t1 =
  KeyEquivalence.key_equivalence key_r key_s k;
  MsgEquivalence.inp_equivalence inp msg;
  ThirdSpec.poly1305_hacl len1 msg k;
  ThirdSpec.poly1305_vale len key_r key_s inp;
  TagEquivalence.tag_equivalence t1 t
