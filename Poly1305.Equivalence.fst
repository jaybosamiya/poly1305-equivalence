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
  len:size_t ->
  key_r:nat128 ->
  key_s:nat128 ->
  inp:MsgEquivalence.vale_msg len ->
  msg:lbytes len ->
  Lemma
    (requires (
        (inp == MsgEquivalence.inp_hacl_to_vale msg)))
    (ensures (
        let k = KeyEquivalence.key_vale_to_hacl key_r key_s in
        let t = ValeSpec.poly1305_hash key_r key_s (ThirdSpec.msg_to_vale inp) len in
        let t1 = HaclSpec.poly1305 len msg k in
        (t == TagEquivalence.tag_hacl_to_vale t1) /\
        (t1 == TagEquivalence.tag_vale_to_hacl t)))

let spec_equal len key_r key_s inp msg =
  let k = KeyEquivalence.key_vale_to_hacl key_r key_s in
  let t = ValeSpec.poly1305_hash key_r key_s (ThirdSpec.msg_to_vale inp) len in
  let t1 = HaclSpec.poly1305 len msg k in
  KeyEquivalence.key_equivalence key_r key_s k;
  MsgEquivalence.inp_equivalence inp msg;
  ThirdSpec.poly1305_hacl len msg k;
  ThirdSpec.poly1305_vale len key_r key_s inp;
  TagEquivalence.tag_equivalence t1 t
