module Poly1305.Equivalence

       (* Need to increase limits to have the proofs go through *)
       #set-options "--z3rlimit 20"

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
  msg:lbytes len ->
  Lemma
    (let k = KeyEquivalence.key_vale_to_hacl key_r key_s in
     let (inp : int->nat128) = MsgEquivalence.inp_hacl_to_vale #len msg in
     let t1 = ValeSpec.poly1305_hash key_r key_s inp len in
     let t2 = HaclSpec.poly1305 len msg k in
     (t1 == TagEquivalence.tag_hacl_to_vale t2) /\
     (t2 == TagEquivalence.tag_vale_to_hacl t1))

let spec_equal len key_r key_s msg =
  let k = KeyEquivalence.key_vale_to_hacl key_r key_s in
  let inp = MsgEquivalence.inp_hacl_to_vale #len msg in
  let t1 = ValeSpec.poly1305_hash key_r key_s inp len in
  let t2 = HaclSpec.poly1305 len msg k in
  KeyEquivalence.key_equivalence key_r key_s k;
  MsgEquivalence.inp_equivalence inp msg;
  ThirdSpec.poly1305_hacl len msg k;
  ThirdSpec.poly1305_vale len key_r key_s inp;
  TagEquivalence.tag_equivalence t2 t1;
  // assert (t1 == TagEquivalence.tag_hacl_to_vale t2);
  admit ();
  ()
