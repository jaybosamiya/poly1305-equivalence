module Poly1305.Equivalence

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
  t:int ->
  len1:size_t ->
  msg:lbytes len1 ->
  k:key ->
  t1:tag ->
  Lemma
    (requires
       True (* TODO: rewrite this part to make the inputs match up *)
    )
    (ensures
       (ValeSpec.poly1305_hash key_r key_s inp len == t) /\
     (HaclSpec.poly1305 len1 msg k == t1)
    )
