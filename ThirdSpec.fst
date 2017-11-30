module ThirdSpec

(** Defines a 3rd spec that is "in-between" the Vale and HACL specs,
    and proves equivalence from both sides *)

open FStar.Mul
open FStar.UInt

let nat128_max = 0x100000000000000000000000000000000
let _ = assert_norm (pow2 128 = nat128_max) 
type nat128 = x:int{0 <= x && x < nat128_max}

type tag=TagEquivalence.vale_tag
type key=tuple2 nat128 nat128
type msg l=MsgEquivalence.vale_msg l

let prime = (nat128_max * 4 - 5)
type elem = e:nat{e < prime}

let encode_r (r:nat128) : nat128 =
  logand #128 r 0x0ffffffc0ffffffc0ffffffc0fffffff

let rec poly #l (r:nat128) (inp:msg l) (i:nat) : elem =
  match i with
  | 0 -> 0
  | _ ->
    let kk = i - 1 in
    let hh = poly r inp kk in
    let pad = if i = (l/16) + 1 then pow2((l % 16) * 8) else nat128_max in
    ((hh + pad + inp kk) * r) % prime

let finish (a:elem) (s:nat128) : tag =
  (a + s) % nat128_max

let poly1305 #l (k:key) (inp:msg l) : tag =
  let r, s = k in
  let r = encode_r r in
  let i = if l % 16 = 0 then l/16 else (l/16) + 1 in
  let a = poly #l r inp i in
  finish a s

(** Now, all the equivalences *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

     (* Need to increase limits to have the proofs go through *)
     #set-options "--z3rlimit 50"

(** Axiom: [nat_from_bytes_le] is same as [nat_from_intseq_le] *)
val bytes_intseq_equiv :
  #len:size_t -> b:lbytes len ->
  Lemma (nat_from_bytes_le b = nat_from_intseq_le b)
    [SMTPat (nat_from_bytes_le b)]
let bytes_intseq_equiv #len b = admit ()

(** Equivalence for [encode_r] *)

val encode_r_hacl :
  r:HaclSpec.block ->
  Lemma (HaclSpec.encode_r r == encode_r (nat_from_bytes_le r))
let encode_r_hacl r = admit () // we will just assume this for now

(* Vale doesn't require a lemma here, since we've defined it from that *)

(** Equivalence for [poly] *)

val poly_hacl :
  #x:nat ->
  len:size_t ->
  text:lbytes len ->
  r:nat128 ->
  Lemma (requires (len%16=0 ==> x=0) /\ (len%16<>0 ==> x=1))
    (ensures
       HaclSpec.poly len text r == poly #len r (MsgEquivalence.inp_hacl_to_vale text) (len/16+x))

let poly_hacl #x len text r = admit () // TODO: Prove

let vale_last_block (len:nat) (inp:msg len) (r:nat128) (acc:elem) : elem =
  if len % 16 = 0 then acc else
    let k = len / 16 in
    let padLast = pow2((len % 16) * 8) in
    ((acc + padLast + ((inp k) % padLast)) * r) % prime


val poly_vale' :
  #l:size_t ->
  len:size_t{len%16=0 /\ len <= l} ->
  r:nat128 ->
  inp:msg l ->
  Lemma ((ValeSpec.poly1305_hash_blocks 0 nat128_max r inp (len/16)) == poly #l r inp (len/16))

let poly_vale' #l len r inp = admit ()

val poly_vale :
  #x:nat ->
  len:size_t ->
  r:nat128 ->
  inp:msg len ->
  Lemma (requires (len%16=0 ==> x=0) /\ (len%16<>0 ==> x=1))
    (ensures
       vale_last_block len inp r
       (ValeSpec.poly1305_hash_blocks 0 nat128_max r inp (len/16)) == poly #len r inp (len/16+x))

let rec poly_vale #x len r inp =
  match x with
  | 0 -> poly_vale' #len len r inp
  | 1 -> let b = len%16 in
    poly_vale' #len (len-b) r inp;
    FStar.Math.Lemmas.modulo_lemma (inp (len/16)) (pow2 (b*8))

(** Equivalence for [finish] *)

val finish_hacl :
  a:elem ->
  s:nat128 ->
  Lemma (nat_from_intseq_le (HaclSpec.finish a s) == finish a s)

let finish_hacl a s = ()

(* Vale doesn't require a lemma here, since we've defined it from that *)

(** Equivalence for [poly1305] *)

val poly1305_hacl :
  len:size_t ->
  msg:lbytes len ->
  k:HaclSpec.key ->
  Lemma (
    nat_from_intseq_le (HaclSpec.poly1305 len msg k) ==
    poly1305 (KeyEquivalence.key_hacl_to_vale k)
      (MsgEquivalence.inp_hacl_to_vale msg))

let poly1305_hacl len msg k =
  encode_r_hacl (slice k 0 16);
  let x = if len%16 = 0 then 0 else 1 in
  let r = HaclSpec.encode_r (slice k 0 16) in
  let s = nat_from_bytes_le (slice k 16 32) in
  let acc = HaclSpec.poly len msg r in
  poly_hacl #x len msg r;
  finish_hacl acc s

val poly1305_vale :
  len:size_t ->
  r:nat128 ->
  s:nat128 ->
  inp:msg len ->
  Lemma (
    ValeSpec.poly1305_hash r s inp len == poly1305 (r, s) inp)

let poly1305_vale len key_r key_s inp =
  let x = if len%16 = 0 then 0 else 1 in
  poly_vale #x len (encode_r key_r) inp
