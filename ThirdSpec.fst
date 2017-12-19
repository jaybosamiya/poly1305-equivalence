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
type idx l=MsgEquivalence.vale_idx l
let sat_idx = MsgEquivalence.sat_idx
type idx' l=(x:nat{x > 0 ==> sat_idx l (x-1)})

let prime = (nat128_max * 4 - 5)
type elem = e:nat{e < prime}

let encode_r (r:nat128) : nat128 =
  logand #128 r 0x0ffffffc0ffffffc0ffffffc0fffffff

let rec poly #l (r:nat128) (inp:msg l) (i:idx' l) : elem =
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
     #set-options "--z3rlimit 100"

(** Equivalence for [encode_r] *)

val encode_r_hacl :
  r:HaclSpec.block ->
  Lemma (HaclSpec.encode_r r == encode_r (nat_from_bytes_le r))
let encode_r_hacl r = admit () // we will just assume this for now

(* Vale doesn't require a lemma here, since we've defined it from that *)

(** Equivalence for [poly] *)

val poly_hacl :
  len:size_t ->
  text:lbytes len ->
  r:nat128 ->
  Lemma
    (let k : idx' len = if len%16 = 0 then len/16 else len/16+1 in
     HaclSpec.poly len text r == poly #len r (MsgEquivalence.inp_hacl_to_vale text) k)

val lemma_hacl_update:
  len:size_t{len <= 16} ->
  b:lbytes len ->
  r:nat128 ->
  acc:elem ->
  l:size_t ->
  inp:msg l ->
  kk:nat{sat_idx l kk} ->
  Lemma (requires
           (poly #l r inp kk = acc) /\
         (nat_from_intseq_le b = inp kk) /\
         ((kk = l/16) <==> (len = l % 16 /\ len <> 0)) /\
         ((kk < l/16) <==> (len = 16)))
    (ensures
       poly #l r inp (kk+1) = HaclSpec.update len b r acc)

let lemma_hacl_update len b r acc l inp kk =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  let pad = pow2 (8 * len) in
  Math.Lemmas.lemma_mod_mul_distr_l (pad + inp kk + acc) r prime

val lemma_slice :
  len:size_t ->
  inp:msg len ->
  i:nat{0 < i /\ i <= len/16} ->
        b:lbytes 16 ->
        Lemma
          (requires
             b == slice (MsgEquivalence.inp_vale_to_hacl inp) (16 * (i-1)) (16 * i))
          (ensures
             nat_from_intseq_le b = inp (i-1))

let lemma_slice len inp i b =
  let msg = MsgEquivalence.inp_vale_to_hacl inp in
  MsgEquivalence.inp_equivalence inp msg;
  Axioms.slice_semantics msg (16 * (i-1)) (16 * i)

val lemma_slice' :
  len:size_t{len%16 <> 0} ->
  inp:msg len ->
  b:lbytes (len%16) ->
  Lemma
    (requires
       b == slice (MsgEquivalence.inp_vale_to_hacl inp) (16 * (len/16)) len)
    (ensures
       nat_from_intseq_le b = inp (len/16))

let lemma_slice' len inp b =
  let msg = MsgEquivalence.inp_vale_to_hacl inp in
  MsgEquivalence.inp_equivalence inp msg;
  Axioms.slice_semantics msg (16 * (len/16)) len

val lemma_hacl_repeati:
  len:size_t ->
  text:lbytes len ->
  r:nat128 ->
  i:size_t{i <= len/16} ->
  Lemma (repeati i (HaclSpec.update' len text r) 0 =
         poly #len r (MsgEquivalence.inp_hacl_to_vale text) i)

let rec lemma_hacl_repeati len text r i =
  let up = HaclSpec.update' len text r in
  Axioms.repeati_semantics i up 0;
  match i with
  | 0 -> ()
  | _ ->
    lemma_hacl_repeati len text r (i-1);
    let b = slice text (16 * (i-1)) (16 * i) in
    let inp = MsgEquivalence.inp_hacl_to_vale text in
    MsgEquivalence.inp_equivalence inp text;
    lemma_slice len inp i b;
    let acc = repeati (i-1) up 0 in
    lemma_hacl_update 16 b r acc len inp (i-1);
    UsefulLemmas.repeati_reverse i up 0

let rec poly_hacl len text r =
  let blocks = len / 16 in
  let rem = len % 16 in
  let init  : elem = 0 in
  let up = HaclSpec.update' len text r in
  let acc : elem =
    repeati blocks up init in
  Axioms.repeati_semantics blocks up init;
  lemma_hacl_repeati len text r blocks;
  let inp = MsgEquivalence.inp_hacl_to_vale text in
  match len with
  | 0 -> ()
  | _ ->
    match len%16 with
    | 0 -> ()
    | _ ->
      let last = slice text (blocks * 16) len in
      MsgEquivalence.inp_equivalence inp text;
      lemma_slice' len inp last;
      lemma_hacl_update rem last r acc len inp blocks

let vale_last_block (len:nat) (inp:msg len) (r:nat128) (acc:elem) : elem =
  if len % 16 = 0 then acc else
    let k = len / 16 in
    let padLast = pow2((len % 16) * 8) in
    ((acc + padLast + ((inp k) % padLast)) * r) % prime

let msg_to_vale (#l:size_t) (inp:msg l) : (int->nat128) =
  fun i ->
    if sat_idx l i && i >= 0
    then inp i
    else 0

val poly_vale' :
  #l:size_t ->
  len:size_t{len%16=0 /\ len <= l} ->
  r:nat128 ->
  inp:msg l ->
  Lemma ((ValeSpec.poly1305_hash_blocks 0 nat128_max r (msg_to_vale inp) (len/16)) == poly #l r inp (len/16))

let rec poly_vale' #l len r inp =
  match len with
  | 0 -> ()
  | _ -> poly_vale' #l (len-16) r inp

val poly_vale :
  len:size_t ->
  inp:msg len ->
  r:nat128 ->
  Lemma
    (let k : idx' len = if len%16 = 0 then len/16 else len/16+1 in
     vale_last_block len inp r
       (ValeSpec.poly1305_hash_blocks 0 nat128_max r (msg_to_vale inp) (len/16)) == poly #len r inp k)

let rec poly_vale len inp r =
  let b = len%16 in
  poly_vale' (len-b) r inp;
  match b with
  | 0 -> ()
  | _ -> FStar.Math.Lemmas.modulo_lemma (inp (len/16)) (pow2 (b*8))

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
  poly_hacl len msg r;
  finish_hacl acc s

val poly1305_vale :
  len:size_t ->
  r:nat128 ->
  s:nat128 ->
  inp:msg len ->
  Lemma (
    ValeSpec.poly1305_hash r s (msg_to_vale inp) len == poly1305 (r, s) inp)

let poly1305_vale len key_r key_s inp =
  poly_vale len inp (encode_r key_r)
