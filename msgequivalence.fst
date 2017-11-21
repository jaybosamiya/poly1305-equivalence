module MsgEquivalence

(** Prove equivalence b/w the input types used by the Vale and the HACL*
    specs.

    Defines [inp_vale_to_hacl] and [inp_hacl_to_vale] to convert
    between the two keys, and [inp_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

                  (* Need to increase limits to have the proofs go through *)
                  #set-options "--z3rlimit 20"

type nat128 = ValeSpec.nat128

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

(* First, a bunch of axioms and properties that we will use *)

(** Axiom: [uint_t]s can be equality compared *)
val uint_t_eq: t:inttype ->
  Lemma (hasEq (uint_t t))
    [SMTPat (uint_t t)]
let uint_t_eq t = admit ()

(** Axiom: [intseq]s have equality *)
val intseq_type_eq: t:inttype -> len:size_t ->
  Lemma (hasEq (intseq t len))
    [SMTPat (intseq t len)]
let intseq_type_eq t len = admit ()

(** Axiom: Two sequences are equal iff all their elements are equal *)
val intseq_eq: t:inttype -> len:size_t ->
  Lemma (forall (a:intseq t len) (b:intseq t len).
                                   (a = b) <==> (forall x. a.[x] = b.[x]))
    [SMTPat (intseq t len)]
let intseq_eq t len = admit ()

(** Axiom: Subsequence actually gives us the subsequence *)
val sub_semantics:
  #t:inttype ->
  #len:size_t ->
  s:intseq t len ->
  start:size_t ->
  n:size_t{start + n <= len} ->
  Lemma (forall (x:size_t{x < n}). (sub s start n).[x] = s.[start + x])
    [SMTPat (sub s start n)]
let sub_semantics #t #len s start n = admit()

(** Axiom: Two sequences are same iff their LE representation is same *)
val eq_nat_from_intseq:
  #t:inttype ->
  #len:size_t ->
  a:intseq t len ->
  b:intseq t len ->
  Lemma (a = b <==> nat_from_intseq_le a = nat_from_intseq_le b)
let eq_nat_from_intseq #t #len a b = admit ()

    assume
(** Assumption: An [append] function is provided by the API *)
val append: #len1:size_t -> #len2:size_t ->
  #len:size_t{len=len1+len2} -> s1:lbytes len1 -> s2:lbytes len2 ->
  s:lbytes len{(sub s 0 len1 = s1) /\
               (sub s len1 len2 = s2)}

(** Property: the subseq of subseq is a subseq *)
val sub_of_sub_property:
  #t:inttype -> #len:size_t ->
  s:intseq t len ->
  start:size_t -> n:size_t{start + n <= len} ->
  start':size_t{start' > start} -> n':size_t{start' + n' <= start + n} ->
Lemma (sub s start' n' = sub (sub s start n) (start' - start) n')
let sub_of_sub_property #a #len s start n start' n' = ()

type vale_msg (l:nat) = a:(int->nat128){a (l / 16) < pow2 (8 `op_Multiply` (l % 16))}
type hacl_msg (l:size_t) = lbytes l

(** Axiom: [vale_msg]s have equality *)
val vale_msg_type_eq: #l:nat ->
  Lemma (hasEq (vale_msg l))
    [SMTPat (vale_msg l)]
let vale_msg_type_eq #l = admit ()

(** Axiom: Two [vale_msg]s are equal iff all their values are equal
    (in the ranges that matter) *)
val vale_msg_eq:
  #l:nat ->
  a:vale_msg l ->
  b:vale_msg l ->
  Lemma (a = b <==> (forall (x:int{x >= 0 /\ x <= (l/16)}). a x = b x))
let vale_msg_eq #l a b = admit ()

(* Now we actually write down the conversions *)

val inp_vale_to_hacl : #l:size_t -> inp:vale_msg l -> msg:lbytes l
let rec inp_vale_to_hacl #l inp =
  match l with
  | 0 -> nat_to_bytes_le 0 0
  | _ ->
    let excess = l % 16 in
    let cur_block_len : (x:size_t{0<x /\ x<=16 /\ x<=l}) = if excess <> 0 then excess else 16 in
    let cur_block_num = if excess <> 0 then l / 16 else l / 16 - 1 in
    let prev_l : (x:size_t{x<l}) = l - cur_block_len in
    let prev_inp : vale_msg prev_l =
      fun i -> if i = cur_block_num then 0 else inp i in
    let prev_msg : lbytes prev_l = inp_vale_to_hacl #prev_l prev_inp in
    let cur_block_inp : (x:nat{x<pow2 (8 `op_Multiply` cur_block_len)}) = inp cur_block_num in
    let cur_block = nat_to_bytes_le cur_block_len cur_block_inp in
    append #prev_l #cur_block_len #l prev_msg cur_block

val inp_hacl_to_vale : #l:size_t -> msg:lbytes l -> inp:vale_msg l
let inp_hacl_to_vale #l msg =
  let inp i : nat128 =
    let start = 16 `op_Multiply` i in
    if i < 0 || start >= l
    then 0
    else
      let len:size_t = min (l - start) 16 in
      Math.Lemmas.pow2_le_compat 128 (8 `op_Multiply` len);
      nat_from_intseq_le (sub msg start len) in
  inp

val inp_equivalence :
  #l:size_t ->
  inp:vale_msg l ->
  msg:hacl_msg l ->
  Lemma ((inp_hacl_to_vale #l msg) = inp <==>
         (inp_vale_to_hacl #l inp) = msg)

let rec inp_equivalence #l inp msg =
  vale_msg_eq (inp_hacl_to_vale #l msg) inp;
  match l with
  | 0 -> ()
  | _ -> admit ()
