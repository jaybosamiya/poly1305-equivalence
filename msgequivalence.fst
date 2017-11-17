module MsgEquivalence

(** Prove equivalence b/w the input types used by the Vale and the HACL*
    specs.

    Defines [inp_vale_to_hacl] and [inp_hacl_to_vale] to convert
    between the two keys, and [inp_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

type nat128 = ValeSpec.nat128

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

(* Allow equality for lseqs *)
val lseq_eq: a:Type -> len:size_t ->
  Lemma (hasEq (lseq a len))
    [SMTPat (lseq a len)]
let lseq_eq a len = admit ()

(* We make the equality same as checking whether the number encoded is the same *)
val intseq_eq: #t:inttype -> #len:size_t -> a:intseq t len -> b:intseq t len ->
  Lemma ((a = b) <==>
         (nat_from_intseq_le a = nat_from_intseq_le b))
    [SMTPat (a = b)]
let intseq_eq #t #len a b = admit ()

    assume
(* Let us say that an [append] function is provided by the API *)
val append: #len1:size_t -> #len2:size_t ->
  #len:size_t{len=len1+len2} -> s1:lbytes len1 -> s2:lbytes len2 ->
  s:lbytes len{(sub s 0 len1 = s1) /\
               (sub s len1 len2 = s2)}

(* Axiom about [sub] which tells us that a subsequence of a subsequence is itself a subsequence *)
val sub_property:
  #a:Type -> #len:size_t ->
  s:lseq a len ->
  start:size_t -> n:size_t{start + n <= len} ->
  start':size_t{start' > start} -> n':size_t{start' + n' <= start + n} ->
Lemma (sub s start' n' = sub (sub s start n) (start' - start) n')
let sub_property #a #len s start n start' n' = admit ()

(* Now we actually write down the conversions *)
type vale_msg (l:nat) = a:(int->nat128){a (l / 16) < pow2 (8 `op_Multiply` (l % 16))}
type hacl_msg (l:size_t) = lbytes l

val inp_hacl_to_vale : #l:size_t -> msg:lbytes l -> inp:vale_msg l
let pick_xth_block (#l:size_t) (msg:lbytes l) (x:nat{16`op_Multiply`x<l}) : nat128 =
  let start = x `op_Multiply` 16 in
  let len':size_t = min (l - start) 16 in
  let y = nat_from_intseq_le (sub msg start len') in
  Math.Lemmas.pow2_le_compat 128 (8 `op_Multiply` len');
  y
let inp_hacl_to_vale #l msg =
  let g (x:int) : nat128 =
    if x < 0 || 16 `op_Multiply` x >= l then 0
    else pick_xth_block msg x in
  g


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

(* Now for the inverse proofs *)
val equal_fns :
  (inp1:int->nat128) -> len1:nat ->
  (inp2:int->nat128) -> len2:nat ->
  eql:bool
let rec equal_fns inp1 len1 inp2 len2 =
  match len1 with
  | 0 -> (len2 = 0)
  | _ -> (len1 = len2) &&
         (inp1 0 = inp2 0) &&
         (equal_fns
            (fun x -> inp1 (x - 1)) (len1 - 1)
            (fun x -> inp2 (x - 1)) (len2 - 1))

val inp_equivalence :
  #l:size_t ->
  inp:vale_msg l ->
  msg:hacl_msg l ->
  Lemma (
    ((equal_fns inp l
        (inp_hacl_to_vale msg)
        l)
     <==>
     (inp_vale_to_hacl #l inp) = msg))

    (* Need to increase limits to prove equivalence lemma below *)
    #set-options "--z3rlimit 20"

let inp_equivalence #l inp msg =
  intseq_eq (inp_vale_to_hacl #l inp) msg
