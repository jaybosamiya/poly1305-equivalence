module MsgEquivalence

(** Prove equivalence b/w the input types used by the Vale and the HACL*
    specs.

    Defines [inp_vale_to_hacl] and [inp_hacl_to_vale] to convert
    between the two inputs, and [inp_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

                  (* Need to increase limits to have the proofs go through *)
                  #set-options "--z3rlimit 100"

type nat128 = ValeSpec.nat128

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Axioms
open UsefulLemmas

let sat_idx (l:nat) a =
  if l % 16 = 0 then a < l/16 else a <= l/16

type vale_idx (l:nat) = a:nat{sat_idx l a}
type vale_msg (l:nat) = a:(vale_idx l->nat128){l % 16 <> 0 ==> a (l/16) < pow2 (8 `op_Multiply` (l % 16))}
type hacl_msg (l:size_t) = lbytes l

(* Now we actually write down the conversions *)

val vale_idx_cast :
  #l1:nat ->
  #l2:nat ->
  a:vale_idx l1{a <= l2 / 16 /\ (l2 % 16 = 0 ==> a < l2 / 16)} ->
  b:vale_idx l2
let vale_idx_cast #l1 #l2 a = let b : nat = a in b

val remove_last_block :
  #l:size_t{l > 0} ->
#lst:size_t{(l % 16 = 0 <==> lst = 16) /\ (l % 16 <> 0 <==> lst = l % 16)} ->
#rem:size_t{rem = l - lst} ->
v:vale_msg l ->
v':vale_msg rem{forall (x:size_t{x >= 0 /\ x < rem/16}). v x = v' x}
let remove_last_block #l #lst #rem v =
  let v' : vale_msg rem =
    fun i -> if i < rem/16 then v (vale_idx_cast i) else 0 in
  v'

val inp_vale_to_hacl : #l:size_t -> inp:vale_msg l -> Tot (msg:lbytes l)
let rec inp_vale_to_hacl #l inp =
  match l with
  | 0 -> nat_to_bytes_le 0 0
  | _ ->
    let len, i : ((x:size_t{x<=l}) * int) =
      if l % 16 <> 0
      then l % 16, l / 16
      else 16, (l / 16) - 1 in
    let cur_block =
      nat_to_bytes_le len (inp i) in
    let prev_blocks =
      inp_vale_to_hacl #(l - len) (remove_last_block #l #len #(l-len) inp) in
    append prev_blocks cur_block

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

val rem_prop :
  #l:size_t{l > 0} ->
#lst:size_t{(l % 16 = 0 <==> lst = 16) /\ (l % 16 <> 0 <==> lst = l % 16)} ->
#rem:size_t{rem = l - lst} ->
i:hacl_msg l ->
Lemma (inp_hacl_to_vale (sub i 0 rem) == remove_last_block #l #lst #rem (inp_hacl_to_vale i))
let rem_prop #l #lst #rem i =
  let a = inp_hacl_to_vale (sub i 0 rem) in
  let b = remove_last_block #l #lst #rem (inp_hacl_to_vale i) in
  assert (FStar.FunctionalExtensionality.feq a b);
  // assert (rem % 16 = 0); // (sometimes) required for the prover to realize this
        ()

        #reset-options "--using_facts_from '* -Axioms.eq_vale_map'"

val part_inv_vale :
  #l:size_t ->
  inp:vale_msg l ->
  Lemma (inp_hacl_to_vale (inp_vale_to_hacl inp) == inp)
let rec part_inv_vale #l inp =
  match l with
  | 0 ->
    assert (FStar.FunctionalExtensionality.feq (inp_hacl_to_vale (inp_vale_to_hacl inp)) inp)
  | _ ->
    let msg = inp_vale_to_hacl inp in
    let (lst:size_t{lst <= 16 /\ lst <= l}) = if l % 16 = 0 then 16 else l % 16 in
    let rem : size_t = l - lst in
    rem_prop #l #lst #rem msg;
    let prev_inp = remove_last_block #l #lst #rem inp in
    part_inv_vale #rem prev_inp;
    let prev_inp' = inp_hacl_to_vale (inp_vale_to_hacl prev_inp) in
    assert (FStar.FunctionalExtensionality.feq  prev_inp prev_inp');
    let inp' = inp_hacl_to_vale (inp_vale_to_hacl inp) in
    assert (forall (x:vale_idx rem). inp (vale_idx_cast x) == inp' (vale_idx_cast x));
    assert (FStar.FunctionalExtensionality.feq inp inp')

val lemma_inp_hacl_to_vale_last_block :
  #l:size_t{l>0} ->
#lst:size_t{(l % 16 = 0 <==> lst = 16) /\ (l % 16 <> 0 <==> lst = l % 16)} ->
#rem:size_t{rem = l - lst} ->
msg:hacl_msg l ->
inp:vale_msg l{inp == inp_hacl_to_vale msg} ->
Lemma (sub msg rem lst == nat_to_bytes_le lst (inp (rem/16)))
let lemma_inp_hacl_to_vale_last_block #l #lst #rem msg inp =
  eq_nat_from_intseq (nat_to_bytes_le lst (inp (rem/16))) (sub msg rem lst)

val part_inv_hacl :
  #l:size_t ->
  msg:hacl_msg l ->
  Lemma (inp_vale_to_hacl (inp_hacl_to_vale msg) == msg)

let rec part_inv_hacl #l msg =
  match l with
  | 0 -> ()
  | _ ->
    let inp = inp_hacl_to_vale msg in
    let lst = if l % 16 = 0 then 16 else l % 16 in
    let rem:size_t = l - lst in
    rem_prop #l #lst #rem msg;
    let prev_msg = sub msg 0 rem in
    part_inv_hacl #rem prev_msg;
    let msg' = inp_vale_to_hacl inp in
    lemma_inp_hacl_to_vale_last_block #l #lst #rem msg inp;
    subs_eq rem msg msg'

val inp_equivalence :
  #l:size_t ->
  inp:vale_msg l ->
  msg:hacl_msg l ->
  Lemma ((inp_hacl_to_vale #l msg) == inp <==>
         (inp_vale_to_hacl #l inp) == msg)

let rec inp_equivalence #l inp msg =
  part_inv_vale inp;
  part_inv_hacl msg
