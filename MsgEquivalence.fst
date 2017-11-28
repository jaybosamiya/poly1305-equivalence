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

(* First, a bunch of axioms and properties that we will use *)

(** Property: the subseq of subseq is a subseq *)
val sub_of_sub_property:
  #t:inttype -> #len:size_t ->
  s:intseq t len ->
  start:size_t -> n:size_t{start + n <= len} ->
  Lemma
    (forall (start':size_t{start' <= start})
       (n':size_t{start + n <= start' + n' /\ start' + n' <= len}).
         sub s start n == sub (sub s start' n') (start - start') n)
    [SMTPat (sub s start n)]
let sub_of_sub_property #t #len s start n = 
  let f (start':size_t{start' <= start})
      (n':size_t{start + n <= start' + n' /\ start' + n' <= len}) :
    Lemma (sub s start n == sub (sub s start' n') (start - start') n) =
    sub_semantics s start n;
    let s' = sub_semantics s start' n'; sub s start' n' in
    sub_semantics s' (start - start') n in
  FStar.Classical.forall_intro_2 f

type vale_msg (l:nat) = a:(int->nat128){l % 16 <> 0 ==> a (l / 16) < pow2 (8 `op_Multiply` (l % 16))}
type hacl_msg (l:size_t) = lbytes l

(** Definitionally: Two [vale_msg]s are equal iff all their values are equal
    (in the ranges that matter) *)
val vale_msg_eq:
  #l:nat ->
  Lemma (
    forall (a:vale_msg l)
      (b:vale_msg l).
        a == b <==>
    ((forall (x:int{x >= 0 /\ x < (l/16)}). a x = b x) /\
     (l % 16 <> 0 ==> a (l/16) = b (l/16))))
    [SMTPat (vale_msg l)]
let vale_msg_eq #l = admit ()

(* Now we actually write down the conversions *)

val remove_last_block :
  #l:size_t{l > 0} ->
#lst:size_t{(l % 16 = 0 <==> lst = 16) /\ (l % 16 <> 0 <==> lst = l % 16)} ->
#rem:size_t{rem = l - lst} ->
v:vale_msg l ->
v':vale_msg rem{forall (x:size_t{x >= 0 /\ x < rem/16}). v x = v' x}
let remove_last_block #l #lst #rem v =
  let v' : vale_msg rem =
    fun i -> if i < rem/16 then v i else 0 in
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
  // assert (rem % 16 = 0); // (sometimes) required for the prover to realize this
        ()

val part_inv_vale :
  #l:size_t ->
  inp:vale_msg l ->
  Lemma (inp_hacl_to_vale (inp_vale_to_hacl inp) == inp)
let rec part_inv_vale #l inp =
  match l with
  | 0 -> ()
  | _ ->
    let msg = inp_vale_to_hacl inp in
    let (lst:size_t{lst <= 16 /\ lst <= l}) = if l % 16 = 0 then 16 else l % 16 in
    let rem = l - lst in
    rem_prop #l #lst #rem msg;
    let prev_inp = remove_last_block #l #lst #rem inp in
    part_inv_vale #rem prev_inp

val lemma_inp_hacl_to_vale_last_block :
  #l:size_t{l>0} ->
#lst:size_t{(l % 16 = 0 <==> lst = 16) /\ (l % 16 <> 0 <==> lst = l % 16)} ->
#rem:size_t{rem = l - lst} ->
msg:hacl_msg l ->
inp:vale_msg l{inp == inp_hacl_to_vale msg} ->
Lemma (sub msg rem lst == nat_to_bytes_le lst (inp (rem/16)))
let lemma_inp_hacl_to_vale_last_block #l #lst #rem msg inp =
  eq_nat_from_intseq (nat_to_bytes_le lst (inp (rem/16))) (sub msg rem lst)

val lemma_subseq :
  #l:size_t ->
  #a:size_t ->
  #b:size_t{a + b = l} ->
  x:lbytes l ->
  y:lbytes l ->
  Lemma (requires
           ((sub x 0 a == sub y 0 a) /\
            (sub x a b == sub y a b)))
    (ensures x == y)
let lemma_subseq #l #a #b x y =
  sub_semantics x 0 a;
  sub_semantics y 0 a;
  assert (forall (i:size_t{i<a}). x.[i] == y.[i]);
  sub_semantics x a b;
  sub_semantics y a b;
  assert (forall (i:size_t{i<b}). x.[i+a] == y.[i+a]);
  assert (forall (j:size_t{a <= j /\ j < l}). x.[(j-a)+a] == y.[j]) // the [(j-a)+a] is required to push the proof through

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
    lemma_subseq #l #rem #lst msg msg'

val inp_equivalence :
  #l:size_t ->
  inp:vale_msg l ->
  msg:hacl_msg l ->
  Lemma ((inp_hacl_to_vale #l msg) == inp <==>
         (inp_vale_to_hacl #l inp) == msg)

let rec inp_equivalence #l inp msg =
  part_inv_vale inp;
  part_inv_hacl msg
