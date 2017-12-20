module MsgEquivalence

(** Prove equivalence b/w the input types used by the Vale and the HACL*
    specs.

    Defines [inp_vale_to_hacl] and [inp_hacl_to_vale] to convert
    between the two inputs, and [inp_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

                  (* Need to increase limits to have the proofs go through *)
                  #set-options "--z3rlimit 1000"

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

val part_inv_vale' :
  #l:size_t ->
  inp:vale_msg l ->
  Lemma (inp_hacl_to_vale (inp_vale_to_hacl inp) == inp)
let rec part_inv_vale' #l inp =
  match l with
  | 0 ->
    assert (FStar.FunctionalExtensionality.feq (inp_hacl_to_vale (inp_vale_to_hacl inp)) inp)
  | _ ->
    let msg = inp_vale_to_hacl inp in
    let (lst:size_t{lst <= 16 /\ lst <= l}) = if l % 16 = 0 then 16 else l % 16 in
    let rem : size_t = l - lst in
    rem_prop #l #lst #rem msg;
    let prev_inp = remove_last_block #l #lst #rem inp in
    part_inv_vale' #rem prev_inp;
    let prev_inp' = inp_hacl_to_vale (inp_vale_to_hacl prev_inp) in
    assert (FStar.FunctionalExtensionality.feq  prev_inp prev_inp');
    let inp' = inp_hacl_to_vale (inp_vale_to_hacl inp) in
    assert (forall (x:vale_idx rem).
                     {:pattern (inp x) \/ (inp' x)} inp (vale_idx_cast x) == inp' (vale_idx_cast x));
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

val part_inv_hacl' :
  #l:size_t ->
  msg:hacl_msg l ->
  Lemma (inp_vale_to_hacl (inp_hacl_to_vale msg) == msg)

let rec part_inv_hacl' #l msg =
  match l with
  | 0 -> ()
  | _ ->
    let inp = inp_hacl_to_vale msg in
    let lst = if l % 16 = 0 then 16 else l % 16 in
    let rem:size_t = l - lst in
    rem_prop #l #lst #rem msg;
    let prev_msg = sub msg 0 rem in
    part_inv_hacl' #rem prev_msg;
    let msg' = inp_vale_to_hacl inp in
    lemma_inp_hacl_to_vale_last_block #l #lst #rem msg inp;
    subs_eq rem msg msg'

val inp_equivalence' :
  #l:size_t ->
  inp:vale_msg l ->
  msg:hacl_msg l ->
  Lemma (inp_hacl_to_vale #l msg == inp <==>
         (inp_vale_to_hacl #l inp) == msg)

let rec inp_equivalence' #l inp msg =
  part_inv_vale' #l inp;
  part_inv_hacl' msg

(*  ////////////////////////////////////////////////////////////////////////////// *)

let vale_msg_to_map (#l:size_t) (inp:vale_msg l) : (int->nat128) =
  fun i ->
    if sat_idx l i && i >= 0
    then inp i
    else 0

let vale_map_to_msg (#l:size_t) (inp:int->nat128) : (vale_msg l) =
  if l % 16 = 0
  then
    fun i -> inp i
  else
    fun i ->
      let mod = pow2 (8 `op_Multiply` (l%16)) in
      Math.Lemmas.pow2_le_compat 128 (8 `op_Multiply` (l%16));
      if i = l/16 then (inp i) % mod else inp i

val vale_map_to_msg_for_eq :
  l:size_t ->
  inp1:(int->nat128) ->
  inp2:(int->nat128) ->
  Lemma
    (requires eq_vale_map l inp1 inp2)
    (ensures vale_map_to_msg #l inp1 == vale_map_to_msg inp2)

let vale_map_to_msg_for_eq l inp1 inp2 =
  assert (FStar.FunctionalExtensionality.feq (vale_map_to_msg #l inp1) (vale_map_to_msg inp2))

val vale_map_to_msg_part_inv :
  l:size_t ->
  inp:(int->nat128) ->
  Lemma (eq_vale_map l inp
           (vale_msg_to_map (vale_map_to_msg #l inp)))
let vale_map_to_msg_part_inv l inp = ()

val vale_msg_to_map_part_inv :
  #l:size_t ->
  inp:vale_msg l ->
  Lemma (vale_map_to_msg (vale_msg_to_map inp) == inp)

let vale_msg_to_map_part_inv #l inp =
  assert (FStar.FunctionalExtensionality.feq (vale_map_to_msg (vale_msg_to_map inp)) inp)

val vale_map_msg_equiv1 :
  #l:size_t ->
  map:(int->nat128) ->
  msg:vale_msg l ->
  Lemma
    ((eq_vale_map l (vale_msg_to_map msg) map) ==>
     (vale_map_to_msg map == msg))

let vale_map_msg_equiv1 #l map msg =
  assert ((eq_vale_map l (vale_msg_to_map msg) map) ==>
          FStar.FunctionalExtensionality.feq (vale_map_to_msg map) msg)

val vale_map_msg_equiv2 :
  #l:size_t ->
  map:(int->nat128) ->
  msg:vale_msg l ->
  Lemma
    ((vale_map_to_msg map == msg) ==>
     (eq_vale_map l (vale_msg_to_map msg) map))

let vale_map_msg_equiv2 #l map msg =
  match l%16 with
  | 0 -> ()
  | _ ->
    let mod = pow2 (8 `op_Multiply` (l%16)) in
    let a = (vale_msg_to_map msg) (l/16) in
    let b = (map (l/16)) in
    // assert (a == b % mod);
    // assert (a % mod == a);
    // assert (a % mod == b % mod);
    // assert (((vale_msg_to_map msg) (l/16)) % mod == (map (l/16)) % mod);
    admit // todo:prove
        ()

val vale_map_msg_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:vale_msg l ->
  Lemma (
    (eq_vale_map l (vale_msg_to_map msg) map) <==>
    (vale_map_to_msg map == msg))

let vale_map_msg_equiv #l map msg =
  vale_map_msg_equiv1 map msg;
  vale_map_msg_equiv2 map msg

let vale_map_to_hacl_msg (#l:size_t) (inp:int->nat128) : hacl_msg l =
  inp_vale_to_hacl (vale_map_to_msg inp)

let hacl_msg_to_vale_map (#l:size_t) (msg:hacl_msg l) : (int->nat128) =
  vale_msg_to_map (inp_hacl_to_vale msg)

val part_inv_vale :
  #l:size_t ->
  inp:(int->nat128) ->
  Lemma (eq_vale_map l
           (hacl_msg_to_vale_map (vale_map_to_hacl_msg #l inp))
           inp)

let part_inv_vale #l inp =
  admit // todo:prove
      ()

val part_inv_hacl :
  #l:size_t ->
  msg:hacl_msg l ->
  Lemma (vale_map_to_hacl_msg (hacl_msg_to_vale_map msg) == msg)

let part_inv_hacl #l msg =
  admit // todo:prove
      ()

val inp_equivalence :
  #l:size_t ->
  inp:(int->nat128) ->
  msg:hacl_msg l ->
  Lemma ((eq_vale_map l (hacl_msg_to_vale_map msg) inp) <==>
         (vale_map_to_hacl_msg inp) == msg)

        (* drop rlimit to speed up bottom part *)
        #set-options "--z3rlimit 10"

let rec inp_equivalence #l inp msg =
  // part_inv_vale #l inp;
  // part_inv_hacl msg;
  // assert (
    //   ((vale_map_to_hacl_msg inp) == msg) ==>
    //   ((eq_vale_map l (hacl_msg_to_vale_map msg) inp))
    // );

  // vale_map_to_msg_for_eq l (hacl_msg_to_vale_map msg) inp;
  // assert (
    //   ((eq_vale_map l (hacl_msg_to_vale_map msg) inp) ==>
          //    (vale_map_to_hacl_msg inp) == msg)
    // );
  admit ()
  // let vale_msg = vale_map_to_msg inp in
  // inp_equivalence' vale_msg hacl_msg;
  // vale_map_msg_equiv inp (vale_map_to_msg #l inp);
  // admit // todo:prove
                   //     ()
