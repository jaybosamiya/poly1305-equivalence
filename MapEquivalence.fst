module MapEquivalence

(** Defines an equivalence b/w Vale "maps" int->nat128 and the
    restricted vale_msg that is used in MsgEquivalence *)

open Spec.Lib.IntTypes

let nat128_max = 0x100000000000000000000000000000000
let _ = assert_norm (pow2 128 = nat128_max)
type nat128 = x:int{0 <= x && x < nat128_max}

type msg l=MsgEquivalence.vale_msg l
let sat_idx = MsgEquivalence.sat_idx

let msg_to_map (#l:size_t) (inp:msg l) : (int->nat128) =
  fun i ->
    if sat_idx l i && i >= 0
    then inp i
    else 0

         #set-options "--z3refresh" // for some reason, required to
                  //                   get the next part to type correctly

let map_to_msg (#l:size_t) (inp:int->nat128) : (msg l) =
  if l % 16 = 0
  then
    fun i -> inp i
  else
    fun i ->
      if i = l/16
      then (
        let a = (inp (l/16)) % (pow2 (8 `op_Multiply` (l % 16))) in
        assert (a >= 0 /\ a < nat128_max);
        a)
      else inp i

(** Proposition for equivalent vale messages *)
type eq_vale_map (l:nat) (m1:int->nat128) (m2:int->nat128) = (
  let mod = pow2 (8 `op_Multiply` (l%16)) in
  (forall (x:nat{x < l/16}). {:pattern (m1 x, m2 x)} m1 x = m2 x) /\
  (l%16 <> 0 ==> (m1 (l/16)) % mod = (m2 (l/16)) % mod))

  (* Need to increase limits to have the proofs go through *)
  #set-options "--z3rlimit 1000"

val forward_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:(msg l) ->
  Lemma ((eq_vale_map l map (msg_to_map msg)) ==>
         msg == map_to_msg map)

let forward_equiv #l map msg =
  let map' = msg_to_map msg in
  let msg' = map_to_msg #l map in
  assert ((eq_vale_map l map map') ==>
          (forall (x:nat{x < l/16}). map x == map' x));
  match l % 16 with
  | 0 ->
    assert ((eq_vale_map l map map') ==>
            FStar.FunctionalExtensionality.feq msg msg')
  | _ ->
    assert ((eq_vale_map l map map') ==>
            msg (l/16) = msg' (l/16));
    assert ((eq_vale_map l map map') ==>
            (forall (x:nat{x < l/16}). msg x == msg' x));
    assert ((eq_vale_map l map map') ==>
            FStar.FunctionalExtensionality.feq msg msg')

val map_msg_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:(msg l) ->
  Lemma ((eq_vale_map l map (msg_to_map msg)) <==>
         msg == map_to_msg map)

let map_msg_equiv #l map msg =
  forward_equiv map msg
