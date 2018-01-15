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

let map_to_msg (#l:size_t) (inp:int->nat128) : (msg l) =
  if l % 16 = 0
  then
    fun i -> inp i
  else
    fun i ->
      if i = l/16
      then (inp (l/16)) % (pow2 (8 `op_Multiply` (l % 16)))
      else inp i

(** Proposition for equivalent vale messages *)
type eq_vale_map (l:nat) (m1:int->nat128) (m2:int->nat128) = (
  let mod = pow2 (8 `op_Multiply` (l%16)) in
  (forall (x:nat{x < l/16}). m1 x = m2 x) /\
  (l%16 <> 0 ==> (m1 (l/16)) % mod = (m2 (l/16)) % mod))

val forward_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:(msg l) ->
  Lemma ((eq_vale_map l map (msg_to_map msg)) ==>
         msg == map_to_msg map)

let forward_equiv #l map msg =
  admit () // TODO: Prove

val backward_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:(msg l) ->
  Lemma (msg == map_to_msg map ==>
         (eq_vale_map l map (msg_to_map msg)))

        (* Need to increase limits to have the proofs go through *)
        #set-options "--z3rlimit 40"

let backward_equiv #l map msg = ()

val map_msg_equiv :
  #l:size_t ->
  map:(int->nat128) ->
  msg:(msg l) ->
  Lemma ((eq_vale_map l map (msg_to_map msg)) <==>
         msg == map_to_msg map)

let map_msg_equiv #l map msg =
  forward_equiv map msg;
  backward_equiv map msg
