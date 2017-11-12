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

val inp_hacl_to_vale : #l:size_t -> msg:lbytes l -> ((inp:int->nat128) * len:nat{l=len})
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
  g, l

val inp_vale_to_hacl : #l:size_t -> (inp:int->nat128) -> len:pos{l=len} -> msg:lbytes l
let inp_vale_to_hacl #l inp len =
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let n'Blocks : nat = if nExtra = 0 then nBlocks else nBlocks + 1 in
  let rec inp_to_list (rem:nat{rem<=n'Blocks}) : (x:list nat128{List.Tot.length x = rem}) =
    match rem with
    | 0 -> []
    | _ -> inp (n'Blocks - rem - 1) :: inp_to_list (rem - 1) in
  let inp_list = inp_to_list n'Blocks in
  let inp_list_of_lseq = List.Tot.map (nat_to_bytes_le 16) inp_list in
  let rec create_msg lst (blk:nat{List.Tot.length lst + blk = n'Blocks}) : lbytes l =
    let blk = n'Blocks - List.Tot.length lst in
    match lst with
    | [] -> create #uint8 len (u8 0)
    | [h] -> update_sub (create_msg [] (blk+1)) (blk `op_Multiply` 16)
               (if nExtra = 0 then 16 else nExtra)
               (sub h 0 (if nExtra = 0 then 16 else nExtra))
    | h :: t -> update_sub (create_msg t (blk+1)) (blk `op_Multiply` 16)
                  16 h in
  create_msg inp_list_of_lseq 0

let equal_intseqs a b =
  nat_from_intseq_le a = nat_from_intseq_le b

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

val sub_update_partial_semantics :
  #len:size_t ->
  x:lbytes len -> s0:size_t -> n0:size_t{s0 + n0 <= len} -> y:lbytes n0 ->
  z:lbytes len ->
  s1:size_t -> n1:size_t{s1+n1 <= len} ->
  Lemma (
    (((s1 >= s0 + n0) \/ (s1 + n1 <= s0)) ==>
     (equal_intseqs
        (sub z s1 n1)
        (sub x s1 n1))) /\
    (((s1 >= s0) /\ (s1+n1 <= s0+n0)) ==>
     (equal_intseqs
        (sub z s1 n1)
        (sub y (s1-s0) n1))))
(* TODO: Probably figure out a better way around this? *)
let sub_update_partial_semantics #len x s0 n0 y z s1 n1 = admit ()

val forward :
  #l:size_t ->
  inp:(int->nat128) ->
  len:nat{l=len} ->
  msg:lbytes l ->
  Lemma (
    (len = 0) \/
    ((equal_fns inp len
        (fst (inp_hacl_to_vale msg))
        (snd (inp_hacl_to_vale msg)))
     ==>
     (equal_intseqs
        (inp_vale_to_hacl #l inp len)
        msg)))

let forward #l inp len msg =
  match len with
  | 0 -> ()
  | _ ->
    let inp', len' = inp_hacl_to_vale msg in
    assert (len = len');
    match equal_fns inp len inp' len' with
    | false -> ()
    | true ->
      admit () // TODO: prove more


val inp_equivalence :
  #l:size_t ->
  inp:(int->nat128) ->
  len:nat{l=len} ->
  msg:lbytes l ->
  Lemma (
    (len = 0) \/
    ((equal_fns inp len
        (fst (inp_hacl_to_vale msg))
        (snd (inp_hacl_to_vale msg)))
     <==>
     (equal_intseqs
        (inp_vale_to_hacl #l inp len)
        msg)))

let inp_equivalence #l inp len msg =
  match len with
  | 0 -> ()
  | _ -> admit () // TODO: prove
