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

    assume
(* Let us say that an [append] function is provided by the API *)
val append: #len1:size_t -> #len2:size_t ->
  #len:size_t{len=len1+len2} -> s1:lbytes len1 -> s2:lbytes len2 ->
  s:lbytes len{(sub s 0 len1 = s1) /\
               (sub s len1 len2 = s2)}

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

(* Specifically all "full" blocks *)
let rec inp_to_lseq'
    (inp:int->nat128)
    (rem_len:size_t{rem_len % 16 = 0})
    (i:pos{i = rem_len / 16})
  : lbytes rem_len =
  match i with
  | 1 -> nat_to_bytes_le rem_len (inp i)
  | _ ->
    let prev = inp_to_lseq' inp (rem_len - 16) (i - 1) in
    let curr = nat_to_bytes_le 16 (inp i) in
    append prev curr
(* Any length *)
let inp_to_lseq
    (inp:int->nat128)
    (rem_len:size_t)
    (i:pos{(rem_len % 16 == 0 <==> i = rem_len / 16) /\ 
           (rem_len % 16 <> 0 <==> i = rem_len / 16 + 1)})
  : lbytes rem_len =
  if rem_len % 16 = 0
  then inp_to_lseq' inp rem_len i
  else
    let cur_block_len : size_t = rem_len % 16 in
    let rem_len' : size_t = rem_len - cur_block_len in
    let curr' = nat_to_bytes_le 16 (inp i) in
    let curr = sub curr' 0 cur_block_len in
    match i with
    | 1 -> curr
    | _ ->
      let i':pos = i - 1 in
      let prev = inp_to_lseq'
          inp rem_len' i' in
      append #rem_len' #cur_block_len #rem_len prev curr

let inp_vale_to_hacl #l inp len =
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let n'Blocks = if nExtra = 0 then nBlocks else nBlocks + 1 in
  inp_to_lseq inp len n'Blocks

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
     (inp_vale_to_hacl #l inp len) =
     msg))

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
     (inp_vale_to_hacl #l inp len) = msg))

let inp_equivalence #l inp len msg =
  match len with
  | 0 -> ()
  | _ -> admit () // TODO: prove
