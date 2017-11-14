module InpEquivalence

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

val lbytes_eq : #len:size_t -> a:lbytes len -> b:lbytes len -> bool
let lbytes_eq #len a b =
  nat_from_intseq_le a = nat_from_intseq_le b

val block_h2v : l:size_t{l<=16} -> h:lbytes l -> v:nat128{v<pow2 (8 `op_Multiply` l)}
let block_h2v l h =
  Math.Lemmas.pow2_le_compat 128 (8 `op_Multiply` l);
  nat_from_intseq_le h
val block_v2h : l:size_t{l<=16} -> v:nat128{v<pow2 (8 `op_Multiply` l)} -> h:lbytes l
let block_v2h l v = nat_to_bytes_le l v
val block_invs :
  l:size_t{l<=16} ->
  v:nat128{v<pow2 (8 `op_Multiply` l)} -> h:lbytes l ->
           Lemma ((v = block_h2v l h) <==> lbytes_eq h (block_v2h l v))
let block_invs l v h = ()

    assume
(* Let us say that an [append] function is provided by the [IntSeq] API *)
val append: #len1:size_t -> #len2:size_t ->
  #len:size_t{len=len1+len2} -> s1:lbytes len1 -> s2:lbytes len2 ->
  s:lbytes len{
      (lbytes_eq (sub s 0 len1) s1) /\
      (lbytes_eq (sub s len1 len2) s2)}

type block_bounded_list = {l:nat ; a:list nat128 ; b:list nat}

val block_bounds: k:block_bounded_list -> Tot bool
    (decreases k.l)
let rec block_bounds k =
  match k.l = List.Tot.length k.a && k.l = List.Tot.length k.b with
  | false -> false
  | true -> match k.a with
    | [] -> true
    | h1 :: t1 -> match k.b with
      | h2 :: t2 ->
        let n = {l=k.l+1; a=t1; b=t2} in
        (h1 < pow2(8 `op_Multiply` h2)) && block_bounds n

val zzz : 
  l:nat ->
  a:list nat128{List.Tot.length a = l} ->
  b:list nat{List.Tot.length b = l} -> bool
let rec block_bounds l a b =
  match a with
  | [] -> true
  | h1 :: t1 -> match b with
    | h2 :: t2 -> h1 < pow2(8 `op_Multiply` h2) && block_bounds (l-1) t1 t2

val vale_to_bb :
  inp:(int->nat128) ->
  len:nat ->
  block_bounded_list


let vale_to_bb inp len =
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let rec f (i:nat{i<=nBlocks}) : Tot block_bounded_list (decreases (nBlocks - i)) =
    if i = nBlocks
    then (if nExtra = 0
          then { l=0 ; a=[] ; b=[] }
          else { l=1 ; a=[inp i] ; b=[nExtra] })
    else
      (let k = f (i+1) in
       { l=k.l + 1 ;
         a=inp i :: k.a;
         b=16 :: k.b }) in
  f 0

val vale_to_bb_lemma :
  inp:(int->nat128) ->
  len:nat ->
  Lemma (block_bounds
           (vale_to_bb inp len).l
           (vale_to_bb inp len).a
           (vale_to_bb inp len).b)


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
  forward #l inp len msg;
  reverse #l inp len msg
