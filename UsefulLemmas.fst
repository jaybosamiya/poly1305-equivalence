module UsefulLemmas

(** Some lemmas that are useful in mutiple proofs *)

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Axioms

(** Property: the subseq of subseq is a subseq *)
val sub_of_sub:
  #t:inttype -> #len:size_t ->
  s:intseq t len ->
  start:size_t -> n:size_t{start + n <= len} ->
  Lemma
    (forall (start':size_t{start' <= start})
       (n':size_t{start + n <= start' + n' /\ start' + n' <= len}).
         sub s start n == sub (sub s start' n') (start - start') n)
    [SMTPat (sub s start n)]
let sub_of_sub #t #len s start n =
  let f (start':size_t{start' <= start})
      (n':size_t{start + n <= start' + n' /\ start' + n' <= len}) :
    Lemma (sub s start n == sub (sub s start' n') (start - start') n) =
    sub_semantics s start n;
    let s' = sub_semantics s start' n'; sub s start' n' in
    sub_semantics s' (start - start') n in
  FStar.Classical.forall_intro_2 f

(** If both parts of 2 sequences are equal, then the sequences themselves are equal *)
val subs_eq :
  #l:size_t ->
  #a:size_t ->
  #b:size_t{a + b = l} ->
  x:lbytes l ->
  y:lbytes l ->
  Lemma (requires
           ((sub x 0 a == sub y 0 a) /\
            (sub x a b == sub y a b)))
    (ensures x == y)
let subs_eq #l #a #b x y =
  sub_semantics x 0 a;
  sub_semantics y 0 a;
  assert (forall (i:size_t{i<a}). x.[i] == y.[i]);
  sub_semantics x a b;
  sub_semantics y a b;
  assert (forall (i:size_t{i<b}). x.[i+a] == y.[i+a]);
  assert (forall (j:size_t{a <= j /\ j < l}). x.[(j-a)+a] == y.[j]) // the [(j-a)+a] is required to push the proof through
