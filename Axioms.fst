module Axioms

(** Whole bunch of axioms that we use throughout the rest of the proofs *)

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

(** Axiom: Two sequences are equal iff all their elements are equal *)
val intseq_eq: t:inttype -> len:size_t ->
  Lemma (forall (a:intseq t len) (b:intseq t len).
                                   (a == b) <==> (forall x. a.[x] == b.[x]))
    [SMTPat (intseq t len)]
let intseq_eq t len = admit ()

(** Axiom: Subsequence actually gives us the subsequence *)
val sub_semantics:
  #t:inttype ->
  #len:size_t ->
  s:intseq t len ->
  start:size_t ->
  n:size_t{start + n <= len} ->
  Lemma (forall (x:size_t{x < n}). (sub s start n).[x] == s.[start + x])
let sub_semantics #t #len s start n = admit()

(** Axiom: Slice gives us the correct subsequence *)
val slice_semantics:
  #t:inttype ->
  #len:size_t ->
  s:intseq t len ->
  start:size_t ->
  fin:size_t{start <= fin /\ fin <= len} ->
  Lemma (slice s start fin == sub s start (fin - start))
let slice_semantics #t #len s start fin = admit ()

(** Axiom: Two sequences are same iff their LE representation is same *)
val eq_nat_from_intseq:
  #t:inttype ->
  #len:size_t ->
  a:intseq t len ->
  b:intseq t len ->
  Lemma (a == b <==> nat_from_intseq_le a == nat_from_intseq_le b)
let eq_nat_from_intseq #t #len a b = admit ()

    assume
(** Assumption: An [append] function is provided by the API *)
val append: #len1:size_t -> #len2:size_t ->
  #len:size_t{len=len1+len2} -> s1:lbytes len1 -> s2:lbytes len2 ->
  s:lbytes len{(sub s 0 len1 == s1) /\
               (sub s len1 len2 == s2)}

(** Axiom: [repeat_range] does what it says it does *)

val repeat_range_semantics :
  #a:Type{hasEq(a)} ->
  min:size_t ->
  max:size_t{min <= max} ->
  f:(s:size_t{s >= min /\ s < max} -> a -> Tot a) ->
  x:a ->
  Lemma (
    ((min = max) ==> repeat_range #a min max f x = x) /\
    ((min < max) ==> repeat_range #a min max f x = repeat_range #a (min+1) max f (f min x)))
    [SMTPat (repeat_range #a min max f x)]
let repeat_range_semantics #a min max f x = admit ()

(** Axiom: [repeati] does what it says it does *)
val repeati_semantics :
  #a:Type{hasEq(a)} ->
  n:size_t ->
  f:(i:size_t{i < n} -> a -> Tot a) ->
  x:a ->
  Lemma (repeati #a n f x = repeat_range #a 0 n f x)
let repeati_semantics #a n f x = admit ()
