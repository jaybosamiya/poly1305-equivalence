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
  a:size_t{a <= l} ->
  x:lbytes l ->
  y:lbytes l ->
  Lemma (requires
           ((sub x 0 a == sub y 0 a) /\
            (sub x a (l-a) == sub y a (l-a))))
    (ensures x == y)
let subs_eq #l a x y =
  let (b : size_t{b <= l}) =
    // for some reason, it refuses to infer [b <= l] on its own
          l - a in
  sub_semantics x 0 a;
  sub_semantics y 0 a;
  assert (forall (i:size_t{i<a}). x.[i] == y.[i]);
  sub_semantics x a b;
  sub_semantics y a b;
  assert (forall (i:size_t{i<b}). x.[i+a] == y.[i+a]);
  assert (forall (j:size_t{a <= j /\ j < l}). x.[(j-a)+a] == y.[j]) // the [(j-a)+a] is required to push the proof through

(** Reverse direction of repeati *)
val repeati_reverse :
  #a:Type{hasEq(a)} ->
  cur:size_t{(0 < cur)} ->
  up:(j:nat{j<cur}->a->a) ->
  x:a ->
  Lemma
    (ensures
       forall (i:size_t{(0<i) /\ (i<=cur)}).
                repeati i up x = up (i-1) (repeati (i-1) up x))

let rec repeati_reverse #a cur up x =
  Axioms.repeati_semantics cur up x;
  Axioms.repeati_semantics (cur-1) up x;
  match cur with
  | 1 -> ()
  | _ ->
    repeati_reverse #a (cur-1) up x;
    match cur with
    | 2 -> ()
    | _ ->
      repeati_reverse #a (cur-2) up x;
      match cur with
      | 3 -> ()
      | _ ->
        repeati_reverse #a (cur-3) up x;
        match cur with
        | 4 -> ()
        | _ -> admit () (* TODO: Prove. I have rolled this out a bit to
                           show a possible direction to go in *)
