module TagEquivalence

(** Prove equivalence b/w the output types used by the Vale and the HACL*
    specs.

    Defines [tag_vale_to_hacl] and [tag_hacl_to_vale] to convert
    between the two tags, and [tag_equivalence] lemma proves that they
    are equivalent. *)

module ValeSpec = Poly1305.Spec_s
module HaclSpec = Spec.Poly1305

                  (* Need to increase limits to have the proofs go through *)
                  #set-options "--z3rlimit 100"


type vale_tag = ValeSpec.nat128 (* Though the ValeSpec returns an int, it
                                   should match with nat128 restrictions anyways *)
type hacl_tag = HaclSpec.tag

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Axioms

val tag_vale_to_hacl : vale_tag -> hacl_tag
let tag_vale_to_hacl t = nat_to_bytes_le 16 t

val tag_hacl_to_vale : hacl_tag -> vale_tag
let tag_hacl_to_vale t = nat_from_intseq_le t

val tag_equivalence :
  t_h : hacl_tag ->
  t_v : vale_tag ->
  Lemma ((tag_vale_to_hacl t_v == t_h) <==> (tag_hacl_to_vale t_h == t_v))
let tag_equivalence t_h t_v = eq_nat_from_intseq (tag_vale_to_hacl t_v) t_h
