Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import ConcreteBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import ParallelProduct.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.

(** Nesting operator *)
Module NestingBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

Example I : NoDupList. Admitted.
Example m : nat. Admitted.
Example X : NoDupList. Admitted.
Example n : nat. Admitted.
Example Y : NoDupList. Admitted.
Example F : bigraph 0 I m X. Admitted.
Example G : bigraph m EmptyNDL n Y. Admitted.
Example dis_i : X # Y. Admitted.

(* Example id_pp_G := 
  bigraph_parallel_product 
    (dis_i := void_disjoint_all_list_right X) 
    (bigraph_identity (s := 0) (i := X)) 
    G. *)


Definition nest {I m X n Y m'} (* nest G F = G.F *)
  (G : bigraph m EmptyNDL n Y) (F : bigraph 1 I m' X) {eq mm' : MyEqNat m m'}
  : bigraph 1 I n (app_merge_NoDupList X Y) :=
  ((bigraph_identity (s := 0) (i := X)) || G) <<o>> F.

Global Notation "G '<.>' F" := (nest G F) (at level 50, left associativity).

Lemma id_union'' : forall X Y:NoDupList, 
  bigraph_equality
  (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
  ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
    + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
    + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Lemma my_id_union : forall X Y:NoDupList, 
  bigraph_equality
    (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
    ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
    + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
    + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.


Theorem nest_associative {I X Y n Z}
  (F : bigraph 1 I 1 X) (G : bigraph 1 EmptyNDL 1 Y) (H : bigraph 1 EmptyNDL n Z) :
  bigraph_equality
    (H <.> (G <.> F))
    ((H <.> G) <.> F).
  Proof.
  unfold nest.
  (* rewrite my_id_union.
  rewrite (id_union'' X Y). *)
  Admitted.


Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph 0 i2 s1 i1. Admitted.

(* Theorem atom_is_empty_ion : 
  bigraph_equality.
  (discrete_ion <o> ∅)
  discrete_atom. *)

End NestingBig.