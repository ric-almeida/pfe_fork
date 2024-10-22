Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import TensorProduct.
Require Import MathCompAddings.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.


From mathcomp Require Import all_ssreflect.

Require Import List.



Module PlaceAxioms (s : SignatureParameter) (n : InfiniteParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Lemma place_axiom_join_sym1_1 : 
  support_equivalence
    (join_big <<o>> symmetry_big 1 EmptyNDL 1 EmptyNDL)
    join_big.
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (join_big <<o>> symmetry_big 1 EmptyNDL 1 EmptyNDL)
      join_big
      (esym (addn0 (1+1))) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bij_void_sum_void) (*n*)
      (bij_void_sum_void) (*e*)
      (fun n => match n with 
      | inl n => bij_rew (void_univ_embedding n) (*p*)
      | inr n => bij_rew (void_univ_embedding n)
      end) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    destruct x.
  + simpl. apply functional_extensionality.
    destruct x as [v | s1]; try destruct v; simpl.
    unfold funcomp, parallel. simpl. reflexivity.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - elim i0.    
    - simpl in v. destruct v.
  Qed.

Lemma place_axiom_join_1_id_1 : 
  support_equivalence
    (join_big <<o>> (big_1 ⊗ bigraph_id 1 EmptyNDL))
    (bigraph_id 1 EmptyNDL).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (join_big <<o>> (big_1 ⊗ bigraph_id 1 EmptyNDL))
      (bigraph_id 1 EmptyNDL)
      (esym (addn0 (1))) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bijection_inv bij_void_sum_sum) (*n*)
      (bijection_inv bij_void_sum_sum) (*e*)
      (fun n => match n with 
      | inl n => bij_rew (void_univ_embedding n) (*p*)
      | inr n => match n with 
        | inl n => bij_rew (void_univ_embedding n)
        | inr n => bij_rew (void_univ_embedding n)
        end
      end) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    destruct x.
  + simpl. apply functional_extensionality.
    destruct x as [v | [s1]]; try destruct v; simpl.
    unfold funcomp, parallel,rearrange. simpl.
    unfold sum_shuffle,rearrange,fintype.split.
    unfold bij_rew_forward.
    rewrite eq_rect_ordinal. simpl. 
    destruct (ltnP s1 0).
    - discriminate i1.
    - f_equal. apply val_inj. simpl. apply lt1_eq0 in i0. auto.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - elim i0.    
    - simpl in v. destruct v.
  Qed.


Lemma place_axiom_join_id_commutes : 
  support_equivalence
    (join_big <<o>> (join_big ⊗ bigraph_id 1 EmptyNDL))
    (join_big <<o>> (bigraph_id 1 EmptyNDL ⊗ join_big)).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (join_big <<o>> (join_big ⊗ bigraph_id 1 EmptyNDL))
      (join_big <<o>> (bigraph_id 1 EmptyNDL ⊗ join_big))
      (addnC 1 2) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bij_id) (*n*)
      (bij_id) (*e*)
      (fun n => match n with 
      | inl n => bij_rew (void_univ_embedding n) (*p*)
      | inr n => match n with 
        | inl n => bij_rew (void_univ_embedding n)
        | inr n => bij_rew (void_univ_embedding n)
        end
      end) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    destruct x as [v|[v|v]]; destruct v.
  + simpl. apply functional_extensionality.
    destruct x as [[v|[v|v]] | [s1]]; try destruct v; simpl.
    unfold funcomp, parallel,rearrange. simpl.
    unfold sum_shuffle,rearrange,fintype.split.
    unfold bij_rew_forward.
    rewrite eq_rect_ordinal. simpl. 
    destruct (ltnP s1 1); destruct (ltnP s1 2);reflexivity.
  + apply functional_extensionality.
    destruct x as [[name] | ([v|[v|v]], tmp)]; simpl; try simpl in v; try destruct v.
    - elim i0.   
  Qed.


End PlaceAxioms.