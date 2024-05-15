Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import TensorProduct.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.


(** * Juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Module ParallelProduct (s : SignatureParameter) (n : NamesParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.

Definition join_big := @merge 2. 

#[export] Instance permutation_id_am_l_PN_empty : PermutationNames
                                  (app_merge_NoDupList EmptyNDL EmptyNDL)
                                  EmptyNDL.
constructor. rewrite merge_left_neutral. exact (permutation_id []).
Qed.

#[export] Instance permutation_id_am_l_PN_empty_r : PermutationNames
                                  EmptyNDL
                                  (app_merge_NoDupList EmptyNDL EmptyNDL).
constructor. rewrite merge_left_neutral. exact (permutation_id []).
Qed.

Theorem bij_void_sum_sum : forall {A : Type}, bijection void (void + (void + void)).
Proof.
intros.
apply (mkBijection void (void + (void + void)) void_univ_embedding 
(fun vvv => match vvv with | inl v => match v with end | inr (inl v) => match v with end | inr (inr v) => match v with end end )).
apply functional_extensionality.
destruct x. destruct v. destruct s0. destruct v. destruct v.  
apply functional_extensionality.
destruct x. 
Defined.

Theorem merge_well_defined : forall n, 
  bigraph_equality
    (@merge (n+1))
    (join_big <<o>> (@bigraph_id 1 EmptyNDL ⊗ @merge n)).
  Proof. 
  intros. simpl. 
  refine (BigEq _ _ _ _ _ _ _ _ 
    (@merge (n+1))
    (join_big <<o>> (@bigraph_id 1 EmptyNDL ⊗ @merge n))
    (PeanoNat.Nat.add_comm n 1)
    (PN_P permutation_id_am_l_PN_empty_r)
    eq_refl
    (PN_P permutation_id_am_l_PN_empty)
    bij_void_sum_sum
    bij_void_sum_sum
    _ _ _ _ 
  ). 
  - simpl. apply functional_extensionality. destruct x as [v|[v|v]]; destruct v. 
  - simpl. apply functional_extensionality. destruct x as [[v|[v|v]]|s]; try destruct v.
  simpl. unfold parallel, funcomp, rearrange, sum_shuffle, extract1, id, bij_rew_forward. destruct s. 
  destruct zero1. unfold inj_fin_add. destruct (PeanoNat.Nat.ltb_spec0 x 1). 
  + f_equal. 
  + f_equal. 
  - simpl. apply functional_extensionality. destruct x as [v|s]; try destruct v.
  + elim f. 
  + destruct s. destruct x as [v|[v|v]]; destruct v. 
  Unshelve. 
  * exact nat. * exact nat. 
  *intros. simpl in n1. destruct n1. 
  Qed.