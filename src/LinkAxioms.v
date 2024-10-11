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



Module LinkAxioms (s : SignatureParameter) (n : NamesParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Lemma sub_eq_id : forall x, 
  support_equivalence
    (substitution (OneelNDL x) x)
    (bigraph_id 0 (OneelNDL x)).
  Proof.
  intros.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (substitution (OneelNDL x) x)
      (bigraph_id 0 (OneelNDL x))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bij_id) (*n*)
      (bij_id) (*e*)
      (fun n => bij_rew (void_univ_embedding n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intros v; destruct v.
  + simpl. apply functional_extensionality.
    intros [v | [s1]]; try destruct v; simpl.
    discriminate i0.
  + apply functional_extensionality.
    intros [[name] | (v, tmp)]; simpl; try simpl in v; try destruct v.
    unfold funcomp,rearrange,switch_link,parallel,sequence.
    simpl.
    f_equal. apply subset_eq_compat.
    simpl in i0. destruct i0.
    apply H.
    elim H.
  Qed.

Lemma closure_o_subst_neutral : forall x, 
  lean_support_equivalence
    (closure x <<o>> substitution EmptyNDL x)
    (bigraph_id 0 EmptyNDL).
  Proof.
  intros.
  unfold lean_support_equivalence. simpl.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (lean (closure x <<o>> substitution EmptyNDL x))
      (lean (bigraph_id 0 EmptyNDL))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bij_void_sum_void) (*n*)
      (_) (*e*)
      (fun n => _) (*p*)
      _ _ _
    ).
  Unshelve. 4:{simpl.
  eapply (mkBijection _ _ 
    (fun xl => match xl with
      | exist xunitvoid Hxuv => 
        match xunitvoid with
        | inl u => _ 
        | inr v => void_univ_embedding v
        end
      end) 
    (fun xv => match xv with
      | exist xvoid Hxv => void_univ_embedding xvoid end)).
  Unshelve. 3:{exfalso.
  destruct xunitvoid.
  - apply not_is_idle_implies_exists_inner_or_node in Hxuv.
  destruct Hxuv as [ip Hxuv].
  destruct ip as [inner | port].
  destruct inner as [inner Hinner].
  elim Hinner.
  simpl in port.
  destruct port as [port Hport].
  destruct port as [port|port]; destruct port.
  
  elim e. }

  apply functional_extensionality.
  intros [xv Hxv]; destruct xv.

  apply functional_extensionality.
  intros [[xu | xv] Hx]; try destruct xv.
  exfalso.
  apply not_is_idle_implies_exists_inner_or_node in Hx.
  destruct Hx as [ip Hxuv].
  destruct ip as [inner | port].
  destruct inner as [inner Hinner].
  elim Hinner.
  simpl in port.
  destruct port as [port Hport].
  destruct port as [port|port]; destruct port. }

  + apply functional_extensionality.
    intros v; destruct v.
  + simpl. apply functional_extensionality.
    intros [v | [s1]]; try destruct v; simpl.
    discriminate i0.
  + apply functional_extensionality.
    intros [[name] | (v, tmp)]; simpl; try simpl in v; try destruct v.
    elim i0.
  + simpl in n. destruct n as [n|n]; destruct n.
  Qed.

    
(*Note that a closure /x ◦ G may create an idle edge, if x is an idle name of G. Intuitively idle edges are ‘invisible’, and indeed we shall see later how to ignore them.*)
Lemma closure_o_sub_eq_closure : forall x y, 
  support_equivalence
    (closure y <<o>> substitution (OneelNDL x) y)
    (closure x).
  Proof.
  intros.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (closure y <<o>> substitution (OneelNDL x) y)
      (closure x)
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bij_void_sum_void) (*n*)
      (bij_void_sum_neutral_r) (*e*)
      (fun n => match n with 
      | inl n => bij_rew (void_univ_embedding n) (*p*)
      | inr n => bij_rew (void_univ_embedding n)
      end) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intros v; destruct v.
  + simpl. apply functional_extensionality.
    intros [v | [s1]]; try destruct v; simpl.
    discriminate i0.
  + apply functional_extensionality.
    intros [[name] | (v, tmp)]; simpl; try simpl in v; try destruct v.
    unfold funcomp,rearrange,switch_link,parallel,sequence.
    simpl. reflexivity.
  Qed. 

Lemma link_axiom_4 {y z X Y} {disYX: Y # X} {disyY : ~ In y Y}: 
  support_equivalence
    (substitution (Y ∪ (OneelNDL y)) z <<o>> 
      (bigraph_tensor_product 
        (dis_o := disj_OneEl y Y disyY) 
        (bigraph_id 0 Y) 
        (substitution X y)))
    (substitution (Y ∪ X) z).
  Proof.
  intros.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (substitution (Y ∪ (OneelNDL y)) z <<o>> 
        ((bigraph_id 0 Y) ⊗ (substitution X y)))
      (substitution (Y ∪ X) z)
      (erefl) (*s*)
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
    intros v; destruct v.
  + simpl. apply functional_extensionality.
    intros [v | [s1]]; try destruct v; simpl.
    discriminate i0.
  + apply functional_extensionality.
    intros [[name] | (v, tmp)]; simpl; try simpl in v; try destruct v.
    unfold funcomp,rearrange,switch_link,parallel,sequence.
    unfold rearrange,sum_shuffle.
    simpl. 
    destruct (in_dec EqDecN name Y); f_equal; simpl; apply subset_eq_compat; reflexivity.
  Qed. 


End LinkAxioms.