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


Module NodeAxiom (s : SignatureParameter) (n : NamesParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Theorem nodeAxiomelementary {N N':Name} 
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) 1} : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗ (elementary_renaming N N'))
      <<o>> @discrete_ion _ tt k (OneelNDL N) Hk)
    (@discrete_ion _ tt k (OneelNDL N') (Hk)).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗ (elementary_renaming N N'))
      <<o>> @discrete_ion _ tt k (OneelNDL N) Hk)
      (@discrete_ion _ tt k (OneelNDL N') (Hk))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_left_neutral_neutral) (*o*)
      (bijection_nest_left_neutral) (*n*)
      (bijection_nest_left_neutral) (*e*)
      (_)  (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ intros. simpl in *. destruct n1 as [[v|v]|nodeion]; try destruct v.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1]; unfold extract1.
      + unfold bij_rew_forward. 
      rewrite eq_rect_ordinal. simpl.
      unfold fintype.split. simpl.
      destruct (ltnP 0 1).
      unfold unsplit,lshift.
      f_equal. apply val_inj. simpl. reflexivity.
      discriminate i0.
      reflexivity.
    - simpl.
      unfold parallel,funcomp,bij_subset_forward,switch_link. simpl.
      apply functional_extensionality.
      intros [v|port].
      exfalso.
      destruct v. apply f.
      unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward,bijection_nest_left_neutral.
      destruct port.
      simpl. unfold funcomp.
      unfold eq_rect_r.
      simpl.
      rewrite rew_const.
      destruct o0.
      unfold extract1,sum_shuffle,bij_list_backward',permut_list_forward.
      destruct m.
      destruct (in_dec EqDecN N EmptyNDL).
      elim i1.
      f_equal. unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      simpl.
      f_equal. 
      apply subset_eq_compat. simpl.
      destruct Hk.
      rewrite eqxy in i0.
      discriminate i0.
  Qed.



Theorem nodeAxiomProductelementary {N N' M M':Name} 
  {ndl : NoDup [M;N]}
  {ndl' : NoDup [M';N']}
  {HN : (OneelNDL M) # (OneelNDL N)}
  {HN' : (OneelNDL M') # (OneelNDL N')}
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) 2}  : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗
       ((elementary_renaming M M') ⊗ (elementary_renaming N N')))
      <<o>> @discrete_ion _ tt k (mkNoDupList [M;N] ndl) Hk)
    (@discrete_ion _ tt k (mkNoDupList [M';N'] ndl') Hk).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗
       ((elementary_renaming M M') ⊗ (elementary_renaming N N')))
      <<o>> @discrete_ion _ tt k (mkNoDupList [M;N] ndl) Hk)
      (@discrete_ion _ tt k (mkNoDupList [M';N'] ndl') Hk)
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_commute (PN_P permaxi)) (*o*)
      (bij_node_axiom_product) (*n*)
      (bij_node_axiom_product) (*e*)
      (_)  (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ intros. simpl in *. destruct n1 as [[v|[v|v]]|nodeion]; try destruct v.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1]; unfold extract1.
      + unfold bij_rew_forward. 
      rewrite eq_rect_ordinal. simpl.
      unfold fintype.split. simpl.
      destruct (ltnP 0 1).
      unfold unsplit,lshift.
      f_equal. apply val_inj. simpl. reflexivity.
      discriminate i0.
      reflexivity.
    - simpl.
      unfold parallel,funcomp,bij_subset_forward,switch_link. simpl.
      apply functional_extensionality.
      intros [v|port].
      exfalso.
      destruct v. apply f.
      unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward,bijection_nest_left_neutral.
      destruct port.
      simpl. unfold funcomp.
      unfold eq_rect_r.
      simpl.
      rewrite rew_const.
      destruct o0.
      unfold extract1,sum_shuffle,bij_list_backward',permut_list_forward.
      simpl in Hk.
      destruct m.
      destruct (in_dec EqDecN M EmptyNDL).
      + elim i1.
      + simpl.
      destruct (EqDecN M M).
      f_equal.  unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      elim n0. reflexivity.
      simpl.
      simpl.
      destruct m.
      destruct (EqDecN M N).
      subst M.
      exfalso. 
      apply NoDup_cons_iff in ndl.
      destruct ndl.
      elim H. constructor. reflexivity.
      f_equal. unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      simpl.
      destruct Hk.
      exfalso.
      rewrite eqxy in i0.
      discriminate i0.
  Qed.


Fixpoint index (n:Name) (l:list Name) := match l with 
  | [] => 0
  | t::q => if EqDecN t n then 0 else 1 + index t q 
  end.
  
Lemma index_size x s : index x s <= size s.
Admitted.

Lemma index_mem x s : (index x s < length s) -> (In x s).
Admitted.

Lemma mem_index x s : (In x s) -> (index x s < length s).
Admitted.

Lemma memNindex x s : (~In x s) -> index x s = size s.
Admitted.

Lemma nth_index x s : In x s -> nth (index x s) s DefaultName = x.
Admitted.

Lemma nthIn n l : (n < length l) -> In (nth n l DefaultName) l.
Admitted.

Lemma index_nth_id i s : i < length s -> NoDup s -> 
  index (nth i s DefaultName) s = i.
Admitted.

Definition mkLinkRenaming (i:NoDupList) (o:NoDupList) 
  {Hlen : length i = length o}: 
  NameSub i + Port void_univ_embedding -> NameSub o + void.
  Proof.
  intros [[inner Hinner]|[v _]];try destruct v.
  left.
  destruct i as [i ndi].
  destruct o as [o ndo].
  unfold NameSub in *.
  exists (nth (index inner i) o DefaultName).
  simpl in *.
  apply nthIn.
  rewrite <- Hlen.
  apply mem_index.
  apply Hinner.
  Defined.


Definition renaming (i o: NoDupList) 
  {Hlen: length i = length o}: bigraph 0 i 0 o.
  refine (@Big 0 i 0 o 
    void 
    void 
    void_univ_embedding
    _ (mkLinkRenaming i o) _
  ).
  apply Hlen.
  Unshelve.
  2:{exact (fun x => x). }
  unfold FiniteParent. intros n;destruct n.
  Defined.

Print  renaming.


Theorem nodeAxiom {N N':NoDupList} 
  {Hlen: length N = length N'} 
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) (length (ndlist N))} : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗ (@renaming N N' Hlen))
      <<o>> @discrete_ion _ tt k N Hk)
    (@discrete_ion _ tt k N' (rewriteEqNat Hlen Hk)).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗ (@renaming N N' Hlen))
      <<o>> @discrete_ion _ tt k N Hk)
      (@discrete_ion _ tt k N' (rewriteEqNat Hlen Hk))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_left_neutral_neutral) (*o*)
      (bijection_nest_left_neutral) (*n*)
      (bijection_nest_left_neutral) (*e*)
      (_) (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ intros. simpl in *. destruct n1 as [[v|v]|nodeion]; try destruct v.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join.
      apply functional_extensionality. intros nodeion.
      unfold eq_rect_r. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1].
      + unfold extract1,eq_rect_r. 
      unfold bij_rew_forward. rewrite eq_rect_ordinal.
      unfold fintype.split.
      simpl.
      destruct (ltnP 0 1).
      f_equal. unfold unsplit,lshift.
      apply val_inj. simpl. reflexivity. 
      + discriminate i0.
      reflexivity. 
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1,switch_link,rearrange.
    simpl.
    apply functional_extensionality. intros [innervoide|ports].
    + destruct innervoide. elim f.
    + destruct ports as [nodeion ports].
    unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward.    
    unfold eq_rect_r. unfold bijection_inv. simpl.
    rewrite rew_const.
    destruct ports as [ports Hports].
    unfold extract1. simpl.
    unfold bij_list_backward',permut_list_forward. 
    destruct N as [N NDL].
    destruct N' as [N' NDL'].
    destruct (in_dec EqDecN (nth ports N DefaultName) EmptyNDL).
    * elim i0.
    * unfold mkLinkRenaming. 
    f_equal.
    unfold bij_subset_forward,bij_list_forward.
    apply subset_eq_compat. simpl.
    rewrite index_nth_id.
    reflexivity.
    destruct Hk as [Hk].
    simpl in Hk.
    rewrite <- Hk.
    apply Hports.
    apply NDL.
    Qed.

End NodeAxiom.