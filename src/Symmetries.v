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



(** * Symmetries
  This section deals with the symmetries. 
  Symmetries are bigraphs that should obey properties specified in (S1),(S2),(S3) and (S4). *)
Module Symmetries (s : SignatureParameter) (n : InfiniteParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Section S1.
Lemma arity_symmetry_eq : forall m:nat, forall X:NoDupList, 
  forall n,
  Arity (get_control (bg := symmetry_big m X 0 EmptyNDL) n) =
  Arity (get_control (bg := bigraph_id m X) n) .
  Proof.
    intros.
    destruct n.
  Qed.

Theorem symmetry_eq_id : forall m:nat, forall X:NoDupList, 
  support_equivalence 
    (symmetry_big m X 0 EmptyNDL)
    (bigraph_id m X). 
  Proof.
    intros m X.
    refine (
      SupEq _ _ _ _ _ _ _ _  
        (symmetry_big m X 0 EmptyNDL)
        (bigraph_id m X)
        (addn0 m) (*s*)
        (fun (name : InfType) => right_empty X name) (*i*)
        (addn0 m) (*r*)
        (fun (name : InfType) => right_empty X name) (*o*)
        bij_id (*n*)
        bij_id (*e*)
        (fun n => bij_rew (@arity_symmetry_eq m X n)) (*p*)
        _ _ _
      ).
    + apply functional_extensionality.
      intro x.
      reflexivity. 
    + simpl. apply functional_extensionality.
      destruct x as [v | s1]; simpl.
      - destruct v.
      - destruct s1. unfold funcomp, parallel. f_equal.
        unfold bij_rew_forward. simpl.
        rewrite eq_rect_ordinal. 
        destruct (ltnP m0 m).
        rewrite eq_rect_ordinal.
        apply val_inj. simpl. apply addn0.
        exfalso.
        apply (lt_ge_contradiction m0 m); assumption.
    + apply functional_extensionality.
      destruct x as [[name] | (v, tmp)]; simpl.
      - unfold funcomp.
        simpl.
        f_equal. apply subset_eq_compat. reflexivity. 
      - destruct v.
  Qed.

End S1.


Section S2.
Definition permutation_union_commute : forall X Y:NoDupList,
  permutation (X ∪ Y) (Y ∪ X).
  Proof.
    intros. 
    unfold permutation.
    intros. split; intros.
    apply in_app_iff in H.
    destruct H. 
    apply in_app_iff. auto.
    apply in_app_iff. auto.
    apply in_app_iff in H.
    destruct H. 
    apply in_app_iff. auto.
    apply in_app_iff. auto.
  Qed.

Definition permutation_union_commutePN : forall X Y:NoDupList,
  PermutationNDL (X ∪ Y) (Y ∪ X).
  Proof.
    intros. constructor.
    apply permutation_union_commute.
  Qed.

Definition commute_plus_MyEqNat : forall m n,
  MyEqNat (m + n) (n + m).
  Proof. intros. constructor. apply addnC. Qed.

Theorem symmetry_eq_tp_id : forall m n:nat, forall X Y:NoDupList, 
  support_equivalence 
    (bigraph_composition (p:=permutation_union_commutePN Y X) (eqsr := commute_plus_MyEqNat m n)
      (symmetry_big m X n Y) 
      (symmetry_big n Y m X))
    (bigraph_id (m + n) (X ∪ Y)). 
  Proof.
    intros m n X Y.
    refine (
      SupEq (n + m) (m + n) (m + n) (m + n) (Y ∪ X) (X ∪ Y) (X ∪ Y) (X ∪ Y)  
        (bigraph_composition (p:=permutation_union_commutePN Y X) (eqsr := commute_plus_MyEqNat m n)
          (symmetry_big m X n Y) 
          (symmetry_big n Y m X))
        (bigraph_id (m + n) (X ∪ Y))
        (addnC n m) (*s*)
        (permutation_union_commute Y X) (*i*)
        (reflexivity (m+n)) (*r*)
        (permutation_id (X ∪ Y)) (*o*)
        bij_void_sum_void (*n*)
        bij_void_sum_void (*e*)
        _
        _ _ _
      ).
    + apply functional_extensionality.
      intro x.
      destruct x.
    + simpl. apply functional_extensionality.
      destruct x as [v | s1]; simpl.
      - destruct v.
      - unfold funcomp, parallel. simpl. f_equal.
        unfold bij_rew_forward.
        destruct s1; simpl.
        rewrite eq_rect_ordinal.
        destruct (ltnP m0 n). 
        rewrite eq_rect_ordinal.
        destruct (ltnP (m0 + m) m).
        exfalso. rewrite addnC in i2. apply (not_s_lt m m0 i2).
        apply val_inj. simpl. rewrite addnC. rewrite subDnCA.
        rewrite subnn.
        rewrite addn0. reflexivity. apply leqnn.
        rewrite eq_rect_ordinal.
        destruct (ltnP (m0 - n) m).
        apply val_inj. simpl. rewrite <- subnA.
        rewrite subnn.
        rewrite subn0. reflexivity. apply leqnn. apply i1.
        exfalso.
        destruct m.
        * rewrite addnC in i0.
        rewrite addn0 in i0.
        apply (lt_ge_contradiction m0 n); assumption.
        * rewrite addnC in i0. rewrite <- ltn_psubLR in i0. apply ltnSE in i0. 
        apply (lt_ge_contradiction m (m0 - n)); try assumption.
        apply ltn0Sn.
    + apply functional_extensionality.
      destruct x as [[name] | (v, tmp)]; simpl.
      - unfold funcomp.
        simpl.
        f_equal. apply subset_eq_compat. reflexivity. 
      - destruct v.
    Unshelve.
    intros [v|v]; destruct v.
  Qed.
End S2.

Section S3.
Theorem symmetry_distributive_arity {si0 ri1 sj0 rj1:nat} {ii0 oi1 ij0 oj1:NoDupList}
  {disi: ii0#ij0} {diso: oi1#oj1}: 
  forall f:bigraph si0 ii0 ri1 oi1, 
  forall g:bigraph sj0 ij0 rj1 oj1,
  forall n,
  Arity (get_control
    (bg := bigraph_composition 
      (symmetry_big ri1 oi1 rj1 oj1) 
      (f ⊗ g)) n) =
  Arity (get_control
    (bg :=bigraph_composition (p:=permutation_union_commutePN ii0 ij0) (eqsr := commute_plus_MyEqNat sj0 si0)
      (bigraph_tensor_product 
        (dis_i := D_ND (rev_disjoint (DN_D disi)))
        (dis_o := D_ND (rev_disjoint (DN_D diso))) 
        g f)
      (symmetry_big si0 ii0 sj0 ij0)) (bij_void_A_B n)).
  Proof. 
    intros.
    destruct n. elim s0.
    destruct s0.
    reflexivity.
    reflexivity.
  Qed.

Theorem symmetry_distributive {si0 ri1 sj0 rj1:nat} {ii0 oi1 ij0 oj1:NoDupList}
  {disi: ii0#ij0} {diso: oi1#oj1}: 
  forall f:bigraph si0 ii0 ri1 oi1, 
  forall g:bigraph sj0 ij0 rj1 oj1,
  support_equivalence 
    (bigraph_composition 
      (symmetry_big ri1 oi1 rj1 oj1) 
      (f ⊗ g))
    (bigraph_composition (p:=permutation_union_commutePN ii0 ij0) (eqsr := commute_plus_MyEqNat sj0 si0)
      (bigraph_tensor_product 
        (dis_i := D_ND (rev_disjoint (DN_D disi)))
        (dis_o := D_ND (rev_disjoint (DN_D diso))) 
        g f)
      (symmetry_big si0 ii0 sj0 ij0)).
  Proof. 
    intros.
    refine (
      SupEq _ _ _ _ _ _ _ _
        (bigraph_composition 
          (symmetry_big ri1 oi1 rj1 oj1) 
          (f ⊗ g))
        (bigraph_composition (p:=permutation_union_commutePN ii0 ij0) (eqsr := commute_plus_MyEqNat sj0 si0)
          (bigraph_tensor_product 
            (dis_i := D_ND (rev_disjoint (DN_D disi)))
            (dis_o := D_ND (rev_disjoint (DN_D diso))) 
            g f)
          (symmetry_big si0 ii0 sj0 ij0))
        (reflexivity (si0 + sj0)) (*s*)
        (permutation_id (ii0 ∪ ij0)) (*i*)
        (addnC ri1 rj1) (*r*)
        (permutation_union_commute oi1 oj1) (*o*)
        bij_void_A_B (*n*)
        bij_void_A_B (*e*)
        (fun n => bij_rew (symmetry_distributive_arity f g n)) (*p*)
        _ _ _
      ).
    + apply functional_extensionality.
      intros [[ng|nf]|v].
      - reflexivity.
      - reflexivity.
      - elim v.
    + simpl. apply functional_extensionality.
      destruct x as [[[ng|nf]|v] | s1]; simpl.
      - unfold funcomp, parallel.
        simpl. 
        unfold rearrange, sum_shuffle, extract1.
        destruct get_parent; try reflexivity.
        f_equal. unfold bij_rew_forward.
        destruct o0.
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP (ri1 + m) ri1).
        elim (not_s_lt ri1 m i1).
        rewrite eq_rect_ordinal.
        unfold lshift. apply val_inj. simpl. rewrite subDnCA.
        rewrite subnn.
        rewrite addn0. reflexivity. apply leqnn.
      - unfold funcomp, parallel.
        simpl. 
        unfold rearrange, sum_shuffle, extract1.
        destruct get_parent; try reflexivity.
        f_equal. unfold bij_rew_forward.
        destruct o0.
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP m ri1).
        rewrite eq_rect_ordinal.
        unfold rshift. apply val_inj;simpl. apply addnC.
        elim (lt_ge_contradiction m ri1 i0 i1).
      - elim v.
      - unfold funcomp, parallel. simpl. f_equal.
        unfold bij_rew_forward, rearrange, sum_shuffle, extract1.
        destruct s1; simpl. unfold fintype.split.
        simpl.  
        destruct (ltnP m si0).
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP (m + sj0) sj0).
        * exfalso. rewrite addnC in i2. elim (not_s_lt sj0 m i2).
        * simpl. symmetry. erewrite <- (parent_proof_irrelevant f).
        instantiate (1:=Ordinal (n:=si0) (m:=m) i1).
        destruct get_parent;try reflexivity.
        f_equal. destruct o0. rewrite eq_rect_ordinal. simpl. 
        destruct (ltnP m0 ri1).
        unfold rshift. rewrite eq_rect_ordinal. 
        apply val_inj. simpl. apply addnC.
        elim (lt_ge_contradiction m0 ri1 i3 i4).
        apply val_inj. simpl. rewrite addnC. rewrite subDnCA.
        rewrite subnn. rewrite addn0. reflexivity. apply leqnn.
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP (m - si0) sj0).
        erewrite <- (parent_proof_irrelevant g).
        instantiate (1:=Ordinal (n:=sj0) (m:=m - si0) i2).
        destruct get_parent;try reflexivity.
        f_equal. destruct o0. rewrite eq_rect_ordinal. simpl. 
        destruct (ltnP (ri1 + m0) ri1).
        * elim (not_s_lt ri1 m0 i4).
        * unfold lshift.
        rewrite eq_rect_ordinal. apply val_inj. simpl. rewrite subDnCA.
        rewrite subnn. rewrite addn0. reflexivity. apply leqnn.
        apply val_inj. simpl. reflexivity.
        exfalso.
        destruct sj0.
        * rewrite addn0 in i0.
        apply (lt_ge_contradiction m si0); assumption.
        * rewrite <- ltn_psubLR in i0. apply ltnSE in i0. apply (lt_ge_contradiction sj0 (m - si0)); try assumption.
        apply ltn0Sn.
    + apply functional_extensionality.
      destruct x as [[name] | (v, tmp)]; simpl.
      - unfold funcomp.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold rearrange, switch_link, extract1.
        destruct (in_dec EqDecN name ii0); destruct (in_dec EqDecN name ij0).
        * exfalso. destruct disi as [disi]. apply (disi name i1 i2).
        * unfold in_app_or_m_nod_dup. 
        destruct (in_dec EqDecN name ii0).
        rewrite <- (innername_proof_irrelevant f i2). 
        destruct get_link; try reflexivity. f_equal. unfold permut_list_forward. destruct s0. apply subset_eq_compat. reflexivity.
        contradiction.
        * unfold in_app_or_m_nod_dup. 
        destruct (in_dec EqDecN name ij0).
        rewrite <- (innername_proof_irrelevant g i1). 
        destruct get_link; try reflexivity. f_equal. unfold permut_list_forward. destruct s0. apply subset_eq_compat. reflexivity.
        contradiction.
        * simpl in i0. exfalso. rewrite in_app_iff in i0. destruct i0; contradiction.
      - unfold parallel, sum_shuffle, choice, funcomp.
        simpl.
        unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
        simpl.
        unfold bij_rew_forward, eq_rect_r, funcomp.
        simpl.
        unfold rearrange, switch_link, extract1, bij_subset_forward.
        simpl.
        destruct v as [[ng|nf] | v].
      (*
          erewrite eq_rect_pi.
          erewrite (eq_rect_pi (x := v1)).
      *)
        * rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        destruct tmp.
        destruct get_link; try reflexivity.
        ** f_equal. destruct s0. apply subset_eq_compat. reflexivity.
        * rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        destruct tmp.
        destruct get_link; try reflexivity.
        ** f_equal. destruct s0. apply subset_eq_compat. reflexivity.
        * destruct v.
  Qed.
End S3.

Section S4.
Lemma MyPN {mI mJ mK:nat} {XI XJ XK:NoDupList}
  {disIJ : XI # XJ} {disKJ : XK # XJ} {disIK : XI # XK}:
  permutation 
    (XI ∪ XK ∪ XJ)
    (ndlist (i ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK)))).
  Proof.
    simpl.
    intros; split; intros; apply in_app_iff in H; destruct H.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    right.
    apply in_app_iff; auto.
    - apply in_app_iff; auto.
    right.
    apply in_app_iff; auto.
    - apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    -  apply in_app_iff in H; destruct H;
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
  Qed.

Definition myEqNatproof {mI mJ mK:nat} : MyEqNat (mI + mK + mJ) (mI + (mJ + mK)).
  Proof. constructor. auto. symmetry. rewrite addnC. rewrite addnCAC. reflexivity. Qed.
Theorem easynat : forall mI mJ mK, mI + mJ + mK = mI + mK + mJ.
  Proof. intros. rewrite addnCAC. rewrite addnC. rewrite addnA. reflexivity. Qed.
Theorem easyperm : forall XI XJ XK, 
  permutation (XI ∪ XJ ∪ XK) (XI ∪ XK ∪ XJ).
  Proof. 
    intros; split; intros; apply in_app_iff in H; destruct H.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    - apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    - apply in_app_iff; auto. 
    left.
    apply in_app_iff; auto.
  Qed.


Theorem symmetry_distributive_s4 {mI mJ mK:nat} {XI XJ XK:NoDupList}
  {disIJ : XI # XJ} {disKJ : XK # XJ} {disIK : XI # XK}:
  support_equivalence
    (symmetry_big (mI+mJ) (XI ∪ XJ) mK XK)
    (bigraph_composition (p := P_NP (permutation_commute (MyPN (mI:=mI) (mJ:=mJ) (mK:=mK)))) (eqsr:= myEqNatproof)
      ((symmetry_big mI XI mK XK) ⊗ (bigraph_id mJ XJ))
      ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK))).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      (symmetry_big (mI+mJ) (XI ∪ XJ) mK XK)
      (bigraph_composition (p := P_NP (permutation_commute (MyPN (mI:=mI) (mJ:=mJ) (mK:=mK)))) (eqsr:= myEqNatproof)
        ((symmetry_big mI XI mK XK) ⊗ (bigraph_id mJ XJ))
        ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK)))
      (esym (addnA mI mJ mK)) (*s*)
      (@tr_permutation XI XJ XK) (*i*)
      (easynat mI mJ mK) (*r*)
      (easyperm XI XJ XK) (*o*)
      bij_void4 (*n*)
      bij_void4 (*e*)
      (fun n => bij_rew (void_univ_embedding n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intros [[v|v]|[v|v]]; destruct v.
  + simpl. apply functional_extensionality.
    destruct x as [[[v|v]|[v|v]] | s1]; try destruct v; simpl.
    unfold funcomp, parallel. simpl. f_equal.
    unfold bij_rew_forward,rearrange,sum_shuffle,extract1.
    destruct s1; simpl.
    unfold fintype.split. simpl.
    destruct (ltnP m mI).
    - rewrite eq_rect_ordinal.
    rewrite eq_rect_ordinal.
    simpl. unfold unsplit,lshift,rshift. simpl.
    destruct (ltnP m (mI + mJ)).
    *  rewrite eq_rect_ordinal.
    destruct (ltnP m (mI + mK)).
    ** f_equal. 
    destruct (ltnP m mI).
    apply val_inj;simpl. reflexivity.
    discriminate (i1).
    ** exfalso. apply leq_addl_trans in i3. 
    apply (lt_ge_contradiction m mI); assumption.
    * rewrite eq_rect_ordinal.
    destruct (ltnP m (mI + mK)).
    ** f_equal. apply val_inj;simpl. destruct (ltnP m mI). simpl.
    exfalso. apply leq_addl_trans in i2. 
    apply (lt_ge_contradiction m mI); assumption.
    discriminate i1. 
    exfalso. apply leq_addl_trans in i2. 
    apply (lt_ge_contradiction m mI); assumption.
    - rewrite eq_rect_ordinal. simpl.
    rewrite eq_rect_ordinal. simpl.
    destruct (ltnP (m - mI) mJ).
    * simpl. destruct (ltnP m (mI + mJ)); rewrite eq_rect_ordinal;
    destruct (ltnP (mI + (m - mI + mK)) (mI + mK)).
    ** f_equal. unfold unsplit,lshift.
    apply val_inj;simpl.
    destruct (ltnP (mI + (m - mI + mK)) mI). simpl.
    exfalso. clear i2. clear i0. clear i3. clear i5.
    rewrite addnC in i4.
    rewrite <- (addnA (m-mI) mK mI) in i4.
    rewrite addBnAC in i4; try assumption.
    rewrite subDnCA in i4.
    rewrite <- addnBA in i4. 
    rewrite subnn in i4. rewrite addn0 in i4. 
    rewrite ltn_add2r in i4.
    apply (lt_ge_contradiction m mI); try assumption. apply leqnn.
    apply leq_addl.
    simpl. exfalso. clear i2. clear i0. clear i3. clear i5.
    rewrite addnC in i4.
    rewrite <- (addnA (m-mI) mK mI) in i4.
    rewrite addBnAC in i4; try assumption.
    rewrite subDnCA in i4.
    rewrite <- addnBA in i4. 
    rewrite subnn in i4. rewrite addn0 in i4. 
    rewrite ltn_add2r in i4.
    apply (lt_ge_contradiction m mI); try assumption. apply leqnn.
    apply leq_addl.
    ** f_equal. unfold unsplit,lshift.
    apply val_inj;simpl.
    symmetry.
    rewrite subnDAC.
    rewrite addnA.
    rewrite addnC.
    rewrite addnA.
    apply eq_sum_r; try reflexivity.
    rewrite <- subDnCA; try assumption.
    rewrite plus_minus. 
    rewrite plus_minus.
    rewrite addnBAC; try assumption.
    rewrite plus_minus. reflexivity. 
    * f_equal. unfold unsplit,lshift,rshift.
    apply val_inj;simpl. symmetry.
    destruct (ltnP (mI + (m - mI + mK)) mI).
    ** simpl. exfalso. clear i2. clear i0. clear i3. clear i5.
    rewrite addnC in i4.
    rewrite <- (addnA (m-mI) mK mI) in i4.
    rewrite addBnAC in i4; try assumption.
    rewrite subDnCA in i4.
    rewrite <- addnBA in i4. 
    rewrite subnn in i4. rewrite addn0 in i4. 
    rewrite ltn_add2r in i4.
    apply (lt_ge_contradiction m mI); try assumption. apply leqnn.
    apply leq_addl.
    ** simpl. exfalso. clear i2. clear i0. clear i3. clear i5.
    rewrite addnC in i4.
    rewrite <- (addnA (m-mI) mK mI) in i4.
    rewrite addBnAC in i4; try assumption.
    rewrite subDnCA in i4.
    rewrite <- addnBA in i4. 
    rewrite subnn in i4. rewrite addn0 in i4. 
    rewrite ltn_add2r in i4.
    apply (lt_ge_contradiction m mI); try assumption. apply leqnn.
    apply leq_addl.
    * f_equal. unfold unsplit,lshift,rshift.
    apply val_inj;simpl. exfalso. clear i1. clear i0. clear i4. 
    apply minus_lt in i2. rewrite addnC in i2. 
    apply (lt_ge_contradiction m (mI+mJ)); assumption.
    - simpl. destruct (ltnP m (mI + mJ)); rewrite eq_rect_ordinal.
     * exfalso.
    rewrite leq_subRL in i2.
    apply (lt_ge_contradiction m (mI+mJ)); assumption.
    apply i1.
    * clear i3.
    destruct (ltnP (mI + (m - mI - mJ)) (mI + mK)).
    ** f_equal. unfold unsplit,lshift,rshift.
    apply val_inj;simpl. destruct (ltnP (mI + (m - mI - mJ)) mI).
    *** simpl.  exfalso.
    apply (not_s_lt mI (m - mI - mJ) i4).
    *** simpl. symmetry. rewrite addnC. rewrite plus_minus.
    rewrite subnDA. reflexivity.
    ** f_equal. unfold unsplit,lshift,rshift.
    apply val_inj;simpl. exfalso.
    rewrite leq_add2l in i3.
    rewrite leq_subRL in i3; try apply i2. 
    rewrite leq_subRL in i3; try apply i1. 
    apply (lt_ge_contradiction m (mI+(mJ+mK))); assumption.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - unfold funcomp,rearrange,switch_link,parallel,sequence.
      simpl.
      unfold funcomp,rearrange,switch_link,parallel,sequence,sum_shuffle,extract1,bij_list_backward',permut_list_forward,bij_list_forward.
      destruct (in_dec EqDecN name XI).
      * destruct (in_dec EqDecN name (XI ∪ XK)).
      ** f_equal. apply subset_eq_compat. reflexivity.
      ** f_equal. apply subset_eq_compat. reflexivity.
      * destruct (in_dec EqDecN name (XI ∪ XK)).
      ** f_equal. apply subset_eq_compat. reflexivity.
      ** f_equal. apply subset_eq_compat. reflexivity.
    - destruct v; simpl in s0; destruct s0. destruct e. destruct e. destruct e. destruct e.
  Qed.

End S4.

Section SymmetryAxiom.
Lemma symmetry_axiom : forall m n X Y, 
  support_equivalence 
    (symmetry_big m X n Y) 
    (symmetry_big m EmptyNDL n EmptyNDL ⊗ bigraph_id 0 (X ∪ Y)).
  Proof.
  intros. 
  refine (
    SupEq _ _ _ _ _ _ _ _
      (symmetry_big m X n Y)
      (symmetry_big m EmptyNDL n EmptyNDL ⊗ bigraph_id 0 (X ∪ Y))
      (esym (addn0 (m+n))) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (esym (addn0 (m+n))) (*r*)
      (permutation_left_neutral_neutral) (*o*)
      (bijection_inv bij_void_sum_void) (*n*)
      (bijection_inv bij_void_sum_void) (*e*)
      (fun n => bij_rew (void_univ_embedding n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intros [v|v]; destruct v.
  + simpl. apply functional_extensionality.
    destruct x as [[v|v] | s1]; try destruct v; simpl.
    unfold funcomp, parallel. simpl.
    unfold bij_rew_forward,rearrange,sum_shuffle,extract1.
    destruct s1; simpl.
    rewrite eq_rect_ordinal.
    unfold fintype.split;simpl.
    destruct (ltnP m0 (m + n)).
    2: {exfalso. rewrite addn0 in i0. elim (lt_ge_contradiction m0 (m+n) i0 i1). }
    unfold unsplit,lshift. f_equal. simpl.
    destruct (ltnP m0 m); rewrite eq_rect_ordinal; apply val_inj;simpl; reflexivity.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - unfold funcomp,rearrange,switch_link,parallel,sequence.
      simpl.
      unfold funcomp,rearrange,switch_link,parallel,sequence,sum_shuffle,extract1,bij_list_backward',permut_list_forward,bij_list_forward.
      f_equal. apply subset_eq_compat. reflexivity.    
    - simpl in v. destruct v as [v|v]; destruct v.
  Qed.

End SymmetryAxiom. 

    
End Symmetries.