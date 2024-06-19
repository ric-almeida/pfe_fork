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


Require Import List.



(** * Juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Module Symmetries (s : SignatureParameter) (n : NamesParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.



Lemma arity_symmetry_eq : forall m:nat, forall X:NoDupList, 
  forall n,
  Arity (get_control (symmetry_big m X 0 EmptyNDL) n) =
  Arity (get_control (bigraph_id m X) n) .
  Proof.
  intros.
  destruct n.
  Qed.

  
Theorem symmetry_eq_id : forall m:nat, forall X:NoDupList, 
  bigraph_equality 
    (symmetry_big m X 0 EmptyNDL)
    (bigraph_id m X). 
Proof.
intros m X.
  refine (
    BigEq _ _ _ _ _ _ _ _  
      (symmetry_big m X 0 EmptyNDL)
      (bigraph_id m X)
      (PeanoNat.Nat.add_0_r m) (*s*)
      (fun (name : Name) => right_empty X name) (*i*)
      (PeanoNat.Nat.add_0_r m) (*r*)
      (fun (name : Name) => right_empty X name) (*o*)
      bij_id (*n*)
      bij_id (*e*)
      (fun n => bij_rew (P := fin) (@arity_symmetry_eq m X n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + simpl. apply functional_extensionality.
    destruct x as [v | s1]; simpl.
    - destruct v.
    - unfold funcomp, parallel. f_equal.
      unfold bij_rew_forward.
      destruct s1; simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) m (m + 0) _ x _).
      simpl. destruct (Compare_dec.lt_dec x m). 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (m+0) m _ (x+0) _).
      apply subset_eq_compat. apply PeanoNat.Nat.add_0_r.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (m+0) m _ (x-m) _).
      apply subset_eq_compat. lia.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - unfold funcomp.
      simpl.
      f_equal. apply subset_eq_compat. reflexivity. 
    - destruct v.
  Qed.


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
  PermutationNames (X ∪ Y) (Y ∪ X).
  intros. constructor.
  apply permutation_union_commute.
  Qed.

Definition commute_plus_MyEqNat : forall m n,
MyEqNat (m + n) (n + m).
intros. constructor. lia. Qed.

Theorem symmetry_eq_tp_id : forall m n:nat, forall X Y:NoDupList, 
  bigraph_equality 
    (bigraph_composition (p:=permutation_union_commutePN Y X) (eqsr := commute_plus_MyEqNat m n)
      (symmetry_big m X n Y) 
      (symmetry_big n Y m X))
    (bigraph_id (m + n) (X ∪ Y)). 
Proof.
intros m n X Y.
  refine (
    BigEq (n + m) (m + n) (m + n) (m + n) (Y ∪ X) (X ∪ Y) (X ∪ Y) (X ∪ Y)  
      (bigraph_composition (p:=permutation_union_commutePN Y X) (eqsr := commute_plus_MyEqNat m n)
        (symmetry_big m X n Y) 
        (symmetry_big n Y m X))
      (bigraph_id (m + n) (X ∪ Y))
      (PeanoNat.Nat.add_comm n m) (*s*)
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
      unfold bij_rew_forward,id.
      destruct s1; simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (m+n) (n + m) _ x _).
      simpl. destruct (Compare_dec.lt_dec x n).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (n+m) (m+n) _ (x+m) _).
      destruct (Compare_dec.lt_dec (x + m) m).
      apply subset_eq_compat. exfalso. lia.
      apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (n+m) (m+n) _ (x-n) _).
      destruct (Compare_dec.lt_dec (x-n) m).
      apply subset_eq_compat. lia.
      apply subset_eq_compat. lia. 
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - unfold funcomp.
      simpl.
      f_equal. apply subset_eq_compat. reflexivity. 
    - destruct v.
  Unshelve.
  exact nat.
  exact nat.
  intros [v|v]; destruct v.
  Qed.

Theorem symmetry_distributive_arity {si0 ri1 sj0 rj1:nat} {ii0 oi1 ij0 oj1:NoDupList}
  {disi: ii0#ij0} {diso: oi1#oj1}: 
  forall f:bigraph si0 ii0 ri1 oi1, 
  forall g:bigraph sj0 ij0 rj1 oj1,
  forall n,
  Arity (get_control
    (bigraph_composition 
      (symmetry_big ri1 oi1 rj1 oj1) 
      (f ⊗ g)) n) =
  Arity (get_control
    (bigraph_composition (p:=permutation_union_commutePN ii0 ij0) (eqsr := commute_plus_MyEqNat sj0 si0)
      (bigraph_tensor_product 
        (dis_i := D_ND (rev_disjoint (DN_D disi)))
        (dis_o := D_ND (rev_disjoint (DN_D diso))) 
        g f)
      (symmetry_big si0 ii0 sj0 ij0)) (bij_void_A_B n)).
  Proof. 
  intros.
  destruct n. elim t.
  destruct t.
  reflexivity.
  reflexivity.
  Qed.


Theorem symmetry_distributive {si0 ri1 sj0 rj1:nat} {ii0 oi1 ij0 oj1:NoDupList}
  {disi: ii0#ij0} {diso: oi1#oj1}: 
  forall f:bigraph si0 ii0 ri1 oi1, 
  forall g:bigraph sj0 ij0 rj1 oj1,
  bigraph_equality 
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
    BigEq _ _ _ _ _ _ _ _
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
      (PeanoNat.Nat.add_comm ri1 rj1) (*r*)
      (permutation_union_commute oi1 oj1) (*o*)
      bij_void_A_B (*n*)
      bij_void_A_B (*e*)
      (fun n => bij_rew (P := fin) (symmetry_distributive_arity f g n)) (*p*)
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
      unfold rearrange, id, sum_shuffle, extract1.
      destruct get_parent; try reflexivity.
      f_equal. unfold bij_rew_forward,surj_fin_add.
      destruct f0.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (ri1 + rj1) _ (ri1 + x) _).
      destruct (Compare_dec.lt_dec (ri1 + x) ri1).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (ri1 + x + rj1) _).
      apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (ri1 + x - ri1) _).
      apply subset_eq_compat. lia.
    - unfold funcomp, parallel.
      simpl. 
      unfold rearrange, id, sum_shuffle, extract1.
      destruct get_parent; try reflexivity.
      f_equal. unfold bij_rew_forward,surj_fin_add.
      destruct f0.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (ri1 + rj1) _ x _).
      destruct (Compare_dec.lt_dec x ri1).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (x + rj1) _).
      apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (x - ri1) _).
      apply subset_eq_compat. lia.
    - elim v.
    - unfold funcomp, parallel. simpl. f_equal.
      unfold bij_rew_forward,id, rearrange, sum_shuffle, inj_fin_add, extract1.
      destruct s1; simpl.
      destruct (PeanoNat.Nat.ltb_spec0 x si0).
      destruct (Compare_dec.lt_dec x si0).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (si0 + sj0) (sj0 + si0) _ (x + sj0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (x + sj0) sj0).
      lia.
      symmetry.
      rewrite <- (parent_proof_irrelevant' f x (x + sj0 - sj0) l0). 
      destruct get_parent; try reflexivity.
      f_equal. unfold surj_fin_add.
      destruct f0.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (ri1 + rj1) _ x0 _).
      destruct (Compare_dec.lt_dec x0 ri1).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (x0 + rj1) _).
      apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (x0 - ri1) _).
      apply subset_eq_compat. lia.
      lia.
      lia.
      destruct (Compare_dec.lt_dec x si0).
      lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (si0 + sj0) (sj0 + si0) _ (x - si0) _). 
      destruct (PeanoNat.Nat.ltb_spec0 (x - si0) sj0).
      rewrite <- (parent_proof_irrelevant g (x - si0) (x - si0) l0). (*so weird, i can also write rewrite <- (parent_proof_irrelevant g (x - si0) x l0)*)
      destruct get_parent; try reflexivity.
      f_equal.
      unfold surj_fin_add. destruct f0. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (ri1 + rj1) _ (ri1 + x0) _).
      destruct (Compare_dec.lt_dec (ri1 + x0) ri1).
      lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (ri1 + rj1) (rj1 + ri1) _ (ri1 + x0 - ri1) _).
      apply subset_eq_compat. lia.
      lia.
      exfalso. apply n1.
      lia.
  + apply functional_extensionality.
    destruct x as [[name] | (v, tmp)]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold rearrange, switch_link, id, extract1.
      destruct (in_dec EqDecN name ii0); destruct (in_dec EqDecN name ij0).
      * exfalso. destruct disi as [disi]. apply (disi name i1 i2).
      * unfold in_app_or_m_nod_dup. 
      destruct (in_dec EqDecN name ii0).
      rewrite <- (innername_proof_irrelevant f name i2). 
      destruct get_link; try reflexivity. f_equal. unfold permut_list_forward. destruct s0. apply subset_eq_compat. reflexivity.
      contradiction.
      * unfold in_app_or_m_nod_dup. 
      destruct (in_dec EqDecN name ij0).
      rewrite <- (innername_proof_irrelevant g name i1). 
      destruct get_link; try reflexivity. f_equal. unfold permut_list_forward. destruct s0. apply subset_eq_compat. reflexivity.
      contradiction.
      * simpl in i0. exfalso. rewrite in_app_iff in i0. destruct i0; contradiction.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
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

Search (permutation (app_merge' _ _)).

Lemma MyPN {mI mJ mK:nat} {XI XJ XK:NoDupList}
  {disIJ : XI # XJ} {disKJ : XK # XJ} {disIK : XI # XK}:
  permutation 
    (XI ∪ XK ∪ XJ)
    (ndlist (i ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK)))).
    simpl.
    intros; split; intros; apply in_app_iff in H; destruct H.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    right.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    right.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
  Qed.

Definition myEqNatproof {mI mJ mK:nat} : MyEqNat (mI + mK + mJ) (mI + (mJ + mK)).
constructor.
auto.
lia.
Qed.

Theorem easynat : forall mI mJ mK, mI + mJ + mK = mI + mK + mJ.
lia. Qed.

Theorem easyperm : forall XI XJ XK, 
permutation (XI ∪ XJ ∪ XK) (XI ∪ XK ∪ XJ).
intros; split; intros; apply in_app_iff in H; destruct H.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    - apply in_app_iff in H; destruct H.
    apply in_app_iff; auto.
    left.
    apply in_app_iff; auto.
    apply in_app_iff; auto.
    apply in_app_iff; auto. 
    left.
    apply in_app_iff; auto.
  Qed.


Theorem symmetry_distributive_s4 {mI mJ mK:nat} {XI XJ XK:NoDupList}
  {disIJ : XI # XJ} {disKJ : XK # XJ} {disIK : XI # XK}:
  bigraph_equality
    (symmetry_big (mI+mJ) (XI ∪ XJ) mK XK)
    (bigraph_composition (p := P_NP (permutation_commute (MyPN (mI:=mI) (mJ:=mJ) (mK:=mK)))) (eqsr:= myEqNatproof)
      ((symmetry_big mI XI mK XK) ⊗ (bigraph_id mJ XJ))
      ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK))).
  Proof.
  refine (
    BigEq _ _ _ _ _ _ _ _
      (symmetry_big (mI+mJ) (XI ∪ XJ) mK XK)
      (bigraph_composition (p := P_NP (permutation_commute (MyPN (mI:=mI) (mJ:=mJ) (mK:=mK)))) (eqsr:= myEqNatproof)
        ((symmetry_big mI XI mK XK) ⊗ (bigraph_id mJ XJ))
        ((bigraph_id mI XI) ⊗ (symmetry_big mJ XJ mK XK)))
      (Arith_base.plus_assoc_reverse_stt mI mJ mK) (*s*)
      (@tr_permutation XI XJ XK) (*i*)
      (easynat mI mJ mK) (*r*)
      (easyperm XI XJ XK) (*o*)
      bij_void4 (*n*)
      bij_void4 (*e*)
      (fun n => bij_rew (P := fin) (void_univ_embedding n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intros [[v|v]|[v|v]]; destruct v.
  + simpl. apply functional_extensionality.
    destruct x as [[[v|v]|[v|v]] | s1]; try destruct v; simpl.
    unfold funcomp, parallel. simpl. f_equal.
    unfold bij_rew_forward,id,rearrange,sum_shuffle,extract1,inj_fin_add,surj_fin_add.
    destruct s1; simpl.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mJ + mK) _ x _).
    simpl. destruct (Compare_dec.lt_dec x (mI + mJ)); destruct (PeanoNat.Nat.ltb_spec0 x mI).
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ x _).
    destruct (PeanoNat.Nat.ltb_spec0 x (mI + mK)).
    destruct (Compare_dec.lt_dec x mI).
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    reflexivity.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    lia.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    lia.
    destruct (Compare_dec.lt_dec (x - mI) mJ).
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ (mI + (x - mI + mK)) _).
    destruct (PeanoNat.Nat.ltb_spec0 (mI + (x - mI + mK)) (mI + mK)); destruct (Compare_dec.lt_dec (mI + (x - mI + mK)) mI).
    lia.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    lia.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    lia.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    apply subset_eq_compat.
    lia.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x+mK) _).
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ (mI + (x - mI - mJ)) _).
    destruct (PeanoNat.Nat.ltb_spec0 (mI + (x - mI - mJ)) (mI + mK)); destruct (Compare_dec.lt_dec (mI + (x - mI - mJ)) mI); try lia.
    f_equal. 
    apply subset_eq_compat.
    lia.
    f_equal.
    apply subset_eq_compat.
    lia.
    f_equal.
    apply subset_eq_compat.
    lia.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ x _).
    destruct (PeanoNat.Nat.ltb_spec0 x (mI + mK)); destruct (Compare_dec.lt_dec x mI); try lia.
    f_equal.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x - (mI + mJ)) _).
    apply subset_eq_compat.
    lia.
    f_equal.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x - (mI + mJ)) _).
    apply subset_eq_compat.
    lia.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x - (mI + mJ)) _).
    f_equal. apply subset_eq_compat.
    lia.
    f_equal. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x - (mI + mJ)) _).
    apply subset_eq_compat.
    lia.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + mJ + mK) (mI + mK + mJ) _ (x - (mI + mJ)) _).
    f_equal. 
    destruct (Compare_dec.lt_dec (x - mI) mJ).
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ (mI + (x - mI + mK)) _).
    destruct (PeanoNat.Nat.ltb_spec0 (mI + (x - mI + mK)) (mI + mK)).
    destruct (Compare_dec.lt_dec (mI + (x - mI + mK)) mI).
    f_equal. 
    apply subset_eq_compat.
    lia.
    f_equal. 
    apply subset_eq_compat.
    lia.
    f_equal. 
    apply subset_eq_compat.
    lia.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (mI + (mJ + mK)) (mI + mK + mJ) _ (mI + (x - mI - mJ)) _).
    destruct (PeanoNat.Nat.ltb_spec0 (mI + (x - mI - mJ)) (mI + mK)).
    destruct (Compare_dec.lt_dec (mI + (x - mI - mJ)) mI).
    f_equal. 
    apply subset_eq_compat.    
    lia.
    f_equal. 
    apply subset_eq_compat.
    lia.
    f_equal. 
    apply subset_eq_compat.
    lia.
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
    - destruct v; simpl in t; destruct t. destruct v. destruct v. destruct v. destruct v.
  Qed.

End Symmetries.