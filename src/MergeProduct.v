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
Module MergeBig (s : Signature) (n : Names) (b: Bigraphs s n).
Module pp := ParallelProduct s n b.
Include pp.

Example zero : fin 1. exists 0. lia. Defined.

Definition merge {n:nat} : bigraph n EmptyNDL 1 EmptyNDL. (* merge n+1 = join <<o>> (id 1 [] ⊗ merge n ) with merge 0 = 1 (1 root that's all)*)
  Proof. 
  apply (Big n EmptyNDL 1 EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (fun s => inr zero) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition rm_useless_root {s r : nat} {i o : NoDupList} (b : bigraph s i (r + 0) o) : bigraph s i r o.
destruct b as [n e c p l ap].
assert (fin (r+0)=fin r).
- unfold fin. f_equal. apply functional_extensionality. intros. 
f_equal. auto.
- refine (Big s i r o n e c _ l _).
Unshelve. 2:{ clear ap. rewrite H in p. exact p. }
unfold eq_rect. destruct H. apply ap.
Defined.

Definition rm_useless_site {s r : nat} {i o : NoDupList} (b : bigraph (s+0) i r o) : bigraph s i r o.
destruct b as [n e c p l ap].
assert (fin (s+0)=fin s).
- unfold fin. f_equal. apply functional_extensionality. intros. f_equal. auto.
- refine (Big s i r o n e c _ l _).
Unshelve. 2:{ clear ap. rewrite H in p. exact p. }
unfold eq_rect. destruct H. apply ap.
Defined.

Definition rm_useless_outer {s r : nat} {i o : NoDupList} (b : bigraph s i r (app_merge_NoDupList EmptyNDL o)) : bigraph s i r o.
destruct b as [n e c p l ap].
exact (Big s i r o n e c p l ap).
Defined. 

Definition bigraph_merge_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : union_possible b1 b2}
    : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) 1 (app_merge_NoDupList o1 o2). 
  set (pp := (@merge (r1 + r2) ⊗ (@bigraph_id 0 (app_merge_NoDupList i1 i2)))).
  set (pprm := rm_useless_site pp).
  refine 
    (rm_useless_outer (bigraph_composition
      (p := _)
      (rm_useless_root (rm_useless_site (@merge (r1 + r2) ⊗ (@bigraph_id 0 (app_merge_NoDupList o1 o2))))) 
      (bigraph_parallel_product (up := up) b1 b2))).
  rewrite merge_left_neutral.
  exact (P_NP (permutation_id (app_merge_NoDupList o1 o2))).
  Defined.


Global Notation "b1 | b2" := (bigraph_merge_product b1 b2) (at level 50, left associativity).

Definition big_1 := @merge 0.

Lemma arity_mp_right_neutral {s i o} (b : bigraph s i 1 o): forall n, 
  Arity (get_control 
    (bigraph_merge_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right i))) b big_1)
    n) = Arity (get_control b (bij_void_void n)).
  Proof.
    intros n.
    destruct n as [[v | v ] | [n | v]].
    + destruct v.
    + destruct v.
    + reflexivity.
    + destruct v.
    Qed.

Theorem mp_right_neutral {s i o} (b : bigraph s i 1 o): 
  bigraph_equality
    (bigraph_merge_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right i))) b big_1) 
    b.
  Proof.
  apply (BigEq _ _ _ _ _ _ _ _ (b | big_1) b
    (PeanoNat.Nat.add_0_r s)
    (right_empty i)
    (PeanoNat.Nat.add_0_r 1)
    (right_empty o)
    bij_void_void (* nodes findec_sum (findec_sum voidfd voidfd) (findec_sum (get_node b) voidfd) <-> get_node b*)
    bij_void_void
    (fun n => bij_rew (P := fin) (arity_mp_right_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      unfold bij_rew_forward, sum_shuffle, rearrange, extract1. 
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 x 2).
      * f_equal.
      destruct zero.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) 1 1 _ x0 _).
      apply subset_eq_compat.
      assert (x = 0).
      ** apply PeanoNat.Nat.lt_1_r. apply l.
      ** assert (x0 = 0). apply PeanoNat.Nat.lt_1_r. apply l1.
      lia.
      * exfalso. apply n. lia. 
    - unfold funcomp, parallel, sum_shuffle.
      unfold bij_rew_forward.
      unfold inj_fin_add, sequence. unfold rearrange.
      simpl.
      unfold extract1.
      destruct s1. unfold eq_sym.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) s (s + O) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x s).      
      * symmetry. 
      rewrite (proof_irrelevance _ _ l0).
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 x0 2).
      ** f_equal.
      destruct zero.
      symmetry. rewrite (@eq_rect_exist nat nat (fun n x => x < n) 1 1 _ x1 _).
      apply subset_eq_compat.
      assert (x0 = 0).
      *** apply PeanoNat.Nat.lt_1_r. apply l1.
      *** assert (x1 = 0). apply PeanoNat.Nat.lt_1_r. apply l3.
      lia.
      ** exfalso. apply n. lia.
      * exfalso. apply n. apply l. 
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward, id.
      destruct i1.
      simpl.
      unfold id, rearrange, switch_link. 
      rewrite <- (innername_proof_irrelevant b x i0).
      destruct get_link; try reflexivity.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward. simpl.
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id, link_juxt.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward, bij_subset_backward, bij_subset_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward.
      unfold id, rearrange, switch_link.  simpl.
      destruct get_link; try reflexivity.
      unfold extract1.
      destruct s0.
      f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Lemma arity_mp_left_neutral {s i o} (b : bigraph s i 1 o): forall n, 
  Arity (get_control 
    (bigraph_merge_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_left i))) big_1 b)
    n) = Arity (get_control b (bij_void_void_r n)).
  Proof.
    intros n.
    destruct n as [[v | v ] | [v | n]].
    + destruct v.
    + destruct v.
    + destruct v.
    + reflexivity.
    Qed.

Theorem mp_left_neutral {s i o} (b : bigraph s i 1 o): 
  bigraph_equality
    (bigraph_merge_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_left i))) big_1 b) 
    b.
  Proof.
  apply (BigEq _ _ _ _ _ _ _ _ (big_1 | b) b
    eq_refl
    (left_empty i)
    eq_refl
    (left_empty o)
    bij_void_void_r (* nodes findec_sum (findec_sum voidfd voidfd) (findec_sum (get_node b) voidfd) <-> get_node b*)
    bij_void_void_r
    (fun n => bij_rew (P := fin) (arity_mp_left_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      unfold bij_rew_forward, sum_shuffle, rearrange, extract1. 
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 (S x) 2).
      * f_equal.
      destruct zero.
      apply subset_eq_compat.
      assert (x = 0).
      ** apply PeanoNat.Nat.lt_1_r. apply l.
      ** assert (x0 = 0). apply PeanoNat.Nat.lt_1_r. apply l1.
      lia.
      * exfalso. apply n. lia. 
    - unfold funcomp, parallel, sum_shuffle.
      unfold bij_rew_forward.
      unfold inj_fin_add, sequence. unfold rearrange.
      simpl.
      unfold extract1.
      destruct s1. unfold eq_sym.
      destruct (PeanoNat.Nat.ltb_spec0 x 0).      
      * 
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct (PeanoNat.Nat.ltb_spec0 0 2).
      ** exfalso. Search (_ < 0). apply PeanoNat.Nat.nlt_0_r in l0. apply l0.
      ** exfalso. apply n. lia.
      * erewrite <- (parent_proof_irrelevant b (x-0) x). 
      assert (forall Hn, exist (fun p0 : nat => p0 < s) (x - 0) Hn = exist (fun p0 : nat => p0 < s) x l).
      { intros. apply subset_eq_compat. lia. }
      rewrite H.
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 (S x0) 2).
      destruct zero.
      ** f_equal. apply subset_eq_compat. lia.
      ** f_equal. apply subset_eq_compat. lia.
      ** lia.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward, id.
      destruct i1.
      simpl.
      unfold id, rearrange, switch_link, in_app_or_m_nod_dup. 
      destruct (in_dec EqDecN x i).
      * rewrite <- (innername_proof_irrelevant b x i0).
      destruct get_link; try reflexivity.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward. simpl.
      destruct s0. f_equal. unfold bij_list_forward. apply subset_eq_compat. reflexivity.
      * exfalso. apply n. apply i0.
    - unfold parallel, sum_shuffle, choice, funcomp, id, link_juxt.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward, bij_subset_backward, bij_subset_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward.
      unfold id, rearrange, switch_link.  simpl.
      destruct get_link; try reflexivity.
      unfold extract1.
      destruct s0.
      f_equal.
      unfold bij_list_forward. apply subset_eq_compat. reflexivity.
    Unshelve. simpl. lia.
  Qed.


End MergeBig.
