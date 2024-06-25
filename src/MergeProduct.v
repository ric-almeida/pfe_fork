Set Warnings "-notation-overridden, -parsing, -masking-absolute-name".

Require Import AbstractBigraphs.
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

(** Merge operator *)
Module MergeBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

#[export] Instance MyEqNat_r_neutral {a} : 
  MyEqNat (a+0) a.
  Proof. 
  constructor. 
  lia.
  Qed.

Definition bigraph_merge_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : UnionPossible b1 b2}
    (* : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) 1 (app_merge_NoDupList o1 o2)  *)
    := 
  ((@merge (r1 + r2) ⊗ (@bigraph_id 0 (app_merge_NoDupList o1 o2)))) <<o>> (b1 || b2).

Global Notation "b1 <|> b2" := (bigraph_merge_product b1 b2) (at level 50, left associativity).

Lemma arity_mp_right_neutral {s i o} (b : bigraph s i 1 o): forall n, 
  Arity (get_control (b <|> big_1) n) = Arity (get_control b (bij_void_void n)).
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
    (b <|> big_1) 
    b.
  Proof.
  apply (BigEq _ _ _ _ _ _ _ _ (b <|> big_1) b
    (PeanoNat.Nat.add_0_r s)
    (right_empty i)
    (PeanoNat.Nat.add_0_r 1)
    (right_empty o)
    bij_void_void
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
      destruct f as (s1', Hs1').
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct (PeanoNat.Nat.ltb_spec0 s1' 2).
      * f_equal. rewrite <- eq_rect_eq. 
      destruct zero1.
      apply subset_eq_compat. lia. 
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
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 x0 2).
      ** f_equal. rewrite <- eq_rect_eq. 
      destruct zero1.
      apply subset_eq_compat. lia. 
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
  Arity (get_control (big_1 <|> b) n) = Arity (get_control b (bij_void_void_r n)).
  Proof.
    intros n.
    destruct n as [[v | v ] | [v | n]].
    + destruct v.
    + destruct v.
    + destruct v.
    + reflexivity.
    Qed.

Theorem mp_left_neutral {s i o} (b : bigraph s i 1 o): 
  bigraph_equality (big_1 <|> b) b.
  Proof.
  apply (BigEq _ _ _ _ _ _ _ _ (big_1 <|> b) b
    eq_refl
    (left_empty i)
    eq_refl
    (left_empty o)
    bij_void_void_r 
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
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 (S x) 2).
      * f_equal. 
      destruct zero1.
      apply subset_eq_compat. lia. 
      * exfalso. apply n. lia. 
    - unfold funcomp, parallel, sum_shuffle.
      unfold bij_rew_forward.
      unfold inj_fin_add, sequence. unfold rearrange.
      simpl.
      unfold extract1.
      destruct s1. unfold eq_sym.
      destruct (PeanoNat.Nat.ltb_spec0 x 0).      
      * 
      rewrite <- eq_rect_eq. destruct zero1. 
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct (PeanoNat.Nat.ltb_spec0 x0 2).
      ** exfalso. apply PeanoNat.Nat.nlt_0_r in l0. apply l0.
      ** exfalso. apply n. lia.
      * erewrite <- (parent_proof_irrelevant b (x-0) x). 
      assert (forall Hn, exist (fun p0 : nat => p0 < s) (x - 0) Hn = exist (fun p0 : nat => p0 < s) x l).
      { intros. apply subset_eq_compat. lia. }
      rewrite H.
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      unfold inj_fin_add, surj_fin_add, id.
      simpl.
      destruct f.
      destruct (PeanoNat.Nat.ltb_spec0 (S x0) 2).
      destruct zero1.
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

#[export] Instance union_possible_assoc_mp {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  {b3 : bigraph s3 i3 r3 o3}
  (up12 : UnionPossible b1 b2) 
  (up23 : UnionPossible b2 b3) 
  (up13 : UnionPossible b1 b3) :
  UnionPossible 
    (b1 <|> b2)
    b3.
  Proof.
  constructor.
  destruct up12 as [up12].
  destruct up23 as [up23].
  destruct up13 as [up13].
   unfold union_possible in *.
   intros [inter12_3 Hinter12_3].
   unfold intersectionNDL in *.
   simpl in *.
   pose Hinter12_3 as Htmp.
   rewrite intersection_eq in Htmp.
   destruct Htmp.
   unfold switch_link, parallel, id, permut_list_forward. 
   unfold sum_shuffle, sum_shuffle, funcomp.
   unfold bij_list_forward, bij_list_backward', sequence, rearrange, link_juxt, in_app_or_m_nod_dup.
   apply in_app_or_m in H.
   destruct H.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right,extract1 in up23.
   rewrite <- (innername_proof_irrelevant b2 inter12_3 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i5. apply up23.
   * apply up23.
   + specialize (up13 (to_intersection inter12_3 H H0)).
   unfold to_intersection,to_left,to_right in up13.
   rewrite <- (innername_proof_irrelevant b1 inter12_3 (not_in_left (from_intersection_left Hinter12_3) n)) in up13.
   destruct get_link. 
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up13.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up13. apply up13.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i4. apply up13. 
   * apply up13.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right in up23.
   rewrite <- (innername_proof_irrelevant b2 inter12_3 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i5. apply up23. 
   * apply up23.
   + exfalso. apply n. apply H.
  Qed.

Lemma arity_mp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : UnionPossible b1 b2} {up23 : UnionPossible b2 b3} {up13 : UnionPossible b1 b3} n12_3,
  Arity (get_control ((b1 <|> b2) <|> b3) n12_3) 
  = 
  Arity (get_control (bigraph_merge_product 
    (up := union_possible_commutes (union_possible_assoc_mp up23 (union_possible_commutes up13) (union_possible_commutes up12))) 
    b1
    (b2 <|> b3)) (bij_sum_assoc_mp n12_3)). 
  Proof.
  intros until n12_3.
  destruct n12_3 as [[v | v] | [[[v|v] |[n1|n2]]|n3]]; try destruct v; try reflexivity.
  Qed. 




Theorem bigraph_mp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : UnionPossible b1 b2} {up23 : UnionPossible b2 b3} {up13 : UnionPossible b1 b3},
  bigraph_equality 
    ((b1 <|> b2) <|>  b3)
    (bigraph_merge_product 
      (up := union_possible_commutes (union_possible_assoc_mp up23 (union_possible_commutes up13) (union_possible_commutes up12))) 
      b1 
      (b2 <|> b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 <|> b2) <|> b3) (b1 <|> (b2 <|> b3))
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    tr_permutation
    (eq_refl)
    permutationtr
    bij_sum_assoc_mp
    bij_sum_assoc_mp
    (fun n12_3 => bij_rew (P := fin) (arity_mp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [[v | v] | [a | [[v|v]|[b|c]]]]; try reflexivity; try (elim v).
  + apply functional_extensionality. rewrite bij_rew_id. 
    intros [[[v | v] | [a | [[v|v]|[b|c]]]] | s1_23']; simpl; unfold funcomp; simpl; try (elim v).
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      unfold inj_fin_add, bij_rew_forward, surj_fin_add.
      destruct f.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (r1 + r2)).
      destruct zero1. unfold id.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) (S (r3 + 0)) _ x0 _).
      destruct (PeanoNat.Nat.ltb_spec0 x0 (S r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      lia.
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      unfold inj_fin_add, bij_rew_forward, surj_fin_add.
      destruct f.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ (r1 + x) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x) (r1 + r2)).
      destruct zero1. unfold id.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) (S (r3 + 0)) _ x0 _).
      destruct (PeanoNat.Nat.ltb_spec0 x0 (S r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2 + r3) (r2 + r3 + 0) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (r2 + r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + (1 + (x - (r2 + r3)))) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + (1 + (x - (r2 + r3)))) (r1 + 1)).
      lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r3) (r2 + r3 + 0) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (r2 + r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + (1 + (x - (r2 + r3)))) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + (1 + (x - (r2 + r3)))) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      lia.
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      unfold inj_fin_add, bij_rew_forward, surj_fin_add.
      destruct f.
      unfold id. destruct zero1.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) (S (r3 + 0)) _ (1+x) _).
      destruct (PeanoNat.Nat.ltb_spec0 (1+x) (S r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2 + r3) (r2 + r3 + 0) _ (r2 + x) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r2 + x) (r2 + r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + (1 + (r2 + x - (r2 + r3)))) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + (1 + (r2 + x - (r2 + r3)))) (r1 + 1)).
      lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r3) (r2 + r3 + 0) _ (r2 + x) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r2 + x) (r2 + r3)).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ (r1 + (1 + (r2 + x - (r2 + r3)))) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + (1 + (r2 + x - (r2 + r3)))) (r1 + 1)).
      f_equal. f_equal. apply subset_eq_compat. lia.
      f_equal. f_equal. apply subset_eq_compat. lia.
    - f_equal. 
      destruct s1_23'; simpl.
      unfold parallel, id, sum_shuffle, inj_fin_add.
      unfold rearrange.
      unfold bij_rew_forward.
      unfold sequence, extract1, rearrange.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s1 + (s2 + s3)) (s1 + s2 + s3) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (s1 + s2)); simpl.
      destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
      destruct get_parent; try reflexivity. unfold surj_fin_add. 
      destruct f.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ x0 _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ x0 _).
      unfold extract1. 
      destruct (PeanoNat.Nat.ltb_spec0 x0 (r1 + r2)). 
      destruct (PeanoNat.Nat.ltb_spec0 x0 (r1 + 1)). 
      destruct zero1. simpl. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      f_equal.
      f_equal. apply subset_eq_compat. lia. 
      destruct zero1. simpl. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      f_equal. apply subset_eq_compat. lia. 
      f_equal. apply subset_eq_compat. lia. 
      exfalso.  apply n. lia. 
      destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2). 
      erewrite <- (parent_proof_irrelevant b2 (x-s1) (x-s1) l1).   
      destruct (get_parent b2); try reflexivity;
      unfold extract1, surj_fin_add. 
      destruct f. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r3) _ _ x0 _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) _ _ (r1+x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + r2)).
      destruct (PeanoNat.Nat.ltb_spec0 x0 (r2 + r3)). 
      destruct zero1. rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) _ _ (r1+x1) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x1) (r1 + 1)).
      destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      reflexivity. 
      f_equal. apply subset_eq_compat. lia. 
      exfalso. lia. 
      exfalso. lia. 
      exfalso. lia.  
      reflexivity. 
      exfalso. lia.
      destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
      exfalso. lia. 
      destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2). 
      exfalso. lia. 
      erewrite <- (parent_proof_irrelevant' b3 (x - (s1 + s2)) (x - s1 - s2) ((ZifyClasses.rew_iff_rev (x - (s1 + s2) < s3) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2)))) (BinInt.Z.of_nat s3)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (x - (s1 + s2)) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2)))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n2 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n2 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) eq_refl (s1 + s2) (BinInt.Z.of_nat (s1 + s2)) eq_refl) s3 (BinInt.Z.of_nat s3) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2))))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2))) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (fun p : BinNums.positive => match p with
        | BinNums.xI _ => BinInt.Z.of_nat x
        | BinNums.xO (BinNums.xI _) => BinNums.Z0
        | BinNums.xO (BinNums.xO _) => BinInt.Z.of_nat (s1 + s2)
        | BinNums.xO BinNums.xH => BinInt.Z.of_nat s3
        | BinNums.xH => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2)))
        end) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2)))) (ZifyClasses.rew_iff (x < s1 + s2 + s3) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.add (BinInt.Z.of_nat (s1 + s2)) (BinInt.Z.of_nat s3))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl (s1 + s2 + s3) (BinInt.Z.add (BinInt.Z.of_nat (s1 + s2)) (BinInt.Z.of_nat s3)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add (s1 + s2) (BinInt.Z.of_nat (s1 + s2)) eq_refl s3 (BinInt.Z.of_nat s3) eq_refl)) (eq_rect (s1 + (s2 + s3)) (fun a : nat => x < a) l (s1 + s2 + s3) (eq_sym (eq_sym (PeanoNat.Nat.add_assoc s1 s2 s3))))) (ZifyClasses.rew_iff (~ x < s1 + s2) (~ BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2))) (ZifyClasses.not_morph (x < s1 + s2) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat (s1 + s2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl (s1 + s2) (BinInt.Z.of_nat (s1 + s2)) eq_refl)) n))))).
      unfold extract1.
      destruct get_parent; try reflexivity.
      unfold surj_fin_add. 
      destruct f. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ (1+x0) _). 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2 + r3) _ _ (r2+x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (1 + x0) (S r3)).
      destruct zero1. destruct (PeanoNat.Nat.ltb_spec0 (r2 + x0) (r2 + r3)). 
      unfold id. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + 1) (r1 + 1 + 0) _ (r1+x1) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x1) (r1 + 1)).
      reflexivity.
      f_equal. apply subset_eq_compat. lia.
      lia.
      destruct (PeanoNat.Nat.ltb_spec0 (r2 + x0) (r2 + r3)).
      destruct zero1.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + 1) (r1 + 1 + 0) _ (r1+x1) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x1) (r1 + 1)).
      f_equal. apply subset_eq_compat. lia.
      f_equal. apply subset_eq_compat. lia.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + 1) (r1 + 1 + 0) _ (r1 + (1 + (r2 + x0 - (r2 + r3)))) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + (1 + (r2 + x0 - (r2 + r3)))) (r1 + 1)).
      f_equal. apply subset_eq_compat. lia.
      f_equal. apply subset_eq_compat. lia.
      lia.
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id, rearrange, switch_link. simpl. 
      unfold in_app_or_m_nod_dup, extract1.
      destruct (in_dec EqDecN i123 (app_merge' i2 i3)).
      * destruct (in_dec EqDecN i123 i3).
      ** destruct get_link; try reflexivity.
      *** unfold permut_list_forward. 
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).      
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i123 i5). 
      destruct get_link; try reflexivity.
      **** unfold permut_list_forward. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_or_m in i4. destruct i4.
      -- apply n0. apply H.
      -- apply n. apply H.
      * destruct (in_dec EqDecN i123 i3).
      ** exfalso. apply n. apply in_right_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_left_list. apply i4.
      *** rewrite <- (innername_proof_irrelevant b1 i123 (not_in_left i0 n)). 
      destruct get_link; try reflexivity.
      **** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
    - destruct p123 as ([[v | v] | [a | [[v|v]|[b|c]]]], (i123, Hvi123)); simpl.
      * simpl in v. destruct v.
      * simpl in v. destruct v.
      * unfold bij_subset_forward, parallel, funcomp.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl. 
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold extract1, id. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
      * simpl in v. destruct v.
      * simpl in v. destruct v.
      * unfold bij_subset_forward, parallel, funcomp.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl. 
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold extract1, id. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, parallel, funcomp.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl. 
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold extract1, id. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed. 

End MergeBig.
