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

(** Nesting operator *)
Module MergeBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

(* Example zero : fin 1. exists 0. lia. Defined.

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
  Defined. *)

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

#[export] Instance MyEqNat_r_neutral {a} : 
  MyEqNat (a+0) a.
Proof. 
constructor. 
lia.
Qed.

(* MyEqNat (r1 + r2 + 0) (r1 + r2) *)


Definition bigraph_merge_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : UnionPossible b1 b2}
    (* : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) 1 (app_merge_NoDupList o1 o2)  *)
    := 
  ((@merge (r1 + r2) ⊗ (@bigraph_id 0 (app_merge_NoDupList o1 o2)))) <<o>> (b1 || b2).


Global Notation "b1 <|> b2" := (bigraph_merge_product b1 b2) (at level 50, left associativity).

(* Definition big_1 := @merge 0. *)

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
  destruct n12_3 as [[v | v] | [[[v|v] |[n1|n2]]|n3]].
  + simpl in v. elim v. 
  + simpl in v. elim v. 
  + simpl in v. elim v.
  + simpl in v. elim v.
  + reflexivity.
  + reflexivity.
  + reflexivity.
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
      destruct (@inj_fin_add (Nat.add r1 r2) O (@bij_rew_forward nat fin (Nat.add r1 r2) (Nat.add (Nat.add r1 r2) O) (@eq_sym nat (Nat.add (Nat.add r1 r2) O) (Nat.add r1 r2) (@eqxy (Nat.add (Nat.add r1 r2) O) (Nat.add r1 r2) (@MyEqNat_r_neutral (Nat.add r1 r2)))) (@surj_fin_add r1 r2 (@inl (fin r1) (fin r2) f)))).
      * destruct (@inj_fin_add (S r3) O (@bij_rew_forward nat fin (S r3) (S (Nat.add r3 O)) (@eq_sym nat (S (Nat.add r3 O)) (S r3) (@eqxy (S (Nat.add r3 O)) (S r3) (@MyEqNat_r_neutral (S r3)))) (@surj_fin_add (S O) r3 (@inl (fin (S O)) (fin r3) (@id (fin (S O)) (@surj_fin_add (S O) O (@inl (fin (S O)) (fin O) zero1))))))).
      destruct zero1. unfold id. 
      destruct (@inj_fin_add (Nat.add r1 (S O)) O (@bij_rew_forward nat fin (Nat.add r1 (S O)) (Nat.add (Nat.add r1 (S O)) O) (@eq_sym nat (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@eqxy (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@MyEqNat_r_neutral (Nat.add r1 (S O))))) (@surj_fin_add r1 (S O) (@inl (fin r1) (fin (S O)) f)))).
      ** reflexivity.
      ** destruct f2. exfalso. apply PeanoNat.Nat.nlt_0_r in l0. elim l0.
      ** unfold id. destruct (@inj_fin_add (Nat.add r1 (S O)) O (@bij_rew_forward nat fin (Nat.add r1 (S O)) (Nat.add (Nat.add r1 (S O)) O) (@eq_sym nat (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@eqxy (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@MyEqNat_r_neutral (Nat.add r1 (S O))))) (@surj_fin_add r1 (S O) (@inl (fin r1) (fin (S O)) f)))).
      *** destruct f1. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      *** destruct f1. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      * unfold id. destruct (@inj_fin_add (Nat.add r1 (S O)) O (@bij_rew_forward nat fin (Nat.add r1 (S O)) (Nat.add (Nat.add r1 (S O)) O) (@eq_sym nat (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@eqxy (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@MyEqNat_r_neutral (Nat.add r1 (S O))))) (@surj_fin_add r1 (S O) (@inl (fin r1) (fin (S O)) f)))).
      ** destruct f0. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      ** destruct f1. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity. 
      destruct (@inj_fin_add (Nat.add r1 r2) O (@bij_rew_forward nat fin (Nat.add r1 r2) (Nat.add (Nat.add r1 r2) O) (@eq_sym nat (Nat.add (Nat.add r1 r2) O) (Nat.add r1 r2) (@eqxy (Nat.add (Nat.add r1 r2) O) (Nat.add r1 r2) (@MyEqNat_r_neutral (Nat.add r1 r2)))) (@surj_fin_add r1 r2 (@inr (fin r1) (fin r2) f)))).
      * destruct (@inj_fin_add (S r3) O (@bij_rew_forward nat fin (S r3) (S (Nat.add r3 O)) (@eq_sym nat (S (Nat.add r3 O)) (S r3) (@eqxy (S (Nat.add r3 O)) (S r3) (@MyEqNat_r_neutral (S r3)))) (@surj_fin_add (S O) r3 (@inl (fin (S O)) (fin r3) (@id (fin (S O)) (@surj_fin_add (S O) O (@inl (fin (S O)) (fin O) zero1))))))).
      ** destruct (@inj_fin_add (Nat.add r2 r3) O (@bij_rew_forward nat fin (Nat.add r2 r3) (Nat.add (Nat.add r2 r3) O) (@eq_sym nat (Nat.add (Nat.add r2 r3) O) (Nat.add r2 r3) (@eqxy (Nat.add (Nat.add r2 r3) O) (Nat.add r2 r3) (@MyEqNat_r_neutral (Nat.add r2 r3)))) (@surj_fin_add r2 r3 (@inl (fin r2) (fin r3) f)))).
      *** destruct (@inj_fin_add (Nat.add r1 (S O)) O (@bij_rew_forward nat fin (Nat.add r1 (S O)) (Nat.add (Nat.add r1 (S O)) O) (@eq_sym nat (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@eqxy (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@MyEqNat_r_neutral (Nat.add r1 (S O))))) (@surj_fin_add r1 (S O) (@inr (fin r1) (fin (S O)) (@id (fin (S O)) (@surj_fin_add (S O) O (@inl (fin (S O)) (fin O) zero1))))))).
      **** unfold id. reflexivity. 
      **** destruct f3. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      *** destruct f2. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      ** destruct f1. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l. 
      * destruct f0. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l. 
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity. 
      destruct (@inj_fin_add (S r3) O (@bij_rew_forward nat fin (S r3) (S (Nat.add r3 O)) (@eq_sym nat (S (Nat.add r3 O)) (S r3) (@eqxy (S (Nat.add r3 O)) (S r3) (@MyEqNat_r_neutral (S r3)))) (@surj_fin_add (S O) r3 (@inr (fin (S O)) (fin r3) f)))).
      * destruct (@inj_fin_add (Nat.add r2 r3) O (@bij_rew_forward nat fin (Nat.add r2 r3) (Nat.add (Nat.add r2 r3) O) (@eq_sym nat (Nat.add (Nat.add r2 r3) O) (Nat.add r2 r3) (@eqxy (Nat.add (Nat.add r2 r3) O) (Nat.add r2 r3) (@MyEqNat_r_neutral (Nat.add r2 r3)))) (@surj_fin_add r2 r3 (@inr (fin r2) (fin r3) f)))).
      ** destruct (@inj_fin_add (Nat.add r1 (S O)) O (@bij_rew_forward nat fin (Nat.add r1 (S O)) (Nat.add (Nat.add r1 (S O)) O) (@eq_sym nat (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@eqxy (Nat.add (Nat.add r1 (S O)) O) (Nat.add r1 (S O)) (@MyEqNat_r_neutral (Nat.add r1 (S O))))) (@surj_fin_add r1 (S O) (@inr (fin r1) (fin (S O)) (@id (fin (S O)) (@surj_fin_add (S O) O (@inl (fin (S O)) (fin O) zero1))))))).
      *** reflexivity.
      *** destruct f2. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      ** destruct f1. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
      * destruct f0. exfalso. apply PeanoNat.Nat.nlt_0_r in l. elim l.
    - f_equal. 
      destruct s1_23'; simpl.
      unfold parallel, id, sum_shuffle, inj_fin_add.
      unfold rearrange.
      unfold bij_rew_forward.
      unfold sequence, extract1, rearrange.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s1 + (s2 + s3)) (s1 + s2 + s3) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (s1 + s2)); simpl.
      * destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
      ++ destruct get_parent; try reflexivity. unfold surj_fin_add. 
      destruct f.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ x0 _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) (r1 + 1 + 0) _ x0 _).
      unfold extract1. 
      destruct (PeanoNat.Nat.ltb_spec0 x0 (r1 + r2)). 
      +++ destruct (PeanoNat.Nat.ltb_spec0 x0 (r1 + 1)). 
      ** destruct zero1. simpl. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      *** f_equal.
      *** f_equal. apply subset_eq_compat. lia. 
      ** destruct zero1. simpl. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      *** f_equal. apply subset_eq_compat. lia. 
      *** f_equal. apply subset_eq_compat. lia. 
      +++ exfalso.  apply n. lia. 
      ++  destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2). 
      +++ erewrite <- (parent_proof_irrelevant b2 (x-s1) (x-s1) l1).   
      destruct (get_parent b2); try reflexivity;
      unfold extract1, surj_fin_add. 
      ** destruct f. 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r3) _ _ x0 _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) _ _ (r1+x0) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x0) (r1 + r2)).
      *** destruct (PeanoNat.Nat.ltb_spec0 x0 (r2 + r3)). 
      **** destruct zero1. rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ x1 _). 
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+1) _ _ (r1+x1) _).
      destruct (PeanoNat.Nat.ltb_spec0 (r1 + x1) (r1 + 1)).
      ++++ destruct (PeanoNat.Nat.ltb_spec0 x1 (S r3)). 
      +++++ reflexivity. 
      +++++ f_equal. apply subset_eq_compat. lia. 
      ++++ exfalso. lia. 
      **** exfalso. lia. 
      *** exfalso. lia.  
      ** reflexivity. 
      +++ exfalso. lia.
      * destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
      ++ exfalso. lia. 
      ++ destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2). 
      +++ exfalso. lia. 
      +++ 
      assert (@get_parent s3 r3 i3 o3 b3 (@inr (type (@get_node s3 r3 i3 o3 b3)) (fin s3) (@exist nat (fun p : nat => lt p s3) (Nat.sub x (Nat.add s1 s2)) (ZifyClasses.rew_iff_rev (lt (Nat.sub x (Nat.add s1 s2)) s3) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2)))) (BinInt.Z.of_nat s3)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (Nat.sub x (Nat.add s1 s2)) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2)))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n2 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n2 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) (Nat.add s1 s2) (BinInt.Z.of_nat (Nat.add s1 s2)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.add s1 s2)))) s3 (BinInt.Z.of_nat s3) (@eq_refl BinNums.Z (BinInt.Z.of_nat s3))) (ZMicromega.ZTautoChecker_sound (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.OR (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2))))) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEsub BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))))) tt)) (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2))) BinNums.Z0)) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEc BinNums.Z BinNums.Z0)) tt))) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEadd BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))) (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH)))) tt) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.NOT (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH)))) tt)) (@None unit) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH))) tt)))) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S O)) (RingMicromega.PsatzIn BinNums.Z O)))) ZMicromega.DoneProof) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (RingMicromega.PsatzIn BinNums.Z O))) ZMicromega.DoneProof) (@nil ZMicromega.ZArithProof))) (@eq_refl bool true) (fun p : BinNums.positive => match p return BinNums.Z with
| BinNums.xI _ => BinInt.Z.of_nat x
| BinNums.xO p0 => match p0 return BinNums.Z with
| BinNums.xI _ => BinNums.Z0
| BinNums.xO _ => BinInt.Z.of_nat (Nat.add s1 s2)
| BinNums.xH => BinInt.Z.of_nat s3
end
| BinNums.xH => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2)))
end) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2)))) (ZifyClasses.rew_iff (lt x (Nat.add (Nat.add s1 s2) s3)) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.add (BinInt.Z.of_nat (Nat.add s1 s2)) (BinInt.Z.of_nat s3))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) (Nat.add (Nat.add s1 s2) s3) (BinInt.Z.add (BinInt.Z.of_nat (Nat.add s1 s2)) (BinInt.Z.of_nat s3)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add (Nat.add s1 s2) (BinInt.Z.of_nat (Nat.add s1 s2)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.add s1 s2))) s3 (BinInt.Z.of_nat s3) (@eq_refl BinNums.Z (BinInt.Z.of_nat s3)))) (@eq_rect nat (Nat.add s1 (Nat.add s2 s3)) (fun a : nat => lt x a) l (Nat.add (Nat.add s1 s2) s3) (@eq_sym nat (Nat.add (Nat.add s1 s2) s3) (Nat.add s1 (Nat.add s2 s3)) (@eq_sym nat (PeanoNat.Nat.add s1 (PeanoNat.Nat.add s2 s3)) (PeanoNat.Nat.add (PeanoNat.Nat.add s1 s2) s3) (PeanoNat.Nat.add_assoc s1 s2 s3))))) (ZifyClasses.rew_iff (not (lt x (Nat.add s1 s2))) (not (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2)))) (ZifyClasses.not_morph (lt x (Nat.add s1 s2)) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat (Nat.add s1 s2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) (Nat.add s1 s2) (BinInt.Z.of_nat (Nat.add s1 s2)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.add s1 s2))))) n)))))
= 
@get_parent s3 r3 i3 o3 b3 (@inr (type (@get_node s3 r3 i3 o3 b3)) (fin s3) (@exist nat (fun p : nat => lt p s3) (Nat.sub (Nat.sub x s1) s2) (ZifyClasses.rew_iff_rev (lt (Nat.sub (Nat.sub x s1) s2) s3) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2))) (BinInt.Z.of_nat s3)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (Nat.sub (Nat.sub x s1) s2) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n2 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n2 m)) Znat.Nat2Z.inj_sub_max (Nat.sub x s1) (BinInt.Z.of_nat (Nat.sub x s1)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.sub x s1))) s2 (BinInt.Z.of_nat s2) (@eq_refl BinNums.Z (BinInt.Z.of_nat s2))) s3 (BinInt.Z.of_nat s3) (@eq_refl BinNums.Z (BinInt.Z.of_nat s3))) (ZMicromega.ZTautoChecker_sound (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.OR (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2)))) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEsub BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))))) tt)) (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2)) BinNums.Z0)) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEc BinNums.Z BinNums.Z0)) tt))) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEadd BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))) (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH)))) tt) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.NOT (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH)))) tt)) (@None unit) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH))) tt)))) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S O)) (RingMicromega.PsatzIn BinNums.Z O)))) ZMicromega.DoneProof) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (RingMicromega.PsatzIn BinNums.Z O))) ZMicromega.DoneProof) (@nil ZMicromega.ZArithProof))) (@eq_refl bool true) (fun p : BinNums.positive => match p return BinNums.Z with
| BinNums.xI _ => BinInt.Z.of_nat (Nat.sub x s1)
| BinNums.xO p0 => match p0 return BinNums.Z with
| BinNums.xI _ => BinNums.Z0
| BinNums.xO _ => BinInt.Z.of_nat s2
| BinNums.xH => BinInt.Z.of_nat s3
end
| BinNums.xH => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2))
end) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2))) (ZifyClasses.rew_iff (lt (Nat.sub x s1) (Nat.add s2 s3)) (BinInt.Z.lt (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.add (BinInt.Z.of_nat s2) (BinInt.Z.of_nat s3))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (Nat.sub x s1) (BinInt.Z.of_nat (Nat.sub x s1)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.sub x s1))) (Nat.add s2 s3) (BinInt.Z.add (BinInt.Z.of_nat s2) (BinInt.Z.of_nat s3)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add s2 (BinInt.Z.of_nat s2) (@eq_refl BinNums.Z (BinInt.Z.of_nat s2)) s3 (BinInt.Z.of_nat s3) (@eq_refl BinNums.Z (BinInt.Z.of_nat s3)))) (ZifyClasses.rew_iff_rev (lt (Nat.sub x s1) (Nat.add s2 s3)) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1))) (BinInt.Z.of_nat (Nat.add s2 s3))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (Nat.sub x s1) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n2 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n2 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) s1 (BinInt.Z.of_nat s1) (@eq_refl BinNums.Z (BinInt.Z.of_nat s1))) (Nat.add s2 s3) (BinInt.Z.of_nat (Nat.add s2 s3)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.add s2 s3)))) (ZMicromega.ZTautoChecker_sound (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.OR (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1)))) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEsub BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))))) tt)) (@Tauto.AND (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.X (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1)) BinNums.Z0)) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpEq (@EnvRing.PEc BinNums.Z BinNums.Z0)) tt))) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEadd BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH))) (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH)))) tt) (@None unit) (@Tauto.IMPL (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.NOT (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z (BinNums.xI BinNums.xH)) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO (BinNums.xO BinNums.xH)))) tt)) (@None unit) (@Tauto.A (RingMicromega.Formula BinNums.Z) Tauto.eKind unit unit Tauto.isProp (@RingMicromega.Build_Formula BinNums.Z (@EnvRing.PEX BinNums.Z BinNums.xH) RingMicromega.OpLt (@EnvRing.PEX BinNums.Z (BinNums.xO BinNums.xH))) tt)))) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S O)) (RingMicromega.PsatzIn BinNums.Z O)))) ZMicromega.DoneProof) (@cons ZMicromega.ZArithProof (ZMicromega.RatProof (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S (S O)))) (@RingMicromega.PsatzAdd BinNums.Z (RingMicromega.PsatzIn BinNums.Z (S (S O))) (RingMicromega.PsatzIn BinNums.Z O))) ZMicromega.DoneProof) (@nil ZMicromega.ZArithProof))) (@eq_refl bool true) (fun p : BinNums.positive => match p return BinNums.Z with
| BinNums.xI _ => BinInt.Z.of_nat x
| BinNums.xO p0 => match p0 return BinNums.Z with
| BinNums.xI _ => BinNums.Z0
| BinNums.xO _ => BinInt.Z.of_nat s1
| BinNums.xH => BinInt.Z.of_nat (Nat.add s2 s3)
end
| BinNums.xH => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1))
end) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1))) (ZifyClasses.rew_iff (lt x (Nat.add s1 (Nat.add s2 s3))) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.add (BinInt.Z.of_nat s1) (BinInt.Z.of_nat (Nat.add s2 s3)))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) (Nat.add s1 (Nat.add s2 s3)) (BinInt.Z.add (BinInt.Z.of_nat s1) (BinInt.Z.of_nat (Nat.add s2 s3))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add s1 (BinInt.Z.of_nat s1) (@eq_refl BinNums.Z (BinInt.Z.of_nat s1)) (Nat.add s2 s3) (BinInt.Z.of_nat (Nat.add s2 s3)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.add s2 s3))))) l) (ZifyClasses.rew_iff (not (lt x s1)) (not (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1))) (ZifyClasses.not_morph (lt x s1) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat s1)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) (@eq_refl BinNums.Z (BinInt.Z.of_nat x)) s1 (BinInt.Z.of_nat s1) (@eq_refl BinNums.Z (BinInt.Z.of_nat s1)))) n0)))) (ZifyClasses.rew_iff (not (lt (Nat.sub x s1) s2)) (not (BinInt.Z.lt (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2))) (ZifyClasses.not_morph (lt (Nat.sub x s1) s2) (BinInt.Z.lt (BinInt.Z.of_nat (Nat.sub x s1)) (BinInt.Z.of_nat s2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (Nat.sub x s1) (BinInt.Z.of_nat (Nat.sub x s1)) (@eq_refl BinNums.Z (BinInt.Z.of_nat (Nat.sub x s1))) s2 (BinInt.Z.of_nat s2) (@eq_refl BinNums.Z (BinInt.Z.of_nat s2)))) n1)))))).
f_equal. f_equal.  apply subset_eq_compat. lia. 
    rewrite <- H. unfold extract1. clear H.  
    destruct get_parent; try reflexivity.
    unfold surj_fin_add. 
    destruct f. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (S r3) _ _ (1+x0) _). 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2 + r3) _ _ (r2+x0) _).
    destruct (PeanoNat.Nat.ltb_spec0 (1 + x0) (S r3)).
    *** destruct zero1. destruct (PeanoNat.Nat.ltb_spec0 (r2 + x0) (r2 + r3)). 
    **** unfold id. f_equal.  
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + 1) _ _ (r1+x1) _).
    destruct (PeanoNat.Nat.ltb_spec0 (r1 + x1) (r1 + 1)).
    ***** reflexivity. 
    ***** exfalso. lia. 
    **** exfalso. lia. 
    *** exfalso. lia. 
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
