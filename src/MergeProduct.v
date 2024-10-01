Set Warnings "-notation-overridden, -parsing, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import ParallelProduct.
Require Import MathCompAddings.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.

From mathcomp Require Import all_ssreflect.

(** Merge operator *)
Module MergeBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

Definition bigraph_merge_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : UnionPossible b1 b2}
    (* : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) 1 (app_merge_NoDupList o1 o2)  *)
    := 
  (@merge (r1 + r2) ⊗ (@bigraph_id 0 (app_merge_NoDupList o1 o2))) <<o>> (b1 || b2).

Global Notation "b1 <|> b2" := (bigraph_merge_product b1 b2) (at level 50, left associativity).

Lemma arity_mp_right_neutral {s i o} (b : bigraph s i 1 o): forall n, 
  Arity (get_control (bg:=b <|> big_1) n) = Arity (get_control (bg:=b) (bij_void_void n)).
  Proof.
    intros n.
    destruct n as [[v | v ] | [n | v]].
    + destruct v.
    + destruct v.
    + reflexivity.
    + destruct v.
    Qed.

Theorem mp_right_neutral {s i o} (b : bigraph s i 1 o): 
  support_equivalence
    (b <|> big_1) 
    b.
  Proof.
  apply (SupEq _ _ _ _ _ _ _ _ (b <|> big_1) b
    (addn0 s)
    (right_empty i)
    (addn0 1)
    (right_empty o)
    bij_void_void
    bij_void_void
    (fun n => bij_rew (arity_mp_right_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel, sequence, sum_shuffle, rearrange, extract1, bij_rew_forward. 
      destruct get_parent; try reflexivity.
      rewrite <- eq_rect_eq.
      simpl.
      destruct o0 as (s1', Hs1').
      unfold split. unfold lshift. simpl.
      destruct (ltnP s1' (1 + 1)).
      f_equal. rewrite eq_rect_ordinal. apply val_inj. simpl. symmetry. apply (lt1_eq0 s1' Hs1').
      exfalso. apply (@leq_addl_trans 1 1 s1') in i0. apply (lt1_eq0 s1') in Hs1'. subst s1'. elim (nlt_0_it 0 i0).
    - unfold funcomp, parallel, sum_shuffle.
      unfold bij_rew_forward.
      unfold sequence. unfold rearrange.
      simpl.
      unfold extract1.
      destruct s1. unfold split. rewrite eq_rect_ordinal. simpl. destruct (ltnP m s).
      rewrite (Ordinal_proof_irrelevance s m i1 i0). 
      destruct get_parent; try reflexivity.
      destruct o0. rewrite eq_rect_ordinal. simpl. destruct (ltnP m0 (1 + 1)).
      * rewrite eq_rect_ordinal. f_equal. apply val_inj. simpl. symmetry. apply (lt1_eq0 m0 i2).
      * exfalso. apply (@leq_addl_trans 1 1 m0) in i3. apply (lt1_eq0 m0) in i2. subst m0. elim (nlt_0_it 0 i3).
      elim (lt_ge_contradiction m s i0 i1).
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward.
      destruct i1.
      simpl.
      unfold rearrange, switch_link. 
      rewrite <- (innername_proof_irrelevant b i0).
      destruct get_link; try reflexivity.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward. simpl.
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, link_juxt.
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
      unfold  rearrange, switch_link.  simpl.
      destruct get_link; try reflexivity.
      unfold extract1.
      destruct s0.
      f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Lemma arity_mp_left_neutral {s i o} (b : bigraph s i 1 o): forall n, 
  Arity (get_control (bg:=big_1 <|> b) n) = Arity (get_control (bg:=b) (bij_void_void_r n)).
  Proof.
    intros n.
    destruct n as [[v | v ] | [v | n]].
    + destruct v.
    + destruct v.
    + destruct v.
    + reflexivity.
    Qed.

Theorem mp_left_neutral {s i o} (b : bigraph s i 1 o): 
  support_equivalence (big_1 <|> b) b.
  Proof.
  apply (SupEq _ _ _ _ _ _ _ _ (big_1 <|> b) b
    erefl
    (left_empty i)
    erefl
    (left_empty o)
    bij_void_void_r 
    bij_void_void_r
    (fun n => bij_rew (arity_mp_left_neutral b n)) 
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
      simpl.
      destruct o0.
      unfold split,rshift,lshift. simpl.
      destruct (ltnP (1 + m) (1 + 1)).
      f_equal. unfold unsplit,lshift.
      apply val_inj. simpl. symmetry. apply (lt1_eq0 m i1).
      exfalso. rewrite leq_add2l in i1. apply (lt1_eq0 m) in i0. subst m. elim (nlt_0_it 0 i1). 
    - unfold funcomp, parallel, sum_shuffle.
      unfold bij_rew_forward.
      unfold rearrange, sequence. 
      simpl.
      unfold extract1,rearrange,split. 
      destruct s1 as [s1]. simpl. 
      destruct (ltnP s1 0).    
      * elim (nlt_0_it s1 i1).
      * erewrite <- (parent_proof_irrelevant b _).
      instantiate (1:= Ordinal (n:=s) (m:=s1) i0).
      destruct get_parent; try reflexivity.
      unfold extract1. rewrite eq_rect_ordinal. simpl. destruct o0.
      simpl. destruct (ltnP (1 + m) (1 + 1)).
      f_equal. unfold unsplit,lshift,rshift. apply val_inj;simpl. symmetry. apply (lt1_eq0 m i2).
      exfalso. rewrite leq_add2l in i3. apply (lt1_eq0 m) in i2. subst m. elim (nlt_0_it 0 i3). 
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward.
      destruct i1.
      simpl.
      unfold  rearrange, switch_link, in_app_or_m_nod_dup. 
      destruct (in_dec EqDecN x i).
      * rewrite <- (innername_proof_irrelevant b i0).
      destruct get_link; try reflexivity.
      unfold extract1, sum_shuffle, bij_list_backward', permut_list_forward. simpl.
      destruct s0. f_equal. unfold bij_list_forward. apply subset_eq_compat. reflexivity.
      * exfalso. apply n. apply i0.
    - unfold parallel, sum_shuffle, choice, funcomp, link_juxt.
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
      unfold  rearrange, switch_link.  simpl.
      destruct get_link; try reflexivity.
      unfold extract1.
      destruct s0.
      f_equal.
      unfold bij_list_forward. apply subset_eq_compat. reflexivity.
    Unshelve. apply val_inj. simpl.  symmetry. apply subn0.
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
   apply intersection_eq in Htmp.
   destruct Htmp.
   unfold switch_link, parallel, permut_list_forward. 
   unfold sum_shuffle, sum_shuffle, funcomp.
   unfold bij_list_forward, bij_list_backward', sequence, rearrange, link_juxt, in_app_or_m_nod_dup.
   apply in_app_or_m in H.
   destruct H.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right,extract1 in up23.
   rewrite <- (innername_proof_irrelevant b2 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i5. apply up23.
   * apply up23.
   + specialize (up13 (to_intersection inter12_3 H H0)).
   unfold to_intersection,to_left,to_right in up13.
   rewrite <- (innername_proof_irrelevant b1 (not_in_left (from_intersection_left Hinter12_3) n)) in up13.
   destruct get_link. 
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 Hi3) in up13.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up13. apply up13.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i4. apply up13. 
   * apply up13.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right in up23.
   rewrite <- (innername_proof_irrelevant b2 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** unfold extract1. destruct s0. destruct (in_dec EqDecN x EmptyNDL). apply i5. apply up23. 
   * apply up23.
   + exfalso. apply n. apply H.
  Qed.

Lemma arity_mp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : UnionPossible b1 b2} {up23 : UnionPossible b2 b3} {up13 : UnionPossible b1 b3} n12_3,
  Arity (get_control (bg:=(b1 <|> b2) <|> b3) n12_3) 
  = 
  Arity (get_control (bg:=bigraph_merge_product 
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
  support_equivalence 
    ((b1 <|> b2) <|>  b3)
    (bigraph_merge_product 
      (up := union_possible_commutes (union_possible_assoc_mp up23 (union_possible_commutes up13) (union_possible_commutes up12))) 
      b1 
      (b2 <|> b3)).
  Proof.
  intros.
  apply (SupEq _ _ _ _ _ _ _ _ ((b1 <|> b2) <|> b3) (b1 <|> (b2 <|> b3))
    (esym (addnA _ _ _))
    tr_permutation
    (erefl)
    permutationtr
    bij_sum_assoc_mp
    bij_sum_assoc_mp
    (fun n12_3 => bij_rew (arity_mp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [[v | v] | [a | [[v|v]|[b|c]]]]; try reflexivity; try (elim v).
  + apply functional_extensionality. rewrite bij_rew_id. 
    intros [[[v | v] | [a | [[v|v]|[b|c]]]] | s1_23']; simpl; unfold funcomp; simpl; try (elim v).
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      unfold  bij_rew_forward.
      destruct o0.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal. unfold split. simpl.
      destruct (ltnP m (r1 + r2)).
      2:{exfalso. apply (leq_addl_trans r1 r2 m) in i4. elim (lt_ge_contradiction m r1 i0 i4). }
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP 0 (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i5. apply (leq_addl_trans 1 r3 0) in i5. apply nlt_0_it in i5. apply i5. }
      destruct (ltnP m (r1 + (1 + 0))).
      * reflexivity.
      * exfalso. rewrite addn0 in i6. apply (leq_addl_trans r1 1 m) in i6. 
      elim (lt_ge_contradiction m r1 i0 i6). 
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      destruct o0. simpl.
      unfold  bij_rew_forward. rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal. unfold split. simpl.
      destruct (ltnP (r1 + m) (r1 + r2)).
      2:{exfalso. rewrite leq_add2l in i4. apply (lt_ge_contradiction m r2 i0 i4). }
      rewrite eq_rect_ordinal. simpl. 
      destruct (ltnP 0 (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i5. apply (leq_addl_trans 1 r3 0) in i5. apply nlt_0_it in i5. apply i5. }
      destruct (ltnP m (r2 + r3)).
      2:{exfalso. apply leq_addl_trans in i6. elim (lt_ge_contradiction m r2 i0 i6). }
      rewrite eq_rect_ordinal. simpl.  
      destruct ( ltnP (r1 + 0) (r1 + (1 + 0))).
      2:{exfalso. rewrite addn0 in i7. rewrite addn0 in i7. apply add1_leq_false in i7. apply i7. }
      simpl. reflexivity.
    - f_equal. 
      simpl. 
      unfold rearrange. unfold extract1, parallel, sum_shuffle. 
      destruct get_parent; try reflexivity.
      destruct o0. simpl.
      unfold  bij_rew_forward.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal. unfold split. simpl.
      destruct (ltnP (1 + 0 + m) (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i4. rewrite (leq_add2l 1 r3 m) in i4. elim (lt_ge_contradiction m r3 i0 i4). }
      destruct (ltnP (r2 + m) (r2 + r3)).
      2:{exfalso. rewrite (leq_add2l r2 r3 m) in i5. elim (lt_ge_contradiction m r3 i0 i5). }
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP (r1 + 0) (r1 + (1 + 0))).
      f_equal.
      exfalso. rewrite addn0 in i6.
      rewrite addn0 in i6.
      apply (add1_leq_false r1 i6).
    - f_equal. 
      destruct s1_23'; simpl.
      unfold parallel, sum_shuffle.
      unfold rearrange.
      unfold bij_rew_forward.
      unfold sequence, extract1, rearrange,split. 
      rewrite eq_rect_ordinal;simpl.
      destruct (ltnP m (s1 + s2));simpl; destruct (ltnP m s1);simpl.
      * destruct get_parent;try reflexivity. destruct o0.
      unfold extract1. rewrite eq_rect_ordinal. rewrite eq_rect_ordinal. simpl.
      destruct (ltnP m0 (r1 + r2)); rewrite eq_rect_ordinal;simpl.
      2:{exfalso. apply leq_addl_trans in i7. elim (lt_ge_contradiction m0 r1 i6 i7). }
      destruct (ltnP 0 (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i8.
      rewrite addnC in i8. rewrite leqn0 in i8. rewrite addn_eq0 in i8.
      generalize i8. 
      move/andP => [Hr3 Hfalse].
      discriminate Hfalse. } 
      destruct ( ltnP m0 (r1 + (1 + 0))).
      reflexivity.
      exfalso. rewrite addn0 in i9. 
      apply (leq_addl_trans r1 1 m0) in i9.
      elim (lt_ge_contradiction m0 r1 i6 i9).
      * destruct (ltnP (m - s1) s2).
      rewrite (Ordinal_proof_irrelevance s2 (m-s1) _ i6).
      destruct get_parent;try reflexivity.
      unfold extract1. rewrite eq_rect_ordinal. simpl. destruct o0. simpl.
      destruct (ltnP (r1 + m0) (r1 + r2)).
      2:{exfalso. rewrite (leq_add2l r1 r2 m0) in i8. elim (lt_ge_contradiction m0 r2 i7 i8). }
      rewrite eq_rect_ordinal. rewrite eq_rect_ordinal. simpl. 
      destruct (ltnP 0 (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i9.
      rewrite addnC in i9. rewrite leqn0 in i9. rewrite addn_eq0 in i9.
      generalize i9. 
      move/andP => [Hr3 Hfalse].
      discriminate Hfalse. }
      destruct (ltnP m0 (r2 + r3)). 
      2:{exfalso. apply (leq_addl_trans r2 r3 m0) in i10. elim (lt_ge_contradiction m0 r2 i7 i10). }
      rewrite eq_rect_ordinal. simpl. 
      destruct (ltnP (r1 + 0) (r1 + (1 + 0))).
      2:{exfalso. rewrite addn0 in i11.
      rewrite addn0 in i11.
      apply (add1_leq_false r1 i11). }
      reflexivity.
      exfalso. rewrite leq_subRL in i6; try assumption. 
      elim (lt_ge_contradiction m (s1+s2) i4 i6).
      exfalso. apply (leq_addl_trans s1 s2 m) in i4.
      elim (lt_ge_contradiction m s1 i5 i4).
      * destruct (ltnP (m - s1) s2).
      exfalso. rewrite <- leq_subRL in i4; try assumption.  
      elim (lt_ge_contradiction (m-s1) s2 i6 i4).
      erewrite <- (parent_proof_irrelevant b3 _).
      instantiate (1:= Ordinal (n:=s3) (m:=m - s1 - s2) (split_subproof (m:=s2) (n:=s3) (i:=Ordinal (n:=s2 + s3) (m:=m - s1) (split_subproof (m:=s1) (n:=s2 + s3) (i:=Ordinal (n:=s1 + (s2 + s3)) (m:=m) i0) i5)) i6)).
      destruct get_parent;try reflexivity.
      destruct o0.
      unfold extract1. rewrite eq_rect_ordinal. simpl. rewrite eq_rect_ordinal;simpl.
      destruct (ltnP (1 + 0 + m0) (1 + 0 + r3)).
      2:{exfalso. rewrite addn0 in i8. rewrite leq_add2l in i8. elim(lt_ge_contradiction m0 r3 i7 i8). }
      destruct (ltnP (r2 + m0) (r2 + r3)).
      2:{exfalso. rewrite leq_add2l in i9. elim(lt_ge_contradiction m0 r3 i7 i9). }
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP (r1 + 0) (r1 + (1 + 0))).
      2:{exfalso. rewrite addn0 in i10.
      rewrite addn0 in i10.
      apply (add1_leq_false r1 i10). }
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
      unfold  rearrange, switch_link. simpl. 
      unfold in_app_or_m_nod_dup, extract1.
      destruct (in_dec EqDecN i123 (app_merge i2 i3)).
      * destruct (in_dec EqDecN i123 i3).
      ** destruct get_link; try reflexivity.
      *** unfold permut_list_forward. 
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).      
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i5). 
      destruct get_link; try reflexivity.
      **** unfold permut_list_forward. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_or_m in i4. destruct i4.
      -- apply n0. apply H.
      -- apply n. apply H.
      * destruct (in_dec EqDecN i123 i3).
      ** exfalso. apply n. apply in_right_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_left_list. apply i4.
      *** rewrite <- (innername_proof_irrelevant b1 (not_in_left i0 n)). 
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
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold extract1. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
      * simpl in v. destruct v.
      * simpl in v. destruct v.
      * unfold bij_subset_forward, parallel, funcomp.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl. 
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold extract1. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, parallel, funcomp.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl. 
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold extract1. simpl. 
        destruct get_link; try reflexivity.
        ** destruct s0. apply f_equal. apply subset_eq_compat. reflexivity.
  Unshelve.
  apply val_inj. simpl. rewrite addnC. rewrite subnDAC. reflexivity.
  Qed. 

(* Lemma arity_mp_commu : forall {s1 i1 r1 o1 s2 i2 r2 o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up12 : UnionPossible b1 b2} n12,
  Arity (get_control (bg:=b1 <|> b2) n12) 
  = 
  Arity (get_control (bg:=bigraph_merge_product (up := union_possible_commutes up12) b2 b1) (bijection_nesting_comu n12)). 
  Proof.
  intros until n12.
  destruct n12 as [[v|v]|[n2'|n1']]; try destruct v; try reflexivity.
  Qed.

Theorem bigraph_mp_comu : forall {s1 i1 r1 o1 s2 i2 r2 o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up12 : UnionPossible b1 b2},
  support_equivalence 
    (b1 <|> b2)
    (bigraph_merge_product (up := union_possible_commutes up12) b2 b1).
  Proof.
  intros.
  eapply (SupEq _ _ _ _ _ _ _ _ (b1 <|> b2) (b2 <|> b1)
    (addnC s1 s2)
    permutation_union_commutes
    (erefl)
    permutation_empty_union_commutes
    bijection_nesting_comu 
    bijection_nesting_comu
    (fun n12 => bij_rew (arity_mp_commu b1 b2 n12))    
  ).
  + apply functional_extensionality.
    destruct x as [[v|v]|[n2'|n1']]; try reflexivity; try (elim v).
  + apply functional_extensionality. rewrite bij_rew_id. 
    intros [[[v|v]|[n2'|n1']] | s1_23']; simpl; unfold funcomp; simpl; try (elim v).
    - simpl. 
    unfold parallel, rearrange, extract1, sum_shuffle.
    destruct get_parent; try reflexivity. 
    destruct o0.
    unfold  bij_rew_forward.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ (r1 + x) _).
    destruct (PeanoNat.Nat.ltb_spec0 (r1 + x) (r1 + r2)).
    destruct zero1. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r1) (r2 + r1 + 0) _ x _).
    destruct (PeanoNat.Nat.ltb_spec0 x (r2 + r1)).
    f_equal. exfalso. apply n. lia.
    exfalso. apply n. lia.
    - simpl. 
    unfold parallel, rearrange, extract1, sum_shuffle.
    destruct get_parent; try reflexivity. 
    destruct o0.
    unfold  bij_rew_forward.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1+r2) (r1 + r2 + 0) _ x _).
    destruct (PeanoNat.Nat.ltb_spec0 x (r1 + r2)).
    destruct zero1. 
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r2+r1) (r2 + r1 + 0) _ (r2 + x) _).
    destruct (PeanoNat.Nat.ltb_spec0 (r2 + x) (r2 + r1)).
    f_equal. exfalso. apply n. lia.
    exfalso. apply n. lia.
    - simpl. 
    unfold parallel, rearrange, extract1, sum_shuffle.
    unfold  bij_rew_forward.
    destruct s1_23'.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s2+s1) (s1+s2) _ x _).
    destruct (PeanoNat.Nat.ltb_spec0 x s1).
    destruct (PeanoNat.Nat.ltb_spec0 x s2).
    destruct get_parent.
    destruct get_parent. 
     f_equal. f_equal. f_equal.  Abort. *)
      
      
End MergeBig.
