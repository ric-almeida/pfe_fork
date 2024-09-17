Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import TensorProduct.
Require Import UnionPossible.
Require Import MathCompAddings.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.
From mathcomp Require Import all_ssreflect.


Require Import List.



(** * Juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Module ParallelProduct (s : SignatureParameter) (n : NamesParameter).
Module mup := UnionPossible s n.
Include mup.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.

Definition link_juxt {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  (*{up : union_possible b1 b2} Ii don't use it in this definition though*)
  (ip :NameSub (i1 ∪ i2) + Port (join (get_control (bg:=b1)) (get_control (bg:=b2)))) :
  NameSub (o1 ∪ o2) +  ((get_edge b1) + (get_edge b2)). 
  Proof.
  destruct ip as [[n npf] | p].
  + (*inner*)  
    apply in_app_or_m_nod_dup in npf; try (apply (nd i2); try (apply (nd i1))).
    destruct npf.
    * (*inner1*)
    destruct (get_link (bg:=b1) (inl (exist (fun name : Name => In name i1) n i0))).
    ** (*l1 (i1) = o1 *)
    left. destruct s0. exists x. apply in_left_list. apply i3.
    ** (*l1 (i1) = e1 *)
    right. simpl. left. exact s0.
    * (*inner2*) 
    destruct (get_link (bg:=b2) (inl (exist (fun name : Name => In name i2) n i0))).
    ** (*l2 (i2) = o2 *)
    left. destruct s0. exists x. apply in_right_list. apply i3.
    ** (*l2 (i2) = e2 *)
    right. simpl. right. exact s0.
    * apply (nd i1).
  + (*Port*)
    destruct p as [np nppf]. destruct np as [np1|np2].
    * (*Port1*)
    destruct (get_link (bg:=b1) (inr (existT _ np1 nppf))).
    ** (*l1 (p1)=o1*)
    left. destruct s0. exists x. apply in_left_list. apply i0.
    ** (*l1 (p1) = e1 *)
    right. simpl. left. exact s0.
    * (*Port2*) 
    destruct (get_link (bg:=b2) (inr (existT _ np2 nppf))).
    ** (*l2 (p2) = o2 *)
    left. destruct s0. exists x. apply in_right_list. apply i0.
    ** (*l2 (p2) = e2 *)
    right. simpl. right. exact s0.
  Defined.

Definition bigraph_parallel_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : UnionPossible b1 b2}
    : bigraph (s1 + s2) (i1 ∪ i2) (r1 + r2) (o1 ∪ o2).
  Proof.
  eapply (@Big 
    (s1 + s2)
    (i1 ∪ i2)
    (r1 + r2)
    (o1 ∪ o2)
    (((get_node b1) + (get_node b2))%type)
    (((get_edge b1) + (get_edge b2))%type)
    (join (get_control (bg:=b1)) (get_control (bg:=b2)))
    ((bij_id <+> bijection_inv bij_ord_sum) <o>
      (bij_sum_shuffle <o> (parallel (get_parent (bg:=b1)) (get_parent (bg:=b2))) <o> (bijection_inv bij_sum_shuffle)) <o> 
      (bij_id <+> bij_ord_sum))
    (link_juxt b1 b2) _
    ). Unshelve. 
  - rewrite <- tensor_alt.
  apply finite_parent_inout.
  apply finite_parent_tensor.
  + exact (@ap _ _ _ _ b1).
  + exact (@ap _ _ _ _ b2).
  Defined. 

Global Notation "b1 || b2" := (bigraph_parallel_product b1 b2) (at level 50, left associativity).

Theorem tp_eq_pp {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {dis_i : i1 # i2} {dis_o : o1 # o2} :
  bigraph_equality 
    (b1 ⊗ b2) 
    (b1 || b2).
  Proof.
  refine (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b2) (b1 || b2)
    erefl
    (permutation_id (app_merge i1 i2))
    erefl
    (permutation_id (app_merge o1 o2))
    bij_id
    bij_id
    _  _ _ _
    ).
  - simpl. apply id_left_neutral.
  - rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  - Unshelve. 2:{ intros. exact bij_id. }
    rewrite bij_sigT_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    simpl.
    apply functional_extensionality.
    intros [inner|port].
    + unfold parallel, funcomp, sum_shuffle, bij_list_backward', link_juxt.
      simpl.
      destruct inner.
      destruct (in_dec EqDecN x i1).
      * destruct (in_app_or_m_nod_dup i1 i2 x (nd i1) (nd i2) i0) eqn:E.
      ** symmetry. rewrite <- (innername_proof_irrelevant b1 i3). 
      destruct get_link; try reflexivity.
      ** exfalso. apply DN_D in dis_i. specialize (dis_i x). apply dis_i; assumption.
      * destruct (in_app_or_m_nod_dup i1 i2 x (nd i1) (nd i2) i0).
      ** exfalso. apply n. apply i3.
      ** rewrite <- (innername_proof_irrelevant b2 i3). 
      destruct get_link; try reflexivity.
    + unfold parallel, funcomp, sum_shuffle, bij_join_port_backward, bij_list_backward', bij_list_forward, link_juxt.
      simpl.
      destruct port as [[p1|p2] [pf]].
      * unfold join. 
      destruct get_link; try reflexivity.
      * unfold join. 
      destruct get_link; try reflexivity.
  Qed.


Lemma arity_pp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bg:=∅ || b) n) = Arity (get_control (bg:=b) (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (∅ || b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ || b) b
    erefl
    (left_empty i)
    erefl
    (left_empty o)
    bij_void_sum_neutral
    bij_void_sum_neutral
    (fun n => bij_rew (arity_pp_left_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      destruct get_parent; try reflexivity.
      destruct o0. f_equal. unfold unsplit,rshift. apply val_inj. reflexivity.  
    - unfold funcomp, parallel, sum_shuffle.
      simpl. 
      destruct s1; unfold fintype.split; simpl.
      destruct (ltnP m 0).
      * exfalso. elim (nlt_0_it m i1). 
      * erewrite <- (parent_proof_irrelevant b _ ).
      instantiate (1:= Ordinal (n:=s) (m:=m) i0).
      destruct get_parent.
      ** reflexivity. 
      ** unfold unsplit,rshift. f_equal. apply val_inj. simpl.
      rewrite addnC. rewrite addn0. reflexivity.
      Unshelve. 2:{apply val_inj;simpl. rewrite subn0. reflexivity. }  
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward.
      destruct i1.
      simpl.
      destruct in_app_or_m_nod_dup.
      * exfalso. apply in_nil in i1. apply i1.
      * rewrite <- (innername_proof_irrelevant b i0 i1).
      destruct get_link; try reflexivity.
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
      destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

Lemma arity_pp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bg:=b || ∅) n) = Arity (get_control (bg:=b) (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_pp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (b || ∅) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b || ∅) b
    (PeanoNat.Nat.add_0_r s)
    (right_empty i)
    (PeanoNat.Nat.add_0_r r)
    (right_empty o)
    bij_void_sum_neutral_r
    bij_void_sum_neutral_r
    (fun n => bij_rew (arity_pp_right_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      destruct get_parent; try reflexivity.
      destruct o0. f_equal. 
      unfold bij_rew_forward.
      rewrite eq_rect_ordinal.
      apply val_inj;simpl. reflexivity.
    - unfold funcomp, parallel, sum_shuffle.
      destruct s1. unfold fintype.split,bij_rew_forward. rewrite eq_rect_ordinal. simpl.
      destruct (ltnP m s).
      * rewrite (Ordinal_proof_irrelevance s m i1 i0).
      destruct get_parent;try reflexivity.
      ** f_equal. rewrite eq_rect_ordinal. destruct o0. apply val_inj. simpl. reflexivity.
      * elim (lt_ge_contradiction m s i0 i1).
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward.
      destruct i1.
      simpl.       
      rewrite <- (innername_proof_irrelevant b i0).
      destruct get_link; try reflexivity.
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
      destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

(* Lemma arity_pp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) {up : UnionPossible b1 b2} n12,
  Arity (get_control (bg := b1 || b2) n12) = 
  Arity (get_control (bg := bigraph_parallel_product (up:=union_possible_commutes up) b2 b1) (bij_sum_comm n12)).
  Proof.
  intros until n12.
  destruct n12.
  + reflexivity.
  + reflexivity.
  Qed. *)

(* Theorem bigraph_pp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) {up : UnionPossible b1 b2},
  bigraph_equality (b1 ||b2) (bigraph_parallel_product (up:=union_possible_commutes up) b2 b1).
  Proof.
  intros.
  refine (BigEq _ _ _ _ _ _ _ _ (b1 || b2) (b2 || b1)
    (@esym _ _ _ _)
    in_app_merge_comu
    (@esym _ _ _ _)
    in_app_merge_comu
    bij_sum_comm
    bij_sum_comm
    (fun n12 => bij_rew (arity_pp_comm b1 b2 n12))
    _ _ _
  ).
  + apply functional_extensionality.
    destruct x as [k2 | k1]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2 | n1] | s21']; simpl; unfold funcomp,parallel,bij_rew_forward ; simpl.
    -  destruct get_parent ; try reflexivity.
    f_equal. destruct o0. rewrite eq_rect_ordinal. unfold unsplit,lshift.
    apply val_inj;simpl.
    rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2) (r2 + r1) _ (r1 + x) _).
    apply subset_eq_compat. try lia.
    Abort. We don't have commutativity *)

#[export] Instance union_possible_assoc_pp {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  {b3 : bigraph s3 i3 r3 o3}
  (up12 : UnionPossible b1 b2) 
  (up23 : UnionPossible b2 b3) 
  (up13 : UnionPossible b1 b3) :
  UnionPossible 
    (b1 || b2)
    b3.
  Proof.
  destruct up12 as [up12]. 
  destruct up13 as [up13].
  destruct up23 as [up23].
  constructor.
   unfold union_possible.
   intros [inter12_3 Hinter12_3].
   unfold intersectionNDL in *.
   simpl in *.
   pose Hinter12_3 as Htmp.
   apply intersection_eq in Htmp.
   destruct Htmp.
   unfold in_app_or_m_nod_dup.
   apply in_app_or_m in H.
   destruct H.
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
   ** apply up23.
   * apply up23.
   + specialize (up13 (to_intersection inter12_3 H H0)).
   unfold to_intersection,to_left,to_right in up13.
   rewrite <- (innername_proof_irrelevant b1 (not_in_left (from_intersection_left Hinter12_3) n)) in up13.
   destruct get_link. 
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 Hi3) in up13.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up13. apply up13.
   ** apply up13.
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
   ** apply up23.
   * apply up23.
   + exfalso. apply n. apply H.
  Qed.

#[export] Instance union_possible_assoc_pp_r {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  {b3 : bigraph s3 i3 r3 o3}
  (up12 : UnionPossible b1 b2) 
  (up23 : UnionPossible b2 b3) 
  (up13 : UnionPossible b1 b3) :
  UnionPossible b1 (b2 || b3):= union_possible_commutes (union_possible_assoc_pp up23 (union_possible_commutes up13) (union_possible_commutes up12)).
   
Lemma arity_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : UnionPossible b1 b2} {up23 : UnionPossible b2 b3} {up13 : UnionPossible b1 b3} n12_3,
  Arity (get_control (bg := (b1 || b2) || b3) n12_3) 
  = 
  Arity (get_control (bg := b1 || (b2 || b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : UnionPossible b1 b2} {up23 : UnionPossible b2 b3} {up13 : UnionPossible b1 b3},
  bigraph_equality 
  ((b1 || b2) || b3)
  (b1 || (b2 || b3)).
  Proof.
  intros.
  destruct up12 as [up12]. 
  destruct up13 as [up13].
  destruct up23 as [up23].
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 || b2) || b3) (b1 || (b2 || b3))
    (esym (addnA _ _ _))
    tr_permutation
    (esym (addnA _ _ _))
    tr_permutation
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (arity_pp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | s1_23']; simpl; unfold funcomp; simpl.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,lshift.
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,rshift.
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,rshift.
      rewrite eq_rect_ordinal. apply val_inj;simpl. rewrite addnA. reflexivity.
    - destruct s1_23'; simpl.
      unfold parallel, sum_shuffle.
      unfold fintype.split,bij_rew_forward.
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP m (s1 + s2)).
      * simpl. destruct (ltnP m s1).
      ** destruct get_parent; try reflexivity. 
      f_equal. unfold unsplit,rshift,lshift. 
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
      ** simpl. destruct (ltnP (m - s1) s2).
      *** rewrite (Ordinal_proof_irrelevance s2 (m-s1) _ i6).
      destruct get_parent; try reflexivity. 
      f_equal. unfold unsplit,rshift,lshift. 
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
      *** exfalso. rewrite leq_subRL in i6; try assumption.
      elim (lt_ge_contradiction m (s1+s2) i4 i6).
      * destruct (ltnP m s1).
      ** exfalso. apply leq_addl_trans in i4.
      elim (lt_ge_contradiction m s1 i5 i4).
      ** simpl. destruct (ltnP (m - s1) s2).
      *** exfalso. rewrite <- leq_subRL in i4; try assumption.
      elim (lt_ge_contradiction (m-s1) s2 i6 i4).
      *** symmetry. erewrite <- (parent_proof_irrelevant b3 _).
      instantiate (1:=Ordinal (n:=s3) (m:=m - (s1 + s2))
        (split_subproof (m:=s1 + s2) (n:=s3) (i:=Ordinal (n:=s1 + s2 + s3) (m:=m) (replace_in_H (Logic.eq_sym (esym (addnA s1 s2 s3))) m i0)) i4)).
      destruct get_parent; try reflexivity.
      f_equal. unfold unsplit,rshift,lshift. 
      rewrite eq_rect_ordinal. apply val_inj;simpl. apply addnA.
      Unshelve. 2:{ apply val_inj. simpl. apply subnDA. }
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
       simpl. 
      unfold in_app_or_m_nod_dup.
      destruct (in_dec EqDecN i123 (app_merge i2 i3)).
      * destruct (in_dec EqDecN i123 i3).
      ** destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).      
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i5). 
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_or_m in i4. destruct i4.
      -- apply n0. apply H.
      -- apply n. apply H.
      * destruct (in_dec EqDecN i123 i3).
      ** exfalso. apply n. apply in_right_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_left_list. apply i4.
      *** rewrite <- (innername_proof_irrelevant b1 (not_in_left i0 n)). 
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
         simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
         simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
         simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

Definition arity_pp_congruence_forward (*TODO: can't we deduce up24 from up13?*)
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : UnionPossible b1 b3} {up24 : UnionPossible b2 b4}
  (bij_n12 : bijection ( (get_node b1)) ( (get_node b2))) (bij_n34 : bijection ( (get_node b3)) ( (get_node b4)))
  (bij_p12 : forall (n1 :  (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 :  (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 :  (get_node (b1 || b3))) :
    ('I_(Arity (get_control (bg:=b1 || b3) n13))) -> 
    ('I_(Arity (get_control (bg:=b2 || b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_pp_congruence_backward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : UnionPossible b1 b3} {up24 : UnionPossible b2 b4}
  (bij_n12 : bijection ( (get_node b1)) ( (get_node b2))) (bij_n34 : bijection ( (get_node b3)) ( (get_node b4)))
  (bij_p12 : forall (n1 :  (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 :  (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 :  (get_node (b1 || b3))) :
  ('I_(Arity (get_control (bg:= b2 || b4) ((bij_n12 <+> bij_n34) n13)))) -> 
  ('I_(Arity (get_control (bg:=b1 || b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_pp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : UnionPossible b1 b3} {up24 : UnionPossible b2 b4}
  (bij_n12 : bijection ( (get_node b1)) ( (get_node b2))) (bij_n34 : bijection ( (get_node b3)) ( (get_node b4)))
  (bij_p12 : forall (n1 :  (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 :  (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 :  (get_node (b1 || b3))),
  bijection 
    ('I_(Arity (get_control (bg:=b1 || b3) n13))) 
    ('I_(Arity (get_control (bg:=b2 || b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  destruct up13 as [up13].
  destruct up24 as [up24].
  apply (mkBijection _ _ 
    (arity_pp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) 
    (arity_pp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
  + destruct n13 as [n1 | n3]; simpl.
    - rewrite <- (fob_id _ _ (bij_p12 n1)).
      reflexivity.
    - rewrite <- (fob_id _ _ (bij_p34 n3)).
      reflexivity.
  + destruct n13 as [n1 | n3]; simpl.
    - rewrite <- (bof_id _ _ (bij_p12 n1)).
      reflexivity.
    - rewrite <- (bof_id _ _ (bij_p34 n3)).
      reflexivity.
  Defined.

Theorem bigraph_pp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : UnionPossible b1 b3} {up24 : UnionPossible b2 b4},
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> 
    bigraph_equality (b1|| b3) (b2 || b4).
  Proof.
  intros until b4.
  intros up13 up24 Heqb1b2 Heqb3b4.
  destruct up13 as [up13].
  destruct up24 as [up24].
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 || b3) (b2 || b4)
    (f_equal2_plus _ _ _ _ bij_s12 bij_s34)
    (app_merge_cong bij_i12 bij_i34)
    (f_equal2_plus _ _ _ _ bij_r12 bij_r34)
    (app_merge_cong bij_o12 bij_o34)
    (bij_n12 <+> bij_n34)
    (bij_e12 <+> bij_e34)
    (arity_pp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
  ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    subst s1. subst r1. subst s3. subst r3.
    destruct x as [[n2' | n4'] | s24']; simpl; unfold funcomp; simpl.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,lshift.
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,rshift.
      rewrite eq_rect_ordinal. apply val_inj;simpl. reflexivity.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel, bij_rew_forward,sum_shuffle,fintype.split.
      destruct s24'.
      rewrite eq_rect_ordinal.
      simpl. 
      destruct (ltnP m s2).
      * destruct get_parent; try reflexivity.
        f_equal. unfold unsplit,lshift. destruct o0.
        rewrite eq_rect_ordinal.
        apply val_inj;simpl. reflexivity.
      * rewrite <- big_parent_eq34.
        simpl.
        unfold parallel, funcomp, bij_rew_forward.
        rewrite <- eq_rect_eq.
        simpl. 
        erewrite <- (parent_proof_irrelevant b3 _).
        instantiate (1:=Ordinal (n:=s4) (m:=m - s2)
        (split_subproof (m:=s2) (n:=s4) (i:=Ordinal (n:=s2 + s4) (m:=m) i0) i5)).
        destruct get_parent; simpl; try reflexivity.
        f_equal. unfold unsplit,rshift. destruct o0.
        rewrite eq_rect_ordinal.
        apply val_inj;simpl. reflexivity.
  + apply functional_extensionality. 
    destruct x as [[i24] | ([n2' | n4'], (i', Hi'))]; simpl.
    - rewrite <- big_link_eq34.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, in_app_or_m_nod_dup, link_juxt, in_app_or_m_nod_dup.
      simpl.
      unfold bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward, parallel, funcomp.
      simpl.
      destruct (in_dec EqDecN i24 i3).
      * destruct (in_dec EqDecN i24 i4).
      ** symmetry. rewrite <- (innername_proof_irrelevant b3 i5).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. apply bij_i34. apply i5.
      * destruct (in_dec EqDecN i24 i4).
      ** exfalso. apply n. apply bij_i34. apply i5.
      ** rewrite <- big_link_eq12.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, in_app_or_m_nod_dup, link_juxt, in_app_or_m_nod_dup.
      simpl.
      unfold bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward, parallel, funcomp.
      simpl.
      set (Hn := match bij_i12 i24 with | conj _ H => H  end
        (eq_ind_r (fun b : Name => In b i2) (not_in_left i0 n0) erefl)).  
      rewrite <- (innername_proof_irrelevant b1 Hn).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    - rewrite <- big_link_eq12.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
      unfold eq_rect_r.
      unfold parallel, funcomp.     
      simpl.
      erewrite <- (eq_rect_map (f := inl) (a := n2')).
      instantiate (1 := (Logic.eq_sym (equal_f (fob_id (get_node b1) (get_node b2) bij_n12) n2'))).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) n2'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity. 
    - rewrite <- big_link_eq34.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
      unfold eq_rect_r.
      unfold parallel, funcomp.
      simpl.
      erewrite <- (eq_rect_map (f := inr) (a := n4')).
      instantiate (1 := (Logic.eq_sym (equal_f (fob_id (get_node b3) (get_node b4) bij_n34) n4'))).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) n4'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity.
  Unshelve. apply val_inj. simpl. reflexivity.
  Qed.


(* Bifunctorial property *)
Theorem arity_comp_pp_dist : forall {s1r3 i1o3 r1 o1 s2r4 i2o4 r2 o2 r3s1 r4s2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1r3 i1o3 r1 o1) 
  (b2 : bigraph s2r4 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3s1 o3i1) 
  (b4 : bigraph s4 i4 r4s2 o4i2)
  {up12 : UnionPossible b1 b2} {up34 : UnionPossible b3 b4}
  {eqs2r4 : MyEqNat s2r4 r4s2} {eqs1r3 : MyEqNat s1r3 r3s1} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  (n12_34 :  (get_node (b1 || b2 <<o>> (b3 || b4)))),
  Arity (get_control (bg:=(b1 || b2) <<o>> (b3 || b4)) n12_34) =
  Arity (get_control (bg:=(b1 <<o>> b3) || (b2 <<o>> b4)) (sum_shuffle n12_34)).
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.

Theorem bigraph_comp_pp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 r3 r4 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2)
  {eqs2r4 : MyEqNat s2 r4} {eqs1r3 : MyEqNat s1 r3} 
  {up12 : UnionPossible b1 b2} {up34 : UnionPossible b3 b4}
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)},
  bigraph_equality 
    ((b1 || b2) <<o>> (b3 || b4))
    ((b1 <<o>> b3) || (b2 <<o>> b4)).
  Proof.
  intros.
  destruct up12 as [up12].
  destruct up34 as [up34].
  apply (BigEq
    _ _ _ _
    _ _ _ _ 
    ((b1 || b2) <<o>> (b3 || b4))
    ((b1 <<o>> b3) || (b2 <<o>> b4))
    (reflexivity (s3 + s4)) (*s3 + s4*)
    reflnames (*i3 + i4*)
    (reflexivity (r1 + r2)) (*r1 + r2*)
    reflnames (*o1 + o2*)
    bij_sum_shuffle(* n1 + n2 + n3 + n4*)
    bij_sum_shuffle (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (arity_comp_pp_dist b1 b2 b3 b4 n12_34)) (* Port *)
  ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|(s34, Hs34)]; simpl; unfold funcomp; simpl; unfold sequence, extract1, inject, sum_shuffle, parallel.
    - destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. destruct get_parent; try reflexivity.
      unfold bij_rew_forward.
      destruct o0 as (s1', Hs1').
      destruct eqs2r4 as [eqs2r4].
      destruct eqs1r3 as [eqs1r3].
      destruct eqs2r4.
      destruct eqs1r3.
      rewrite <- eq_rect_eq. 
      rewrite unsplitK.
      rewrite eq_rect_ordinal.
      rewrite (Ordinal_proof_irrelevance s1 s1' _ Hs1').
      destruct get_parent; try reflexivity.
    - destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. destruct get_parent; try reflexivity.
      unfold bij_rew_forward.
      destruct o0 as (s1', Hs1').
      destruct eqs2r4 as [eqs2r4].
      destruct eqs1r3 as [eqs1r3].
      destruct eqs2r4.
      destruct eqs1r3.
      rewrite eq_rect_ordinal. simpl. 
      rewrite eq_rect_ordinal. simpl. 
      unfold fintype.split. simpl.
      destruct (ltnP (s1 + s1') s1).
      * elim (not_s_lt s1 s1' i0).
      * erewrite <- (parent_proof_irrelevant b2 _).
      instantiate (1:=Ordinal (n:=s2) (m:=s1') (replace_in_H (erefl s2) s1' Hs1')).
      destruct get_parent; try reflexivity.
      unfold rearrange,fintype.split. simpl.
      destruct (ltnP s34 s3).
      ** destruct get_parent; try reflexivity.
      unfold extract1,bij_rew_forward.
      destruct o0.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP m s1).
      *** rewrite (Ordinal_proof_irrelevance s1 m _ i2).
      destruct get_parent; try reflexivity.
      destruct eqs1r3 as [eqs1r3].
      subst s1.
      elim (lt_ge_contradiction m r3 i1 i2).
      destruct get_parent; try reflexivity.
      unfold extract1,bij_rew_forward.
      destruct o0.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal. simpl. 
      destruct eqs1r3. subst s1.
      destruct (ltnP (r3 + m) r3).
      **** exfalso. elim (not_s_lt r3 m i2).
      **** erewrite <- (parent_proof_irrelevant b2 _).
      instantiate (1:= Ordinal (n:=s2) (m:=m) (replace_in_H (Logic.eq_sym eqxy) m i1)).
      destruct get_parent; try reflexivity.
  + apply functional_extensionality.
    destruct x as [[i' ipf]|p].
    - (*bijs l1234(i34) =l1324(i34)*)
      rewrite bij_subset_compose_id.
      rewrite bij_subset_compose_id.
      simpl.
      unfold bij_list_forward, sequence, switch_link, rearrange, parallel, extract1, funcomp.
      unfold bij_subset_forward.
      unfold permut_list_forward. 
      unfold link_juxt, bij_subset_backward.      
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      unfold union_possible in *.
      destruct (in_dec EqDecN i' i4).
      * (*bijs l1234(i4) =l1324(i4)*) 
      destruct get_link; try reflexivity.
      destruct s0 as [o' opf]. 
      destruct (in_dec EqDecN o' i2o4).
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i1). 
      destruct get_link; try reflexivity.
      *** exfalso. apply n. destruct p24 as [p24]. apply (p24 o'). assumption.
      * (*bijs l1234(i3) =l1324(i3)*)
      destruct get_link eqn:E; try reflexivity. 
      destruct s0 as [o' opf']. 
      destruct (in_dec EqDecN o' i2o4).
      *** 
      (* exfalso.  *)
      (* unfold Disjoint in dis_i12. *)
      (* apply (dis_i12 o'). *)
      pose opf' as opf''.
      unfold permutation in *. destruct p13 as [p13].
      apply (p13 o') in opf''.
      specialize (up12 (to_intersection o' opf'' i0)).
      unfold to_left, to_right, to_intersection in up12.
      rewrite <- (innername_proof_irrelevant b1 (from_intersection_left
      (in_both_in_intersection opf'' i0))).
      destruct get_link eqn:E'.
      **** rewrite <- (innername_proof_irrelevant b2 i0) in up12.      
      destruct (get_link (bg:=b2)
      (inl (exist (fun name : Name => In name i2o4) o' i0))).
      ++ f_equal. destruct s0. destruct s5. apply subset_eq_compat.
      simpl in up12. symmetry. apply up12.
      ++ exfalso. apply up12. 
      **** exfalso. apply up12.
      *** rewrite <- (innername_proof_irrelevant b1 (match PN_P p13 o' with
      | conj H _ => H
      end opf')).
      assert ((@exist Name (fun inner : Name => @In Name inner (ndlist i1o3)) o'
        (match
          @PN_P (@reverse_coercion NoDupList (list Name) o3i1 (ndlist o3i1))
            (@reverse_coercion NoDupList (list Name) i1o3 (ndlist i1o3)) p13 o'
          return
            (forall
                _ : @In Name o'
                      (ndlist (@reverse_coercion NoDupList (list Name) o3i1 (ndlist o3i1))),
              @In Name o'
                (ndlist (@reverse_coercion NoDupList (list Name) i1o3 (ndlist i1o3))))
        with
        | conj H _ => H
        end opf')) =
        (@exist Name (fun name : Name => @In Name name (ndlist i1o3)) o'
                    (match
                      @PN_P o3i1 i1o3 p13 o'
                      return (forall _ : @In Name o' (ndlist o3i1), @In Name o' (ndlist i1o3))
                    with
                    | conj H _ => H
                    end opf'))
        ). 
      auto.
      rewrite H.
      assert (
        @get_link s1 r1 i1o3 o1 b1
              (@inl (@sig Name (fun inner : Name => @In Name inner (ndlist i1o3)))
                 (@Port ( (@get_node s1 r1 i1o3 o1 b1)) (@get_control s1 r1 i1o3 o1 b1))
                 (@exist Name (fun name : Name => @In Name name (ndlist i1o3)) o'
                    (match
                       @PN_P o3i1 i1o3 p13 o'
                       return (forall _ : @In Name o' (ndlist o3i1), @In Name o' (ndlist i1o3))
                     with
                     | conj H0 _ => H0
                     end opf')))
          =
                     
        @get_link s1 r1 i1o3 o1 b1 
            (@inl (@sig Name (fun inner : Name => @In Name inner (ndlist i1o3)))
               (@Port ( (@get_node s1 r1 i1o3 o1 b1)) (@get_control s1 r1 i1o3 o1 b1))
               (@exist Name (fun name : Name => @In Name name (ndlist i1o3)) o'
                  (match
                     @PN_P o3i1 i1o3 p13 o'
                     return (forall _ : @In Name o' (ndlist o3i1), @In Name o' (ndlist i1o3))
                   with
                   | conj H0 _ => H0
                   end opf')))).
      auto.
      rewrite <- H.
      destruct (get_link (bg:=b1) (inl (exist (fun inner : Name => In inner i1o3) o' (match PN_P p13 o' with | conj H1 _ => H1 end opf')))) eqn:E'.
      **** f_equal.
      **** reflexivity.
    - (*bijs l1234(p34) =l1324(p34)*)
    unfold union_possible in *.
    destruct p as ([[v1 | v2] | [v3 | v4]], (i1234, Hvi1234)); unfold bij_join_port_backward; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward.
      unfold bij_rew_forward, funcomp.
      rewrite <- eq_rect_eq. simpl. unfold equal_f. unfold f_equal, eq_rect_r. 
      rewrite <- eq_rect_eq. simpl.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0.
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      destruct (in_dec EqDecN x i2o4).
      ** unfold permutation in *.
      pose i0 as i0'. destruct p13 as [p13].
      apply (p13 x) in i0'.
      clear Hvi1234.
      specialize (up12 (to_intersection x i0' i1)).
      unfold to_left, to_right, to_intersection in up12.
      rewrite <- (innername_proof_irrelevant b1 (match PN_P {| pn := p13 |} x with
      | conj H _ => H
      end i0)) in up12.
      destruct get_link eqn:E'.
      *** rewrite <- (innername_proof_irrelevant b2 i1) in up12.      
      destruct (get_link (bg:=b2)
      (inl (exist (fun name : Name => In name i2o4) x i1))).
      ++ f_equal. destruct s0. destruct s5. apply subset_eq_compat.
      simpl in up12. symmetry. apply up12.
      ++ exfalso. apply up12. 
      *** exfalso. apply up12.
      ** 
      assert (
        @get_link s1 r1 i1o3 o1 b1
              (@inl
                 (@sig Name (fun name : Name => @In Name name (ndlist i1o3)))
                 (@Port ( (@get_node s1 r1 i1o3 o1 b1))
                    (@get_control s1 r1 i1o3 o1 b1))
                 (@exist Name (fun name : Name => @In Name name (ndlist i1o3))
                    x
                    (@not_in_left x (ndlist i1o3) (ndlist i2o4)
                       (match
                          @PN_P (app_merge_NoDupList o3i1 o4i2)
                            (app_merge_NoDupList i1o3 i2o4)
                            (@permutation_distributive_PN o3i1 o4i2 i1o3 i2o4
                               p13 p24) x
                          return
                            (forall
                               _ : @In Name x
                                     (app_merge (ndlist o3i1) (ndlist o4i2)),
                             @In Name x
                               (app_merge (ndlist i1o3) (ndlist i2o4)))
                        with
                        | conj H _ => H
                        end (in_left_list x (ndlist o3i1) (ndlist o4i2) i0)) n)))
        =
        @get_link s1 r1 i1o3 o1 b1
            (@inl
               (@sig Name (fun inner : Name => @In Name inner (ndlist i1o3)))
               (@Port ( (@get_node s1 r1 i1o3 o1 b1))
                  (@get_control s1 r1 i1o3 o1 b1))
               (@exist Name (fun name : Name => @In Name name (ndlist i1o3)) x
                  (match
                     @PN_P o3i1 i1o3 p13 x
                     return
                       (forall _ : @In Name x (ndlist o3i1),
                        @In Name x (ndlist i1o3))
                   with
                   | conj H _ => H
                   end i0)))
      ). auto. 
      rewrite <- (innername_proof_irrelevant b1 (match PN_P p13 x with
      | conj H _ => H
      end i0)). auto.
      rewrite <- H.
      destruct get_link.
      **** f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
      **** reflexivity.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    *  unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      unfold permutation_distributive, permut_list_forward.
      destruct get_link; unfold rearrange; unfold extract1; simpl; try reflexivity.
      ** destruct s0.
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      destruct (in_dec EqDecN x i2o4).
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply n. destruct p24 as [p24]. apply (p24 x). assumption.
  Unshelve.
  apply val_inj;simpl. rewrite addnC. rewrite plus_minus. reflexivity.  
  apply val_inj;simpl. rewrite addnC. rewrite plus_minus. reflexivity.  
  Qed. 



(*Lemmas about decomposition bigraph_id*)
Lemma id_union : forall X Y:NoDupList, 
  bigraph_equality
  (bigraph_id 0 (X ∪ Y))
  ((bigraph_id 0 X) || (bigraph_id 0 Y)).
  Proof.
    intros X Y.
    unfold bigraph_id.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 (0+0) _ _ _ _ _ (bigraph_id 0 (X ∪ Y)) (bigraph_id 0 X || (bigraph_id 0 Y))
        erefl
        (permutation_id (X ∪ Y))
        erefl
        (permutation_id (X ∪ Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
    + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
    + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      destruct p. exfalso. rewrite addn0 in i0. elim (nlt_0_it m i0).
    + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

(* Packed parallel Product*)
Definition bigraph_packed_pp (b1 b2 : bigraph_packed)
  {HUP : UnionPossiblePacked b1 b2} := 
  packing ((big b1) || (big b2)).

Definition bigraph_packed_up_pair_pp (pp : bigraph_packed_up_pair) := 
  @bigraph_packed_pp (fst_ppair_pp pp) (snd_ppair_pp pp) (up_ppair_pp pp).


Add Parametric Morphism : bigraph_packed_up_pair_pp with
  signature bigraph_packed_up_pair_equality ==> bigraph_packed_equality as pp_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_up_pair_pp, bigraph_packed_pp.
  destruct x; destruct y; simpl.
  destruct 1.
  simpl in * |- *.
  apply bigraph_pp_congruence.
  + assumption.
  + assumption.
  Qed.

Notation "b1 [||] b2" := (bigraph_packed_up_pair_pp (Build_bigraph_packed_up_pair b1 b2)) (at level 50, left associativity).

Theorem bigraph_packed_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_pp bigraph_empty b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_pp_left_neutral.
  Qed.

Theorem bigraph_packed_pp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_pp b bigraph_empty) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_pp_right_neutral.
  Qed. 

Theorem bigraph_packed_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {HUP12 : UnionPossiblePacked b1 b2} 
  {HUP13 : UnionPossiblePacked b1 b3} 
  {HUP23 : UnionPossiblePacked b2 b3},
  bigraph_packed_equality 
    (bigraph_packed_pp (bigraph_packed_pp b1 b2) b3)
    (bigraph_packed_pp b1 (bigraph_packed_pp b2 b3)).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros. destruct HUP13. destruct HUP12. destruct HUP23. simpl in upp1. simpl in upp0. simpl in upp2.
  simpl.
  apply (@bigraph_pp_assoc s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 b1 b2 b3 upp1 upp2 upp0).
  Qed. 

End ParallelProduct.

