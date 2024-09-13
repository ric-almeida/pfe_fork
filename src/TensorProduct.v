Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Composition.
Require Import MathCompAddings.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.

From mathcomp Require Import all_ssreflect.


(** Disjoint juxtaposition/ Tensor Product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove existence of a unit, commutativity, associativity and congruence. *)
Module TensorProduct (s : SignatureParameter) (n : NamesParameter).
Module c := CompositionBigraphs s n.
Include c.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Definition FiniteParent_tensorproduct
  {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}
  {dis_i : i1 # i2} {dis_o : o1 # o2}
  {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2} : 
  FiniteParent 
    (((bij_id <+> bijection_inv bij_ord_sum) <o> 
    ((bij_sum_shuffle <o> (get_parent (bg:=b1) ||| get_parent (bg:=b2))) <o> 
    bijection_inv bij_sum_shuffle)) <o> (bij_id <+> bij_ord_sum)).
  Proof.
    rewrite <- tensor_alt.
    apply finite_parent_inout.
    apply finite_parent_tensor.
    + exact (@ap _ _ _ _ b1).
    + exact (@ap _ _ _ _ b2).
  Qed.

Definition bigraph_tensor_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {dis_i : i1 # i2}
  {dis_o : o1 # o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    : bigraph (s1 + s2) (i1 ∪ i2) (r1 + r2) (o1 ∪ o2)
    := 
    (@Big 
    (s1 + s2)
    (i1 ∪ i2) (*app_merge_id says it's eq to i1 ++ i2*)
    (r1 + r2)
    (o1 ∪ o2)
    ((get_node b1) + (get_node b2))%type
    ((get_edge b1) + (get_edge b2))%type
    (join (get_control (bg:= b1)) (get_control (bg:= b2)))
    ((bij_id <+> bijection_inv bij_ord_sum) <o>
      (bij_sum_shuffle <o> (parallel (get_parent (bg:=b1)) (get_parent (bg:=b2))) <o> (bijection_inv bij_sum_shuffle)) <o> 
      (bij_id <+> bij_ord_sum))
    (((@bij_list_names o1 o2 (DN_D dis_o)) <+> bij_id) <o>
      bij_sum_shuffle <o> (parallel (get_link (bg:= b1)) (get_link (bg:= b2))) <o> (bijection_inv bij_sum_shuffle) <o> 
      (bijection_inv ((@bij_list_names i1 i2 (DN_D dis_i)) <+> (bij_join_port (get_control (bg:= b1)) (get_control (bg:= b2))))))
      FiniteParent_tensorproduct
    ).
  (* 
  Defined.  *)

Global Notation "b1 ⊗ b2" := (bigraph_tensor_product b1 b2) (at level 50, left associativity).

(** Section on neutal element for tensor product*)
Section M2.
Lemma arity_tp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bg:=∅ ⊗ b) (bijection_inv bij_void_sum_neutral n)) =  Arity (get_control (bg:=b) n).
  Proof.
  intros s i r o b n.
  unfold bijection_inv. simpl. 
  reflexivity.
  Qed.

Theorem bigraph_tp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality b (∅ ⊗ b).
  Proof.
  intros s i r o b.
  apply (BigEq s r s r i o (EmptyNDL ∪ i) (EmptyNDL ∪ o) b (∅ ⊗ b)
    erefl
    (left_empty i)
    erefl
    (left_empty o)
    (bijection_inv bij_void_sum_neutral)
    (bijection_inv bij_void_sum_neutral)
    (fun n => bij_rew (arity_tp_left_neutral b n)) 
    ). 
  + apply functional_extensionality.
    intros [v|x]. 
    - elim v.
    - unfold bijection_inv. simpl. unfold funcomp. 
    reflexivity. 
  + apply functional_extensionality. 
    destruct x as [[v|n1] | s1]; simpl. 
    - elim v.
    - unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal. apply val_inj. reflexivity.
    - unfold funcomp, parallel, sum_shuffle.
      simpl.
      destruct s1; simpl. 
      symmetry.
      erewrite <- (parent_proof_irrelevant b _ ).
      instantiate (1:= (Ordinal (n:=s) (m:=m) i0)).
      unfold surj_ord_add, split.
      destruct (ltnP (@nat_of_ord (addn O s) (@Ordinal s m i0)) O).
      exfalso. auto.
      erewrite <- (parent_proof_irrelevant b _ ).
      instantiate (1:= (Ordinal (n:=s) (m:=m) i0)).
      destruct get_parent; try reflexivity. f_equal.
      unfold unsplit.
      unfold rshift.
      apply val_inj. reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | ([v|v1], (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl. 
      destruct i1 as [iname1 Hiname1]. 
      rewrite <- (innername_proof_irrelevant b Hiname1).
      symmetry.
      rewrite <- (innername_proof_irrelevant b Hiname1).
      simpl. symmetry. destruct get_link; try reflexivity. 
      f_equal. destruct s0. simpl. apply subset_eq_compat. reflexivity.
    - exfalso. simpl in v. destruct v. 
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl. 
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Unshelve. apply val_inj.
  reflexivity.
  apply val_inj.
  simpl. rewrite subn0.
  reflexivity.
  Qed.

Lemma arity_tp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bg:= b ⊗ ∅) n) = 
  Arity (get_control (bg:=b) (bij_void_sum_neutral_r n)).
  Proof.
    intros s i r o b n.
    destruct n as [ n | v].
    + reflexivity.
    + destruct v.
  Qed.
  
Theorem bigraph_tp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (b ⊗ ∅) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b ⊗ ∅) b
    (addn0 _)
    (right_empty i)
    (addn0 _)
    (right_empty o)
    bij_void_sum_neutral_r
    bij_void_sum_neutral_r
    (fun n => bij_rew (arity_tp_right_neutral b n)) 
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward.
      simpl. unfold lshift. simpl.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity.
    - unfold funcomp, parallel.
      simpl.
      destruct s1; simpl.
      unfold bij_rew_forward, split, unsplit, sum_shuffle.
      simpl. rewrite eq_rect_ordinal.
      simpl. destruct (ltnP m s).
      rewrite (Ordinal_proof_irrelevance s m i0).
      destruct get_parent; try reflexivity.
    - f_equal. destruct o0.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity.
    - exfalso. apply (lt_ge_contradiction m s); assumption.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.       
      destruct i1 as [iname1 Hiname1].
      destruct (in_dec EqDecN iname1 i).
      * rewrite <- (innername_proof_irrelevant b Hiname1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * exfalso. apply n. apply Hiname1.
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. 
      apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Qed.
End M2.

(** Section on associativity of tensor product*)
Section M1.
Lemma arity_tp_assoc : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  {dis_i12 : i1 # i2} {dis_i23 : i2 # i3} {dis_i13 : i1 # i3}
  {dis_o12 : o1 # o2} {dis_o23 : o2 # o3} {dis_o13 : o1 # o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) n12_3,
  Arity (get_control (bg:=(b1 ⊗ b2) ⊗ b3) n12_3) 
  = 
  Arity (get_control (bg:=b1 ⊗ (b2 ⊗ b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_tp_assoc : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  {dis_i12 : i1 # i2} {dis_i23 : i2 # i3} {dis_i13 : i1 # i3}
  {dis_o12 : o1 # o2} {dis_o23 : o2 # o3} {dis_o13 : o1 # o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_equality
    ((b1 ⊗ b2) ⊗ b3) 
    (b1 ⊗ (b2 ⊗ b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 ⊗ b2) ⊗ b3) (b1 ⊗ (b2 ⊗ b3))
    (esym (addnA _ _ _))
    in_app_merge_transi
    (esym (addnA _ _ _))
    in_app_merge_transi
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (arity_tp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | s1_23']; simpl; unfold funcomp; simpl.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,lshift.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,rshift.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity.
    - destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward,rshift. simpl. 
      rewrite eq_rect_ordinal.
      apply val_inj. simpl. 
      rewrite addnA. reflexivity.
    - unfold parallel,sum_shuffle,split,unsplit,bij_rew_forward. 
      destruct s1_23'. rewrite eq_rect_ordinal. 
      simpl. 
      destruct (ltnP m (s1 + s2));
      destruct (ltnP m s1); simpl.
      destruct (ltnP m s1); simpl.
      rewrite (Ordinal_proof_irrelevance s1 m i5).
      destruct get_parent; try reflexivity.
      f_equal. unfold lshift.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity.
      exfalso. apply (lt_ge_contradiction m s1); assumption.
      destruct (ltnP m s1); simpl in i5.
      exfalso. apply (lt_ge_contradiction m s1); assumption.
      destruct (ltnP (m - s1) s2).
      simpl.
      erewrite (Ordinal_proof_irrelevance s2 (m-s1) _).
      instantiate (1:=i7).
      destruct get_parent; try reflexivity.
      unfold lshift,rshift.
      f_equal.
      rewrite eq_rect_ordinal.
      apply val_inj. simpl. reflexivity.
      exfalso.
      apply (lt_ge_contradiction m (s1+s2)); try assumption.
      set (H := leq_subRL s2 i5).
      rewrite <- H.
      apply i7.
      exfalso.
      apply leq_addl_trans in i4.
      apply (lt_ge_contradiction m s1); try assumption.
      destruct (ltnP (m - s1) s2).
      exfalso.
      apply (lt_ge_contradiction m (s1+s2)); try assumption.
      rewrite addnC.
      apply minus_lt. apply i6.
      erewrite (Ordinal_proof_irrelevance s3 (m- s1 - s2) _).
      erewrite (Ordinal_proof_irrelevance s3 (m - (s1 + s2)) _).
      simpl.
      eassert (Ordinal (n:=s3) (m:=m - (s1 + s2)) ?[i10] = 
      Ordinal (n:=s3) (m:=m - s1 - s2) ?[i1]).
      apply val_inj. simpl. apply subnDA.
      rewrite H.
      instantiate (1:=(split_subproof (m:=s2) (n:=s3) (i:=Ordinal (n:=s2 + s3) (m:=m - s1) (split_subproof (m:=s1) (n:=s2 + s3) (i:=Ordinal (n:=s1 + (s2 + s3)) (m:=m) i0) i5)) i6)).
      instantiate (1:=(split_subproof (m:=s2) (n:=s3) (i:=Ordinal (n:=s2 + s3) (m:=m - s1) (split_subproof (m:=s1) (n:=s2 + s3) (i:=Ordinal (n:=s1 + (s2 + s3)) (m:=m) i0) i5)) i6)).
      destruct get_parent;try reflexivity.
      f_equal. 
      unfold rshift. destruct o0.
      rewrite eq_rect_ordinal.
      apply val_inj. simpl. rewrite addnA. reflexivity.
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
       simpl. 
      destruct (in_dec EqDecN i123 (app_merge i1 i2)).
      * destruct (in_dec EqDecN i123 i1).
      destruct get_link; try reflexivity.
      ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).
      *** rewrite <- (innername_proof_irrelevant b2 i5).      
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_iff in i4. destruct i4. apply n. apply H. apply n0. apply H.
      * destruct (in_dec EqDecN i123 i1).
      ** exfalso. apply n. apply in_left_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_right_list. apply i4.
      *** 
      set (Hn' := match
        in_app_or_m_nod_dup (app_merge i1 i2) i3 i123 (NoDup_app_merge i1 i2 (nd i1) (nd i2))
          (match
            i3 as n2
            return ((In i123 (app_merge i1 i2) -> ~ In i123 n2) -> In i123 (app_merge (app_merge i1 i2) n2) -> NoDup n2)
          with
          | {| ndlist := ndlist0; nd := nd0 |} =>
              fun (_ : In i123 (app_merge i1 i2) -> ~ In i123 ndlist0) (_ : In i123 (app_merge (app_merge i1 i2) ndlist0))
              => nd0
          end (DN_D (disj_app_left i1 i2 i3 dis_i13 dis_i23) i123)
            (in_app_merge_trans i123 (eq_ind_r (fun b : Name => In b (app_merge i1 (app_merge i2 i3))) i0 erefl)))
          (in_app_merge_trans i123 (eq_ind_r (fun b : Name => In b (app_merge i1 (app_merge i2 i3))) i0 erefl))
        with
        | inl i4 => False_ind (In i123 i3) (n i4)
        | inr i4 => i4
        end).
      symmetry. rewrite <- (innername_proof_irrelevant b3 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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
    Unshelve.
      + rewrite subnDA. 
      destruct s3.
      * exfalso.
      rewrite addn0 in i0.
      apply (lt_ge_contradiction m (s1+s2)); try assumption.
      * rewrite ltn_psubLR.
      erewrite <- (ltn_psubLR _ ) in i0.
      apply i0.
      * apply ltn_addl.
      apply ltn0Sn.
      apply ltn0Sn.
      + rewrite subnDA. 
      destruct s3.
      * exfalso.
      rewrite addn0 in i0.
      apply (lt_ge_contradiction m (s1+s2)); try assumption.
      * rewrite ltn_psubLR.
      erewrite <- (ltn_psubLR _ ) in i0.
      apply i0.
      * apply ltn_addl.
      apply ltn0Sn.
      apply ltn0Sn.
  Qed.
End M1.

(** Congruence of TP*)
Definition arity_tp_congruence_forward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection ((get_node b1)) ((get_node b2))) (bij_n34 : bijection ((get_node b3)) ((get_node b4)))
  (bij_p12 : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:= b1) n1))) ('I_(Arity (get_control (bg:= b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 : (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 : (get_node (b1 ⊗ b3))) :
  ('I_(Arity (get_control (bg:=b1 ⊗ b3) n13))) -> ('I_(Arity (get_control (bg:=b2 ⊗ b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_tp_congruence_backward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection ((get_node b1)) ((get_node b2))) (bij_n34 : bijection ((get_node b3)) ((get_node b4)))
  (bij_p12 : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:= b1) n1))) ('I_(Arity (get_control (bg:= b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 : (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 : (get_node (b1 ⊗ b3))) :
  ('I_(Arity (get_control (bg:=b2 ⊗ b4) ((bij_n12 <+> bij_n34) n13)))) -> ('I_(Arity (get_control (bg:=b1 ⊗ b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_tp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection ((get_node b1)) ((get_node b2))) (bij_n34 : bijection ((get_node b3)) ((get_node b4)))
  (bij_p12 : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:= b1) n1))) ('I_(Arity (get_control (bg:= b2) (bij_n12 n1)))))
  (bij_p34 : forall (n3 : (get_node b3)), bijection ('I_(Arity (get_control (bg:=b3) n3))) ('I_(Arity (get_control (bg:=b4) (bij_n34 n3)))))
  (n13 : (get_node (b1 ⊗ b3))),
  bijection ('I_(Arity (get_control (bg:=b1 ⊗ b3) n13))) ('I_(Arity (get_control (bg:=b2 ⊗ b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ (arity_tp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) (arity_tp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
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

Theorem bigraph_tp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4),
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> 
    bigraph_equality 
      (b1 ⊗ b3) 
      (b2 ⊗ b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b3) (b2 ⊗ b4)
    (f_equal2_plus _ _ _ _ bij_s12 bij_s34)
    (app_merge_cong bij_i12 bij_i34)
    (f_equal2_plus _ _ _ _ bij_r12 bij_r34)
    (app_merge_cong bij_o12 bij_o34)
    (bij_n12 <+> bij_n34)
    (bij_e12 <+> bij_e34)
    (arity_tp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
    ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2' | n4'] | s24']; simpl; unfold funcomp; simpl.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward.
      unfold lshift.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal.
      apply val_inj. reflexivity. 
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct o0; simpl.
      f_equal.
      unfold bij_rew_forward.
      unfold rshift,lshift.
      rewrite eq_rect_ordinal.
      rewrite eq_rect_ordinal.
      apply val_inj. simpl. rewrite bij_r12. reflexivity. 
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel, bij_rew_forward, split, unsplit, sum_shuffle.
      destruct s24'.
      simpl.
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP m s1); destruct (ltnP m s2).
      * rewrite eq_rect_ordinal. symmetry.
        erewrite (Ordinal_proof_irrelevance s1 m _).
        instantiate (1:= i5).
        destruct get_parent; try reflexivity. destruct o0.
        rewrite eq_rect_ordinal.
        rewrite eq_rect_ordinal.
        unfold rshift,lshift. f_equal.
        apply val_inj. reflexivity. 
      * exfalso. rewrite bij_s12 in i5.
        apply (lt_ge_contradiction m s2); assumption.
      * exfalso. rewrite bij_s12 in i5.
        apply (lt_ge_contradiction m s2); assumption.
      * rewrite <- big_parent_eq34.
        simpl.
        unfold parallel, funcomp, bij_rew_forward.
        rewrite eq_rect_ordinal.
        subst s1. subst s4.
        symmetry. rewrite (Ordinal_proof_irrelevance s3 (m-s2) (split_subproof (m:=s2) (n:=s3) (i:=Ordinal (n:=s2 + s3) (m:=m) (replace_in_H (Logic.eq_sym (f_equal2_plus s2 s2 s3 s3 (erefl s2) (erefl s3))) m i0)) i5)).
        destruct s3.
        * exfalso.
        rewrite addn0 in i0.
        apply (lt_ge_contradiction m s2); try assumption.
        * rewrite ltn_psubLR.
        apply i0.
        * apply ltn0Sn.
      * intros.
        erewrite (Ordinal_proof_irrelevance s3 (m-s2) _).
        instantiate (1:=Hyp0).
        destruct get_parent; simpl; try reflexivity.
        f_equal.
        destruct o0.
        unfold rshift,lshift.
        rewrite eq_rect_ordinal.
        rewrite eq_rect_ordinal.
        apply val_inj;simpl. subst r2. reflexivity.
  + apply functional_extensionality.
    destruct x as [[i24] | ([n2' | n4'], (i', Hi'))]; simpl.
    - rewrite <- big_link_eq12.
      simpl.
      unfold funcomp.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.      
      destruct (in_dec EqDecN i24 i1).
      * (*link i1 = link i2 *) 
      destruct (in_dec EqDecN i24 i2).
      ** 
      set (Hn' := 
        match bij_i12 i24 with
        | conj _ H => H
        end (eq_ind_r (fun b : Name => In b i2) i6 erefl)).
      rewrite (innername_proof_irrelevant b1 i5 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. apply bij_i12. apply i5.
      * (*link i2 = link i1 *)  
      destruct (in_dec EqDecN i24 i2).
      ** exfalso. apply n. apply bij_i12. apply i5.
      **  
      set (Hn' := match
          in_app_or_m_nod_dup i1 i3 i24
            (match i1 as n1 return ((In i24 n1 -> ~ In i24 i3) -> In i24 (app_merge n1 i3) -> ~ In i24 n1 -> NoDup n1) with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 ndlist0 -> ~ In i24 i3) (_ : In i24 (app_merge ndlist0 i3)) (_ : ~ In i24 ndlist0) => nd0
            end (DN_D dis_i13 i24)
              (match app_merge_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge i2 i4)) i0 erefl)) n)
            (match i3 as n1 return ((In i24 i1 -> ~ In i24 n1) -> In i24 (app_merge i1 n1) -> NoDup n1) with
            | {| ndlist := ndlist0; nd := nd0 |} => fun (_ : In i24 i1 -> ~ In i24 ndlist0) (_ : In i24 (app_merge i1 ndlist0)) => nd0
            end (DN_D dis_i13 i24)
              (match app_merge_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge i2 i4)) i0 erefl)))
            (match app_merge_cong bij_i12 bij_i34 i24 with
            | conj _ H => H
            end (eq_ind_r (fun b : Name => In b (app_merge i2 i4)) i0 erefl))
        with
        | inl i5 => False_ind (In i24 i3) (n i5)
        | inr i5 => i5
        end).
      rewrite <- big_link_eq34.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
      
      symmetry. rewrite <- (innername_proof_irrelevant b3 Hn'). 
      destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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
      instantiate (1 := esym (equal_f (fob_id ((get_node b1)) ((get_node b2)) bij_n12) n2')).
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
      instantiate (1 := esym (equal_f (fob_id ((get_node b3)) ((get_node b4)) bij_n34) n4')).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) n4'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity.
  Qed.


(** Bifunctorial property*)
Section M3.
Theorem arity_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 r3 r4 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2) 
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {eqs2r4 : MyEqNat s2 r4} {eqs1r3 : MyEqNat s1 r3} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  (n12_34 : (get_node (b1 ⊗ b2 <<o>> (b3 ⊗ b4)))),
  Arity (get_control
    (bg:=(b1 ⊗ b2) <<o>> (b3 ⊗ b4)) n12_34) =
  Arity (get_control 
    (bg:=((b1 <<o>> b3) ⊗ (b2 <<o>> b4))) 
    (sum_shuffle n12_34)).
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.



Theorem bigraph_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r3 r4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2)
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {eqs2r4 : MyEqNat s2 r4} {eqs1r3 : MyEqNat s1 r3} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)},
  bigraph_equality 
  ((b1 ⊗ b2) <<o>> (b3 ⊗ b4))
  ((b1 <<o>> b3) ⊗ (b2 <<o>> b4)).
  Proof.
  intros.
  apply (BigEq
    _ _ _ _
    _ _ _ _ 
    ((b1 ⊗ b2) <<o>> (b3 ⊗ b4)) 
    ((b1 <<o>> b3) ⊗ (b2 <<o>> b4))
    (reflexivity (s3 + s4)) (*s3 + s4*)
    reflnames (*i3 + i4*)
    (reflexivity (r1 + r2)) (*r1 + r2*)
    reflnames (*o1 + o2*)
    bij_sum_shuffle(* n1 + n2 + n3 + n4*)
    bij_sum_shuffle (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (arity_comp_tp_dist b1 b2 b3 b4 n12_34)) (* Port *)
    ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality. rewrite bij_rew_id. rewrite bij_rew_id. simpl. 
    unfold funcomp; simpl; unfold sequence, extract1, inject, sum_shuffle, parallel.
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
      symmetry.
      erewrite (Ordinal_proof_irrelevance s1 s1' _).
      instantiate (1:=  Hs1').
      destruct get_parent; try reflexivity.
    - destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. destruct get_parent; try reflexivity. 
      unfold bij_rew_forward.
      destruct o0 as (s1', Hs1').
      destruct eqs2r4 as [eqs2r4].
      destruct eqs1r3 as [eqs1r3].
      destruct eqs2r4.
      destruct eqs1r3.
      unfold split.
      rewrite eq_rect_ordinal. 
      rewrite eq_rect_ordinal.
      simpl. 
      destruct (ltnP (s1 + s1') s1).
      * exfalso. apply not_s_lt in i0. apply i0. 
      * assert (
          @Ordinal s2 (subn (addn s1 s1') s1) (@split_subproof s1 s2 (@Ordinal (addn s1 s2) (addn s1 s1') (@replace_in_H (addn s1 s2) (addn s1 s2) (@Logic.eq_sym nat (addn s1 s2) (addn s1 s2) (@eqxy (addn s1 s2) (addn s1 s2) (@MyEqNat_add_bis s1 s1 s2 s2 (Build_MyEqNat s2 s2 (@Logic.eq_refl nat s2)) (Build_MyEqNat s1 s1 (@Logic.eq_refl nat s1))))) (addn s1 s1') (@rshift_subproof s1 s2 (@Ordinal s2 s1' Hs1')))) i0) =
          @Ordinal s2 s1' (@replace_in_H s2 s2 (@Logic.eq_refl nat s2) s1' Hs1')).
      ** apply val_inj. simpl.
      rewrite subDnCA.
      rewrite subnn.
      rewrite addn0. reflexivity. apply leqnn.
      ** rewrite H. 
      destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. 
      destruct eqs2r4 as [eqs2r4].
      destruct eqs1r3 as [eqs1r3].
      destruct eqs2r4.
      destruct eqs1r3.
      unfold split. simpl.
      destruct (ltnP s34 s3).
    * destruct get_parent; try reflexivity. destruct o0.
      unfold bij_rew_forward.
      rewrite eq_rect_ordinal. 
      simpl.
      destruct (ltnP m s1). symmetry.
      erewrite (Ordinal_proof_irrelevance s1 m _).
      instantiate (1:= i2).
      destruct get_parent; try reflexivity.
      exfalso. apply (lt_ge_contradiction m s1); assumption. 
    * destruct get_parent; try reflexivity. destruct o0.
      unfold bij_rew_forward.
      rewrite eq_rect_ordinal. simpl.
      destruct (ltnP (s1 + m) s1).
      ** exfalso. apply (not_s_lt s1 m); try assumption.
      ** erewrite <- (parent_proof_irrelevant b2).
      instantiate (1 := (Ordinal (n:=s2) (m:=m) i1)).
      destruct get_parent; try reflexivity.
      apply val_inj. simpl.
      rewrite subDnCA.
      rewrite subnn.
      rewrite addn0. reflexivity. apply leqnn.
  + apply functional_extensionality.
    destruct x as [[i']|p]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    - unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
      destruct (in_dec EqDecN i' i3).
      * destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0 as [n npf]. 
      destruct (in_dec EqDecN n i1o3).
      *** symmetry.
      rewrite <- (innername_proof_irrelevant b1 i2).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply n0.
      destruct p13 as [p13].
      destruct p24 as [p24].
      unfold permutation in p13. destruct (p13 n). apply H. apply npf.
      * unfold permutation_distributive, permut_list_forward.
      set (Hn := 
        match
          in_app_or_m_nod_dup i3 i4 i'
            (match
              i3 as n0 return ((In i' n0 -> ~ In i' i4) -> In i' (app_merge n0 i4) -> ~ In i' n0 -> NoDup n0)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i' ndlist0 -> ~ In i' i4) (_ : In i' (app_merge ndlist0 i4)) (_ : ~ In i' ndlist0) =>
                nd0
            end (DN_D dis_i34 i') i0 n)
            (match i4 as n0 return ((In i' i3 -> ~ In i' n0) -> In i' (app_merge i3 n0) -> NoDup n0) with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i' i3 -> ~ In i' ndlist0) (_ : In i' (app_merge i3 ndlist0)) => nd0
            end (DN_D dis_i34 i') i0) i0
        with
        | inl i1 => False_ind (In i' i4) (n i1)
        | inr i1 => i1
        end).
      rewrite <- (innername_proof_irrelevant b4 Hn).
      destruct get_link; try reflexivity. 
      destruct s0 as [n' npf']. 
      destruct (in_dec EqDecN n' i1o3).
      *** exfalso. set (dis_i12' := DN_D dis_i12). unfold Disjoint in dis_i12'. specialize (dis_i12' n'). apply dis_i12'; try assumption.
      destruct p24 as [p24].
      unfold permutation in p24. destruct (p24 n'). apply H; assumption.
      ***
      rewrite <- (innername_proof_irrelevant b2 (match PN_P p24 n' with
      | conj H _ => H
      end npf')).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - destruct p as ([[v1 | v2] | [v3 | v4]], (i1234, Hvi1234)); unfold bij_join_port_backward; simpl.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0.
      destruct (in_dec EqDecN x i1o3).
      ** symmetry.
      rewrite <- (innername_proof_irrelevant b1 i1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. 
      destruct p13 as [p13].
      destruct p24 as [p24].
      unfold permutation in p13. destruct (p13 x). apply H; assumption.
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
      destruct get_link; unfold rearrange; unfold extract1; simpl.
      ** destruct s0.
      destruct (in_dec EqDecN x i1o3).
      *** exfalso. set (dis_i12' := DN_D dis_i12). unfold Disjoint in dis_i12'. specialize (dis_i12' x).
      apply dis_i12'; try assumption.
      destruct p13 as [p13].
      destruct p24 as [p24].
      unfold permutation in p24. destruct (p24 x). apply H; assumption. 
      ***
      rewrite <- (innername_proof_irrelevant b2 (match PN_P p24 x with
      | conj H _ => H
      end i0)).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** reflexivity.
  Qed.
End M3.

(** Small lemma about the merge bigraph*)
Theorem merge_well_defined : forall n, 
  bigraph_equality
    (@merge (n+1))
    (join_big <<o>> (@bigraph_id 1 EmptyNDL ⊗ @merge n)).
  Proof. 
    intros. simpl. 
    refine (BigEq _ _ _ _ _ _ _ _ 
      (@merge (n+1))
      (join_big <<o>> (@bigraph_id 1 EmptyNDL ⊗ @merge n))
      (addnC n 1)
      (PN_P permutation_id_am_l_PN_empty_r)
      erefl
      (PN_P permutation_id_am_l_PN_empty)
      bij_void_sum_sum
      bij_void_sum_sum
      _ _ _ _ 
    ). 
    - simpl. apply functional_extensionality. destruct x as [v|[v|v]]; destruct v. 
    - simpl. apply functional_extensionality. destruct x as [[v|[v|v]]|s]; try destruct v.
    simpl. unfold parallel, funcomp, rearrange, sum_shuffle, extract1, bij_rew_forward. destruct s. 
    unfold split. simpl. destruct (ltnP m 1); reflexivity. 
    - simpl. apply functional_extensionality. destruct x as [v|s]; try destruct v.
    + elim f. 
    + destruct s. destruct x as [v|[v|v]]; destruct v. 
    Unshelve. 
    * exact nat. * exact nat. 
    * intros. simpl in n1. destruct n1. 
  Qed.
  


(*Section for Packed Tensor Product*)
Section PTP.
Class DisjointNamesPacked (b1 b2 : bigraph_packed) :=
  { disj_inner :: DisjointNames (i b1) (i b2);
    disj_outer :: DisjointNames (o b1) (o b2)
  }.
  
#[export] Instance disj_packed (b1 b2 : bigraph_packed) (Disji12 : DisjointNames (i b1) (i b2)) (Disjo12 : DisjointNames (o b1) (o b2)) : 
  DisjointNamesPacked b1 b2.
  Proof.
  constructor.
  + exact Disji12.
  + exact Disjo12.
  Qed.
  
Record bigraph_packed_disjoint_pair :=
  { 
    fst_ppair_tp  : bigraph_packed;
    snd_ppair_tp  : bigraph_packed;
    disj_ppair_tp :: DisjointNamesPacked fst_ppair_tp snd_ppair_tp
  }.
Arguments Build_bigraph_packed_disjoint_pair _ _ {disj_ppair_tp}. (*What does this do?*)
  
Record bigraph_packed_disjoint_pair_equality (pp1 pp2 : bigraph_packed_disjoint_pair) : Prop :=
  { 
    fst_ppair_tp_equ : bigraph_packed_equality (fst_ppair_tp pp1) (fst_ppair_tp pp2);
    snd_ppair_tp_equ : bigraph_packed_equality (snd_ppair_tp pp1) (snd_ppair_tp pp2)
  }. (*Why 4 bigraphs?*)
  
Lemma bigraph_packed_disjoint_pair_equality_refl (pp : bigraph_packed_disjoint_pair) :
  bigraph_packed_disjoint_pair_equality pp pp.
  Proof.
  constructor.
  + apply bigraph_equality_refl.
  + apply bigraph_equality_refl.
  Qed.
  
Lemma bigraph_packed_disjoint_pair_equality_sym (pp1 pp2 : bigraph_packed_disjoint_pair):
  bigraph_packed_disjoint_pair_equality pp1 pp2 -> bigraph_packed_disjoint_pair_equality pp2 pp1.
  Proof.
  intros H12.
  constructor.
  + symmetry.
    apply (fst_ppair_tp_equ _ _ H12).
  + symmetry.
    apply (snd_ppair_tp_equ _ _ H12).
  Qed.
  
Lemma bigraph_packed_disjoint_pair_equality_trans (pp1 pp2 pp3 : bigraph_packed_disjoint_pair):
  bigraph_packed_disjoint_pair_equality pp1 pp2 -> bigraph_packed_disjoint_pair_equality pp2 pp3 ->
    bigraph_packed_disjoint_pair_equality pp1 pp3.
  Proof.
  intros H12 H23.
  constructor.
  + etransitivity.
    - apply (fst_ppair_tp_equ _ _ H12).
    - apply (fst_ppair_tp_equ _ _ H23).
  + etransitivity.
    - apply (snd_ppair_tp_equ _ _ H12).
    - apply (snd_ppair_tp_equ _ _ H23).
  Qed.
  
Add Parametric Relation : 
  bigraph_packed_disjoint_pair bigraph_packed_disjoint_pair_equality
  reflexivity proved by (bigraph_packed_disjoint_pair_equality_refl)
  symmetry proved by (bigraph_packed_disjoint_pair_equality_sym)
  transitivity proved by (bigraph_packed_disjoint_pair_equality_trans)
    as bigraph_packed_disjoint_pair_equality_rel.
    
Definition bigraph_packed_tp (b1 b2 : bigraph_packed)
  {Hdisj12 : DisjointNamesPacked b1 b2} := 
  packing ((big b1) ⊗ (big b2)).

Definition bigraph_packed_disjoint_pair_tp (pp : bigraph_packed_disjoint_pair) := 
  @bigraph_packed_tp (fst_ppair_tp pp) (snd_ppair_tp pp) (disj_ppair_tp pp).

Add Parametric Morphism : bigraph_packed_disjoint_pair_tp with
  signature bigraph_packed_disjoint_pair_equality ==> 
  bigraph_packed_equality as tp_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_disjoint_pair_tp, bigraph_packed_tp.
  destruct x; destruct y; simpl.
  destruct 1.
  simpl in * |- *.
  apply bigraph_tp_congruence.
  + assumption.
  + assumption.
  Qed.
End PTP.
End TensorProduct.