Require Import ConcreteBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import Composition.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.



(** Disjoint juxtaposition/ Tensor Product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove existence of a unit, commutativity, associativity and congruence. *)
Module TensorProduct (s : Signature) (n : Names) (b: Bigraphs s n).
Module c := CompositionBigraphs s n b.
Include c.

Definition bigraph_tensor_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {dis_i : i1 # i2}
  {dis_o : o1 # o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2).
  Proof. 
  apply (Big 
    (s1 + s2)
    (app_merge_NoDupList i1 i2) (*app_merge'_id says it's eq to i1 ++ i2*)
    (r1 + r2)
    (app_merge_NoDupList o1 o2)
    (findec_sum (get_node b1) (get_node b2))
    (findec_sum (get_edge b1) (get_edge b2))
    (join (get_control b1) (get_control b2))
    ((bij_id <+> bijection_inv bij_fin_sum) <o>
      (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle)) <o> 
      (bij_id <+> bij_fin_sum))
    (((@bij_list_names o1 o2 dis_o) <+> bij_id) <o>
      bij_sum_shuffle <o> (parallel (get_link b1) (get_link b2)) <o> (bijection_inv bij_sum_shuffle) <o> 
      (bijection_inv ((@bij_list_names i1 i2 dis_i) <+> (bij_join_port (get_control b1) (get_control b2)))))
    ).
  rewrite <- tensor_alt.
  apply finite_parent_inout.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined. 

Global Notation "b1 ⊗ b2" := (bigraph_tensor_product b1 b2) (at level 50, left associativity).


Lemma arity_tp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_tensor_product (dis_i := void_disjoint_all_list_left i) (dis_o := void_disjoint_all_list_left o) ∅ b) n) = 
  Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_tp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_tensor_product (dis_i := void_disjoint_all_list_left i) (dis_o := void_disjoint_all_list_left o) ∅ b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ ⊗ b) b
    eq_refl
    (left_empty i)
    eq_refl
    (left_empty o)
    bij_void_sum_neutral
    bij_void_sum_neutral
    (fun n => bij_rew (P := fin) (arity_tp_left_neutral b n)) 
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      apply subset_eq_compat; reflexivity.
    - unfold funcomp, parallel.
      simpl.
      destruct s1; simpl.
      destruct PeanoNat.Nat.ltb_spec0; simpl.
      * elim (PeanoNat.Nat.nlt_0_r _ l0).
      * erewrite (subset_eq_compat _ _ (x - 0) x _ _ (PeanoNat.Nat.sub_0_r x)).
        instantiate (1 := l).
        destruct get_parent; try reflexivity.
        destruct f; simpl.
        f_equal.
        apply subset_eq_compat.
        reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. 
      destruct i1 as [iname1 Hiname1].
      rewrite <- (innername_proof_irrelevant b iname1 Hiname1).
      simpl. destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp, id.
      simpl.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Qed.

Lemma arity_tp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_tensor_product (dis_i := void_disjoint_all_list_right i) (dis_o := void_disjoint_all_list_right o) b ∅) n) = 
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [ n | v].
  + reflexivity.
  + destruct v.
  Qed.
  
Theorem bigraph_tp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_tensor_product (dis_i := void_disjoint_all_list_right i) (dis_o := void_disjoint_all_list_right o) b ∅) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b ⊗ ∅) b
    (PeanoNat.Nat.add_0_r _)
    (right_empty i)
    (PeanoNat.Nat.add_0_r _)
    (right_empty o)
    bij_void_sum_neutral_r
    bij_void_sum_neutral_r
    (fun n => bij_rew (P := fin) (arity_tp_right_neutral b n)) 
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + 0) r _ x _).
      apply subset_eq_compat; reflexivity.
    - unfold funcomp, parallel.
      simpl.
      destruct s1; simpl.
      unfold bij_rew_forward, inj_fin_add.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) s (s + 0) _ x _).
      destruct PeanoNat.Nat.ltb_spec0; simpl.
      * rewrite (proof_irrelevance _ l0 l).
        destruct get_parent; simpl; try reflexivity.
        destruct f; simpl.
        f_equal.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + 0) r _ x0 _).
        apply subset_eq_compat.
        reflexivity.
      * contradiction.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. 
      destruct i1 as [iname1 Hiname1].
      destruct (in_dec EqDecN iname1 i).
      * rewrite <- (innername_proof_irrelevant b iname1 Hiname1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * exfalso. apply n. apply Hiname1.
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp, id.
      simpl.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. 
      apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Qed.

Lemma arity_tp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} 
 {dis_i : i1 # i2} {dis_o : o1 # o2} 
 (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) n12,
  Arity (get_control (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) n12) = Arity (get_control (bigraph_tensor_product (dis_i:= rev_disjoint dis_i) (dis_o := rev_disjoint dis_o) b2 b1) (bij_sum_comm n12)).
  Proof.
  intros until n12.
  destruct n12.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_tp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} 
  {dis_i : i1 # i2} {dis_o : o1 # o2}   
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  bigraph_equality 
    (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) 
    (bigraph_tensor_product (dis_i:= rev_disjoint dis_i) (dis_o := rev_disjoint dis_o) b2 b1).
  Proof.
  intros.
Abort. 

Lemma arity_tp_assoc : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  {dis_i12 : i1 # i2} {dis_i23 : i2 # i3} {dis_i13 : i1 # i3}
  {dis_o12 : o1 # o2} {dis_o23 : o2 # o3} {dis_o13 : o1 # o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) n12_3,
  Arity (get_control (bigraph_tensor_product (dis_i := dis_trans dis_i23 dis_i13) (dis_o := dis_trans dis_o23 dis_o13) (bigraph_tensor_product (dis_i:= dis_i12) (dis_o := dis_o12) b1 b2) b3) n12_3) 
  = 
  Arity (get_control (bigraph_tensor_product (dis_i := dis_trans_r dis_i12 dis_i13) (dis_o := dis_trans_r dis_o12 dis_o13) b1 (bigraph_tensor_product (dis_i:= dis_i23) (dis_o := dis_o23) b2 b3)) (bij_sum_assoc n12_3)).
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
    (bigraph_tensor_product (dis_i := dis_trans dis_i23 dis_i13) (dis_o := dis_trans dis_o23 dis_o13) (bigraph_tensor_product (dis_i:= dis_i12) (dis_o := dis_o12) b1 b2) b3) 
    (bigraph_tensor_product (dis_i := dis_trans_r dis_i12 dis_i13) (dis_o := dis_trans_r dis_o12 dis_o13) b1 (bigraph_tensor_product (dis_i:= dis_i23) (dis_o := dis_o23) b2 b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 ⊗ b2) ⊗ b3) (b1 ⊗ (b2 ⊗ b3))
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    in_app_merge'_transi
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    in_app_merge'_transi
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (P := fin) (arity_tp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | s1_23']; simpl; unfold funcomp; simpl.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ x _).
      apply subset_eq_compat.
      reflexivity.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + x) _).
      apply subset_eq_compat.
      reflexivity.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + r2 + x) _).
      apply subset_eq_compat.
      rewrite PeanoNat.Nat.add_assoc.
      reflexivity.
    - destruct s1_23'; simpl.
      unfold parallel, id, sum_shuffle, inj_fin_add.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s1 + (s2 + s3)) (s1 + s2 + s3) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (s1 + s2)); simpl.
      * destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
        ++ destruct get_parent; try reflexivity.
          f_equal.
          destruct f; simpl.
          rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ x0 _).
          apply subset_eq_compat.
          reflexivity.
        ++ destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2); simpl.
          -- rewrite (proof_irrelevance _ _ l1).
              destruct (get_parent b2); try reflexivity.
              f_equal.
              destruct f; simpl.
              rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + x0) _).
              apply subset_eq_compat.
              reflexivity.
          -- simpl. exfalso. apply n0. lia. 
      * destruct (PeanoNat.Nat.ltb_spec0 x s1).
        ++ lia.
        ++ destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2).
          -- lia.
          -- assert (forall H H', exist (fun p => p < s3) (x - (s1 + s2)) H =
                                  exist (fun p => p < s3) (x - s1 - s2) H').
              ** intros H H'.
                apply subset_eq_compat.
                lia.
              ** assert (x - s1 - s2 < s3) as H'; [ lia | unfold lt in H' ].
                rewrite (H _ H').
                symmetry.
                rewrite (proof_irrelevance _ _ H').
                destruct get_parent; simpl; try reflexivity.
                destruct f; simpl.
                f_equal.
                rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + r2 + x0) _).
                apply subset_eq_compat.
                rewrite PeanoNat.Nat.add_assoc.
                reflexivity.
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. simpl. 
      destruct (in_dec EqDecN i123 (app_merge' i1 i2)).
      * destruct (in_dec EqDecN i123 i1).
      destruct get_link; try reflexivity.
      ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).
      ***
      set (Hn' := match
          in_app_or_m_nod_dup i1 i2 i123
            (match
              i1 as n0
              return
                ((In i123 n0 -> ~ In i123 i2) ->
                  In i123 (app_merge' n0 i2) ->
                  ~ In i123 n0 -> NoDup n0)
            with
            | {|
                ndlist := ndlist0; nd := nd0
              |} =>
                fun
                  (_ : In i123 ndlist0 ->
                        ~ In i123 i2)
                  (_ : In i123
                        (app_merge' ndlist0
                        i2))
                  (_ : ~ In i123 ndlist0) =>
                nd0
            end (dis_i12 i123) i4 n)
            (match
              i2 as n0
              return
                ((In i123 i1 -> ~ In i123 n0) ->
                  In i123 (app_merge' i1 n0) ->
                  NoDup n0)
            with
            | {|
                ndlist := ndlist0; nd := nd0
              |} =>
                fun
                  (_ : In i123 i1 ->
                        ~ In i123 ndlist0)
                  (_ : In i123
                        (app_merge' i1
                        ndlist0)) => nd0
            end (dis_i12 i123) i4) i4
        with
        | inl i6 =>
            False_ind (In i123 i2) (n i6)
        | inr i6 => i6
        end).
      rewrite (innername_proof_irrelevant b2 i123 i5 Hn').      
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_iff in i4. destruct i4. apply n. apply H. apply n0. apply H.
      * destruct (in_dec EqDecN i123 i1).
      ** exfalso. apply n. apply in_left_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_right_list. apply i4.
      *** 
      set (Hn' :=
        match
        in_app_or_m_nod_dup (app_merge' i1 i2) i3 i123
        (NoDup_app_merge i1 i2 (nd i1) (nd i2))
        (match
        i3 as n2
        return
        ((In i123 (app_merge' i1 i2) -> ~ In i123 n2) ->
        In i123 (app_merge' (app_merge' i1 i2) n2) ->
        NoDup n2)
        with
        | {| ndlist := ndlist0; nd := nd0 |} =>
        fun
        (_ : In i123 (app_merge' i1 i2) ->
        ~ In i123 ndlist0)
        (_ : In i123
        (app_merge' (app_merge' i1 i2) ndlist0))
        => nd0
        end (dis_trans dis_i23 dis_i13 i123)
        (in_app_merge'_trans i123
        (eq_ind_r
        (fun b : Name =>
        In b (app_merge' i1 (app_merge' i2 i3)))
        i0 eq_refl)))
        (in_app_merge'_trans i123
        (eq_ind_r
        (fun b : Name =>
        In b (app_merge' i1 (app_merge' i2 i3))) i0
        eq_refl))
        with
        | inl i4 => False_ind (In i123 i3) (n i4)
        | inr i4 => i4
        end).       
      symmetry. rewrite <- (innername_proof_irrelevant b3 i123 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. (*TODO best example of tactic use*)
  Qed.

Definition arity_tp_congruence_forward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))) :
  (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))) -> (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
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
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))) :
  (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))) -> (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))).
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
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))),
  bijection (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))) (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
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
      (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) 
      (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b3) (b2 ⊗ b4)
    (f_equal2_plus _ _ _ _ bij_s12 bij_s34)
    (app_merge'_cong bij_i12 bij_i34)
    (f_equal2_plus _ _ _ _ bij_r12 bij_r34)
    (app_merge'_cong bij_o12 bij_o34)
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
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r3) (r2 + r4) _ x _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) r1 r2 _ x _).
      apply subset_eq_compat.
      reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r3) (r2 + r4) _ (r1 + x) _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) r3 r4 _ x _).
      apply subset_eq_compat.
      congruence.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel, id, bij_rew_forward, inj_fin_add.
      destruct s24'.
      simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s2 + s4) (s1 + s3) _ x _).
      subst.
      destruct (PeanoNat.Nat.ltb_spec0 x s2).
      * rewrite (@eq_rect_exist nat nat (fun n x => x < n) s2 s2 _ x).
        rewrite <- eq_rect_eq.
        destruct get_parent; try reflexivity.
        rewrite <- eq_rect_eq.
        destruct f; simpl.
        f_equal.
        rewrite <- eq_rect_eq.
        apply subset_eq_compat.
        reflexivity.
      * rewrite <- big_parent_eq34.
        rewrite <- eq_rect_eq.
        simpl.
        unfold parallel, funcomp, bij_rew_forward.
        rewrite <- eq_rect_eq.
        destruct get_parent; simpl; try reflexivity.
        f_equal.
        destruct f.
        rewrite <- eq_rect_eq.
        apply subset_eq_compat.
        reflexivity.
  + apply functional_extensionality.
    destruct x as [[i24] | ([n2' | n4'], (i', Hi'))]; simpl.
    - rewrite <- big_link_eq12.
      simpl.
      unfold funcomp.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      destruct (in_dec EqDecN i24 i1).
      * (*link i1 = link i2 *) 
      destruct (in_dec EqDecN i24 i2).
      ** 
      set (Hn' := 
        match bij_i12 i24 with
        | conj _ H => H
        end (eq_ind_r (fun b : Name => In b i2) i6 eq_refl)).
      rewrite (innername_proof_irrelevant b1 i24 i5 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. apply bij_i12. apply i5.
      * (*link i2 = link i1 *)  
      destruct (in_dec EqDecN i24 i2).
      ** exfalso. apply n. apply bij_i12. apply i5.
      **  
      set (Hn' := 
          match
          in_app_or_m_nod_dup i2 i4 i24
            (match
              i2 as n1
              return
                ((In i24 n1 -> ~ In i24 i4) ->
                  In i24 (app_merge' n1 i4) -> ~ In i24 n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 ndlist0 -> ~ In i24 i4)
                  (_ : In i24 (app_merge' ndlist0 i4)) (_ : ~ In i24 ndlist0) => nd0
            end (dis_i24 i24) i0 n0)
            (match
              i4 as n1
              return
                ((In i24 i2 -> ~ In i24 n1) -> In i24 (app_merge' i2 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 i2 -> ~ In i24 ndlist0)
                  (_ : In i24 (app_merge' i2 ndlist0)) => nd0
            end (dis_i24 i24) i0) i0
        with
        | inl i5 => False_ind (In i24 i4) (n0 i5)
        | inr i5 => i5
        end).
      set (Hn := 
          match
          in_app_or_m_nod_dup i1 i3 i24
            (match
              i1 as n1
              return
                ((In i24 n1 -> ~ In i24 i3) ->
                  In i24 (app_merge' n1 i3) -> ~ In i24 n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 ndlist0 -> ~ In i24 i3)
                  (_ : In i24 (app_merge' ndlist0 i3)) 
                  (_ : ~ In i24 ndlist0) => nd0
            end (dis_i13 i24)
              (match app_merge'_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl))
              n)
            (match
              i3 as n1
              return
                ((In i24 i1 -> ~ In i24 n1) ->
                  In i24 (app_merge' i1 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 i1 -> ~ In i24 ndlist0)
                  (_ : In i24 (app_merge' i1 ndlist0)) => nd0
            end (dis_i13 i24)
              (match app_merge'_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl)))
            (match app_merge'_cong bij_i12 bij_i34 i24 with
            | conj _ H => H
            end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl))
        with
        | inl i5 => False_ind (In i24 i3) (n i5)
        | inr i5 => i5
        end).
      simpl. simpl.
      rewrite <- big_link_eq34.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      set (Hn'' := 
        match bij_i34 i24 with
        | conj _ H => H
        end (eq_ind_r (fun b : Name => In b i4) Hn' eq_refl
        )).
      rewrite (innername_proof_irrelevant b3 i24 Hn Hn'').
      destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - rewrite <- big_link_eq12.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold eq_rect_r.
      unfold parallel, funcomp.     
      simpl.
      erewrite <- (eq_rect_map (f := inl) (a := n2')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b1)) (type (get_node b2)) bij_n12) n2')).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) n2'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity. 
    - rewrite <- big_link_eq34.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold eq_rect_r.
      unfold parallel, funcomp.
      simpl.
      erewrite <- (eq_rect_map (f := inr) (a := n4')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b3)) (type (get_node b4)) bij_n34) n4')).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) n4'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity.
  Qed.


Definition bigraph_packed_tp (b1 b2 : bigraph_packed) 
 (dis_i : (i b1) # (i b2)) (dis_o : (o b1) # (o b2)) := 
  packing (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) (big b1) (big b2)).

(* Bifunctorial property*)
Theorem arity_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (n12_34 : type (get_node (b1 ⊗ b2 <<o>> (b3 ⊗ b4)))),
  Arity (get_control
    (bigraph_composition (p := permutation_distributive p13 p24)
      (bigraph_tensor_product (dis_i := dis_i12) (dis_o := dis_o12) b1 b2) 
      (bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o34) b3 b4)) n12_34) =
  Arity (get_control 
    ((bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o12) 
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4))) 
    (sum_shuffle n12_34)).
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.

Theorem bigraph_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)},
  bigraph_equality 
  (bigraph_composition (p := permutation_distributive p13 p24)
    (bigraph_tensor_product (dis_i := dis_i12) (dis_o := dis_o12) b1 b2) 
    (bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o34) b3 b4))
  ((bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o12) 
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4))) .
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
    (fun n12_34 => bij_rew (P := fin) (arity_comp_tp_dist b1 b2 b3 b4 n12_34)) (* Port *)
    ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|(s34, Hs34)]; simpl; unfold funcomp; simpl; unfold sequence, extract1, inject, sum_shuffle, parallel, id.
    - destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. destruct get_parent; try reflexivity.
      destruct f as (s1', Hs1').
      simpl.
      destruct PeanoNat.Nat.ltb_spec0.
      * rewrite (proof_irrelevance _ l Hs1').
        destruct get_parent; try reflexivity.
      * contradiction.
    - destruct get_parent; try reflexivity.
    - destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2'). unfold rearrange, extract1.
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    * exfalso. assert (forall a b, ~ a + b < a).
      {intros. lia. } 
      apply (H s1 s2'). apply l.
    * assert 
    (exist (fun p : nat => p < s2) (s1 + s2' - s1)
      (ZifyClasses.rew_iff_rev (s1 + s2' - s1 < s2)
        (BinInt.Z.lt
            (BinInt.Z.max BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1))) (BinInt.Z.of_nat s2))
        (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
            BinInt.Z.lt Znat.Nat2Z.inj_lt 
            (s1 + s2' - s1)
            (BinInt.Z.max BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1)))
            (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
              BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat
              BinInt.Z.of_nat BinInt.Z.of_nat
              (fun n0 m : BinNums.Z =>
                BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m))
              Znat.Nat2Z.inj_sub_max (s1 + s2')
              (BinInt.Z.of_nat (s1 + s2')) eq_refl s1
              (BinInt.Z.of_nat s1) eq_refl) s2 
            (BinInt.Z.of_nat s2) eq_refl)
        (ZMicromega.ZTautoChecker_sound
            (Tauto.IMPL
              (Tauto.OR
                  (Tauto.AND
                    (Tauto.X Tauto.isProp
                        (BinInt.Z.lt BinNums.Z0
                          (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                              (BinInt.Z.of_nat s1))))
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpEq;
                          RingMicromega.Frhs :=
                            EnvRing.PEsub
                              (EnvRing.PEX (BinNums.xI BinNums.xH))
                              (EnvRing.PEX
                                (BinNums.xO (BinNums.xO BinNums.xH)))
                        |} tt))
                  (Tauto.AND
                    (Tauto.X Tauto.isProp
                        (BinInt.Z.le
                          (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                              (BinInt.Z.of_nat s1)) BinNums.Z0))
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpEq;
                          RingMicromega.Frhs := EnvRing.PEc BinNums.Z0
                        |} tt))) None
              (Tauto.IMPL
                  (Tauto.A Tauto.isProp
                    {|
                      RingMicromega.Flhs :=
                        EnvRing.PEX (BinNums.xI BinNums.xH);
                      RingMicromega.Fop := RingMicromega.OpLt;
                      RingMicromega.Frhs :=
                        EnvRing.PEadd
                          (EnvRing.PEX
                              (BinNums.xO (BinNums.xO BinNums.xH)))
                          (EnvRing.PEX (BinNums.xO BinNums.xH))
                    |} tt) None
                  (Tauto.IMPL
                    (Tauto.NOT
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEX (BinNums.xI BinNums.xH);
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEX
                                (BinNums.xO (BinNums.xO BinNums.xH))
                          |} tt)) None
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpLt;
                          RingMicromega.Frhs :=
                            EnvRing.PEX (BinNums.xO BinNums.xH)
                        |} tt))))
            [ZMicromega.RatProof
              (RingMicromega.PsatzAdd
                  (RingMicromega.PsatzIn BinNums.Z 3)
                  (RingMicromega.PsatzAdd
                    (RingMicromega.PsatzIn BinNums.Z 2)
                    (RingMicromega.PsatzAdd
                        (RingMicromega.PsatzIn BinNums.Z 1)
                        (RingMicromega.PsatzIn BinNums.Z 0))))
              ZMicromega.DoneProof;
            ZMicromega.RatProof
              (RingMicromega.PsatzAdd
                  (RingMicromega.PsatzIn BinNums.Z 3)
                  (RingMicromega.PsatzAdd
                    (RingMicromega.PsatzIn BinNums.Z 2)
                    (RingMicromega.PsatzIn BinNums.Z 0)))
              ZMicromega.DoneProof] eq_refl
            (fun p : BinNums.positive =>
            match p with
            | BinNums.xI _ => BinInt.Z.of_nat (s1 + s2')
            | BinNums.xO p0 =>
                match p0 with
                | BinNums.xI _ => BinNums.Z0
                | BinNums.xO _ => BinInt.Z.of_nat s1
                | BinNums.xH => BinInt.Z.of_nat s2
                end
            | BinNums.xH =>
                BinInt.Z.max BinNums.Z0
                  (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                      (BinInt.Z.of_nat s1))
            end)
            (BinInt.Z.max_spec BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1)))
            (ZifyClasses.rew_iff (s1 + s2' < s1 + s2)
              (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.add (BinInt.Z.of_nat s1)
                    (BinInt.Z.of_nat s2)))
              (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                  BinInt.Z.lt Znat.Nat2Z.inj_lt 
                  (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                  (s1 + s2)
                  (BinInt.Z.add (BinInt.Z.of_nat s1)
                    (BinInt.Z.of_nat s2))
                  (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
                    BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat
                    BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add
                    Znat.Nat2Z.inj_add s1 
                    (BinInt.Z.of_nat s1) eq_refl s2
                    (BinInt.Z.of_nat s2) eq_refl))
              (ZifyClasses.rew_iff_rev (s1 + s2' < s1 + s2)
                  (BinInt.Z.lt
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2'))
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2)))
                  (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                    BinInt.Z.lt Znat.Nat2Z.inj_lt 
                    (s1 + s2')
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2'))
                    (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                        BinNums.Z BinNums.Z PeanoNat.Nat.add
                        BinInt.Z.of_nat BinInt.Z.of_nat
                        BinInt.Z.of_nat BinInt.Z.add
                        Znat.Nat2Z.inj_add s1 
                        (BinInt.Z.of_nat s1) eq_refl s2'
                        (BinInt.Z.of_nat s2') eq_refl) 
                    (s1 + s2)
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2))
                    (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                        BinNums.Z BinNums.Z PeanoNat.Nat.add
                        BinInt.Z.of_nat BinInt.Z.of_nat
                        BinInt.Z.of_nat BinInt.Z.add
                        Znat.Nat2Z.inj_add s1 
                        (BinInt.Z.of_nat s1) eq_refl s2
                        (BinInt.Z.of_nat s2) eq_refl))
                  (ZMicromega.ZTautoChecker_sound
                    (Tauto.IMPL
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEX (BinNums.xO BinNums.xH);
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEX (BinNums.xI BinNums.xH)
                          |} tt) None
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEadd 
                                (EnvRing.PEX BinNums.xH)
                                (EnvRing.PEX (BinNums.xO BinNums.xH));
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEadd 
                                (EnvRing.PEX BinNums.xH)
                                (EnvRing.PEX (BinNums.xI BinNums.xH))
                          |} tt)) [] eq_refl
                    (fun p : BinNums.positive =>
                      match p with
                      | BinNums.xI _ => BinInt.Z.of_nat s2
                      | BinNums.xO _ => BinInt.Z.of_nat s2'
                      | BinNums.xH => BinInt.Z.of_nat s1
                      end)
                    (ZifyClasses.rew_iff 
                        (s2' < s2)
                        (BinInt.Z.lt (BinInt.Z.of_nat s2')
                          (BinInt.Z.of_nat s2))
                        (ZifyClasses.mkrel nat BinNums.Z lt
                          BinInt.Z.of_nat BinInt.Z.lt
                          Znat.Nat2Z.inj_lt s2' 
                          (BinInt.Z.of_nat s2') eq_refl s2
                          (BinInt.Z.of_nat s2) eq_refl) Hs2'))))
            (ZifyClasses.rew_iff (~ s1 + s2' < s1)
              (~
                BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1))
              (ZifyClasses.not_morph (s1 + s2' < s1)
                  (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                    (BinInt.Z.of_nat s1))
                  (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                    BinInt.Z.lt Znat.Nat2Z.inj_lt 
                    (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                    s1 (BinInt.Z.of_nat s1) eq_refl)) n)))
          = exist (fun p : nat => p < s2) s2' Hs2').
    apply subset_eq_compat. lia.
    rewrite <- H.
    destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. 
    destruct PeanoNat.Nat.ltb_spec0.
    * destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2').
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    ** rewrite (proof_irrelevance _ l0 Hs2').
      destruct get_parent; try reflexivity.
    ** contradiction.
    * destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2').
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    ** exfalso. assert (forall a b, ~ a + b < a).
      {intros. lia. } 
      apply (H s1 s2'). apply l.
    ** 
    assert (exist (fun p : nat => p < s2) (s1 + s2' - s1)
      (ZifyClasses.rew_iff_rev (s1 + s2' - s1 < s2)
       (BinInt.Z.lt
          (BinInt.Z.max BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1))) (BinInt.Z.of_nat s2))
       (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
          BinInt.Z.lt Znat.Nat2Z.inj_lt 
          (s1 + s2' - s1)
          (BinInt.Z.max BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1)))
          (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
             BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat
             BinInt.Z.of_nat BinInt.Z.of_nat
             (fun n1 m : BinNums.Z =>
              BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n1 m))
             Znat.Nat2Z.inj_sub_max (s1 + s2')
             (BinInt.Z.of_nat (s1 + s2')) eq_refl s1
             (BinInt.Z.of_nat s1) eq_refl) s2 
          (BinInt.Z.of_nat s2) eq_refl)
       (ZMicromega.ZTautoChecker_sound
          (Tauto.IMPL
             (Tauto.OR
                (Tauto.AND
                   (Tauto.X Tauto.isProp
                      (BinInt.Z.lt BinNums.Z0
                         (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                            (BinInt.Z.of_nat s1))))
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpEq;
                        RingMicromega.Frhs :=
                          EnvRing.PEsub
                            (EnvRing.PEX (BinNums.xI BinNums.xH))
                            (EnvRing.PEX
                               (BinNums.xO (BinNums.xO BinNums.xH)))
                      |} tt))
                (Tauto.AND
                   (Tauto.X Tauto.isProp
                      (BinInt.Z.le
                         (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                            (BinInt.Z.of_nat s1)) BinNums.Z0))
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpEq;
                        RingMicromega.Frhs := EnvRing.PEc BinNums.Z0
                      |} tt))) None
             (Tauto.IMPL
                (Tauto.A Tauto.isProp
                   {|
                     RingMicromega.Flhs :=
                       EnvRing.PEX (BinNums.xI BinNums.xH);
                     RingMicromega.Fop := RingMicromega.OpLt;
                     RingMicromega.Frhs :=
                       EnvRing.PEadd
                         (EnvRing.PEX
                            (BinNums.xO (BinNums.xO BinNums.xH)))
                         (EnvRing.PEX (BinNums.xO BinNums.xH))
                   |} tt) None
                (Tauto.IMPL
                   (Tauto.NOT
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEX (BinNums.xI BinNums.xH);
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEX
                               (BinNums.xO (BinNums.xO BinNums.xH))
                         |} tt)) None
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpLt;
                        RingMicromega.Frhs :=
                          EnvRing.PEX (BinNums.xO BinNums.xH)
                      |} tt))))
          [ZMicromega.RatProof
             (RingMicromega.PsatzAdd
                (RingMicromega.PsatzIn BinNums.Z 3)
                (RingMicromega.PsatzAdd
                   (RingMicromega.PsatzIn BinNums.Z 2)
                   (RingMicromega.PsatzAdd
                      (RingMicromega.PsatzIn BinNums.Z 1)
                      (RingMicromega.PsatzIn BinNums.Z 0))))
             ZMicromega.DoneProof;
           ZMicromega.RatProof
             (RingMicromega.PsatzAdd
                (RingMicromega.PsatzIn BinNums.Z 3)
                (RingMicromega.PsatzAdd
                   (RingMicromega.PsatzIn BinNums.Z 2)
                   (RingMicromega.PsatzIn BinNums.Z 0)))
             ZMicromega.DoneProof] eq_refl
          (fun p : BinNums.positive =>
           match p with
           | BinNums.xI _ => BinInt.Z.of_nat (s1 + s2')
           | BinNums.xO p0 =>
               match p0 with
               | BinNums.xI _ => BinNums.Z0
               | BinNums.xO _ => BinInt.Z.of_nat s1
               | BinNums.xH => BinInt.Z.of_nat s2
               end
           | BinNums.xH =>
               BinInt.Z.max BinNums.Z0
                 (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                    (BinInt.Z.of_nat s1))
           end)
          (BinInt.Z.max_spec BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1)))
          (ZifyClasses.rew_iff (s1 + s2' < s1 + s2)
             (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.add (BinInt.Z.of_nat s1)
                   (BinInt.Z.of_nat s2)))
             (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                BinInt.Z.lt Znat.Nat2Z.inj_lt 
                (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                (s1 + s2)
                (BinInt.Z.add (BinInt.Z.of_nat s1)
                   (BinInt.Z.of_nat s2))
                (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
                   BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat
                   BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add
                   Znat.Nat2Z.inj_add s1 
                   (BinInt.Z.of_nat s1) eq_refl s2
                   (BinInt.Z.of_nat s2) eq_refl))
             (ZifyClasses.rew_iff_rev (s1 + s2' < s1 + s2)
                (BinInt.Z.lt
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2'))
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2)))
                (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                   BinInt.Z.lt Znat.Nat2Z.inj_lt 
                   (s1 + s2')
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2'))
                   (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                      BinNums.Z BinNums.Z PeanoNat.Nat.add
                      BinInt.Z.of_nat BinInt.Z.of_nat
                      BinInt.Z.of_nat BinInt.Z.add
                      Znat.Nat2Z.inj_add s1 
                      (BinInt.Z.of_nat s1) eq_refl s2'
                      (BinInt.Z.of_nat s2') eq_refl) 
                   (s1 + s2)
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2))
                   (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                      BinNums.Z BinNums.Z PeanoNat.Nat.add
                      BinInt.Z.of_nat BinInt.Z.of_nat
                      BinInt.Z.of_nat BinInt.Z.add
                      Znat.Nat2Z.inj_add s1 
                      (BinInt.Z.of_nat s1) eq_refl s2
                      (BinInt.Z.of_nat s2) eq_refl))
                (ZMicromega.ZTautoChecker_sound
                   (Tauto.IMPL
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEX (BinNums.xO BinNums.xH);
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEX (BinNums.xI BinNums.xH)
                         |} tt) None
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEadd 
                               (EnvRing.PEX BinNums.xH)
                               (EnvRing.PEX (BinNums.xO BinNums.xH));
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEadd 
                               (EnvRing.PEX BinNums.xH)
                               (EnvRing.PEX (BinNums.xI BinNums.xH))
                         |} tt)) [] eq_refl
                   (fun p : BinNums.positive =>
                    match p with
                    | BinNums.xI _ => BinInt.Z.of_nat s2
                    | BinNums.xO _ => BinInt.Z.of_nat s2'
                    | BinNums.xH => BinInt.Z.of_nat s1
                    end)
                   (ZifyClasses.rew_iff 
                      (s2' < s2)
                      (BinInt.Z.lt (BinInt.Z.of_nat s2')
                         (BinInt.Z.of_nat s2))
                      (ZifyClasses.mkrel nat BinNums.Z lt
                         BinInt.Z.of_nat BinInt.Z.lt
                         Znat.Nat2Z.inj_lt s2' 
                         (BinInt.Z.of_nat s2') eq_refl s2
                         (BinInt.Z.of_nat s2) eq_refl) Hs2'))))
          (ZifyClasses.rew_iff (~ s1 + s2' < s1)
             (~
              BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1))
             (ZifyClasses.not_morph (s1 + s2' < s1)
                (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                   (BinInt.Z.of_nat s1))
                (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                   BinInt.Z.lt Znat.Nat2Z.inj_lt 
                   (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                   s1 (BinInt.Z.of_nat s1) eq_refl)) n0))) = 
        exist (fun p : nat => p < s2) s2' Hs2'). 
    apply subset_eq_compat. lia.
    rewrite <- H.
    destruct get_parent; try reflexivity.
  + apply functional_extensionality.
    destruct x as [[i']|p]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    - unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
      destruct (in_dec EqDecN i' i3).
      * destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0 as [n npf]. 
      destruct (in_dec EqDecN n i1o3).
      ***
      set (npf' := match p13 n with
        | conj H _ => H
        end npf).
      rewrite <- (innername_proof_irrelevant b1 n i2 npf').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply n0. unfold permutation in p13. destruct (p13 n). apply H. apply npf.
      * unfold permutation_distributive, permut_list_forward.
      set (Hn := match
          in_app_or_m_nod_dup i3 i4 i'
            (match
              i3 as n0
              return
                ((In i' n0 -> ~ In i' i4) ->
                  In i'
                    (app_merge' n0 i4) ->
                  ~ In i' n0 -> NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : 
                    In i' ndlist0 ->
                    ~ In i' i4)
                  (_ : 
                    In i'
                      (app_merge' ndlist0
                      i4))
                  (_ : ~ In i' ndlist0)
                => nd0
            end (dis_i34 i')
              (match reflnames i' with
                | conj _ H => H
                end
                  (eq_ind_r
                    (fun b : Name =>
                      In b
                      (app_merge' i3 i4))
                    i0 eq_refl)) n)
            (match
              i4 as n0
              return
                ((In i' i3 -> ~ In i' n0) ->
                  In i'
                    (app_merge' i3 n0) ->
                  NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : 
                    In i' i3 ->
                    ~ In i' ndlist0)
                  (_ : 
                    In i'
                      (app_merge' i3
                      ndlist0)) => nd0
            end (dis_i34 i')
              (match reflnames i' with
                | conj _ H => H
                end
                  (eq_ind_r
                    (fun b : Name =>
                      In b
                      (app_merge' i3 i4))
                    i0 eq_refl)))
            (match reflnames i' with
            | conj _ H => H
            end
              (eq_ind_r
                  (fun b : Name =>
                  In b
                    (app_merge' i3 i4))
                  i0 eq_refl))
        with
        | inl i5 =>
            False_ind (In i' i4) (n i5)
        | inr i5 => i5
        end). 
      set (Hn' := 
        match
          in_app_or_m_nod_dup i3 i4 i'
            (match
                i3 as n0
                return
                  ((In i' n0 -> ~ In i' i4) ->
                  In i' (app_merge' n0 i4) ->
                  ~ In i' n0 -> NoDup n0)
              with
              | {|
                  ndlist := ndlist0;
                  nd := nd0
                |} =>
                  fun
                    (_ : In i' ndlist0 ->
                        ~ In i' i4)
                    (_ : In i'
                        (app_merge' ndlist0
                        i4))
                    (_ : ~ In i' ndlist0) =>
                  nd0
              end (dis_i34 i') i0 n)
            (match
                i4 as n0
                return
                  ((In i' i3 -> ~ In i' n0) ->
                  In i' (app_merge' i3 n0) ->
                  NoDup n0)
              with
              | {|
                  ndlist := ndlist0;
                  nd := nd0
                |} =>
                  fun
                    (_ : In i' i3 ->
                        ~ In i' ndlist0)
                    (_ : In i'
                        (app_merge' i3
                        ndlist0)) => nd0
              end (dis_i34 i') i0) i0
        with
        | inl i5 =>
            False_ind (In i' i4) (n i5)
        | inr i5 => i5
        end).
      rewrite <- (innername_proof_irrelevant b4 i' Hn Hn').
      destruct get_link; try reflexivity. 
      destruct s0 as [n' npf']. 
      destruct (in_dec EqDecN n' i1o3).
      *** exfalso. unfold Disjoint in dis_i12. specialize (dis_i12 n'). apply dis_i12; try assumption.
      unfold permutation in p24. destruct (p24 n'). apply H; assumption.
      *** destruct in_app_or_m. {exfalso. apply n0. unfold permutation in p13. destruct (p13 n'). apply H; assumption. }
      set (Hn'' := match
        in_app_or_m_nod_dup i1o3 i2o4 n'
            (match
              i1o3 as n1
              return
                ((In n' n1 -> ~ In n' i2o4) ->
                  In n' (app_merge' n1 i2o4) ->
                  ~ In n' n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In n' ndlist0 -> ~ In n' i2o4)
                  (_ : In n' (app_merge' ndlist0 i2o4))
                  (_ : ~ In n' ndlist0) => nd0
            end (dis_i12 n')
              match p13 n' with
              | conj _ _ =>
                  match p24 n' with
                  | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                  end
              end n0)
            (match
              i2o4 as n1
              return
                ((In n' i1o3 -> ~ In n' n1) ->
                  In n' (app_merge' i1o3 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In n' i1o3 -> ~ In n' ndlist0)
                  (_ : In n' (app_merge' i1o3 ndlist0)) => nd0
            end (dis_i12 n')
              match p13 n' with
              | conj _ _ =>
                  match p24 n' with
                  | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                  end
              end)
            match p13 n' with
            | conj _ _ =>
                match p24 n' with
                | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                end
            end
        with
        | inl i2 => False_ind (In n' i2o4) (n0 i2)
        | inr i2 => i2
        end). fold Hn''.
      set (Hn'''' := match p24 n' with
        | conj H _ => H
        end npf').
      rewrite <- (innername_proof_irrelevant b2 n' Hn'' Hn'''').
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
      **
      set (Hn := match p13 x with
        | conj H _ => H
        end i0). 
      rewrite <- (innername_proof_irrelevant b1 x i1 Hn).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. unfold permutation in p13. destruct (p13 x). apply H; assumption.
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
      *** exfalso. unfold Disjoint in dis_i12. specialize (dis_i12 x).
      apply dis_i12; try assumption.
      unfold permutation in p24. destruct (p24 x). apply H; assumption. 
      *** 
      set (i0' := match p24 x with
        | conj H _ => H
        end i0).
      rewrite <- (innername_proof_irrelevant b2 x i0').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** reflexivity.
  Qed.

End TensorProduct.