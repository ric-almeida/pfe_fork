Set Warnings "-notation-overridden, -parsing, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.

(** * Composition
  This section deals with the operation of composition. This is the act
  of putting a bigraph inside another one. To do b1 <<o>> b2, the outerface 
  of b2 needs to be the innerface of b1. TODO/note: or just a bijection? 
  We prove left and right neutral for identity bigraph and associativity *)
Module CompositionBigraphs (s : SignatureParameter) (n : NamesParameter).
Module eb := EquivalenceBigraphs s n.
Include eb.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.

  

Definition bigraph_composition {s1 r1 s2 r2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: PermutationNames o2i1 i1o2} {eqsr : MyEqNat s1 r2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 r2 o2i1) 
    : bigraph s2 i2 r1 o1. (*s1=r2*)
  Proof. 
    set (sl2:= (bij_id <+> bij_permut_list o2i1 i1o2 (PN_P p)) <o> (switch_link (get_link b2))). 
    set (sl1:= switch_link (get_link b1)). 
    apply (Big s2 i2 r1 o1
          (findec_sum (get_node b1) (get_node b2))
          (findec_sum (get_edge b1) (get_edge b2))
          (join (get_control b1) (get_control b2))
          ((get_parent b2) >> ((bij_id <+> (bij_rew eqxy) -->> (bij_id <+> bij_id)) (get_parent b1)))
          (switch_link (sl2 >> sl1) <o>
            (backward (@bij_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))).
    apply (finite_parent_sequence).
    + unfold bij_rew. simpl. 
    unfold parallel, funcomp, id.  (* exact (ap _ _ _ _ b1).*)
    set (ap1 := ap _ _ _ _ b1).
    unfold FiniteParent in *.
    change (forall n : type (node s1 i1o2 r1 o1 b1), Acc (fun n' n0 : type (node s1 i1o2 r1 o1 b1) => match get_parent b1 (inl n0) with
    | inl a => inl a
    | inr c => inr c
    end = inl n') n).
    assert ((fun n' n0 : type (node s1 i1o2 r1 o1 b1) => parent s1 i1o2 r1 o1 b1 (inl n0) = inl n') 
      = (fun n' n0 : type (node s1 i1o2 r1 o1 b1) => match get_parent b1 (inl n0) with
    | inl a => inl a
    | inr c => inr c
    end = inl n')).
    * apply functional_extensionality. intros. apply functional_extensionality. intros. 
      change ((get_parent b1 (inl x0) = inl x) = (match get_parent b1 (inl x0) with
    | inl a => inl a
    | inr c => inr c
    end = inl x)). 
    destruct (get_parent b1 (inl x0)); auto. 
    * rewrite <- H. exact ap1.
    + exact (ap _ _ _ _ b2).
    Defined.
  (* l :  i2 + (p1 + px2) -> o1 + (e1 + e2) *)
  (* l1 : i1o2 + p1 -> o1 + e1 *)
  (* l2 : i2 + p2 -> o2i1 + e2, o2i1 <=> i1o2 *)
  
Global Notation "b1 '<<o>>' b2" := (bigraph_composition b1 b2) (at level 50, left associativity).

Lemma arity_comp_left_neutral : forall {s i r o} 
  (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_id r o <<o>> b) n) =
  Arity (get_control b (bij_void_sum_neutral n)).
  (* b : s i r o, -> b_id : r (p o) r (p (p o)) *)
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
    + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_comp_left_neutral : forall {s i r o} 
  (b : bigraph s i r o), 
  bigraph_equality (bigraph_id r o <<o>> b) b.
  Proof.
  intros s i r o b.
  refine (
    BigEq s r s r i o i o (bigraph_id r o <<o>> b) b
      eq_refl (*s*)
      (fun (name : Name) => reflexivity (In name i)) (*i*)
      eq_refl (*r*)
      (left_empty o) (*o*)
      bij_void_sum_neutral (*n*)
      bij_void_sum_neutral (*e*)
      (fun n => bij_rew (P := fin) (arity_comp_left_neutral b n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + simpl. apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      unfold rearrange, id. simpl. 
      destruct get_parent; try reflexivity. 
      f_equal. unfold bij_rew_forward. 
      rewrite <- eq_rect_eq. reflexivity.
    - unfold funcomp, parallel.
      simpl. 
      unfold rearrange, id. simpl. 
      destruct get_parent; try reflexivity.
      f_equal. unfold bij_rew_forward. 
      rewrite <- eq_rect_eq. reflexivity.
  + apply functional_extensionality.
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
    simpl. 
    unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
    simpl.
    unfold rearrange, switch_link, id. simpl.
    rewrite <- (innername_proof_irrelevant b name i0).
    destruct get_link; try reflexivity.
    * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

Lemma arity_comp_right_neutral : forall {s i r o}
  (b : bigraph s i r o) n, 
  Arity (get_control (b <<o>> bigraph_id s i) n) =
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_comp_right_neutral : forall {s i r o}
  (b : bigraph s i r o), 
  bigraph_equality (b <<o>> bigraph_id s i) b.
  Proof.
  intros s i r o b.
  apply 
    (BigEq _ _ _ _ _ _ _ _ (b <<o>> bigraph_id s i) b
      eq_refl
      (fun (name : Name) => reflexivity (In name i))
      eq_refl
      (fun (name : Name) => reflexivity (In name o))
      bij_void_sum_neutral_r
      bij_void_sum_neutral_r 
      (fun n => bij_rew (P := fin) (arity_comp_right_neutral b n)) 
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - unfold funcomp, parallel.
      simpl. 
      unfold extract1, id. simpl. 
      unfold bij_rew_forward. 
      rewrite <- eq_rect_eq. 
      destruct get_parent; try reflexivity.
  + apply functional_extensionality.      
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      rewrite <- (innername_proof_irrelevant b name i0).
      destruct get_link; try reflexivity. 
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. 
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.


Lemma arity_comp_assoc : 
  forall {s1 i1o2 r1 o1 s2 r2 r3 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : PermutationNames (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : PermutationNames (ndlist o3i2) (ndlist i2o3)}
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 r2 o2i1) 
  (b3 : bigraph s3 i3 r3 o3i2) n12_3, 
  Arity (get_control ((b1 <<o>> b2) <<o>> b3) n12_3) = 
  Arity (get_control (b1 <<o>> (b2 <<o>> b3)) (bij_sum_assoc n12_3)).
  Proof. (*s1=r2*) (*s2 = r3*)
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_comp_assoc : forall {s1 i1o2 r1 o1 s2 r2 r3 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : PermutationNames (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : PermutationNames (ndlist o3i2) (ndlist i2o3)}
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 r2 o2i1) 
  (b3 : bigraph s3 i3 r3 o3i2),
  bigraph_equality 
  ((b1 <<o>> b2) <<o>> b3) 
  (b1 <<o>> (b2 <<o>> b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 <<o>> b2) <<o>> b3) (b1 <<o>> (b2 <<o>> b3))
    eq_refl
    (fun (name : Name) => iff_refl (In name i3))
    eq_refl
    (fun (name : Name) => iff_refl (In name o1))
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (P := fin) (arity_comp_assoc b1 b2 b3 n12_3))
  ). 
  + apply functional_extensionality.
    destruct x as [n1 | [n2 | n3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1' | [n2' | n3']] | s123]; simpl; unfold funcomp; simpl.
    - destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl; unfold parallel, id. destruct get_parent. reflexivity.
    destruct s1. destruct (MyEqNat_refl 0). simpl. destruct f. 
    destruct get_parent; try reflexivity. destruct get_parent; try reflexivity.
    - unfold rearrange; unfold extract1; simpl; unfold parallel, id. 
    unfold rearrange. 
    destruct get_parent. reflexivity. 
    destruct get_parent. reflexivity. 
    unfold extract1. destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl; unfold parallel, id. destruct get_parent. reflexivity. unfold rearrange. destruct get_parent. reflexivity. unfold extract1. destruct get_parent; reflexivity. 
  + apply functional_extensionality.
    destruct x as [[i3'] | p123]; simpl; unfold funcomp; simpl. 
    - unfold parallel. unfold switch_link. simpl. unfold rearrange.
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      rewrite <- (innername_proof_irrelevant b3 i3' i0).
      destruct get_link; try reflexivity.
      * destruct get_link; try reflexivity.
      ** destruct get_link; try reflexivity. apply f_equal. destruct s5. apply subset_eq_compat. reflexivity. 
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold parallel. unfold switch_link. simpl. unfold rearrange.
        unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
        unfold id.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, bij_subset_backward, bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link; try reflexivity. 
        destruct get_link; try reflexivity. 
        apply f_equal. destruct s4. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, bij_subset_backward, bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link; try reflexivity.
        unfold id.
        unfold sequence.
        unfold rearrange.
        unfold extract1. 
        destruct get_link; try reflexivity. 
        destruct get_link; try reflexivity. 
        apply f_equal. destruct s5. apply subset_eq_compat. reflexivity.
  Qed.

Definition arity_comp_congruence_forward 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 r3 r4 i3 o3i1 s4 i4 o4i2} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  {eqs1r3 : MyEqNat s1 r3} {eqs2r4 : MyEqNat s2 r4}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2) 
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (b1 <<o>> b3) n13))) -> 
  (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof. (*s1 = r3*) (*s2 = r4*)
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_comp_congruence_backward
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 r3 r4 i3 o3i1 s4 i4 o4i2} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  {eqs1r3 : MyEqNat s1 r3} {eqs2r4 : MyEqNat s2 r4}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2) 
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))) -> 
  (fin (Arity (get_control (b1 <<o>> b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_comp_congruence : forall 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 r3 r4 i3 o3i1 s4 i4 o4i2} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  {eqs1r3 : MyEqNat s1 r3} {eqs2r4 : MyEqNat s2 r4}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2) 
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))),
  bijection 
  (fin (Arity (get_control (b1 <<o>> b3) n13))) 
  (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ (arity_comp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) (arity_comp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
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

Theorem bigraph_comp_congruence : forall 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 r3 r4 i3 o3i1 s4 i4 o4i2} 
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  {eqs1r3 : MyEqNat s1 r3} {eqs2r4 : MyEqNat s2 r4}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 r3 o3i1) 
  (b4 : bigraph s4 i4 r4 o4i2) 
  (be12 : bigraph_equality b1 b2)
  (be34 : bigraph_equality b3 b4), 
  bigraph_equality (b1 <<o>> b3) (b2 <<o>> b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34_s12, bij_o34_i12, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq 
    s3 r1 
    s4 r2 
    i3 o1 i4 o2
    (b1 <<o>> b3)
    (b2 <<o>> b4)
    (bij_s34)
    (bij_i34)
    (bij_r12)
    (bij_o12)
    (bij_n12 <+> bij_n34)
    (bij_e12 <+> bij_e34)
    (arity_comp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
  ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2' | n4'] | s4']; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold parallel; simpl; auto; unfold id, bij_rew_forward.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel.
      simpl.
      destruct get_parent.
      * reflexivity.
      * unfold bij_rew_forward. 
      erewrite eq_rect_compose.
      erewrite eq_rect_compose.
      instantiate (1 := eq_sym eqxy). 
      destruct get_parent; try reflexivity.
    - rewrite <- big_parent_eq34.
      rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel.
      simpl.
      destruct get_parent.
      * reflexivity.
      * unfold bij_rew_forward. 
      erewrite eq_rect_compose.
      erewrite eq_rect_compose.
      instantiate (1 := eq_sym eqxy). 
      destruct get_parent; try reflexivity.
  + apply functional_extensionality.
    destruct x as [[i4'] | p123]; simpl; unfold funcomp; simpl. 
    - rewrite <- big_link_eq34. simpl.
      unfold funcomp, parallel. unfold switch_link. simpl. unfold rearrange.
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      destruct get_link; try reflexivity.
      rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold rearrange, switch_link, id. 
      destruct s0. unfold permut_list_forward.
      set (Hn' := match PN_P p13 x with
      | conj H _ => H
      end i1). symmetry.
      rewrite <- (innername_proof_irrelevant b1 x Hn').
      destruct get_link; try reflexivity.
    - destruct p123 as ([v2 | v3], (i123, Hvi123)); simpl.
      * unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold extract1, rearrange, bij_rew_forward, eq_rect_r, funcomp, parallel, id.
      simpl. (*pourquoi j'ai un get_link b3?*)
      unfold extract1.
      erewrite <- (eq_rect_map (f := inl) (a := v2)).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b1)) (type (get_node b2)) bij_n12) v2)).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) v2))).
      destruct get_link; try reflexivity.
      * unfold extract1, rearrange, bij_rew_forward, eq_rect_r, funcomp, parallel, id.
      simpl.
      rewrite <- big_link_eq34. simpl.
      unfold funcomp, parallel. 
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      erewrite <- (eq_rect_map (f := inr) (a := v3)).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b3)) (type (get_node b4)) bij_n34) v3)).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) v3))).
      destruct get_link; try reflexivity.
      ** rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      destruct s0. unfold permut_list_forward.
      set (Hn := match PN_P p13 x0 with
      | conj H _ => H
      end i0). symmetry.
      rewrite <- (innername_proof_irrelevant b1 x0 Hn).
      destruct get_link; try reflexivity. 
  Unshelve.
  *** destruct eqs2r4 as [eqs2r4]. lia.
  *** destruct eqs2r4 as [eqs2r4]. lia.
  Qed. 
  (*Missing a hypothesis that says bij_s12 = bij_r34_s12 in the equalities *)

Definition bigraph_packed_composition {s1 i1o2 r1 o1 s2 i2 o2i1 r2} {p: PermutationNames o2i1 i1o2} {myeq: MyEqNat s1 r2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 r2 o2i1) : bigraph_packed :=
  packing (b1 <<o>> b2).

(* Definition bigraph_packed_composition' (*{s1 i1 r1 o1 s2 i2 : FinDecType} *)
  (b1 : bigraph_packed) (b2 : bigraph_packed) : bigraph_packed. Admitted.

Theorem bigraph_packed_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')}
  (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_composition (p:=p) (bigraph_identity (p := p')) b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_left_neutral.
  Qed. 

Theorem bigraph_packed_comp_assoc : forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2),
  bigraph_packed_equality 
    (bigraph_packed_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) 
    (bigraph_packed_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)).
  Proof.
  unfold bigraph_packed_equality.
  intros.
  apply bigraph_comp_assoc.
  Qed.

Lemma bigraph_packed_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o), 
    bigraph_packed_equality (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_right_neutral.
  Qed. 

Fail Add Parametric Morphism : bigraph_packed_composition with
  signature bigraph_packed_equality ==> 
  bigraph_packed_equality ==> 
  bigraph_packed_equality as composition_morphism.
   (* Proof.
   unfold bigraph_packed_equality, bigraph_packed_composition.
   destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
   apply bigraph_comp_congruence.
   assumption.
   Qed. *) *)
End CompositionBigraphs.