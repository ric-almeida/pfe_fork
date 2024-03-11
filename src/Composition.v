Require Import ConcreteBigraphs.
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

Import ListNotations.

(** * Composition
  This section deals with the operation of composition. This is the act
  of putting a bigraph inside another one. To do b1 <<o>> b2, the outerface 
  of b2 needs to be the innerface of b1. TODO/note: or just a bijection? 
  We prove left and right neutral for identity bigraph and associativity *)
Module CompositionBigraphs (s : Signature) (n : Names) (b: Bigraphs s n).
Module eb := EquivalenceBigraphs s n b.
Include eb.

Definition permut_list_forward (l1 l2 : list Name) (p : permutation l1 l2)
  (nl1 : {name:Name|In name l1}) : {name:Name|In name l2}.
  Proof.
    destruct nl1.
    exists x.
    unfold permutation in p. 
    apply p in i0. apply i0.
  Defined.

Definition bij_permut_list (l1 l2 : list Name) (p : permutation l1 l2) :
  bijection {name:Name|In name l1} {name:Name|In name l2}.
  Proof.
    refine (mkBijection
    {name:Name|In name l1} {name:Name|In name l2}
    (permut_list_forward l1 l2 p)
    (permut_list_forward l2 l1 (symmetry p)) _ _
    ).
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    Unshelve. apply symmetric_permutation.
  Defined.

Definition bigraph_composition {s1 r1 s2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: permutation o2i1 i1o2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 s1 o2i1) 
    : bigraph s2 i2 r1 o1.
  Proof. 
  set (sl2:= (bij_id <+> bij_permut_list  o2i1 i1o2 p) <o> (switch_link (get_link b2))). 
  set (sl1:= switch_link (get_link b1)). 
  apply (Big s2 i2 r1 o1
        (findec_sum (get_node b1) (get_node b2))
        (findec_sum (get_edge b1) (get_edge b2))
        (join (get_control b1) (get_control b2))
        ((get_parent b2) >> (get_parent b1))
        (switch_link (sl2 >> sl1) <o>
          (backward (@bij_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))).
  apply (finite_parent_sequence).
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined.
  (* l :  i2 + (p1 + p2) -> o1 + (e1 + e2) *)
  (* l1 : i1o2 + p1 -> o1 + e1 *)
  (* l2 : i2 + p2 -> o2i1 + e2, o2i1 <=> i1o2 *)
  
Global Notation "b1 '<<o>>' b2" := (bigraph_composition b1 b2) (at level 50, left associativity).

Definition bigraph_identity {s i i'} {p:permutation (ndlist i) (ndlist i')}: bigraph s i s i'. (*actually s i s (permutation i) *)
  Proof.
  apply (Big s i s i'
          voidfd (*node : ∅*)
          voidfd (*edge : ∅*)
          (@void_univ_embedding _) (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  - intros [inner | port]. (*link_|{names} : id*)
    + left. destruct inner. exists x. unfold permutation in p. apply p in i0. apply i0.
    + destruct port. destruct x.
  - intro n. (*acyclic parent*)
    destruct n.
  Defined.

Lemma arity_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')}
  (b : bigraph s i r o) n,  
  let b_id := bigraph_identity (s := r) (i := o') (i' := o'') (p:=p') in
  Arity (get_control (bigraph_composition (p := p) (bigraph_identity (p:=p')) b) n) =
  Arity (get_control b (bij_void_sum_neutral n)).
  (* b : s i r o, -> b_id : r (p o) r (p (p o)) *)
  Proof.
  intros s i r o o' o'' p p' b n b_id.
  destruct n as [ v | n].
    + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')} (b : bigraph s i r o), 
  bigraph_equality (bigraph_composition (p := p) (bigraph_identity (p := p')) b) b.
  Proof.
  intros s i r o o' o'' p p' b.
  refine (
    BigEq s r s r i o'' i o (bigraph_identity <<o>> b) b
      eq_refl (*s*)
      (fun (name : Name) => reflexivity (In name i)) (*i*)
      eq_refl (*r*)
      (fun (name : Name) => transitivity (symmetry p' name) (symmetry p name)) (*o*)
      bij_void_sum_neutral (*n*)
      bij_void_sum_neutral (*e*)
      (fun n => bij_rew (P := fin) (@arity_comp_left_neutral s i r o o' o'' p p' b n)) (*p*)
      _ _ _
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
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
  Unshelve. apply symmetric_permutation. apply symmetric_permutation.
  Qed.

Lemma arity_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o) n,  
  let b_id := bigraph_identity (s := s) (i := i') (i' := i'') (p:=p') in 
  Arity (get_control (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) n) =
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o i' i'' p p' b n b_id.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o), 
  bigraph_equality (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) b.
  Proof.
  intros s i r o i' i'' p p' b.
  apply 
    (BigEq _ _ _ _ _ _ _ _ (b <<o>> bigraph_identity) b
      eq_refl
      (fun (name : Name) => transitivity (p' name) (p name))
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
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
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
  forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2) n12_3,
  Arity (get_control (bigraph_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) n12_3) = 
  Arity (get_control (bigraph_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_comp_assoc : forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2),
  bigraph_equality 
  (bigraph_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) 
  (bigraph_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)).
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
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. unfold rearrange. destruct get_parent. reflexivity. unfold extract1. destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. unfold rearrange. destruct get_parent. reflexivity. unfold extract1. destruct get_parent; reflexivity. 
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
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))) -> 
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_comp_congruence_backward
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))) -> 
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_comp_congruence : forall 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))),
  bijection 
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))) 
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
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
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (be12 : bigraph_equality b1 b2)
  (be34 : bigraph_equality b3 b4), 
  bigraph_equality (bigraph_composition (p:=p13) b1 b3) (bigraph_composition (p:=p24) b2 b4).
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
    destruct x as [[n2' | n4'] | s4']; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold parallel; simpl; auto.
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
        instantiate (1 := eq_refl). simpl. 
        destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel.
      destruct get_parent.
      * reflexivity.
      * unfold bij_rew_forward.
        erewrite eq_rect_compose.
        instantiate (1 := eq_refl). simpl. 
        destruct get_parent; reflexivity.
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
      set (Hn' := match bij_i12 x with
        | conj _ H => H
        end
          (eq_ind_r (fun b : Name => In b i2o4)
            (match p24 x with
              | conj H _ => H
              end (proj1 (bij_o34_i12 x) i1)) eq_refl)).
      set (Hn := match p13 x with
        | conj H _ => H
        end i1). 
      rewrite (innername_proof_irrelevant b1 x Hn Hn').
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
      set (Hn := match p13 x0 with
        | conj H _ => H
        end i0).
      set (Hn' := match bij_i12 x0 with
        | conj _ H => H
        end
          (eq_ind_r (fun b : Name => In b i2o4)
            (match p24 x0 with
              | conj H _ => H
              end (proj1 (bij_o34_i12 x0) i0)) eq_refl)).
      rewrite (innername_proof_irrelevant b1 x0 Hn Hn').
      destruct get_link; try reflexivity. 
  Qed. 
  (*Missing a hypothesis that says bij_s12 = bij_r34_s12 in the equalities *)

Definition bigraph_packed_composition {s1 i1o2 r1 o1 s2 i2 o2i1} {p: permutation (ndlist o2i1) (ndlist i1o2)}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 s1 o2i1) : bigraph_packed :=
  packing (bigraph_composition (p := p) b1 b2).

Definition bigraph_packed_composition' (*{s1 i1 r1 o1 s2 i2 : FinDecType} *)
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
   Qed. *)
End CompositionBigraphs.