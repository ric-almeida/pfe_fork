Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import ConcreteBigraphs.
Require Import InfSets.
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


From mathcomp Require Import all_ssreflect.

Import ListNotations.

(** Nesting operator *)
Module NestingBig (s : SignatureParameter) (n : InfiniteParameter).
Module pp := ParallelProduct s n.
Include pp.

Definition nest {s1 r1 s2 r2 : nat} {o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  {eqs1r2 : MyEqNat s1 r2}
  (* {p : PermutationNDL i1 EmptyNDL} *)
  (* : bigraph s2 i2 r1 (app_merge_NoDupList o1 o2)  *)
  := ((bigraph_id 0 o2) || b1) <<o>> b2.


Global Notation "G '<.>' F" := (nest G F) (at level 50, left associativity).

(* Lemma id_union'' : forall X Y:NoDupList, 
  support_equivalence
  (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
  ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (SupEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
    + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
    + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold , parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Lemma my_id_union : forall X Y:NoDupList, 
  bigraph_pkd_s_e
    (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list InfType) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
    ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (SupEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list InfType) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
  + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
  + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold , parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Theorem testimportant {I X Y}
  (F : bigraph 1 I 1 X) (G : bigraph 1 EmptyNDL 1 Y) :
  bigraph_pkd_s_e F G -> bigraph_pkd_s_e F F.
  Proof. 
    intros H. 
    rewrite H. auto. reflexivity. 
  Qed. 

Theorem intermediaire_rewrie {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  (b3 : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2))
  {up : UnionPossible b1 b2} :
  bigraph_pkd_s_e (b1 || b2) b3
  <-> bigraph_pkd_s_e ((packing b1) || (packing b2)) b3.
  split. auto. auto. Qed. 

Theorem intermediaire_rewrie' {s1 r1 s2 r2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: PermutationNDL o2i1 i1o2} {eqsr : MyEqNat s1 r2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 r2 o2i1) 
  (b3 : bigraph s2 i2 r1 o1)
  {up : UnionPossible b1 b2} :
  bigraph_pkd_s_e (b1 <<o>> b2) b3
  <-> bigraph_pkd_s_e ((packing b1) <<o>> (packing b2)) b3.
  split. auto. auto. Qed. 

Lemma my_id_union' : forall X Y:NoDupList, 
  bigraph_pkd_s_e
    (@packing O (app_merge_NoDupList X Y) O (app_merge_NoDupList X Y) (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list InfType) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))))
    (packing ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))).
  intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (SupEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list InfType) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        erefl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ). 
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
  + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
  + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold , parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Print my_id_union'.  *)

Lemma nest_arity_associative : forall {s1 r1 o1 s2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 EmptyNDL r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3},
  forall n,
  Arity (get_control (bg:=(b1 <.> b2) <.>  b3) n) =
  Arity (get_control (bg:=b1 <.> (b2 <.> b3)) (bij_nesting_assoc n)).
  Proof.
  intros until n.
  destruct n as [[v|[[v|a']|b']] | c']; try elim v; reflexivity.
  Qed. 


Theorem nest_associative : forall {s1 r1 o1 s2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 EmptyNDL r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3},
  support_equivalence 
    ((b1 <.> b2) <.>  b3)
    (b1 <.> (b2 <.> b3)).
  Proof.
    intros.
    refine (SupEq _ _ _ _ _ _ _ _ ((b1 <.> b2) <.> b3) (b1 <.> (b2 <.> b3))
    (reflexivity s3)
    (permutation_id i3)
    (erefl)
    (permutation_commute tr_permutation)
    bij_nesting_assoc
    bij_nesting_assoc
    (fun n12_3 => bij_rew (nest_arity_associative b1 b2 b3 n12_3)) _ _ _ 
    ).
    + apply functional_extensionality. simpl.
      destruct x as [[v|a']|[[v|b']|c']]; try elim v; try reflexivity.
    + apply functional_extensionality. rewrite bij_rew_id. 
      intros [[[v|a']|[[v|b']|c']] | s1_23']; simpl; unfold funcomp; simpl; try (elim v).
      - unfold extract1, parallel, sum_shuffle. 
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold bij_rew_forward,unsplit,rshift.
        destruct o0.
        rewrite eq_rect_ordinal.
        apply val_inj;simpl. rewrite addnC. rewrite addn0. reflexivity.
      - unfold extract1, parallel, sum_shuffle. 
        unfold rearrange.
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold extract1, bij_rew_forward, rearrange.
        destruct o0. simpl.
        rewrite eq_rect_ordinal. 
        rewrite eq_rect_ordinal. simpl. 
        unfold split. simpl.
        destruct (ltnP m 0).
        * elim (nlt_0_it m i1).
        * destruct (ltnP (0 + m) 0).
        ** elim (nlt_0_it (0+m) i2).
        ** symmetry. erewrite <- (parent_proof_irrelevant b1 _).
        instantiate (1:= Ordinal (n:=s1) (m:=m - 0) (split_subproof (m:=0) (n:=s1) (i:=Ordinal (n:=0 + s1) (m:=m) (replace_in_H (Logic.eq_sym eqxy) m i0)) i1)).
        destruct get_parent; try reflexivity.
        f_equal. f_equal. f_equal. unfold unsplit,rshift. destruct o0.
        apply val_inj;simpl. rewrite addnC; rewrite addn0;reflexivity. 
      - unfold extract1, parallel, sum_shuffle. 
        unfold rearrange.
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold extract1, bij_rew_forward, rearrange,sequence.
        destruct o0. 
        rewrite eq_rect_ordinal. unfold split. simpl.
        destruct (ltnP m 0).
        * elim (nlt_0_it m i1).
        * unfold rearrange.
        destruct get_parent; try reflexivity.
        unfold extract1. destruct o0.
        rewrite eq_rect_ordinal.
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP m0 0).
        ** elim (nlt_0_it m0 i4).
        ** destruct (ltnP (0 + m0) 0).
        *** elim (nlt_0_it (0 + m0) i5).
        *** symmetry. erewrite <- (parent_proof_irrelevant b1 _).
        instantiate (1:= Ordinal (n:=s1) (m:=m0 - 0) (split_subproof (m:=0) (n:=s1) (i:=Ordinal (n:=0 + s1) (m:=m0) (replace_in_H (Logic.eq_sym eqxy) m0 i2)) i4)).
        destruct get_parent; try reflexivity.
        f_equal. f_equal. f_equal. unfold unsplit,rshift. destruct o0.
        apply val_inj. simpl. rewrite addnC. rewrite addn0. reflexivity.
      - unfold extract1, parallel, sum_shuffle, rearrange. 
        destruct get_parent; try reflexivity.
        unfold extract1, bij_rew_forward, rearrange,sequence.
        destruct o0; destruct s1_23'.
        rewrite eq_rect_ordinal. simpl. unfold split. simpl.
        destruct (ltnP m 0).
        * elim (nlt_0_it m i2).
        * unfold rearrange.
        destruct get_parent; try reflexivity.
        unfold extract1. destruct o0.
        rewrite eq_rect_ordinal.
        rewrite eq_rect_ordinal. simpl.
        destruct (ltnP m1 0).
        ** elim (nlt_0_it m1 i5).
        ** destruct (ltnP (0+m1) 0).
        *** elim (nlt_0_it (0+m1) i6).
        *** symmetry. erewrite <- (parent_proof_irrelevant b1 _).
        instantiate (1:= Ordinal (n:=s1) (m:=m1 - 0) (split_subproof (m:=0) (n:=s1) (i:=Ordinal (n:=0 + s1) (m:=m1) (replace_in_H (Logic.eq_sym eqxy) m1 i4)) i5)).
        destruct get_parent; try reflexivity.
        f_equal. f_equal. f_equal. unfold unsplit,rshift. destruct o0.
        apply val_inj. simpl. rewrite addnC. rewrite addn0. reflexivity.
    + apply functional_extensionality.
      destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
      - unfold parallel, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold rearrange, switch_link. simpl. 
        unfold in_app_or_m_nod_dup, extract1.
        rewrite <- (innername_proof_irrelevant b3 i0). 
        destruct get_link; try reflexivity.
        unfold permut_list_forward. destruct s0.
        f_equal. apply subset_eq_compat. reflexivity.
      - unfold parallel, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp. 
        simpl.
        unfold rearrange, switch_link. simpl.
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, extract1. 
        unfold bij_join_port_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward.
        destruct p123. simpl.  
        destruct x as [[v|a']|[[v|b']|c']]; try destruct v.
        * unfold bij_rew_forward, funcomp, join, void_univ_embedding. destruct o0.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. f_equal. destruct s0. apply subset_eq_compat. reflexivity.
          reflexivity.
        * unfold bij_rew_forward, funcomp, join, void_univ_embedding, permut_list_forward. destruct o0.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
          reflexivity.
        * unfold bij_rew_forward, funcomp, join, void_univ_embedding, permut_list_forward. destruct o0.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
          reflexivity.
  Unshelve. 
  apply val_inj;simpl. rewrite addnC. rewrite addn0. reflexivity.
  apply val_inj;simpl. rewrite addnC. rewrite addn0. reflexivity.
  apply val_inj;simpl. rewrite addnC. rewrite addn0. reflexivity.
  Qed.


Lemma arity_nest_right_neutral {s1 r1 : nat} {o1 : NoDupList} 
  (b1 : bigraph s1 EmptyNDL r1 o1) :
  forall n, 
  Arity (get_control (bg:=b1 <.> bigraph_id s1 EmptyNDL) n) =
  Arity (get_control (bg:=b1) (bijection_nest_right_neutral n)).
  Proof.
  intros.
  destruct n as [[v| n] | v]; try elim v; reflexivity.
  Qed. 

Lemma nest_right_neutral {s1 r1 : nat} {o1 : NoDupList} 
  (b : bigraph s1 EmptyNDL r1 o1) :
  support_equivalence 
    (b <.> bigraph_id s1 EmptyNDL)
    b.
  Proof.
  eapply 
    (SupEq s1 r1 s1 r1 _ _ _ _ (b <.> bigraph_id s1 EmptyNDL) b
      erefl
      (left_empty EmptyNDL)
      erefl
      (left_empty o1)
      bijection_nest_right_neutral
      bijection_nest_right_neutral
      (fun n => bij_rew (arity_nest_right_neutral b n))
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1']; simpl.
    - unfold funcomp,parallel,sum_shuffle,extract1.
      simpl. unfold extract1.
      destruct get_parent; try reflexivity.
      f_equal. destruct o0. unfold unsplit,rshift. apply Ordinal_proof_irrelevance.
    - unfold funcomp,parallel,sum_shuffle,extract1.
      simpl. unfold extract1.
      unfold bij_rew_forward. 
      destruct s1'.
      rewrite eq_rect_ordinal. unfold split. simpl.
      destruct (ltnP m 0). elim (nlt_0_it m i1).
      erewrite <- (parent_proof_irrelevant b _).
      instantiate (1:=Ordinal (n:=s1) (m:=m) i0).   
      destruct get_parent; try reflexivity.
      f_equal. destruct o0. unfold unsplit,rshift. apply Ordinal_proof_irrelevance.
  + apply functional_extensionality.      
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - destruct i0. 
    - unfold parallel, sum_shuffle, choice, funcomp.
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
      * f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Unshelve.
  apply val_inj. simpl. rewrite subn0. reflexivity.
  Qed.

Lemma arity_nest_left_neutral {s1 r1 : nat} {o1 : NoDupList} 
  (b1 : bigraph s1 EmptyNDL r1 o1) :
  forall n, 
  Arity (get_control (bg:=bigraph_id r1 EmptyNDL <.> b1) n) =
  Arity (get_control (bg:=b1) (bijection_nest_left_neutral n)).
  Proof.
  intros.
  destruct n as [[v| v] | n]; try elim v; reflexivity.
  Qed. 

Lemma nest_left_neutral {s1 r1 : nat} {o1 : NoDupList} 
  (b : bigraph s1 EmptyNDL r1 o1) :
  support_equivalence 
    (bigraph_id r1 EmptyNDL <.> b)
    b.
  Proof.
  eapply 
    (SupEq s1 r1 s1 r1 _ _ _ _ (bigraph_id r1 EmptyNDL <.> b) b
      erefl
      (left_empty EmptyNDL)
      erefl
      (right_empty o1)
      bijection_nest_left_neutral
      bijection_nest_left_neutral
      (fun n => bij_rew (arity_nest_left_neutral b n))
    ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1']; simpl.
    - unfold funcomp,parallel,sum_shuffle,extract1,rearrange.
      simpl. unfold rearrange.
      destruct get_parent; try reflexivity.
      unfold extract1, bij_rew_forward. 
      destruct o0. 
      rewrite eq_rect_ordinal.
      unfold split. simpl. destruct (ltnP m 0).
      * elim (nlt_0_it m i1).
      * f_equal. unfold unsplit,rshift. apply val_inj. simpl. rewrite addnC. rewrite addn0. rewrite subn0. reflexivity.
    - unfold funcomp,parallel,sum_shuffle,extract1.
      simpl. unfold rearrange.
      destruct get_parent; try reflexivity.
      unfold extract1,bij_rew_forward.
      destruct s1'; destruct o0. 
      rewrite eq_rect_ordinal.
      unfold split;simpl. destruct (ltnP m0 0).
      * elim (nlt_0_it m0 i2).
      * f_equal. unfold unsplit,rshift. apply val_inj. simpl. rewrite addnC. rewrite addn0. rewrite subn0. reflexivity.
  + apply functional_extensionality.      
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - destruct i0. 
    - unfold parallel, sum_shuffle, choice, funcomp.
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
      unfold permut_list_forward.
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
  Qed.

End NestingBig.