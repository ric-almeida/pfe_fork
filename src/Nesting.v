Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

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
Module NestingBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

Example I : NoDupList. Admitted.
Example m : nat. Admitted.
Example X : NoDupList. Admitted.
Example n : nat. Admitted.
Example Y : NoDupList. Admitted.
Example F : bigraph 0 I m X. Admitted.
Example G : bigraph 1 EmptyNDL n Y. Admitted.
Example dis_i : X # Y. Admitted.

(* Example id_pp_G := 
  bigraph_parallel_product 
    (dis_i := void_disjoint_all_list_right X) 
    (bigraph_identity (s := 0) (i := X)) 
    G. *)


Definition nest {I m X n Y m'} (* nest G F = G.F *)
  (G : bigraph m EmptyNDL n Y) (F : bigraph 1 I m' X) {eq mm' : MyEqNat m m'}
  : bigraph 1 I n (app_merge_NoDupList X Y) :=
  ((bigraph_identity (s := 0) (i := X)) || G) <<o>> F.


Global Notation "G '<.>' F" := (nest G F) (at level 50, left associativity).

Lemma id_union'' : forall X Y:NoDupList, 
  bigraph_equality
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
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
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
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Lemma my_id_union : forall X Y:NoDupList, 
  bigraph_packed_equality
    (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
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
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
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
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Theorem testimportant {I X Y}
  (F : bigraph 1 I 1 X) (G : bigraph 1 EmptyNDL 1 Y) :
  bigraph_packed_equality F G -> bigraph_packed_equality F F.
  Proof. 
    intros H. 
    rewrite H. auto. reflexivity. 
  Qed. 

Theorem intermediaire_rewrie {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  (b3 : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2))
  {up : UnionPossible b1 b2} :
  bigraph_packed_equality (b1 || b2) b3
  <-> bigraph_packed_equality ((packing b1) || (packing b2)) b3.
  split. auto. auto. Qed. 

Theorem intermediaire_rewrie' {s1 r1 s2 r2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: PermutationNames o2i1 i1o2} {eqsr : MyEqNat s1 r2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 r2 o2i1) 
  (b3 : bigraph s2 i2 r1 o1)
  {up : UnionPossible b1 b2} :
  bigraph_packed_equality (b1 <<o>> b2) b3
  <-> bigraph_packed_equality ((packing b1) <<o>> (packing b2)) b3.
  split. auto. auto. Qed. 

Lemma my_id_union' : forall X Y:NoDupList, 
  bigraph_packed_equality
    (@packing O (app_merge_NoDupList X Y) O (app_merge_NoDupList X Y) (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))))
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
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
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
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

(* Print my_id_union'.  *)

Theorem nest_associative {I X Y n Z}
  (F : bigraph 1 I 1 X) (G : bigraph 1 EmptyNDL 1 Y) (H : bigraph 1 EmptyNDL n Z) :
  bigraph_equality
    (H <.> (G <.> F))
    ((H <.> G) <.> F).
  Proof.
    apply eq_packed_eq_eq. 
    unfold nest. 
    assert (
      bigraph_packed_equality 
        (@packing (S O) I n (app_merge_NoDupList (app_merge_NoDupList X Y) Z) 

        (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) 
        (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) 
        (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) Z) I 
        (permutation_id_am_PN (app_merge_NoDupList X Y)) (MyEqNat_refl (S O)) 
        (@bigraph_parallel_product O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (@disjoint_innernames_implies_union_possible O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (disj_right_neutral (app_merge_NoDupList X Y)))) 
        (@bigraph_composition (Nat.add O (S O)) (Nat.add O (S O)) (S O) (S O) (app_merge_NoDupList X EmptyNDL) X (app_merge_NoDupList X Y) I (permutation_id_am_PN X) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) (S O) X X EmptyNDL Y (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) G (@disjoint_innernames_implies_union_possible O O (S O) (S O) X X EmptyNDL Y (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) G (disj_right_neutral X))) F))) 


        (@packing (S O) I n (app_merge_NoDupList X (app_merge_NoDupList Y Z)) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList X EmptyNDL) X (app_merge_NoDupList X (app_merge_NoDupList Y Z)) I (permutation_id_am_PN X) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n X X EmptyNDL (app_merge_NoDupList Y Z) (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList Y EmptyNDL) Y (app_merge_NoDupList Y Z) EmptyNDL (permutation_id_am_PN Y) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (@disjoint_innernames_implies_union_possible O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (disj_right_neutral Y))) G) (@disjoint_innernames_implies_union_possible O O (S O) n X X EmptyNDL (app_merge_NoDupList Y Z) (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList Y EmptyNDL) Y (app_merge_NoDupList Y Z) EmptyNDL (permutation_id_am_PN Y) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (@disjoint_innernames_implies_union_possible O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (disj_right_neutral Y))) G) (disj_right_neutral X))) F))

          <-> 
          bigraph_packed_equality 
        (bigraph_packed_composition 
        (packing (@bigraph_parallel_product O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (@disjoint_innernames_implies_union_possible O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (disj_right_neutral (app_merge_NoDupList X Y))))) 
        (packing (@bigraph_composition (Nat.add O (S O)) (Nat.add O (S O)) (S O) (S O) (app_merge_NoDupList X EmptyNDL) X (app_merge_NoDupList X Y) I (permutation_id_am_PN X) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) (S O) X X EmptyNDL Y (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) G (@disjoint_innernames_implies_union_possible O O (S O) (S O) X X EmptyNDL Y (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) G (disj_right_neutral X))) F))) 


        (@packing (S O) I n (app_merge_NoDupList X (app_merge_NoDupList Y Z)) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList X EmptyNDL) X (app_merge_NoDupList X (app_merge_NoDupList Y Z)) I (permutation_id_am_PN X) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n X X EmptyNDL (app_merge_NoDupList Y Z) (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList Y EmptyNDL) Y (app_merge_NoDupList Y Z) EmptyNDL (permutation_id_am_PN Y) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (@disjoint_innernames_implies_union_possible O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (disj_right_neutral Y))) G) (@disjoint_innernames_implies_union_possible O O (S O) n X X EmptyNDL (app_merge_NoDupList Y Z) (@bigraph_identity O X X (permutation_id_PN (@reverse_coercion NoDupList (list Name) X (ndlist X)))) (@bigraph_composition (Nat.add O (S O)) (Nat.add O n) (S O) (S O) (app_merge_NoDupList Y EmptyNDL) Y (app_merge_NoDupList Y Z) EmptyNDL (permutation_id_am_PN Y) (MyEqNat_refl (S O)) (@bigraph_parallel_product O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (@disjoint_innernames_implies_union_possible O O (S O) n Y Y EmptyNDL Z (@bigraph_identity O Y Y (permutation_id_PN (@reverse_coercion NoDupList (list Name) Y (ndlist Y)))) H (disj_right_neutral Y))) G) (disj_right_neutral X))) F))

          ).
          - simpl. split. auto. intros. simpl. unfold bigraph_packed_equality. simpl. auto. 
          - rewrite H0. clear H0. 
          assert (@packing (Nat.add O (S O)) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (Nat.add O n) (app_merge_NoDupList (app_merge_NoDupList X Y) Z) 
        (@bigraph_parallel_product O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (@disjoint_innernames_implies_union_possible O O (S O) n (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) EmptyNDL Z (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))) H (disj_right_neutral (app_merge_NoDupList X Y))))
        = 
        bigraph_parallel_product 
        (packing (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))))
        H 
        ). 
        + simpl. auto. 
        + rewrite H0. clear H0. 


        (* Set Printing All.  *)
        (* Print my_id_union'.  *)
        (* rewrite my_id_union'.    *)

    
    (*simpl. constructor. unfold bigraph_packed_equality. simpl. 
    rewrite my_id_union. 
    Set Printing All. *)
    (* rewrite my_id_union.  *)
    (* rewrite (id_union'' X Y). *)
  Admitted.


(* Compute type (get_node (G <.> bigraph_identity)). 

Definition mybij {n Y} (G : bigraph 1 EmptyNDL n Y) : 
bijection (void + match match G with
| {| node := node |} => node
end with
| {| type := type |} => type
end + void) 
(type (get_node G)).
Admitted.


Lemma arity_nest_right_neutral {n Y} (G : bigraph 1 EmptyNDL n Y) :
  forall n, 
  Arity (get_control (G <.> bigraph_identity) n) =
  Arity (get_control G (bij_void_sum_neutral n)).
  Proof.
  intros s i r o i' i'' p p' b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed. *)



 
(* Theorem nest_neutral_elt {n Y} (G : bigraph 1 EmptyNDL n Y) : 
  bigraph_equality (G <.> bigraph_identity) G.
  Proof.
    unfold nest. simpl. 
  apply 
    (BigEq _ _ _ _ _ _ _ _ (G <.> bigraph_identity) G
      eq_refl
      (fun (name : Name) => transitivity (P_NP (permutation_id Y)) (P_NP (permutation_id Y)))
      eq_refl
      (fun (name : Name) => reflexivity (In name Y))
      bij_void_sum_neutral_r
      bij_void_sum_neutral_r 
      (fun n => bij_rew (P := fin) (arity_comp_right_neutral b n)) 
    ).
  +  *)




Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph 0 i2 s1 i1. Admitted.

(* Theorem atom_is_empty_ion : 
  bigraph_equality.
  (discrete_ion <o> ∅)
  discrete_atom. *)

End NestingBig.