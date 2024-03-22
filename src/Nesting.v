Set Warnings "-notation-overridden, -notation-overriden".

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
Module NestingBig (s : Signature) (n : Names) (b: Bigraphs s n).
Module pp := ParallelProduct s n b.
Include pp.

Example I : NoDupList. Admitted.
Example m : nat. Admitted.
Example X : NoDupList. Admitted.
Example n : nat. Admitted.
Example Y : NoDupList. Admitted.
Example F : bigraph 0 I m X. Admitted.
Example G : bigraph m EmptyNDL n Y. Admitted.
Example dis_i : X # Y. Admitted.

(* Example id_pp_G := 
  bigraph_parallel_product 
    (dis_i := void_disjoint_all_list_right X) 
    (bigraph_identity (s := 0) (i := X)) 
    G. *)


Definition nest {I m X n Y} (* nest G F = G.F *)
  (G : bigraph m EmptyNDL n Y) (F : bigraph 0 I m X) 
  : bigraph 0 I n (app_merge_NoDupList X Y) :=
  ((bigraph_identity (s := 0) (i := X)) || G) <<o>> F.

Global Notation "F '<.>' G" := (nest F G) (at level 50, left associativity).


Theorem nest_associative {I X m Y n Z}
  (F : bigraph 0 I 0 X) (G : bigraph 0 EmptyNDL m Y) (H : bigraph m EmptyNDL n Z) :
  bigraph_equality
    (H <.> (G <.> F))
    ((H <.> G) <.> F).
  Proof.
  unfold nest.
  Fail rewrite id_union'.
  Admitted.

(* 
Theorem nest_associative_1 {I k X m Y n Z sF}
  (F : bigraph sF I k X) (G : bigraph k EmptyNDL m Y) (H : bigraph m EmptyNDL n Z) :
  bigraph_equality
    ((F <.> G) <.> H)
    (bigraph_composition
      (p:=permutation_id' X (app_merge_NoDupList X EmptyNDL) (merge_right_neutral' X))
      (bigraph_composition
        (p:=permutation_id' (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (merge_right_neutral' ((app_merge_NoDupList X Y))))
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right (app_merge_NoDupList X Y)))) (@bigraph_identity 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id (app_merge_NoDupList X Y))) H)
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right X))) (@bigraph_identity 0 X X (permutation_id X)) G)
      )
      F
    ). Admitted.
    (*Supposed to be H.(G.F) = (idX∪Y ‖ H) ◦ (idX ‖ G) ◦ F
  or from the bottom (H.G).F = (idX∪Y ‖ H) ◦ (idX ‖ G) ◦ F *)
    (*But I have     (F.G).H = (idX∪Y ‖ H) ◦ (idX ‖ G) ◦ F *)

Theorem nest_associative_2 {I k X m Y n Z sF}
  (F : bigraph sF I k X) (G : bigraph k EmptyNDL m Y) (H : bigraph m EmptyNDL n Z) :
  bigraph_equality
    (bigraph_composition
      (p:=permutation_id' X (app_merge_NoDupList X EmptyNDL) (merge_right_neutral' X))
      (bigraph_composition
        (p:=permutation_id' (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (merge_right_neutral' ((app_merge_NoDupList X Y))))
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right (app_merge_NoDupList X Y)))) (@bigraph_id 0 (app_merge_NoDupList X Y)) H)
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right X))) (@bigraph_id 0 X) G)
      )
      F
    )
    (bigraph_composition
      (p:=permutation_id' X (app_merge_NoDupList X EmptyNDL) (merge_right_neutral' X))
      (bigraph_composition
        (p:=permutation_id' (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (merge_right_neutral' ((app_merge_NoDupList X Y))))
        (bigraph_parallel_product 
          (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right (app_merge_NoDupList X Y)))) 
          (bigraph_parallel_product
            (up := union_possible_id) 
            (@bigraph_id 0 X)
            (@bigraph_id 0 Y)) 
          H)
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right X))) (@bigraph_identity 0 X X (permutation_id X)) G)
      )
      F
    ).
  Proof.
    Fail rewrite <- id_union. Admitted.

Theorem nest_associative_2' {I k X m Y n Z sF}
  (F : bigraph sF I k X) (G : bigraph k EmptyNDL m Y) (H : bigraph m EmptyNDL n Z) :
  bigraph_packed_equality
    (packing (bigraph_composition
      (p:=permutation_id' X (app_merge_NoDupList X EmptyNDL) (merge_right_neutral' X))
      (bigraph_composition
        (p:=permutation_id' (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (merge_right_neutral' ((app_merge_NoDupList X Y))))
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right (app_merge_NoDupList X Y)))) (@bigraph_id 0 (app_merge_NoDupList X Y)) H)
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right X))) (@bigraph_id 0 X) G)
      )
      F
    ))
    (packing (bigraph_composition
      (p:=permutation_id' X (app_merge_NoDupList X EmptyNDL) (merge_right_neutral' X))
      (bigraph_composition
        (p:=permutation_id' (app_merge_NoDupList X Y) (app_merge_NoDupList (app_merge_NoDupList X Y) EmptyNDL) (merge_right_neutral' ((app_merge_NoDupList X Y))))
        (bigraph_parallel_product 
          (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right (app_merge_NoDupList X Y)))) 
          (bigraph_parallel_product
            (up := union_possible_id) 
            (@bigraph_id 0 X)
            (@bigraph_id 0 Y)) 
          H)
        (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (D_ND (void_disjoint_all_list_right X))) (@bigraph_identity 0 X X (permutation_id X)) G)
      )
      F
    )).
  Proof. Admitted.



Fail Theorem nest_associative {I k X m Y n Z sF}
  (F : bigraph sF I k X) (G : bigraph k EmptyNDL m Y) (H : bigraph m EmptyNDL n Z) :
  bigraph_equality
    (nest H (nest G F))
    (nest (nest H G) F).

 
Definition rm_void_parent {s1 r1 node0: FinDecType} 
  (p : type node0 + type (findec_sum voidfd s1) ->
    type node0 + type (findec_sum voidfd r1)) : 
    type node0 + type s1 -> type node0 + type r1.
  Proof. intros [n|s].
    - destruct (p (inl n)) eqn:Epn.
    + left. exact t.
    + right. destruct t. destruct t. exact t.
    - destruct (p (inr (inr s))) eqn:Epn.
    + left. exact t.
    + right. destruct t. destruct t. exact t. Defined.

Definition rm_void_sumtype {r1 : FinDecType} (x:type (findec_sum voidfd r1)) : type r1 := 
  match x with
    | inl t =>
        match t return (type r1) with
        end
    | inr t => t end.
  (* destruct x. destruct t. exact t. Defined. *)

Definition rm_void_sumtype' {r1 : FinDecType} (x:type (findec_sum voidfd r1)) : type r1.
  Proof.
  destruct x. destruct t. exact t. Defined.

Definition rm_void_pair {node root : FinDecType} (pns : type node + type (findec_sum voidfd root)):
  type node + type root :=
  match pns with 
  | inl n => inl n
  | inr (v_r) => inr (rm_void_sumtype' v_r) 
  end.


Definition rm_void_parent' {s1 r1 node0: FinDecType} 
  (p : type node0 + type (findec_sum voidfd s1) ->
    type node0 + type (findec_sum voidfd r1)) : 
    type node0 + type s1 ->
      type node0 + type r1 :=
  (fun ns => match ns with 
    | inl n => rm_void_pair (p (inl n))
    | inr s => rm_void_pair (p (inr (inr s)))
    end).   

Definition rm_void_link {i1 o1 node0 edge0: FinDecType} {control0 : (type node0) -> Kappa} 
  (l : type (findec_sum i1 voidfd) + Port control0 ->
    type (findec_sum i1 o1) + type edge0) : 
      type i1 + Port control0 ->
        type (findec_sum i1 o1) + type edge0 :=
  (fun ip => match ip with 
  | inl i => match l (inl (inl i)) with 
    | inl i1o1 => inl i1o1
    | inr e => inr e 
    end 
  | inr p => match l (inr p) with
    | inl i1o1 => inl i1o1
    | inr e => inr e 
  end end).    *)

(* Lemma acyclic_rm_void_parent {node s r: FinDecType} {n:type node}
  {p: type node + type (findec_sum voidfd s) ->
  type node + type (findec_sum voidfd r)} :
  Acc (fun n' n : type node => p (inl n) = inl n') n
  -> Acc
  (fun n' n0 : type node => rm_void_parent' p (inl n0) = inl n') n.
  Proof. 
    intros H.
    unfold rm_void_parent'.
    unfold rm_void_pair.
    unfold rm_void_sumtype'. simpl.

    eapply Acc_inv in H.
    destruct H as [H_acc].
    - admit.
    - admit.
  Admitted. *)

(* Definition rm_void_finDecSum {s1 i1 o1 r1} 
  (b : bigraph (findec_sum voidfd s1) (app_NoDupList i1 EmptyNDL) (findec_sum voidfd r1) (app_NoDupList i1 o1)) : 
  bigraph s1 i1 r1 (app_NoDupList i1 o1).
  Proof. 
  destruct b. Admitted. *)
  (* apply 
    (Big
      s1 i1 r1 (app_NoDupList i1 o1)
      node0
      edge0
      control0
      (rm_void_parent' parent0)
      (rm_void_link link0)
    ).
    unfold FiniteParent in *.
    intros n.
    specialize (ap0 n).
    apply acyclic_rm_void_parent.
    apply ap0.
    Qed. *)

(* Definition nest {s1 i1 r1 o1 i2} (* TODO check definition*)
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph 0 i2 s1 i1) :=
  (rm_void_finDecSum ((@bigraph_identity voidfd i1) || b1)) <<o>> b2. *)

(* *)




Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph 0 i2 s1 i1. Admitted.


End NestingBig.