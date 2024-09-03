Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".


(* Require Import Coq.Logic.Decidable.
Require Import Coq.Setoids.Setoid. *)
(* Require Import ToolsForBigraphs. *)
(* Require Import FinFun. *)
Require Import MyBasics.
Require Import MyEqNat.
Require Import Basics.
Require Import Morphisms.
Require Import FinDecTypes.
Require Import Bijections.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import SignatureBig.
Require Import Names.


Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Lia.
Require Import Coq.Arith.Compare_dec.


(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finfun.  *)



Include MyEqNat. 

Import ListNotations.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs (sp : SignatureParameter) (np : Names.NamesParameter).
Module s := Signature sp.
Module n := Names np.
Include s.
Include n.
(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.

Record bigraph  (site: nat) 
                (innername: NoDupList) 
                (root: nat) 
                (outername: NoDupList) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    control : type node -> Kappa ;
    parent : type node + fin site -> 
                (type node) + (fin root) ; 
    link : NameSub innername + Port control -> 
                (NameSub outername) + (type edge); 
    ap : FiniteParent parent ;
  }.
  

End IntroBigraphs.

(** * Getters
  This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  node s i r o bg.
Definition get_edge {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  edge s i r o bg.
Definition get_control {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : type (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : (type (get_node bg)) + (fin s) -> (type (get_node bg)) + (fin r) :=
  @parent s i r o bg.
Definition get_link {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : {inner:Name | In inner i} + Port (get_control bg) -> {outer:Name | In outer o} + type (get_edge bg) :=
  @link s i r o bg.
End GettersBigraphs.

(** Tools for proof irrelevance *)

Theorem parent_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n n': nat, forall Hn Hn', n = n' ->
  get_parent b (inr (exist _ n Hn)) = get_parent b (inr (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Theorem parent_proof_irrelevant' {s i r o} (b:bigraph s i r o): 
  forall n n': nat, forall Hn Hn', n = n' ->
  get_parent b (inr (exist _ n Hn)) = get_parent b (inr (exist _ n' Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. apply H.
  Qed.

Theorem innername_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n:Name, forall Hn: In n i, forall Hn':In n i,
  get_link b (inl (exist _ n Hn)) = get_link b (inl (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.

(** Section defining some elementary bigraphs *)
Section ElementaryBigraphs. 
Definition bigraph_id (s: nat) (i : NoDupList) : bigraph s i s i. (*actually s i s (permutation i) *)
  Proof.
  apply (Big s i s i
          voidfd (*node : ∅*)
          voidfd (*edge : ∅*)
          (@void_univ_embedding _) (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  - intros [inner | port]. (*link_|{names} : id*)
    + left. apply inner. 
    + destruct port. destruct x.
  - intro n. (*acyclic parent*)
    destruct n.
  Defined.

Definition bigraph_empty : bigraph 0 EmptyNDL 0 EmptyNDL := bigraph_id 0 EmptyNDL.
Example zero1 : type (findec_fin 1). exists 0. auto. Defined.

Definition discrete_atom {A} 
  (a:type A) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 0 EmptyNDL 1 o.
  eapply (Big
      0 EmptyNDL 1 o
      A
      voidfd
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr zero1
        | inr s => _
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    3:{ intros [i|p].  
      - destruct i as [i H]. elim H. 
      - left. unfold NameSub. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (nth p o DefaultName). 
      apply nth_In. destruct Hkappa as [Hkappa]. rewrite <- Hkappa. assumption. } (*link*)
    2:{ destruct s. apply Nat.nlt_0_r in l. elim l. } (*parent*)
    unfold FiniteParent. simpl. (*acyclic*)
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    Defined. 

Definition discrete_ion {A} 
  (a:type A) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 1 EmptyNDL 1 o.
  eapply (Big
      1 EmptyNDL 1 o
      A
      voidfd
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr zero1
        | inr s => inl a
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    2:{ intros [i|p].  
      - destruct i as [i H]. elim H. 
      - left. unfold NameSub. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (nth p o DefaultName). 
      apply nth_In. destruct Hkappa as [Hkappa]. rewrite <- Hkappa. assumption. } (*link*)
    unfold FiniteParent. simpl.
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    Defined. 

Definition permutationbig (n : nat) : bigraph n EmptyNDL n EmptyNDL. 
  Proof. 
  apply (Big n EmptyNDL n EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_-> Kappa*)
    (fun sn => match sn with |inr s => inr s | inl n => match n with end end) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition merge {n:nat} : bigraph n EmptyNDL 1 EmptyNDL.
  Proof. 
  apply (Big n EmptyNDL 1 EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅ ->_Kappa*)
    (fun s => inr zero1) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition big_1 := @merge 0.

Definition symmetry_big (m:nat) (X:NoDupList) (n:nat) (Y:NoDupList) :
  bigraph (m+n) (X ∪ Y) (m+n) (X ∪ Y).
  Proof. 
    eapply (Big (m+n) (X ∪ Y) (m+n) (X ∪ Y)
      voidfd (*node : ∅*)
      voidfd (*edge : ∅*)
      (@void_univ_embedding _) (*control : ∅ ->_Kappa*)
      _ _ _
    ).
    Unshelve.
    - intros [v|s]. (*parent*)
      + destruct v.
      + right. destruct s as [s Hs].
      destruct (lt_dec s m).
      * exists (s+n). lia.
      * exists (s-m). lia.
    - intros [inner | port]. (*link : ∅*)
      + left. apply inner.
      + destruct port. destruct x.
    - intro n'. (*acyclic parent*)
    destruct n'.
  Defined.

Definition substitution (i:NoDupList) (name:Name) : bigraph 0 i 0 (OneelNDL name).
  Proof. 
  apply (Big 0 i 0 (OneelNDL name)
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero)) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. exists name. simpl. left. reflexivity.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition closure (name:Name) : bigraph 0 (OneelNDL name) 0 EmptyNDL.
  Proof. 
  apply (Big 0 (OneelNDL name) 0 EmptyNDL
    voidfd (*node : ∅*)
    findec_unit (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero)) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + right. simpl. exact tt. 
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition join_big := @merge 2. 
End ElementaryBigraphs.

Global Notation "∅" := bigraph_empty.

End Bigraphs.

