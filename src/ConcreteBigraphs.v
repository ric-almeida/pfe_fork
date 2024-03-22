Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".


Require Import Coq.Logic.Decidable.
Require Import Coq.Setoids.Setoid.
(* Require Import ToolsForBigraphs. *)
Require Import FinFun.
Require Import MyBasics.
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


Import ListNotations.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Type Bigraphs (s : Signature) (n : Names).
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
    control : (type node) -> Kappa ;
    parent : (type node) + (fin site) -> (type node) + (fin root) ; 
    link : (NameSub innername) + (Port control) -> (NameSub outername) + (type edge); 
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

Theorem innername_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n:Name, forall Hn: In n i, forall Hn':In n i,
  get_link b (inl (exist _ n Hn)) = get_link b (inl (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Definition bigraph_empty : bigraph 0 EmptyNDL 0 EmptyNDL.
  Proof.
  eapply (Big 0 EmptyNDL 0 EmptyNDL
            voidfd voidfd
            (@void_univ_embedding _)
            (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero))
            _ 
            ).
  - intro n.
  destruct n.
  Unshelve.
  intros. destruct X.
  + left. apply n.
  + destruct p0. right. apply x.
  Defined. (*TODO unsure of the definition of link def 2.7*)

Global Notation "∅" := bigraph_empty.

Definition bigraph_identity {s i i'} {p:PermutationNames (ndlist i) (ndlist i')}: bigraph s i s i'. (*actually s i s (permutation i) *)
  Proof.
  apply (Big s i s i'
          voidfd (*node : ∅*)
          voidfd (*edge : ∅*)
          (@void_univ_embedding _) (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  - intros [inner | port]. (*link_|{names} : id*)
    + left. destruct inner. exists x. destruct p as[p]. unfold permutation in p. apply p in i0. apply i0.
    + destruct port. destruct x.
  - intro n. (*acyclic parent*)
    destruct n.
  Defined.
  
Definition bigraph_id (s: nat) (i : NoDupList) := @bigraph_identity s i i (P_NP (permutation_id i)).
End Bigraphs.

