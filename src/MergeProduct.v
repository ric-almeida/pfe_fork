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
Module MergeBig (s : Signature) (n : Names) (b: Bigraphs s n).
Module pp := ParallelProduct s n b.
Include pp.

Example zero : fin 1. exists 0. lia. Defined.

Definition merge {n:nat} : bigraph n EmptyNDL 1 EmptyNDL. (* merge n+1 = join <<o>> (id 1 [] ⊗ merge n ) with merge 0 = 1 (1 root that's all)*)
  Proof. 
  apply (Big n EmptyNDL 1 EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (fun s => inr zero) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.


(* Definition bigraph_merge_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : union_possible b1 b2}
    : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) 1 (app_merge_NoDupList o1 o2) := 
    bigraph_composition
      (p := _)
      (merge ) 
      (bigraph_parallel_product (up := up) b1 b2).
    
    bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2).
  Proof. *)

End MergeBig.
