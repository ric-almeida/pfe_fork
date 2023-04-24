From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.


Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Decidable.
Require Import Lia.


Set Warnings "-parsing".
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "parsing".

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope bool_scope.
Import ListNotations.  

Set Implicit Arguments.

(* From MyProofs Require Import Decidable.  *)



Module Bigraph.

(* Definition node : Type := Type.
Definition root : Type := Type.
Definition site : Type.
Definition edge : Type.
Definition innername : Type.
Definition outername : Type.
Definition port : Type.

Definition place : Type := root + node + site.
Definition link : Type := edge + outername.
Definition point : Type := port + innername.

Definition kappa : Type := ADec.A * nat.
Definition control : Type := node -> kappa.

Definition parent : Type := node + site -> node + root. *)

(* Function decidability_A (A : Type) : Prop := forall (x y : A), {x = y} + {~x = y}.

Definition decidability_nat : forall (x y : nat), {x = y} + {~x = y} := (decidability_A nat). *)

(* Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }. *)

Record bigraph {site innername root outername : Type} : Type := Big 
  { 
    node : Type ;
    edge : Type ;
    control : node -> nat * nat; (* k * nat *)
    parent : node + site -> node + root ; 
    link : innername + {x : node * nat | snd x < snd (control (fst x))} -> outername + edge; 
    sd : EqDec site ;
    sf : Finite site ;
    id_ : EqDec innername ;
    if_ : Finite innername ;
    rd : EqDec root ;
    rf : Finite root ;
    od : EqDec outername ;
    of : Finite outername ;
    nd : EqDec node ;
    nf : Finite node ;
    ed : EqDec edge ;
    ef : Finite edge ;
  }.


  (* Definition mySite : Type := nat.
  Definition myInnerName : Type := nat.
  Definition myRoot : Type := nat.
  Definition myOuterName : Type := nat.
  Definition myNode : Type := {n:nat | n<3}.
  Definition myEdge : Type := nat.
  
  Definition myControl : myNode -> nat * nat := fun _ => (10, 20).
  Definition myParent : myNode + mySite -> myNode + myRoot := fun _ => inr 2.
  Definition myLink : myInnerName + {x : myNode * nat | snd x < snd (myControl (fst x))} -> 
    myOuterName + myEdge := fun _ => inr 1.


  Definition Full (l:list myNode) :=
  forall n:myNode, In n l.


  Definition node0 : myNode.
  Proof. unfold myNode. exists 0. auto. Qed.

  Definition node1 : myNode.
  Proof. unfold myNode. exists 1. auto. Qed.

  Definition node2 : myNode.
  Proof. unfold myNode. exists 2. auto. Qed.




  Lemma myFinite : forall n:myNode, exists (l:list myNode), Full l.
  Proof.
  intros n. 
  unfold Full. exists [node0;node1;node2]. intros. destruct n0 as [n0 Hn0 Hn1 Hn2].
  apply Hn0. exists. unfold node0. 
  
  
  
  right. right. right. contradiction.  

  Instance EqDec_nat : EqDec nat := {| eq_dec := PeanoNat.Nat.eq_dec |}.

  
  Definition myBigraph : bigraph :=
    Big myParent myLink EqDec_nat. *)
  






End Bigraph.