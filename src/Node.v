From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.


Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.


Notation " f @@ x " := (apply f x)
  (at level 42, right associativity).


Set Warnings "-parsing".
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "parsing".

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope bool_scope.
Local Open Scope N. 
Import ListNotations.

Set Implicit Arguments.

From MyProofs Require Import Decidable Iterable. 

(*********************START OF DOC*********************)

(****** Nodes as a decidable type ******)
Module Node.
Import ADec.
Definition node := A.
Definition eq_dec_nodes := eq_dec_As.

Definition eq_nodes (n1 n2 : node) : Prop :=
    n1 = n2.

Theorem eq_nodes_dec: forall (n1 n2 : node),
    { n1 = n2 } + { ~ n1 = n2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_nodes_b (n1 n2 : node) : bool.
destruct (eq_dec_nodes (n1) (n2)).
- exact true.
- exact false.
Defined.

Theorem eqnodeb_eqnode_reflects : forall (n1 n2 : node),
    reflect (eq_nodes n1 n2) (eq_nodes_b n1 n2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_nodes_refl : forall n : node, 
    eq_nodes n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_nodes_sym : forall (n1 n2 : node), 
    eq_nodes n1 n2 -> eq_nodes n2 n1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_nodes_trans : forall (n1 n2 n3: node), 
    (eq_nodes n1 n2) -> (eq_nodes n2 n3) -> (eq_nodes n1 n3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_nodes : forall (n1 n2 : node), 
    n1 = n2 <-> eq_nodes n1 n2.
Proof. apply eq_eq_eq_As. Qed.

End Node.


Module Nodes.
Import Iterable.
Import Node.
Parameter T : Type.
#[refine] Instance nodes : Iter T node := {}. (* refine car nodes pas entièrement instancié *)
Proof. intros; auto. Qed.   
End Nodes.
