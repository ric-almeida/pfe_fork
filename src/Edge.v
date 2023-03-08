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

(****** Edge as a decidable type ******)
Module Edges.
Import ADec.
Definition edge := A.
Definition eq_dec_edges := eq_dec_As.

Definition eq_edges (e1 e2 : edge) : Prop :=
    e1 = e2.

Theorem eq_edges_dec: forall (e1 e2 : edge),
    { e1 = e2 } + { ~ e1 = e2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_edges_b (e1 e2 : edge) : bool.
destruct (eq_dec_edges (e1) (e2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (e1 e2 : edge),
    reflect (eq_edges e1 e2) (eq_edges_b e1 e2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_edges_refl : forall n : edge, 
    eq_edges n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_edges_sym : forall (e1 e2 : edge), 
    eq_edges e1 e2 -> eq_edges e2 e1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_edges_trans : forall (e1 e2 e3: edge), 
    (eq_edges e1 e2) -> (eq_edges e2 e3) -> (eq_edges e1 e3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_edges : forall (e1 e2 : edge), 
    e1 = e2 <-> eq_edges e1 e2.
Proof. apply eq_eq_eq_As. Qed.

Import Iterable.
Parameter T : Type.
#[refine] Instance edges : Iter T edge := {}.
Proof. intros; auto. Qed. 

End Edges.
