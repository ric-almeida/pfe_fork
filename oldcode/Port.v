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

From MyProofs Require Import Decidable Iterable Node. 

(*********************START OF DOC*********************)


(******* Ports as a decidable type ******)

Module Ports.
Import ADec.
Import Nodes.
Definition IdP := A.
Definition eq_dec_IdP := eq_dec_As.

Theorem eq_IdP_dec: forall (id1 id2 : IdP), {id1 = id2} + {~ id1 = id2}.
Proof. apply eq_dec_IdP. Qed.


Definition port : Type := node * IdP.
Theorem eq_dec_ports : forall (p1 p2 : port), {p1 = p2} + {~ p1 = p2}.
Proof. intros (a, b) (c, d). 

destruct (eq_dec_As (a) (c)); destruct (eq_dec_As (b) (d)).
- rewrite e. rewrite e0. left. reflexivity.
- right. injection. auto.
- right. injection. auto.
- right. injection. auto.
Qed.

Definition eq_ports (p1 p2 : port) : Prop :=
    p1 = p2.

Definition eq_ports_b (p1 p2 : port) : bool.
destruct (eq_dec_ports (p1) (p2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (p1 p2 : port),
    reflect (eq_ports p1 p2) (eq_ports_b p1 p2).
Proof. intros. 
unfold eq_ports_b; destruct (eq_dec_ports (p1) (p2)) as [H1|H2] ; destruct (eq_dec_ports (p1) (p2)) as [H3|H4].
- constructor. apply H1.
- constructor. apply H1.
- constructor. apply H2.
- constructor. apply H2. Qed.

Lemma eq_ports_refl : forall n : port, 
    eq_ports n n.
Proof. intros. unfold eq_ports. reflexivity. Qed.   

Lemma eq_ports_sym : forall (p1 p2 : port), 
    eq_ports p1 p2 -> eq_ports p2 p1.
Proof. intros. unfold eq_ports. symmetry. apply H. Qed.   

Lemma eq_ports_trans : forall (p1 p2 p3: port), 
    (eq_ports p1 p2) -> (eq_ports p2 p3) -> (eq_ports p1 p3).
Proof. intros. unfold eq_ports. 
unfold eq_ports in H.
unfold eq_ports in H0. rewrite <- H0. rewrite <- H. reflexivity. Qed.   

Theorem eq_eq_eq_ports : forall (p1 p2 : port), 
    p1 = p2 <-> eq_ports p1 p2.
Proof. intros. unfold eq_ports. split; auto. Qed.

Import Iterable.
Parameter T : Type.
#[refine] Instance ports : Iter T port := {}.
Proof. intros; auto. Qed. 

End Ports.


