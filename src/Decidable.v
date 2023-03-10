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

(*********************START OF DOC*********************)

(****** A module for basic proofs of decidable types ******)
Module ADec.

Parameter A : Type.
Parameter eq_dec_As : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

Definition eq_As (a1 a2 : A) : Prop :=
    a1 = a2.

Theorem eq_As_dec: forall (a1 a2 : A),
    { a1 = a2 } + { ~ a1 = a2 }.
Proof. intros. 
destruct (eq_dec_As (a1) (a2)); [left | right].
- apply e.
- apply n.
Qed.

Definition eq_As_b (a1 a2 : A) : bool.
destruct (eq_dec_As (a1) (a2)).
- exact true.
- exact false.
Defined.

Theorem eqAb_eqA_reflects : forall (a1 a2 : A),
    reflect (eq_As a1 a2) (eq_As_b a1 a2).
Proof.
intros. unfold eq_As_b.
destruct (eq_As_dec a1 a2) as [H1 | H2].
- destruct eq_dec_As as [h1 | h2].
+ constructor. apply h1.
+ constructor. apply h2.
- destruct eq_dec_As as [h1 | h2].
+ constructor. apply h1.
+ constructor. apply h2.
Qed.

Lemma eq_As_refl : forall n : A, 
    eq_As n n.
Proof. intros. unfold eq_As. reflexivity. Qed.   

Lemma eq_As_sym : forall (a1 a2 : A), 
    eq_As a1 a2 -> eq_As a2 a1.
Proof. intros. unfold eq_As.
unfold eq_As in H. symmetry in H. apply H. Qed.   

Lemma eq_As_trans : forall (a1 a2 a3: A), 
    (eq_As a1 a2) -> (eq_As a2 a3) -> (eq_As a1 a3).
Proof. intros. unfold eq_As. 
unfold eq_As in H. 
rewrite H. rewrite H0. reflexivity. Qed.   

Theorem eq_eq_eq_As : forall (a1 a2 : A), 
    a1 = a2 <-> eq_As a1 a2.
Proof. intros. split; intros; apply H. Qed.

End ADec.


Module AADec.
Import ADec.
Definition AA : Type := A*A .

Theorem eq_AAs_dec: forall (aa1 aa2 : AA),
    { aa1 = aa2 } + { ~ aa1 = aa2 }.
Proof. intros (a, b) (c, d). 

destruct (eq_dec_As (a) (c)); destruct (eq_dec_As (b) (d)).
- rewrite e. rewrite e0. Admitted.