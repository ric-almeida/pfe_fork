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

(****** Roots as a decidable type ******)
Module Roots.
Import ADec.
Definition root := A.
Definition eq_dec_roots := eq_dec_As.

Definition eq_roots (r1 r2 : root) : Prop :=
    r1 = r2.

Theorem eq_roots_dec: forall (r1 r2 : root),
    { r1 = r2 } + { ~ r1 = r2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_roots_b (r1 r2 : root) : bool.
destruct (eq_dec_roots (r1) (r2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (r1 r2 : root),
    reflect (eq_roots r1 r2) (eq_roots_b r1 r2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_roots_refl : forall n : root, 
    eq_roots n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_roots_sym : forall (r1 r2 : root), 
    eq_roots r1 r2 -> eq_roots r2 r1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_roots_trans : forall (r1 r2 r3: root), 
    (eq_roots r1 r2) -> (eq_roots r2 r3) -> (eq_roots r1 r3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_roots : forall (r1 r2 : root), 
    r1 = r2 <-> eq_roots r1 r2.
Proof. apply eq_eq_eq_As. Qed.

Import Iterable.
Parameter T : Type.
#[refine] Instance roots : Iter T root := {}.
Proof. intros; auto. Qed. 

End Roots.