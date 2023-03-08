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


(****** Sites as a decidable type ******)
Module Sites.
Import ADec.
Definition site := A.
Definition eq_dec_sites := eq_dec_As.

Definition eq_sites (s1 s2 : site) : Prop :=
    s1 = s2.

Theorem eq_sites_dec: forall (s1 s2 : site),
    { s1 = s2 } + { ~ s1 = s2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_sites_b (s1 s2 : site) : bool.
destruct (eq_dec_sites (s1) (s2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (s1 s2 : site),
    reflect (eq_sites s1 s2) (eq_sites_b s1 s2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_sites_refl : forall n : site, 
    eq_sites n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_sites_sym : forall (s1 s2 : site), 
    eq_sites s1 s2 -> eq_sites s2 s1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_sites_trans : forall (s1 s2 s3: site), 
    (eq_sites s1 s2) -> (eq_sites s2 s3) -> (eq_sites s1 s3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_sites : forall (s1 s2 : site), 
    s1 = s2 <-> eq_sites s1 s2.
Proof. apply eq_eq_eq_As. Qed.

Import Iterable.
Parameter T : Type.
#[refine] Instance sites : Iter T site := {}.
Proof. intros; auto. Qed. 

End Sites.