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

(****** Innername as a decidable type ******)
Module Innernames.
Import ADec.
Definition innername := A.
Definition eq_dec_innernames := eq_dec_As.

Definition eq_innernames (i1 i2 : innername) : Prop :=
    i1 = i2.

Theorem eq_innernames_dec: forall (i1 i2 : innername),
    { i1 = i2 } + { ~ i1 = i2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_innernames_b (i1 i2 : innername) : bool.
destruct (eq_dec_innernames (i1) (i2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (i1 i2 : innername),
    reflect (eq_innernames i1 i2) (eq_innernames_b i1 i2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_innernames_refl : forall n : innername, 
    eq_innernames n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_innernames_sym : forall (i1 i2 : innername), 
    eq_innernames i1 i2 -> eq_innernames i2 i1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_innernames_trans : forall (i1 i2 i3: innername), 
    (eq_innernames i1 i2) -> (eq_innernames i2 i3) -> (eq_innernames i1 i3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_innernames : forall (i1 i2 : innername), 
    i1 = i2 <-> eq_innernames i1 i2.
Proof. apply eq_eq_eq_As. Qed.

End Innernames.