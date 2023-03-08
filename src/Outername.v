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

(****** Outername as a decidable type ******)
Module Outernames.
Import ADec.
Definition outername := A.
Definition eq_dec_outernames := eq_dec_As.

Definition eq_outernames (o1 o2 : outername) : Prop :=
    o1 = o2.

Theorem eq_outernames_dec: forall (o1 o2 : outername),
    { o1 = o2 } + { ~ o1 = o2 }.
Proof. apply eq_As_dec. Qed.

Definition eq_outernames_b (o1 o2 : outername) : bool.
destruct (eq_dec_outernames (o1) (o2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (o1 o2 : outername),
    reflect (eq_outernames o1 o2) (eq_outernames_b o1 o2).
Proof. apply eqAb_eqA_reflects. Qed.

Lemma eq_outernames_refl : forall n : outername, 
    eq_outernames n n.
Proof. apply eq_As_refl. Qed.   

Lemma eq_outernames_sym : forall (o1 o2 : outername), 
    eq_outernames o1 o2 -> eq_outernames o2 o1.
Proof. apply eq_As_sym. Qed.   

Lemma eq_outernames_trans : forall (o1 o2 o3: outername), 
    (eq_outernames o1 o2) -> (eq_outernames o2 o3) -> (eq_outernames o1 o3).
Proof. apply eq_As_trans. Qed.   

Theorem eq_eq_eq_outernames : forall (o1 o2 : outername), 
    o1 = o2 <-> eq_outernames o1 o2.
Proof. apply eq_eq_eq_As. Qed.

End Outernames.