From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.



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

(****** Nodes as a decidable type ******)
Module Nodes.
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

End Nodes.


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

End Roots.


(****** Sites as a decidable type ******)

(****** Outername as a decidable type ******)

(****** Innername as a decidable type ******)

(****** Edge as a decidable type ******)

(****** Port as a decidable type ******)


Module Bigraph.
    Import Nodes.

    Check node : Type.
    Fail Check root : Type.

End Bigraph.