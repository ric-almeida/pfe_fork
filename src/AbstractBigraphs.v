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


Module IdDec.

Parameter A : Type.
Parameter eq_dec_A : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

End IdDec.


Module Nodes.
Definition node := IdDec.A.
Definition hyp_eq_dec_nodes := IdDec.eq_dec_A.

Definition eq_nodes (n1 n2 : node) : Prop :=
    n1 = n2.

Theorem eq_nodes_dec: forall (n1 n2 : node),
    { n1 = n2 } + { ~ n1 = n2 }.
Proof. intros. 
destruct (hyp_eq_dec_nodes (n1) (n2)); [left | right].
- apply e.
- apply n.
Qed.

Definition eq_nodes_b (n1 n2 : node) : bool.
destruct (hyp_eq_dec_nodes (n1) (n2)).
- exact true.
- exact false.
Defined.

Theorem eqb_eq_dec_reflects : forall (n1 n2 : node),
    reflect (eq_nodes n1 n2) (eq_nodes_b n1 n2).
Proof.
intros. unfold eq_nodes_b.
destruct (eq_nodes_dec n1 n2) as [H1 | H2].
- destruct hyp_eq_dec_nodes as [h1 | h2].
+ constructor. apply h1.
+ constructor. apply h2.
- destruct hyp_eq_dec_nodes as [h1 | h2].
+ constructor. apply h1.
+ constructor. apply h2.
Qed.

Lemma eq_nodes_refl : forall n : node, 
    eq_nodes n n.
Proof. intros. unfold eq_nodes. reflexivity. Qed.   

Lemma eq_nodes_sym : forall (n1 n2 : node), 
eq_nodes n1 n2 -> eq_nodes n2 n1.
Proof. intros. unfold eq_nodes.
unfold eq_nodes in H. symmetry in H. apply H. Qed.   

Lemma eq_nodes_trans : forall (n1 n2 n3: node), 
(eq_nodes n1 n2) -> (eq_nodes n2 n3) -> (eq_nodes n1 n3).
Proof. intros. unfold eq_nodes. 
unfold eq_nodes in H. 
rewrite H. rewrite H0. reflexivity. Qed.   

(* id1 = id2 <-> eq_nodes (Node (Id id1)) (Node (Id id2)) *)
End Nodes.
