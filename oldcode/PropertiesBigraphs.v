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


Require Export Bool DecidableType OrderedType.
Set Implicit Arguments.

From MyProofs Require Import AlgebraBigraphs. 



(* Module Type IdDec.

Parameter A : Type.
Parameter eq_decA : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

End IdDec.

Module Properties (IDD : IdDec).
  Import IDD.
  Definition A := IDD.A.

  Definition getIdNode (n : node A) : A :=
    match n with Node (Id idn) => idn 
    end.

  Definition eq_nodes (n1 n2:node A) : Prop :=
      getIdNode n1 = getIdNode n2.
  
  Definition eq_nodes_dec: forall (n1 n2 : node A),
    { getIdNode n1 = getIdNode n2 } + { ~ getIdNode n1 = getIdNode n2 }.
    intros. destruct n1 as [a1], n2 as [a2].
    destruct (eq_decA (getIdNode (Node a1)) (getIdNode (Node a2))); [left | right].
    - apply e.
    - apply n.
  Defined.

  Definition eq_nodes_b (n1:node A) (n2:node A) : bool.
    destruct (eq_decA (getIdNode n1) (getIdNode n2)).
    - exact true.
    - exact false.
    Defined.

  Theorem eqb_eq_dec_reflects : forall (n1 n2 : node A),
    reflect (eq_nodes n1 n2) (eq_nodes_b n1 n2).
  Proof.
    intros. unfold eq_nodes_b.
    destruct (eq_nodes_dec n1 n2) as [H1 | H2].
    - destruct eq_decA as [h1 | h2].
      + constructor. apply h1.
      + constructor. apply h2.
    - destruct eq_decA as [h1 | h2].
      + constructor. apply h1.
      + constructor. apply h2.
  Qed.

  Lemma eq_nodes_refl : forall n : node A, 
    eq_nodes n n.
  Proof. intros. unfold eq_nodes. unfold getIdNode. reflexivity. Qed.   

  Lemma eq_nodes_sym : forall (n1 n2 : node A), 
    eq_nodes n1 n2 -> eq_nodes n2 n1.
  Proof. intros. unfold eq_nodes.
  unfold eq_nodes in H. symmetry in H. apply H. Qed.   

  Lemma eq_nodes_trans : forall (n1 n2 n3: node A), 
    ((eq_nodes n1 n2) /\ (eq_nodes n2 n3)) -> (eq_nodes n1 n3).
  Proof. intros. unfold eq_nodes. 
  unfold eq_nodes in H. destruct H as [H1 H2].
  rewrite H1. rewrite H2. reflexivity. Qed.    *)


  (* Fixpoint getk {A:Type} (n:node A) (c:control A) : option :=
    match c with 
      | [] => None
      | (n', idk, k) :: q => if (eq_nodes_b n n') then Some k else getk n q
    end. 


  Example k_v0: getk v0 mybig = Some 2.
  Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
  Example k_v1: getk v1 mybig = Some 2.
  Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
  Example k_v2: getk v2 mybig = Some 4.
  Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.

  Fixpoint count_links_to_node {A: Type} (n:node A) (b:bigraph A) :=
    0. 

End Properties.
*)
