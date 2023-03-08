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
Module Node.
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

End Node.


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

End Sites.

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

End Edges.

(****** Port as a decidable type ++ ******)


Module Iterable.
Class Iter (T A : Type) : Type := {
    iter : forall {S E : Type},
      S -> (S -> A -> S + E) -> T -> S + E }.

    Module Example_list_nodes.
        Import Node.
        Instance list_nodes : Iter (list node) node := {
            iter := fun S E =>
              fix iter (s : S) (f : S -> node -> S + E) (l : list node) : S + E :=
                match l with
                | [] => inl s
                | x :: l =>
                  match f s x with
                  | inl s => iter s f l
                  | inr e => inr e
                  end
                end }.
    End Example_list_nodes.

Definition fold {T A : Type} `{Iter T A} {S : Type} (s : S)
(f : S -> A -> S) (l : T) : S :=
    match iter (E := Empty_set) s (fun s x => inl @@ f s x) l with
    | inl x => x
    | inr e => match e with end
    end.


Definition length {T A : Type} `{Iter T A} (l : T) : N :=
    fold 0 (fun n _ => N.succ n) l.
End Iterable.

Module Nodes.
Import Iterable.
Import Node.
Parameter T : Type.
#[refine] Instance nodes : Iter T node := {}. (* refine car nodes pas entièrement instancié *)
Proof. intros; auto. Qed.   
End Nodes.


Module Bigraph.
    Import Nodes.

End Bigraph.