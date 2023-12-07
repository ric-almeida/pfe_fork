(** Finite Decidable Types *)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import List.
Require Import Euclid.
Require Import Lists.List.
Require Import Arith.
Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Require Import Lia.

Import ListNotations. 
Require Import MyBasics.
Require Import Fintypes.

Record FinDecType : Type :=
    {
      type : Type ;
      finite_type : Finite type ;
      dec_type : EqDec type
    }.

Lemma dec_eq_void : dec_eq void.
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_unit : dec_eq unit.
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_bool : dec_eq bool.
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_nat : dec_eq nat.
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_sum : forall {A B}, dec_eq A -> dec_eq B -> dec_eq (A + B).
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_prod : forall {A B}, dec_eq A -> dec_eq B -> dec_eq (A * B).
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_list : forall {A}, dec_eq A -> dec_eq (list A).
Proof.
unfold dec_eq, decidable.
decide equality.
Qed.

Lemma dec_eq_subset : forall {A} (P : A -> Prop), dec_eq A -> dec_eq { a : A | P a }.
Proof.
unfold dec_eq, decidable.
intros A P Heqaa' a a'.
destruct a as (a, Ha); destruct a' as (a', Ha').
destruct (Heqaa' a a') as [Haa' |Hnaa'].
+ left.
  apply subset_eq_compat.
  assumption.
+ right.
  intro H.
  apply Hnaa'.
  injection H.
  auto.
Qed.

Lemma dec_eq_fun : forall {A B}, dec_eq B -> Finite A -> dec_eq (A -> B).
Proof.
unfold dec_eq, decidable.
intros A B HeqB FA f g.
destruct FA as (lA, (Hl1, Hl2)).
assert (decidable (Forall (fun a => f a = g a) lA)).
+ apply Forall_dec.
  intro a.
  apply HeqB.
+ destruct H as [H | Hnot].
  - left.
    apply functional_extensionality.
    intro a.
    generalize (Hl1 a).
    revert a.
    apply Forall_forall.
    exact H.
  - right.
    intro Heq.
    apply Hnot.
    rewrite Heq.
    apply forall_Forall.
    reflexivity.
Qed.

Lemma dec_eq_dep_prod : forall {A} {B : A -> Type}, (forall a, dec_eq (B a)) -> Finite A -> dec_eq (forall a, B a).
Proof.
unfold dec_eq, decidable.
intros A B HeqBa FA f g.
destruct FA as (lA, (Hl1, Hl2)).
assert (decidable (Forall (fun a => f a = g a) lA)).
+ apply Forall_dec.
  intro a.
  apply (HeqBa a).
+ destruct H as [H | Hnot].
  - left.
    apply functional_extensionality_dep.
    intro a.
    generalize (Hl1 a).
    revert a.
    apply Forall_forall.
    exact H.
  - right.
    intro Heq.
    apply Hnot.
    rewrite Heq.
    apply forall_Forall.
    reflexivity.
Qed.

Lemma dec_eq_dep_sum : forall {A} {B : A -> Type}, dec_eq A -> (forall a, dec_eq (B a)) -> Finite A -> dec_eq ({ a : A &  B a }).
Proof.
unfold dec_eq, decidable.
intros A B HeqA HeqBa FA a1 a2.
destruct FA as (lA, (Hl1, Hl2)).
destruct a1 as (a1, ba1).
destruct a2 as (a2, ba2).
destruct (HeqA a1 a2).
+ subst.
  destruct (HeqBa a2 ba1 ba2).
  - subst.
    left.
    reflexivity.
  - right.
    intro H.
    apply n.
    generalize (projT2_eq H).
    simpl.
    intro H'.
    rewrite <- eq_rect_eq in H'.
    exact H'.
+ right.
  intro H.
  apply n.
  exact (projT1_eq H).
Qed.

Lemma dec_eq_fin : forall {n}, dec_eq (fin n).
Proof.
unfold dec_eq, decidable.
intro n.
destruct a as (a, Ha).
destruct a' as (a', Ha').
destruct (dec_eq_nat a a') as [Heqa' | Hneqaa'].
+ subst.
  left.
  apply subset_eq_compat.
  reflexivity.
+ right.
  intro H.
  apply Hneqaa'.
  injection H.
  auto.
Qed.

Theorem dec_eq_powerset : forall A, Finite A -> dec_eq A -> dec_eq (A -> bool).
Proof.
intros A (lA, (HlA1, HlA2)) HeqA p q.
assert (forall a, decidable (p a = q a)).
+ intro a.
  apply dec_eq_bool.
+ destruct (dec_Forall _ (fun a => p a = q a) X lA).
  - left.
    apply functional_extensionality.
    intro a.
    generalize (HlA1 a).
    revert a.
    apply Forall_forall.
    assumption.
  - right.
    intro Hpq.
    apply n.
    rewrite Hpq.
    apply forall_Forall.
    reflexivity.
Qed.

Theorem dec_injective : forall {A B} (f : A -> B), Finite A -> dec_eq A -> dec_eq B -> decidable (InjectiveXT f).
Proof.
intros A B f (lA, (HlA1, HlA2)) HeqA HeqB.
assert (decidable (Forall (fun a1 => Forall (fun a2 => f a1 = f a2 -> a1 = a2) lA) lA)).
+ apply Forall_dec.
  intro a1.
  apply Forall_dec.
  intro a2.
  destruct (HeqB (f a1) (f a2)).
  - destruct (HeqA a1 a2).
    * left; auto.
    * right; intuition.
  - left; intuition.
+ destruct H.
  - left.
    generalize (Forall_forall _ _ _ f0).
    clear f0.
    intros H a1.
    generalize (Forall_forall _ _ _ (H a1 (HlA1 a1))).
    clear H; intro H.
    intro a2.
    apply H.
    exact (HlA1 a2).
  - right.
    intro Hinjf.
    apply n.
    apply forall_Forall.
    intros a1 Ha1.
    apply forall_Forall.
    intros a2 Ha2.
    apply Hinjf.
Qed.

Definition voidfd :=
  {|
    type        := void;
    dec_type    := dec_eq_void;
    finite_type := finite_void
  |}.

Definition findec_unit :=
  {|
    type        := unit;
    dec_type    := dec_eq_unit;
    finite_type := finite_unit
  |}.

Definition findec_bool :=
  {|
    type        := bool;
    dec_type    := dec_eq_bool;
    finite_type := finite_bool
  |}.

Definition findec_sum (A B : FinDecType) :=
 {|
    type        := (type A) + (type B);
    dec_type    := dec_eq_sum (dec_type A) (dec_type B);
    finite_type := finite_sum _ _ (finite_type A) (finite_type B)
  |}.

Definition findec_prod (A B : FinDecType) :=
 {|
    type        := (type A) * (type B);
    dec_type    := dec_eq_prod (dec_type A) (dec_type B);
    finite_type := finite_prod _ _ (finite_type A) (finite_type B)
  |}.

Definition findec_subset (A : FinDecType) (P : (type A) -> Prop) (HdecP : forall a, decidable (P a)) :=
 {|
    type        := { a : (type A) | P a };
    dec_type    := dec_eq_subset P (dec_type A);
    finite_type := finite_subset P (finite_type A) HdecP
  |}.

Definition findec_fin (n : nat) :=
 {|
    type        := fin n;
    dec_type    := @dec_eq_fin n;
    finite_type := finite_fin n 
  |}.

Definition findec_image (A B : FinDecType) (f : (type A) -> (type B)) :=
 {|
    type        := { b : (type B) | exists a, b = f a };
    dec_type    := dec_eq_subset (fun b => exists a, b = f a) (dec_type B);
    finite_type := finite_image _ _ f (dec_type B) (finite_type A)
  |}.

Definition findec_fun (A B : FinDecType) :=
 {|
    type        := (type A) -> (type B);
    dec_type    := dec_eq_fun (dec_type B) (finite_type A);
    finite_type := finite_power (dec_type A) (finite_type A) (finite_type B)
  |}.

Definition findec_dep_prod (A : FinDecType) (B : type A -> FinDecType) :=
 {|
    type        := forall a : type A, (type (B a));
    dec_type    := dec_eq_dep_prod (fun a => dec_type (B a)) (finite_type A);
    finite_type := finite_dep_prod (dec_type A) (finite_type A) (fun a => finite_type (B a))
  |}.

Definition findec_dep_sum (A : FinDecType) (B : type A -> FinDecType) :=
 {|
    type        := { a : type A & type (B a) };
    dec_type    := dec_eq_dep_sum (dec_type A) (fun a => dec_type (B a)) (finite_type A);
    finite_type := finite_dep_sum (finite_type A) (fun a => finite_type (B a))
  |}.

Definition findec_powerset (A : FinDecType) := findec_fun A findec_bool.

Definition findec_injective_fun (A B : FinDecType) :=
  findec_subset (findec_fun A B) _ (fun f => dec_injective f (finite_type A) (dec_type A) (dec_type B)).



