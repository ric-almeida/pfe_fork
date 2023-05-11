
Definition decidable (P : Prop) := { P } + { ~P }.

Definition DecPred (A : Type) := { P : A -> Prop & forall a, decidable (P a) }.

Inductive finite : Type -> Type :=
| finite_void : finite Empty_set
| finite_unit : finite unit
| finite_sum : forall A B, finite A -> finite B -> finite (A+B)
| finite_subset : forall A (P : DecPred A), finite A -> finite { a : A | projT1 P a }.

Definition proj1_decpred_sum (A B : Type) (P : DecPred (A+B)) : DecPred A.
Proof.
destruct P as (P, pr).
exists (fun a => P (inl a)).
intro a.
apply (pr (inl a)).
Defined.

Definition proj2_decpred_sum (A B : Type) (P : DecPred (A+B)) : DecPred B.
Proof.
destruct P as (P, pr).
exists (fun a => P (inr a)).
intro a.
apply (pr (inr a)).
Defined.

Definition comp_decpred (A : Type) (P : DecPred A) (Q : DecPred {a : A | projT1 P a }) : DecPred A.
Proof.
destruct P as (P, prP).
destruct Q as (Q, prQ).
simpl in Q, prQ.
exists (fun a => match prP a with | left Pa => Q (exist _ a Pa) | right _ => False end).
intro a.
destruct (prP a).
+ destruct (prQ (exist _ a p)); intuition.
+ right; intuition.
Defined.

Definition DecPredTrue (A : Type) : DecPred A.
Proof.
exists (fun a => True).
intro a.
left.
trivial.
Defined.

Fixpoint count (T : Type) (fin : finite T) : DecPred T -> nat :=
 match fin in finite T return (DecPred T -> nat) with
 | finite_void              => (fun P => 0)
 | finite_unit              => (fun P => let (P, prP) := P in if prP tt then 1 else 0)
 | finite_sum A B finA finB => (fun P => count A finA (proj1_decpred_sum A B P) + count B finB (proj2_decpred_sum A B P))
 | finite_subset A Q finA   => (fun P => count A finA (comp_decpred A Q P))
 end.

Definition cardinal (A : Type) (finA : finite A) : nat := count A finA (DecPredTrue A).
