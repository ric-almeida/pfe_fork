Require Import ConcreteBigraphs.
Require Import SignatureBig.
Require Import FinDecTypes.
Require Import MyBasics.

Set Printing All.

Locate Signature.
Print SignatureBig.Signature.
Module MySig <: Signature. (*with (Kappa := type (findec_fin 3)).*)
Definition Kappa : Type := type (findec_fin 1).

Definition Arity : Kappa -> nat := 
  (fun 
    k => match k with 
    | exist _ n _ => n + 1
    end
  ).

End MySig.

Module MyBigraph.
  Module Mb := Bigraphs MySig.

  Print Mb.Kappa.
  Import Mb.

  Example zero : Kappa. exists 0. auto. Defined.

  Example zero1 : type (findec_fin 1). exists 0. auto. Defined.
  (* Variable A : Type.

Variable f : A -> nat.
Require Import Nat.
Definition ltof (a b:A) := f a < f b.
  Theorem well_founded_ltof : well_founded ltof.
  Proof.
  assert (H : forall n (a:A), f a < n -> Acc ltof a).
  { intro n; induction n as [|n IHn].
    - intros a Ha. absurd (f a < 0). auto. admit. 
    - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
      apply IHn. apply Nat.lt_le_trans with (f a); auto. now apply Nat.succ_le_mono. }
  intros a. apply (H (S (f a))). apply Nat.lt_succ_diag_r.
Defined. *)

Variable A : Type.
Variable f : A -> nat.
Variable R : A -> A -> Prop.


(* Theorem well_founded_lt_compat : well_founded R.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc R a).
  { intro n; induction n as [|n IHn].
    - intros a Ha; absurd (f a < 0); auto. admit . (*apply Nat.nlt_0_r.*)
    - intros a Ha. apply Acc_intro. intros b Hb.
      apply IHn. admit. }
  intros a. apply (H (S (f a))). apply Nat.lt_succ_diag_r.
Defined. *)

Lemma forallfin1 (P : type (findec_fin 1) -> Prop) :
forall n0 : type (findec_fin 1), P n0 -> 
  P zero.
  intros [n pf]. 
  unfold zero.
  assert (n=0).
  - induction n as [| n']. 
    + reflexivity.        
    + inversion pf. inversion H0.
  - Admitted.  

Example simplBig : 
  bigraph (findec_fin 1) (findec_fin 1) (findec_fin 1) (findec_fin 1).
  apply (Big
    (findec_fin 1) (findec_fin 1) (findec_fin 1) (findec_fin 1)
    (findec_fin 1)
    (findec_fin 0)
    (fun n => match n with | _ => zero end) (*control*)
    (fun ns => match ns with 
      | inl _ => inl zero1
      | inr _ => inl zero
    end) (*parent*)
    (fun ip => match ip with 
      | inl _ => inl zero1 
      | inr _ => inl zero1
    end) (*link*)
  ).
  unfold FiniteParent.
  intros [n pf]. 
  unfold zero1.
  assert (n=0).
  - induction n as [| n']. 
    + reflexivity.        
    + inversion pf. inversion H0. (* n = 0, done *)
  - simpl. 
  Admitted.
  
  (* assert (
    (exist (fun p : nat => p < 1) 0 (le_n 1))
    =
    (exist (fun p : nat => p < 1) n pf)
  ).
  + induction n as [|n' Hn'].
    ++ apply f_equal. admit. 
    ++ exfalso. inversion pf. inversion H1.
  + rewrite H0.  
  set (p1 := (exist (fun p : nat => p < 1) n pf)). *)
  


End MyBigraph.