Require Import ConcreteBigraphs.
Require Import SignatureBig.
Require Import FinDecTypes.
Require Import MyBasics.
Require Import Bijections.
Require Import FunctionalExtensionality.

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
Import SignatureBig.
Fail End MySig. (*TODO figure out how ot import the definitions*)

Definition Port {node : Type} (control : node -> Kappa): Type :=
  { n : node & fin (Arity (control n)) }.

Definition join {A B C : Type} (p : A -> C) (q : B -> C) (ac : A+B) : C :=
  match ac with
  | inl a => (p a)
  | inr b => (q b)
  end.

Definition bij_join_port_forward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa) :
  Port c1 + Port c2 -> 
  Port (join c1 c2).
  Proof.
  refine (fun p => match p with
              | inl (existT _ vi1 Hvi1) => _
              | inr (existT _ vi2 Hvi2) => _
              end).
  + exists (inl vi1).
    destruct Hvi1 as (i1, Hi1).
    exists i1.
    exact Hi1.
  + exists (inr vi2).
    destruct Hvi2 as (i2, Hi2).
    exists i2.
    exact Hi2.
  Defined.

Definition bij_join_port_backward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  Port (join c1 c2) -> Port c1 + Port c2.
  Proof.
    destruct 1 as ([v1 | v2], (i, Hvi)).
    + left.
      exists v1.
      exists i.
      apply Hvi.
    + right.
      exists v2.
      exists i.
      apply Hvi.
    Defined.

Definition bij_join_port { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  bijection (Port c1 + Port c2) (Port (join c1 c2)).
  Proof.
  apply 
    (mkBijection _ _ 
    (bij_join_port_forward c1 c2) 
    (bij_join_port_backward c1 c2)).
  + apply functional_extensionality.
    destruct x as ([v1|v2], (i, Hvi)).
    - reflexivity.
    - reflexivity.
  + apply functional_extensionality.
    destruct x as [(v1, (i1, Hvi1)) | (v2, (i2, Hvi2))].
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
  Defined.

Definition bij_port_void (c : void -> Kappa) : bijection (Port c) void.
  Proof.
  apply (mkBijection _ _ (fun vi => match vi with existT _ v _ => void_univ_embedding v end) (void_univ_embedding)).
  + apply functional_extensionality.
    destruct x.
  + apply functional_extensionality.
    destruct x as (v, (i, H)).
    destruct v.
  Defined.

End MySig.

Module MyBigraph.
  Module Mb := Bigraphs MySig.

  Fail Print Mb.Kappa.
  Fail Import Mb.

  (* Example zero : Kappa. exists 0. auto. Defined. *)

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
  P zero1.
  intros [n pf]. 
  unfold zero1.
  assert (n=0).
  - induction n as [| n']. 
    + reflexivity.        
    + inversion pf. inversion H0.
  - Admitted.  

(* Example simplBig : 
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
  Admitted. *)
  
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