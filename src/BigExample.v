Require Import ConcreteBigraphs.
Require Import SignatureBig.
Require Import FinDecTypes.
Require Import MyBasics.
Require Import Bijections.
Require Import Names.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.CRelationClasses.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Sumbool.





Import ListNotations.

Module MySigP <: SignatureParameter. (*with (Kappa := type (findec_fin 3)).*)
Definition Kappa : Type := nat.

Definition Arity : Kappa -> nat := id.

End MySigP. (*TODO figure out how ot import the definitions*)


Module MyNamesP <: Names.NamesParameter.
Definition Name := string.
Definition EqDecN : forall x y : Name, {x = y} + {x <> y} := string_dec.
Local Open Scope string_scope.
Definition InfName : forall l : list string, exists n : string, ~ In n l. 
  intros.
  induction l as [|x l IHl].
  - exists "a". auto.
  - Admitted.
End MyNamesP.

Module MyBigraph := Bigraphs MySigP MyNamesP.
Include MyBigraph.

Example zero1 : type (findec_fin 1). exists 0. auto. Defined.
Example b : string := "b".
Example bNDL : NoDupList.
exists [b]. constructor; auto. constructor. Defined.

Example a : string := "a".
Example aNDL : NoDupList.
exists [a]. constructor; auto. constructor. Defined.

Example simplBig : 
  bigraph 1 bNDL 1 aNDL.
  eapply (Big
    1 bNDL 1 aNDL
    (findec_fin 2)
    findec_unit
    (fun n => match n with | exist _ n _ => n+1 end) (*control*)
    (fun ns => match ns with 
      | inl n => inr zero1
      | inr s => _
    end) (*parent*)
    _ (*link*)
  ). 
  Unshelve.
  3:{ intros [b|p]. (*link*)
  + (*link b*) right. exact tt.
  + destruct p. destruct x.
  induction x as [|x' H] eqn:E.
  * right. exact tt.
  * assert (x'=0).
  ** lia.
  ** rewrite H0 in f.
  simpl in f. unfold Arity,id in f.
  destruct f as [i Hi].
  induction i as [|i' Hi'] eqn:Ei.
  *** right. exact tt.
  *** left. unfold NameSub. exists a.  
  unfold aNDL. simpl.
  left. reflexivity. }
  2:{ (*p s*) left. simpl. exists 0. lia. }
  unfold FiniteParent. simpl.
  intros u.
  apply Acc_intro.
  intros u' H.
  exfalso. discriminate H.
  Defined. 


Example simplBigbool : 
  bigraph 1 bNDL 1 aNDL.
  eapply (Big
    1 bNDL 1 aNDL
    findec_bool
    findec_unit
    (fun n => match n with | false => 1 | true => 2 end) (*control*)
    (fun ns => match ns with 
      | inl n => inr zero1
      | inr s => inl false
    end) (*parent*)
    _ (*link*)
  ). 
  Unshelve.
  2:{ intros [b|p]. (*link*)
  + (*link b*) right. exact tt.
  + destruct p. destruct x eqn:E.
  * destruct f as [i Hi].
  induction i as [|i' Hi'] eqn:Ei.
  *** right. exact tt.
  *** left. unfold NameSub. exists a.  
  unfold aNDL. simpl.
  left. reflexivity.
  * right. exact tt. 
  }
  unfold FiniteParent. simpl.
  intros u.
  apply Acc_intro.
  intros u' H.
  exfalso. discriminate H.
  Defined. 

  Print simplBigbool.



  (* Example zero : Kappa. exists 0. auto. Defined. *)

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

(* Variable A : Type.
Variable f : A -> nat.
Variable R : A -> A -> Prop. *)


(* Theorem well_founded_lt_compat : well_founded R.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc R a).
  { intro n; induction n as [|n IHn].
    - intros a Ha; absurd (f a < 0); auto. admit . (*apply Nat.nlt_0_r.*)
    - intros a Ha. apply Acc_intro. intros b Hb.
      apply IHn. admit. }
  intros a. apply (H (S (f a))). apply Nat.lt_succ_diag_r.
Defined. *)
(* 
Lemma forallfin1 (P : type (findec_fin 1) -> Prop) :
forall n0 : type (findec_fin 1), P n0 -> 
  P zero1.
  intros [n pf]. 
  unfold zero1.
  assert (n=0).
  - induction n as [| n']. 
    + reflexivity.        
    + inversion pf. inversion H0.
  - Admitted.   *)

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
  

