Set Warnings "-notation-overridden, -parsing".

Require Import ConcreteBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import ParallelProduct.
Require Import MergeProduct.
Require Import Nesting.


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

Module MySigP <: SignatureParameter.
Definition Kappa : Type := nat.

Definition Arity : Kappa -> nat := id.

End MySigP. 


Module MyNamesP <: Names.NamesParameter.
Definition Name := string.
Definition EqDecN : forall x y : Name, {x = y} + {x <> y} := string_dec.
Local Open Scope string_scope.
Definition InfName : forall l : list string, exists n : string, ~ In n l. 
  intros.
  induction l as [|x l IHl].
  - exists "a". auto.
  - Admitted.
Definition DefaultName := "default".
Definition freshName : list Name -> Name. 
Proof. 
intros l. induction l as [|name l H].
- exact DefaultName.
- exact H.
Defined. 
Lemma notInfreshName : forall l:list Name, ~ In (freshName l) l. 
Proof. 
intros.
unfold not. intros H. 
induction l as [|name l Hl].
- elim H.
- destruct H.
+ unfold freshName in H. 
unfold list_rec in *. unfold list_rect in *.
simpl in H. admit.
+ 

Admitted.

End MyNamesP.



Module MB := MergeBig MySigP MyNamesP.
Import MB.

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
    _
    (*(fun ns => match ns with 
      | inl n => inr zero1
      | inr s => _
    end)*) (*parent*)
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
  2:{ intros [n|s]. 
  - right. exact zero1. 
  - left. simpl. exists 0. lia. }
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

(* 
Example simplBigboolOp : 
  bigraph 1 EmptyNDL 1 EmptyNDL := 
    (discrete_ion (A := findec_bool) false EmptyNDL) <|> (discrete_atom (A := findec_bool) true EmptyNDL). *) 
