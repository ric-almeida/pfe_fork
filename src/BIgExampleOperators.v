Set Warnings "-notation-overridden, -parsing".

Require Import AbstractBigraphs.
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
- exact (H ++ "g").
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
Include MB.

Example b : string := "b".
Example bNDL : NoDupList.
exists [b]. constructor; auto. constructor. Defined.

Example a : string := "a".
Example aNDL : NoDupList.
exists [a]. constructor; auto. constructor. Defined.

Example e : string := "e".
Example eNDL : NoDupList.
exists [e]. constructor; auto. constructor. Defined.




Example simplBig : 
  bigraph 1 bNDL 1 aNDL.
  eapply (Big
    1 bNDL 1 aNDL
    (findec_fin 2)
    findec_unit
    (fun n => match n with | exist n _  => n+1 end) (*control*)
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

Definition mycontrol (node:type findec_bool) : Kappa := 
  match node with | false => 1 | true => 2 end.

Definition myparent (ns : type findec_bool + fin 1) : 
  type findec_bool + fin 1 :=
  match ns with | inl n => inr zero1 | inr s => inl false end.

Definition mylink (ip : NameSub bNDL + Port mycontrol) : 
  NameSub aNDL +  type findec_unit.
Proof.
  destruct ip as [b|p].
  + right. exact tt.
  + destruct p as [n ps]. destruct n eqn:E.
  * destruct ps as [i Hi].
  induction i as [|i' Hi'] eqn:Ei.
  *** right. exact tt.
  *** left. unfold NameSub. exists a.  
  unfold aNDL. simpl.
  left. reflexivity.
  * right. exact tt. 
Defined.

Example simplBigbool : 
  bigraph 1 bNDL 1 aNDL.
  Proof.
  eapply (Big
    1 bNDL 1 aNDL (*s i r o*)
    findec_bool (*node*)
    findec_unit (*edge*)
    mycontrol (*control*)
    myparent (*parent*)
    mylink (*link*)
  ). 
  unfold FiniteParent. simpl.
  intros u.
  apply Acc_intro.
  intros u' H.
  exfalso. discriminate H.
  Defined. 


Inductive MyNodes : Type :=
| Process
| Semantic 
| Component 
| NodeType 
| Persistent 
| Init 
| On.

Definition MyNodesFDT : FinDecType.
exists MyNodes.
Proof.
  - unfold Finite. 
  exists [Process; Semantic; Component; NodeType; Persistent; Init; On].
  split.
  + unfold SurjectiveList. intros. induction n; simpl.
  * left. reflexivity.
  * right. left. reflexivity.
  * right. right. left. reflexivity.
  * right. right. right. left. reflexivity.
  * right. right. right. right. left. reflexivity.
  * right. right. right. right. right. left. reflexivity.
  * right. right. right. right. right.  right. left. reflexivity.
  + unfold InjectiveXTList. 
  intros i j Hi.
  destruct i; simpl.
  * destruct j; simpl.
    ** reflexivity.
    ** intro H.  
    destruct j; simpl.
    discriminate.
    simpl in H. 
    destruct j. 
    simpl in H. discriminate.
    destruct j.
    simpl in H. discriminate.
    destruct j.
    simpl in H. discriminate.
    destruct j.
    simpl in H. discriminate.
    destruct j.
    simpl in H. discriminate.
    destruct j.
    simpl in H. discriminate.
    simpl in H. discriminate.
  * destruct j; simpl.
    ** destruct i0; simpl.
      discriminate.
      destruct i0. discriminate.
      destruct i0. discriminate.
      destruct i0. discriminate.
      destruct i0. discriminate.
      destruct i0. discriminate.
      destruct i0. discriminate.
      discriminate. 
      destruct i0; simpl.
      ++ destruct j; simpl.
      reflexivity.
      intros. destruct j. discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl. simpl in H.
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      reflexivity.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      reflexivity.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      reflexivity.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      reflexivity.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      reflexivity.
      destruct j; simpl. 
      discriminate.
      discriminate.
      ++ destruct i0; simpl.
      destruct j; simpl.
      intros. discriminate.
      destruct j; simpl. 
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl.
      discriminate.
      destruct j; simpl. 
      reflexivity.    
      simpl in Hi; lia.
      ++ destruct i0; simpl.
      simpl in Hi; lia.
      simpl in Hi; lia.
  - unfold FinFun.EqDec. 
  decide equality.
Defined.


Definition controlComponent (node:type MyNodesFDT) : Kappa := 
match node with 
  | Process => 1
  | Semantic => 0
  | Component => 0
  | NodeType => 0
  | Persistent=> 0 
  | Init => 0
  | On  => 0
end.

Definition parentComponent (ns : type MyNodesFDT + fin 2) : 
  type MyNodesFDT + fin 1 :=
  match ns with 
  | inl Process => inr zero1
  | inl Semantic => inl Process
  | inl Component => inl Semantic
  | inl NodeType => inl Process
  | inl Persistent => inl NodeType
  | inl Init => inl Process
  | inl On => inl Init
  | inr (exist s' _) => 
    match s' with 
    | 0 => inl Component 
    | _ => inr zero1
    end
end.

Definition linkComponent (ip : NameSub EmptyNDL + Port controlComponent) : 
  NameSub eNDL +  type voidfd.
Proof.
  destruct ip as [b|p].
  + destruct b; elim i0.
  + destruct p as [n ps]. 
  destruct n eqn:E; simpl in ps; unfold Arity,id in ps; destruct ps as [i Hi]; try apply Nat.nlt_0_r in Hi; try elim Hi.
  left. unfold NameSub. exists e. constructor. reflexivity.
Defined. 

Example componentBig : 
  bigraph 2 EmptyNDL 1 eNDL.
  Proof.
  eapply (Big
    2 EmptyNDL 1 eNDL (*s i r o*)
    MyNodesFDT (*node*)
    voidfd (*edge*)
    controlComponent (*control*)
    parentComponent (*parent*)
    linkComponent (*link*)
  ). 
  unfold FiniteParent. simpl.
  intros n.
  destruct n. 
  - (*Process*) 
  apply Acc_intro.
  intros u' H. discriminate H.
  - (*Semantic*)
  apply Acc_intro.
  intros u' H.
  apply Acc_intro.
  intros u'' H'.
  destruct u'; try discriminate.
  - (*Component*)
  apply Acc_intro.
  intros u'' H'.
  apply Acc_intro.
  intros u''' H''.
  apply Acc_intro.
  intros x Hx.
  destruct u''; try discriminate;
  destruct u'''; try discriminate.
  - (*NodeType*)
  apply Acc_intro.
  intros u' H.
  apply Acc_intro.
  intros u'' H'.
  destruct u'; try discriminate.
  - (*Persistent*)
  apply Acc_intro.
  intros u'' H'.
  apply Acc_intro.
  intros u''' H''.
  apply Acc_intro.
  intros x Hx.
  destruct u''; try discriminate;
  destruct u'''; try discriminate.
  - (* Init*)
  apply Acc_intro.
  intros u' H.
  apply Acc_intro.
  intros u'' H'.
  destruct u'; try discriminate.
  - (*On*)
  apply Acc_intro.
  intros u'' H'.
  apply Acc_intro.
  intros u''' H''.
  apply Acc_intro.
  intros x Hx.
  destruct u''; try discriminate;
  destruct u'''; try discriminate.
  Defined. 

(* #[export] Instance MyEqNat_refl_0 (x:nat) : MyEqNat x x.
Proof. 
constructor. reflexivity. 
Qed.
Arity 0 = Datatypes.length EmptyNDL *)
(* :  bigraph 1 EmptyNDL 1 EmptyNDL  *)

Example eaNDL : NoDupList.
exists (e::aNDL). constructor; auto.
- simpl. unfold not. intros. destruct H. ** discriminate H. ** elim H.
- exact (noDupSingle a). 
Defined. 


Compute (freshNames eNDL 1).
Compute (freshNames eNDL 2).
Compute (freshNames EmptyNDL 3).

Definition myPN : PermutationNames
     (app_merge_NoDupList
        (app_merge_NoDupList EmptyNDL
           (app_merge_NoDupList {| ndlist := [e]; nd := noDupSingle e |}
              eaNDL)) {| ndlist := [e]; nd := noDupSingle e |})
     (app_merge_NoDupList {| ndlist := [e]; nd := noDupSingle e |} aNDL).
simpl. unfold app_merge_NoDupList. 
simpl. constructor. simpl. 
unfold permutation. intros. split; intros. 
- destruct H.
+ rewrite H. simpl. right. left. reflexivity.
+ destruct H.
* rewrite H. simpl. left. reflexivity.
* elim H. 
- destruct H.
+ rewrite H. simpl. right. left. reflexivity.
+ destruct H.
* rewrite H. simpl. left. reflexivity.
* elim H. 
Defined.

Definition myPN' :
PermutationNames
     (app_merge_NoDupList EmptyNDL
        (app_merge_NoDupList
           (app_merge_NoDupList {| ndlist := [e]; nd := noDupSingle e |} eNDL)
           eaNDL))
     (app_merge_NoDupList {| ndlist := [e]; nd := noDupSingle e |} aNDL).
simpl. constructor. simpl. 
exact (permutation_id [e;a]).
Defined.


Definition mydisi : {| ndlist := [e]; nd := noDupSingle e |} # aNDL.
constructor.
intros. simpl in *. 
destruct H; destruct H0.
- rewrite <- H in H0. discriminate H0.
- elim H0. 
- elim H. 
- elim H.
Defined.



(*produit tensoriel implicite? *)
Example simplBigboolOp := 
  (bigraph_composition (p:=myPN)
  (bigraph_tensor_product (dis_i := mydisi) (closure e) (bigraph_id 1 aNDL)) 
  ((discrete_ion (A := findec_bool) false (mkNoDupList [e] (noDupSingle e)) (k := 1)) 
  <|> 
  (discrete_atom (A := findec_bool) true eaNDL (k := 2))
  ||
  (substitution bNDL e))).


Theorem eqmesbig : 
  bigraph_equality simplBigbool simplBigboolOp. 
  Admitted.
  

(* Example simplBigboolOp := 
  ((closure e) ⊗ (bigraph_id 1 aNDL)) 
  <<o>> 
  ((discrete_ion (A := findec_bool) false (mkNoDupList [e] (noDupSingle e)) (k := 1)) 
  <|> 
  (discrete_atom (A := findec_bool) true eaNDL (k := 2))
  ||
  (substitution bNDL e))). *)
(*cest moi qui ait compris que faut rajouter l'id*)


(*myPN' should be found on its own*) (*: bigraph 1 bNDL 1 aNDL *)
Example simplBigboolOp' 
  := 
  (bigraph_composition (p:=myPN')
    (bigraph_tensor_product (dis_i := mydisi) (closure e) (bigraph_id 1 aNDL))
    ((substitution bNDL e)
    ||
    (discrete_ion (A := findec_bool) false eNDL (k := 1)) 
    <|> 
    (discrete_atom (A := findec_bool) true eaNDL (k := 2))
    )).



Definition btmp : {inner : Name
   | In inner
       (app_merge_NoDupList (app_merge_NoDupList EmptyNDL EmptyNDL) bNDL)} +
   Port (get_control simplBigboolOp). 
Proof.
   left. exists b. simpl. left. reflexivity. Defined.


Definition btmp' :
({inner : Name
   | In inner
       (app_merge_NoDupList (app_merge_NoDupList bNDL EmptyNDL) EmptyNDL)} +
   Port (get_control simplBigboolOp')).
Proof.
   left. exists b. simpl. left. reflexivity. Defined.



(*Compute ((s simplBigboolOp)). 
Compute (ndlist (i simplBigboolOp)). 
Compute ((r simplBigboolOp)). 
Compute (ndlist (o simplBigboolOp)). 
Compute (type (get_edge simplBigboolOp)). 
Compute (type (get_node simplBigboolOp)). 
Compute ((get_parent simplBigboolOp (inr zero1))).  
Compute ((get_link simplBigboolOp btmp)).  

Compute ((s simplBigboolOp')). 
Compute (ndlist (i simplBigboolOp')). 
Compute ((r simplBigboolOp')). 
Compute (ndlist (o simplBigboolOp')). 
Compute (type (get_edge simplBigboolOp')). 
Compute (type (get_node simplBigboolOp')). 
Compute ((get_parent simplBigboolOp' (inr zero1))).  
Compute ((get_link simplBigboolOp' btmp')).   *)