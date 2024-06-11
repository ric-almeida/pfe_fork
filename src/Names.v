
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Bijections.
Require Import MyBasics.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.CRelationClasses.


Import ListNotations.


Module Type NamesParameter.
Parameter Name : Type.
Parameter EqDecN : forall x y : Name, {x = y} + {x <> y}.
Parameter InfName: forall l:list Name, exists n:Name, ~ In n l.
Parameter DefaultName : Name.
Parameter freshName : list Name -> Name. 
Parameter notInfreshName : forall l:list Name, ~ In (freshName l) l. 
End NamesParameter.


Module Names (NP: NamesParameter).
Include NP.




Record NoDupList : Type :=
mkNoDupList
  {
    ndlist :> list Name ;
    nd : NoDup ndlist ;
  }.
Definition EmptyNDL : NoDupList := {| ndlist := []; nd := NoDup_nil Name |}.

Definition OneelNDL (n : Name): NoDupList.
eapply (mkNoDupList [n]).
constructor; auto; constructor. 
Defined.

Definition list_to_NDL (l:list Name) : NoDupList.
apply (
    mkNoDupList 
    (nodup EqDecN l)
).
apply NoDup_nodup.
Defined.

Lemma in_elt' (l1: list Name) : forall (x:Name) l2, In x (l1 ++ x :: l2).
Proof. intros.
    apply in_or_app.
    right; left; reflexivity.
Qed.

Fixpoint app_merge' (l1 : list Name) (l2 : list Name) {struct l1} : list Name :=  
    match l1 with
    | nil => l2
    | a :: l1' =>  
      if in_dec EqDecN a l2 then app_merge' l1' l2
        else a :: app_merge' l1' l2
  end.


Lemma merge'_head {l1' l2' : list Name} {a : Name}:
app_merge' (a::l1') (a::l2') = app_merge' l1' (a::l2').
Proof.
    simpl.
    destruct (EqDecN a a).
    - reflexivity.
    - exfalso. apply n. reflexivity.
Qed.

Lemma app_merge'_empty_right (l1 : list Name) :
app_merge' l1 [] = l1.
Proof.
    induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity. 
Qed.

Lemma app_merge'_empty_left (l1 : list Name) :
app_merge' [] l1 = l1.
Proof.
    induction l1.
    simpl. reflexivity.
    simpl. reflexivity. 
Qed.

(* Theorem app_merge'_assoc {l1 l2 l3 : list Name} :
app_merge' (app_merge' l1 l2) l3 = 
    app_merge' l1 (app_merge' l2 l3).
Proof. Abort. *)


Lemma in_eq_m {a:Name} {l}: 
In a (app_merge' [a] l).
Proof.
    intros. simpl. destruct (in_dec EqDecN a l).
    apply i.
    constructor. reflexivity. 
Qed.

Lemma in_cons_m : forall (a b:Name) (l:list Name), 
In b l -> In b (app_merge' [a] l).
Proof. 
    intros. simpl. destruct (in_dec EqDecN a l).
    - apply H. 
    - apply in_cons. apply H.
Qed.

Lemma in_head_right_list {a:Name} {l1 l2}:
In a (app_merge' l1 (a::l2)).
Proof.
    induction l1 as [|a1 l1' IHl1].
    - simpl. left. reflexivity.
    - simpl. destruct (EqDecN a a1).
    + apply IHl1.
    + destruct (in_dec EqDecN a1 l2).
    * apply IHl1.
    * apply in_cons. apply IHl1.
Qed.

Theorem in_right_list : forall (b:Name) (l1:list Name) (l2:list Name), 
In b l2 -> In b (app_merge' l1 l2).
Proof. 
    intros.
    induction l1.
    - simpl. apply H.
    - simpl. destruct (in_dec EqDecN a l2).
    + apply IHl1.
    + simpl. right. apply IHl1. 
Qed. 

Lemma in_head_left_list {a:Name} {l1 l2}:
In a (app_merge' (a :: l1) l2).
Proof.
    induction l1 as [|a1 l1' IHl1].
    - apply in_eq_m.
    - simpl. destruct (in_dec EqDecN a l2).
    + destruct (in_dec EqDecN a1 l2).
    * apply in_right_list. apply i.
    * apply in_cons. apply in_right_list. apply i.
    + constructor. reflexivity.
Qed.

Lemma NoDup_in_or_exclusive {a h:Name} {t:list Name} :
In a (h::t) -> NoDup (h::t) -> 
(a = h /\ ~ In a t) \/ (a <> h /\ In a t).
Proof.
    intros H nd.
    destruct (EqDecN a h).
    - left. destruct e. split.
    + reflexivity.
    + apply NoDup_cons_iff in nd. 
    destruct nd. apply H0.
    - right. split.
    + apply n.
    + simpl in H. destruct H.
    * exfalso. apply n; symmetry; apply H.
    * apply H. 
Qed.

Lemma NoDup_in_or_exclusive' {a h:Name} {t:list Name} :
In a (h::t) -> NoDup (h::t) -> 
(a = h /\ ~ In a t) + (a <> h /\ In a t).
Proof.
    intros H nd.
    destruct (EqDecN a h).
    - left. destruct e. split.
    + reflexivity.
    + apply NoDup_cons_iff in nd. 
    destruct nd. apply H0.
    - right. split.
    + apply n.
    + simpl in H. destruct H.
    * exfalso. apply n; symmetry; apply H.
    * apply H. 
Qed.

Lemma eq_means_cons_eq {a1 a2:Name} {l1 l2} :
a1 = a2 /\ l1 = l2 -> a1::l1 = a2::l2.
Proof. 
    intros.
    destruct H. rewrite H. rewrite H0. reflexivity. 
Qed.

Lemma NoDupFalse {a:Name} {l1 l2} :
~ NoDup (a :: l1 ++ a :: l2). 
Proof.
    unfold not. 
    intros nd.
    apply NoDup_cons_iff in nd. 
    destruct nd. apply H. apply in_or_app. right. constructor. reflexivity.
Qed.

Lemma NoDup_id {a : Name} {l1 l2} :
NoDup (l1 ++ a :: l2) -> l1 ++ a :: l2 = app_merge' l1 (a :: l2).
Proof. 
    intros nd.
    induction l1.
    - simpl. reflexivity.
    - simpl. destruct (EqDecN a a0).
    + exfalso. rewrite e in nd. apply NoDupFalse in nd. apply nd. 
    + destruct (in_dec EqDecN a0 l2).
    * exfalso. simpl in nd. apply NoDup_cons_iff in nd. 
    destruct nd. apply H. apply in_or_app. right. apply in_cons. apply i.
    * apply eq_means_cons_eq. split.
    ** reflexivity.
    ** apply IHl1. simpl in nd. apply NoDup_cons_iff in nd. 
    destruct nd. apply H0. 
Qed.

Theorem NoDup_id_app {l1 l2} :
NoDup (l1 ++ l2) -> l1 ++ l2 = app_merge' l1 l2.
Proof. 
    intros nd.
    induction l1.
    - simpl. reflexivity.
    - simpl. destruct (in_dec EqDecN a l2).
    + exfalso. simpl in nd. apply NoDup_cons_iff in nd. destruct nd.
    apply H. apply in_or_app. right; assumption.
    + apply eq_means_cons_eq. split. {reflexivity. }
    apply IHl1. simpl in nd. apply NoDup_cons_iff in nd. destruct nd.
    apply H0.
Qed.

Lemma in_split_m_dup (a:Name) (l:list Name) :
NoDup l -> In a l -> exists l1 l2, l = app_merge' l1 (a :: l2).
Proof.
  intros nd H.
  generalize dependent a.
  induction l as [| h t IH].
  - (* l = []*)
    intros. inversion H.    
  - (* l = h:: t*)
    intros.      
    apply NoDup_in_or_exclusive in H. 
    * destruct H.
    + (* l = a::t *)
      exists [].
      exists t.
      simpl. destruct H. rewrite H. 
      reflexivity.
    + (* l = h :: l1 ++ a :: t*)
      destruct H as [H H'].
      apply in_split in H'.
      destruct H' as [l1 [l2 H']].
      exists (h::l1).
      exists (l2).
      simpl.
      destruct (EqDecN a h). {exfalso; apply H; apply e. }
      destruct (in_dec EqDecN h l2). 
      {exfalso. rewrite H' in nd. apply NoDup_cons_iff in nd. 
      destruct nd. apply H0. apply in_or_app. right. apply in_cons. apply i. }
       simpl. rewrite H'. apply eq_means_cons_eq.
       split. {reflexivity. }
       rewrite NoDup_id. {reflexivity. }
       rewrite <- H'. 
       apply NoDup_cons_iff in nd. 
      destruct nd. apply H1.
    * apply nd.
Qed.

Theorem not_inr_not_interesting (a: Name) (b:Name) (l1:list Name) (l2:list Name) : 
~ In b l2 -> a <> b -> In b (app_merge' l1 l2) -> In b (app_merge' (a :: l1) l2).
Proof.
    intros. simpl. 
    destruct (in_dec EqDecN a l2).
    - apply H1.
    - apply in_cons. apply H1.
Qed.

Theorem inl_useless (a:Name) (l1:list Name) (l2:list Name) : 
In a l2 -> app_merge' (a :: l1) l2 = app_merge' l1 l2.
Proof.
    intros.
    simpl.
    destruct (in_dec EqDecN a l2).
    - reflexivity.
    - exfalso. apply n. apply H.
Qed. 

Theorem not_right (b:Name) (l1:list Name) (l2:list Name) : 
~ In b l2 -> In b l1 -> In b (app_merge' l1 l2).
Proof. 
    intros H H'.
    induction l1.
    - exfalso. apply H'.
    - destruct (EqDecN a b).
    + destruct e. apply in_head_left_list.
    + destruct (in_dec EqDecN a l2).
    * rewrite inl_useless. 
    ** apply IHl1. apply in_inv in H'. destruct H'.
    *** exfalso. apply n. apply H0.
    *** apply H0.
    ** apply i.
    * apply not_inr_not_interesting.
    ** apply H.
    ** apply n.
    ** apply IHl1.
    apply in_inv in H'.
    destruct H'. { exfalso. apply n. apply H0. }
    apply H0.
Qed.

Theorem in_left_list : forall (b:Name) (l1:list Name) (l2:list Name), 
In b l1 -> In b (app_merge' l1 l2).
Proof.
    intros b l1 l2 H. 
    destruct (in_dec EqDecN b l2).
    - apply in_right_list. apply i.
    - apply in_split in H.
    destruct H as [l1_1 [l1_2]].
    rewrite H.
    induction l1_1 as [| a l1_1' IHl1_1]. 
    + apply in_head_left_list.
    + apply not_right. {apply n. }
    apply in_or_app. right. constructor. reflexivity. 
Qed.
    
Lemma in_split_m (a:Name) (l:list Name) :
In a l -> exists l1 l2, l = app_merge' l1 (a :: l2).
Proof. (* FALSE !! If l has dup, then app_merge will remove them *)
Abort.

Lemma in_or_app_m : forall (l m:list Name) (a:Name), 
In a l \/ In a m -> In a (app_merge' l m).
Proof. 
    intros.
    destruct H.
    - apply in_left_list. apply H.
    - apply in_right_list. apply H.
Qed.

Theorem not_in_cons_m (x a : Name) (l : list Name):
~ In x (app_merge' [a] l) <-> x <> a /\ ~ In x l.
Proof. split.
    - split.
    + unfold not. intros. apply H. rewrite H0. simpl.
    destruct (in_dec EqDecN a l).
    apply i.
    constructor. reflexivity.
    + unfold not. intros. apply H.
    apply in_right_list. apply H0.
    - intros. unfold not. intros. destruct H.
    simpl in H0. destruct (in_dec EqDecN a l).
    apply H1. apply H0.
    apply H1. apply in_inv in H0. destruct H0.
    + exfalso. apply H. symmetry. apply H0.
    + apply H0.
Qed. 

Lemma not_in_merge {a} {l1 l2}:
~ In a l1 -> ~ In a l2 ->
~ In a (app_merge' l1 l2).
Proof. 
    intros H1 H2.
    induction l1 as [|a1 l1' IHl1].
    + apply H2.
    + simpl. destruct (in_dec EqDecN a1 l2).
    ++ apply IHl1.
    unfold not in *. intros. apply H1. 
    apply in_cons.
    apply H.
    ++ unfold not. intros. 
    apply in_inv in H.
    destruct H as [H | H'].
    * apply H1. rewrite H. constructor. reflexivity.
    * apply IHl1.
    ** unfold not. intros. apply H1. apply in_cons. apply H.
    ** apply H'. 
Qed.

Theorem not_in_left {a:Name} {l m} : 
In a (app_merge' l m) -> ~ In a m -> In a l.
Proof.
    intros H H'.
    destruct (in_dec EqDecN a l).
    - apply i.
    - exfalso. apply (not_in_merge n H'). (*need comu?*)
    apply H.
Qed. 

Theorem not_in_right {a:Name} {l m} : 
In a (app_merge' l m) -> ~ In a l -> In a m.
Proof.
    intros H H'.
    destruct (in_dec EqDecN a m).
    - apply i.
    - exfalso. apply (not_in_merge H' n). apply H.
Qed.

Lemma in_app_or_m : forall (l m:list Name) (a:Name), 
In a (app_merge' l m) -> In a l \/ In a m.
Proof.
    intros.
    destruct (in_dec EqDecN a m).
    - right. apply i. 
    - left. apply not_in_left in H; assumption.
Defined.

Lemma in_app_or_m_nod_dup : forall (l m:list Name) (a:Name), 
NoDup l -> NoDup m -> In a (app_merge' l m) -> In a l + In a m.
Proof.
    intros l m a ndl ndm H.
    destruct (in_dec EqDecN a m).
    - right. apply i. 
    - left. apply not_in_left in H; assumption.
Defined.

Lemma in_app_or_m_nod_dup' : forall (l m:list Name), 
NoDup l -> NoDup m -> {a:Name | In a (app_merge' l m)} -> {a | In a l} + {a | In a m}.
Proof.
    intros l m ndl ndm H.
    destruct H.
    destruct (in_dec EqDecN x m).
    - right. exists x. apply i0. 
    - left. exists x. apply not_in_left in i; assumption.
Qed.

Lemma in_app_iff {b:Name} {l1 l2} :
In b (app_merge' l1 l2) <-> In b l1 \/ In b l2.
Proof. 
    intros. split. 
    - apply in_app_or_m.
    - apply in_or_app_m.
Qed.

Theorem in_app_merge'_com {l1 l2 : list Name} : forall a,
In a (app_merge' l1 l2) -> In a (app_merge' l2 l1).
Proof.
    intros.
    apply in_app_or_m in H.
    destruct H.
    - apply in_right_list; assumption.
    - apply in_left_list; assumption.
Qed.

Theorem in_app_merge'_comu {l1 l2 : list Name} : forall a,
In a (app_merge' l1 l2) <-> In a (app_merge' l2 l1).
Proof.
    intros. split; apply in_app_merge'_com.
Qed.

Theorem in_app_merge'_trans {l1 l2 l3 : list Name} : forall a,
In a (app_merge' l1 (app_merge' l2 l3)) -> In a (app_merge' (app_merge' l1 l2) l3).
Proof.
    intros. 
    apply in_app_or_m in H.
    destruct H.
    - apply in_left_list. apply in_left_list. assumption.
    - apply in_app_or_m in H.
    destruct H. 
    + apply in_left_list. apply in_right_list. assumption.
    + apply in_right_list. assumption.
Defined.

Theorem in_app_merge'_transi {l1 l2 l3 : list Name} : forall a,
In a (app_merge' (app_merge' l1 l2) l3) <-> In a (app_merge' l1 (app_merge' l2 l3)).
Proof.
    intros. split.
    - intros. 
    apply in_app_or_m in H.
    destruct H.
    + apply in_app_or_m in H.
    destruct H. 
    ++ apply in_left_list. assumption.
    ++ apply in_right_list. apply in_left_list. assumption.
    + apply in_right_list. apply in_right_list. assumption.
    - apply in_app_merge'_trans.
Defined.

Lemma rm_headNoDUP {a:Name} {l}: 
~ In a l -> (NoDup (a::l) <-> NoDup l).
Proof.
    intros.
    split.
    - intros. apply NoDup_cons_iff in H0.
    destruct H0 as [H0 H']. apply H'.
    - intros. constructor; assumption.
Qed.

Theorem NoDup_app_merge (l1 : list Name) (l2 : list Name) :
NoDup l1 -> NoDup l2 -> NoDup (app_merge' l1 l2).
Proof.
    intros nd1 nd2.
    induction l1 as [|a1 l1' IHl1]. 
    - simpl. apply nd2.
    - simpl. destruct (in_dec EqDecN a1 l2).
    + apply IHl1.
    apply NoDup_cons_iff in nd1. 
    destruct nd1 as [nd1' nd1''].
    apply nd1''.
    + apply NoDup_cons_iff in nd1.
    destruct nd1 as [nd1' nd1''].
    constructor.
    * apply not_in_merge; assumption.
    * apply IHl1. apply nd1''. 
Qed.

Lemma rearrangenodup {a a':Name} {l}: 
NoDup (a::a'::l) <-> NoDup (a'::a::l).
Proof. 
    split.
    - intros. constructor;
    apply NoDup_cons_iff in H;
    destruct H as [H H'];
    apply NoDup_cons_iff in H';
    destruct H' as [H' H'']. 
    + unfold not. intros. apply H.
    apply in_inv. (*not working idk why*)
    destruct (EqDecN a a').
    ++ rewrite e. constructor. reflexivity.
    ++ apply in_inv in H0; destruct H0 as [H0 | H0'].
    * rewrite H0. constructor. reflexivity.
    * exfalso. apply H'. apply H0'.
    + constructor.
    ++ unfold not. intros.
    apply H. apply in_cons. apply H0.
    ++ apply H''.
    - intros. constructor;
    apply NoDup_cons_iff in H;
    destruct H as [H H'];
    apply NoDup_cons_iff in H';
    destruct H' as [H' H'']. 
    + unfold not. intros. apply H.
    apply in_inv. (*not working idk why*)
    destruct (EqDecN a a').
    ++ rewrite e. constructor. reflexivity.
    ++ apply in_inv in H0; destruct H0 as [H0 | H0'].
    * rewrite H0. constructor. reflexivity.
    * exfalso. apply H'. apply H0'.
    + constructor.
    ++ unfold not. intros.
    apply H. apply in_cons. apply H0. 
    ++ apply H''.
Qed.



Lemma app_merge'_id {i1 i2}: 
NoDup i1 -> NoDup i2 -> (forall name, In name i1 -> ~ In name i2) -> app_merge' i1 i2 = i1 ++ i2.
Proof.
intros.
induction i1.
simpl. reflexivity.
simpl. destruct (in_dec EqDecN a i2).
- exfalso. specialize (H1 a). apply H1; auto. constructor. reflexivity.
- rewrite IHi1; auto. apply nodup_tl in H. assumption.
intros. apply H1. right. assumption. 
Qed.

Definition permutation (l1: list Name) (l2: list Name) := forall name, In name l1 <-> In name l2.
Definition permutation_id (l: list Name) : permutation l l.
Proof. unfold permutation. intros. tauto. Defined.

Definition permutation_id' (l: list Name) (l': list Name) : l = l' -> permutation l l'.
Proof. intros. destruct H. exact (permutation_id l).
Defined. 

Theorem TODO : forall l1 l2, permutation l1 l2 <-> Permutation l1 l2.
Proof.
intros.
split; intros.
- unfold permutation in H. 
induction l1.
+ induction l2.
* constructor.
* edestruct H. admit.
+ admit.
- unfold permutation. intros name. destruct H.
+ tauto.
+ Admitted.


Theorem symmetric_permutation: Symmetric permutation.
Proof.
  constructor; unfold permutation in H; specialize (H name); destruct H; assumption.
Qed.

Theorem transitive_permutation: Transitive permutation.
Proof.
  constructor; unfold permutation in *; specialize (H name); destruct H; specialize (H0 name); destruct H0; intros; auto.
Qed.

Theorem reflexive_permutation: Reflexive permutation.
Proof.
  constructor; unfold permutation in *; auto. 
Qed.

Definition tr_permutation {i1 i2 i3} : 
  permutation
    (app_merge' (app_merge' i1 i2) i3)
    (app_merge' i1 (app_merge' i2 i3)).
  Proof.
    unfold permutation. intros. split; intros.
    - apply in_app_or_m in H.
    destruct H.
    + apply in_app_or_m in H.
    destruct H. 
    ++ apply in_left_list. assumption.
    ++ apply in_right_list. apply in_left_list. assumption.
    + apply in_right_list. apply in_right_list. assumption.
    - apply in_app_or_m in H.
    destruct H.
    + apply in_left_list. apply in_left_list. assumption.
    + apply in_app_or_m in H.
    destruct H. 
    ++ apply in_left_list. apply in_right_list. assumption.
    ++ apply in_right_list. assumption.
  Defined.

Lemma app_merge'_cong {i1 i2 i3 i4}:  
permutation i1 i2 -> permutation i3 i4 -> 
permutation (app_merge' i1 i3) (app_merge' i2 i4).
Proof.
intros H12 H34.
split; intros H.
- apply in_app_iff in H. destruct H.
+ apply H12 in H. apply in_left_list. apply H.
+ apply H34 in H. apply in_right_list. apply H.
- apply in_app_iff in H. destruct H.
+ apply H12 in H. apply in_left_list. apply H.
+ apply H34 in H. apply in_right_list. apply H.
Qed.


(* INTERESTING PART ABOUT NODUPLISTS *)

Definition app_merge_NoDupList (l1 : NoDupList) (l2 : NoDupList) : NoDupList :=
{|
ndlist := app_merge' l1 l2 ;
nd := NoDup_app_merge l1 l2 (nd l1) (nd l2)
|}.

Notation "l1 ∪ l2" := (app_merge_NoDupList l1 l2) (at level 50, left associativity).


Lemma app_merge_or {l1 l2 n} :
 In n (app_merge_NoDupList l1 l2) -> In n l1 \/ In n l2.
 Proof. apply in_app_iff. Qed.

Theorem left_empty (i:NoDupList) :
forall name : Name,
  In name (app_merge_NoDupList EmptyNDL i) <->
  In name i.
Proof. intros.
    split; intros; simpl in *; apply H.
Qed.

Theorem right_empty (i:NoDupList) :
forall name : Name,
  In name (app_merge_NoDupList i EmptyNDL) <->
  In name i.
Proof. intros.
    split; intros; simpl in *. rewrite app_merge'_empty_right in H. apply H. rewrite app_merge'_empty_right. apply H.
Qed.

Theorem eq_NDL (l1:list Name) (l2:list Name) 
  {nd1 : NoDup l1} {nd2 : NoDup l2} : 
    {|ndlist := l1 ; nd := nd1|} = {|ndlist := l2 ; nd := nd2|} 
    <-> l1 = l2.
    split; intros.
    - inversion H. reflexivity.
    - destruct H.
    rewrite (proof_irrelevance (NoDup l1) nd1 nd2).
    reflexivity.
    Qed. 

Theorem merge_right_neutral : forall (l:NoDupList),
  app_merge_NoDupList l EmptyNDL = l.
  Proof. intros l. unfold EmptyNDL.
  unfold app_merge_NoDupList. 
  destruct l. simpl.
  apply (eq_NDL (app_merge' ndlist0 []) ndlist0).
  simpl. apply app_merge'_empty_right.
  Qed.

Theorem merge_left_neutral : forall (l:NoDupList),
  app_merge_NoDupList EmptyNDL l = l.
  Proof. intros l. unfold EmptyNDL.
  unfold app_merge_NoDupList. 
  destruct l. simpl.
  apply (eq_NDL (app_merge' [] ndlist0) ndlist0).
  simpl. apply app_merge'_empty_left.
  Qed.

Theorem merge_right_neutral' : forall (l:NoDupList),
  ndlist l = ndlist (app_merge_NoDupList l EmptyNDL).
  Proof.
  symmetry.
  destruct l.
  simpl.
  apply  app_merge'_empty_right.
  Qed.

Theorem permutation_distributive {o3i1 o4i2 i1o3 i2o4}
(p13 : permutation (ndlist o3i1) (ndlist i1o3))
(p24 : permutation (ndlist o4i2) (ndlist i2o4)) : 
permutation
   (app_merge_NoDupList o3i1 o4i2)
   (app_merge_NoDupList i1o3 i2o4).
Proof.
unfold permutation in *.
intros; split; intros; specialize (p13 name); specialize (p24 name); destruct p13; destruct p24; apply in_app_or_m in H; destruct H.
- apply in_left_list. apply H0. apply H.
- apply in_right_list. apply H2. apply H.
- apply in_left_list. apply H1. apply H.
- apply in_right_list. apply H3. apply H.  
Defined.

(* Theorem woopsie : forall l1 l2, app_merge' (ndlist l1) (ndlist l2) = nodup EqDecN ((ndlist l1)++(ndlist l2)).
Proof.
intros [l1 nd1].
intros [l2 nd2].
induction l1.
- simpl. 
induction l2. simpl. reflexivity.
simpl. destruct (in_dec EqDecN a l2).
* exfalso. apply NoDup_cons_iff in nd2. destruct nd2. apply H. apply i.
* simpl. admit.
- simpl. destruct (in_dec EqDecN a l2); destruct (in_dec EqDecN a (l1++l2)).
* admit.
* exfalso. admit.
* exfalso. admit.
* admit.
Admitted.  *)

(* PART ABOUT DISJOINT LISTS *)

Definition Disjoint (l1:NoDupList) (l2:NoDupList) : Prop :=
forall name, In name l1 -> ~ In name l2.

Notation "l1 # l2" := (Disjoint l1 l2) (at level 50, left associativity).

Remark void_disjoint_all_list_left : forall l:NoDupList, EmptyNDL # l.
  Proof.
    intros. unfold Disjoint. intros. unfold EmptyNDL. auto. 
  Qed. 

Remark void_disjoint_all_list_right : forall l:NoDupList, l # EmptyNDL.
  Proof.
    intros. unfold Disjoint. intros. unfold EmptyNDL. auto. 
  Qed. 

Definition rev_disjoint {l1:NoDupList} {l2:NoDupList} (d: l1 # l2) : l2 # l1.
Proof.
unfold Disjoint in *.
intros.
unfold not.
intros.
apply d in H0.
apply H0. apply H.
Qed. (*Or Defined?*)

Definition reflnames {r} : forall name : Name,
  In name r <-> In name r.
  reflexivity. Defined.


Lemma disjoint_NoDup_app : forall (l1 l2 : list Name),
  NoDup l1 -> NoDup l2 -> (forall a : Name, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 H3.
  induction H1 as [| x l1' H1' H1''].
  - (* Base case: l1 is empty *)
    apply H2.
  - (* Inductive case: l1 = x :: l1' *)
    simpl.
    apply NoDup_cons.
    + (* Prove ~ In x l2 *)
      intro H_in_x_l2.
      apply H3 with (a := x).
      * left; reflexivity.
      * apply in_app_or in H_in_x_l2.
        destruct H_in_x_l2.
        ** exfalso. apply H1'. apply H.
        ** assumption.
    + (* Apply the induction hypothesis *)
      apply IHH1''; auto.
      intros a H_in_a_l1'.
      apply H3 with (a := a).
      right; assumption.
Qed.

Theorem nodupmergedisjointlist (l1:NoDupList) (l2:NoDupList) :
Disjoint l1 l2 -> 
ndlist (list_to_NDL (l1 ++ l2)) = (ndlist l1) ++ (ndlist l2).
Proof.
unfold Disjoint.
intros.
simpl.
destruct l1 as [l1 nd1].
destruct l2 as [l2 nd2].
simpl.
apply nodup_fixed_point.
apply disjoint_NoDup_app; assumption.
Qed.



Remark nodupproofirrelevant : forall l1 l2, 
    ndlist l1 = ndlist l2 -> l1 = l2.
    Proof. 
    intros.  
    destruct l1 as [ndlist1  nd1]. 
    destruct l2 as [ndlist2  nd2].
    simpl in * |- *.
    subst.
    rewrite (proof_irrelevance _ nd1 nd2).
    reflexivity.
    Qed.

Lemma app_merge_NoDupList_id (l1 : NoDupList) (l2 : NoDupList) :
Disjoint l1 l2 -> ndlist (app_merge_NoDupList l1 l2) = (ndlist l1) ++ (ndlist l2).
Proof.
intros.
unfold app_merge_NoDupList.
Abort.

Theorem not_in_both : forall l1 l2, forall n, In n (ndlist l1) -> In n (ndlist l2) -> Disjoint l1 l2 -> False.
intros. unfold Disjoint in H1. specialize (H1 n). apply H1; assumption. Qed.

Theorem dis_trans {i1 i2 i3}
  (dis_i23 : Disjoint i2 i3) 
  (dis_i13 : Disjoint i1 i3) : Disjoint (app_merge_NoDupList i1 i2) i3.
  Proof.
  unfold Disjoint.
  intros.
  apply in_app_iff in H. destruct H.
  - apply dis_i13. apply H.
  - apply dis_i23. apply H.
  Qed.

Theorem dis_trans_r {i1 i2 i3}
  (dis_i12 : Disjoint i1 i2) 
  (dis_i13 : Disjoint i1 i3) : Disjoint i1 (app_merge_NoDupList i2 i3).
  Proof.
  unfold Disjoint.
  intros. unfold not. intros.
  apply in_app_iff in H0. destruct H0.
  - apply (not_in_both i1 i2 name H H0 dis_i12). 
  - apply (not_in_both i1 i3 name H H0 dis_i13). 
  Qed.

(* End DisjointLists. *)


Section NameSubsets.

Definition NameSub (nl : NoDupList) : Type :=
  {name:Name | In name nl}.

Remark nodupproofirrelevantns : forall l1 l2, 
    ndlist l1 = ndlist l2 -> NameSub l1 = NameSub l2.
    Proof. intros. unfold NameSub. rewrite H. reflexivity. Qed. 


Definition bij_list_forward (i1:NoDupList) (i2:NoDupList) : 
  (NameSub i1) + (NameSub i2) ->  NameSub (app_merge_NoDupList i1 i2).
  Proof.
  refine (fun name => match name with
                | inl (exist _ name' H1) => _
                | inr (exist _ name' H2) => _
                end).
    + exists (name'). 
      apply in_left_list; assumption. 
    + exists (name'). 
      apply in_right_list; assumption. 
    Defined.


Definition bij_list_backward (i1:NoDupList) (i2:NoDupList) :
  NameSub (app_merge_NoDupList i1 i2)
  ->
  (NameSub i1) + (NameSub i2).
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros Hn.
  apply in_app_or_m_nod_dup' in Hn; assumption.
  Defined.

Definition bij_list_backward' (i1:NoDupList) (i2:NoDupList) {dis_i:Disjoint i1 i2}:
  NameSub (app_merge_NoDupList i1 i2)
  ->
  (NameSub i1) + (NameSub i2).
  Proof.
  unfold Disjoint in dis_i.
  intros.
  destruct X.
  destruct (in_dec EqDecN x i1).
  - left. exists x. apply i0.
  - right. exists x. specialize (dis_i x). 
  apply in_app_or_m_nod_dup in i. destruct i.
  * exfalso; apply n; apply i.
  * apply i.
  * destruct i1. assumption.
  * destruct i2. assumption.
  Defined.
  

Definition bij_list_names (i1:NoDupList) (i2:NoDupList) {dis_i:Disjoint i1 i2} : 
  bijection ((NameSub i1) + (NameSub i2)) (NameSub (app_merge_NoDupList i1 i2)).
  Proof.
  apply 
  (mkBijection _ _ 
  (bij_list_forward i1 i2) 
  (@bij_list_backward' i1 i2 dis_i)).
  - apply functional_extensionality.
  intros. unfold id, funcomp, bij_list_forward, bij_list_backward'.
  simpl.
  destruct x.
  destruct (in_dec EqDecN x i1) as [Hini1 | Hnotini1].
  + apply subset_eq_compat. reflexivity.
  + destruct in_app_or_m_nod_dup; apply subset_eq_compat; reflexivity.
  - apply functional_extensionality.
  intros. unfold id, funcomp, bij_list_forward, bij_list_backward'.
  simpl.
  destruct x as [ns1 | ns2].
  + destruct ns1 as [name Hini1].
  destruct (in_dec EqDecN name i1).
  * apply f_equal. apply subset_eq_compat. reflexivity.
  * exfalso. apply n. apply Hini1.
  + destruct ns2 as [name Hini2].
  destruct (in_dec EqDecN name i1).
  * exfalso. 
  unfold Disjoint in dis_i. apply dis_i in i. apply i. apply Hini2.
  * apply f_equal. apply subset_eq_compat. reflexivity.
Defined.


Definition bij_list_names' (i1:NoDupList) (i2:NoDupList) {dis_i:Disjoint i1 i2} : 
  bijection ((NameSub i1) + (NameSub i2)) (NameSub (app_merge_NoDupList i1 i2)).
  Proof.
  apply 
  (mkBijection _ _ 
  (bij_list_forward i1 i2) 
  (bij_list_backward i1 i2)).
  - apply functional_extensionality.
  intros. unfold id, funcomp, bij_list_forward, bij_list_backward.
  simpl.
  destruct i1.
  destruct i2.
  destruct (in_app_or_m_nod_dup' ndlist0 ndlist1 nd0 nd1 x); destruct s;
  destruct x; apply subset_eq_compat. (*Lost information somewhere*)
  Abort.



End NameSubsets.


Section IntersectionNDL.
Fixpoint myintersection (l1 : list Name) (l2 : list Name) : list Name := 
  match l1 with
    | nil => []
    | a :: l1' =>  
      if in_dec EqDecN a l2 then a::myintersection l1' l2
        else myintersection l1' l2
  end.

Lemma in_both_in_intersection {i1 i2 : list Name} {i : Name} :
  In i i1 -> In i i2 ->
  In i (myintersection i1 i2).
  Proof.
  intros H1 H2.
  unfold myintersection.
  simpl in *.
  induction i1.
  - apply H1.
  - destruct (in_dec EqDecN a i2).
  + simpl in *. 
  destruct (EqDecN a i).
  * left. apply e.
  * right. apply IHi1.
  destruct H1.
  ** exfalso. apply n. apply H.
  ** apply H.
  + apply IHi1.
  destruct (EqDecN a i).
  * destruct e. exfalso. apply n. apply H2.
  * simpl in H1. destruct H1.
  ** destruct H. exfalso. apply n0. reflexivity.
  ** apply H.
  Qed.



Definition from_intersection_left {i1 i2 : list Name} {i : Name} :
  In i (myintersection i1 i2) ->  In i i1.
  Proof.
  intros Hin.
  unfold myintersection in Hin.
  simpl in *.
  induction i1.
  - apply Hin.
  - simpl. 
    destruct (EqDecN a i).
    + left. apply e.
    + right.
      apply IHi1.
      destruct (in_dec EqDecN a i2).
      ** simpl in Hin. destruct Hin.
      *** exfalso. apply n. apply H.
      *** apply H.
      ** apply Hin.
  Qed.



Theorem intersection_commutes {i1 i2 : list Name} {i : Name} :
  In i (myintersection i1 i2) ->
  In i (myintersection i2 i1).
  Proof.
  intros.  
  unfold myintersection in *.
  simpl in *.
  induction i1.
  - exfalso. apply H.
  - destruct (EqDecN a i).
  + destruct e. destruct (in_dec EqDecN a i2).
  * fold myintersection in *. apply (in_both_in_intersection i).
    simpl. left. reflexivity.
  * exfalso. fold myintersection in *.
  apply IHi1 in H.
  apply from_intersection_left in H.
  apply n. apply H.
  + apply in_both_in_intersection.  
  * destruct (in_dec EqDecN a i2).
  ** simpl in H. destruct H.
  *** exfalso. apply n. apply H.
  *** fold myintersection in *.
  apply IHi1 in H.
  apply from_intersection_left in H. apply H.
  ** fold myintersection in *.
  apply IHi1 in H.
  *** apply from_intersection_left in H. apply H.
  * destruct (in_dec EqDecN a i2).
  ** fold myintersection in *. simpl in H. destruct H.
  *** exfalso. apply n. apply H.
  *** apply from_intersection_left in H.
  simpl. right. apply H.
  ** fold myintersection in *. apply from_intersection_left in H.
  simpl. right. apply H.
  Qed.



Definition from_intersection_right {i1 i2 : list Name} {i : Name} :
  In i (myintersection i1 i2) ->  In i i2.
  Proof.
  intros Hin.
  apply intersection_commutes in Hin.
  apply from_intersection_left in Hin.
  apply Hin. 
  Qed.

Theorem intersection_eq {i1 i2 : list Name} {i : Name} :
  In i (myintersection i1 i2) <->  (In i i1 /\ In i i2).
  Proof.
  split; intros.
  - split.
  + apply from_intersection_left in H. apply H.
  + apply from_intersection_right in H. apply H.
  - destruct H. apply in_both_in_intersection; assumption.
  Qed.




Definition intersectionNDL (i1 i2 : NoDupList) : NoDupList.
  Proof.
  exists (myintersection i1 i2).
  (*Proof NoDup myintersection i1 i2*)
    destruct i1 as [i1 nd1].
    destruct i2 as [i2 nd2].
    simpl in *.
    induction i1.
    - simpl. constructor.
    - simpl. destruct (in_dec EqDecN a i2).
    * constructor.
    ** unfold not.
    intros. apply from_intersection_left in H.
    simpl in nd1.
    apply NoDup_cons_iff in nd1.
    destruct nd1. apply H0. apply H.
    ** apply IHi1.
    apply nodup_tl in nd1. apply nd1.
    * apply IHi1.
    apply nodup_tl in nd1. apply nd1.
  Defined.

Definition to_left {i1 i2 : NoDupList} (i : NameSub(intersectionNDL i1 i2))
  : NameSub i1.
  Proof.
    unfold NameSub.
    destruct i.
    exists x.
    apply from_intersection_left in i. apply i.
  Defined.

Definition to_right {i1 i2 : NoDupList} (i : NameSub(intersectionNDL i1 i2))
  : NameSub i2.
  Proof.
    unfold NameSub.
    destruct i.
    exists x.
    apply from_intersection_right in i. apply i.
  Defined.

Definition to_intersection {i1 i2 : NoDupList}
(name:Name) (ini1 : In name i1) (ini2 : In name i2) : 
  NameSub (intersectionNDL i1 i2).
  Proof. 
  unfold NameSub.
  exists name.
  unfold intersectionNDL.
  simpl.
  unfold myintersection.
  apply in_both_in_intersection; assumption.
  Defined.

Definition to_commute {i1 i2 : NoDupList}
  (name:NameSub (intersectionNDL i1 i2)) : 
    NameSub (intersectionNDL i2 i1).
    Proof. 
    unfold NameSub in *.
    destruct name as [name H].
    exists name.
    apply intersection_commutes.
    apply H.
    Defined.

Theorem intersection_disjoint_empty_NDL {i1 i2 : NoDupList} : 
  i1 # i2 -> myintersection i1 i2 = [].
  Proof.
  intros.
  unfold myintersection.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  unfold Disjoint in H.
  simpl in *.
  induction i1.
  - reflexivity.
  - destruct (in_dec EqDecN a i2).
  + exfalso. unfold not in H. apply (H a); simpl; try auto; try assumption.
  + apply IHi1.
  * apply nodup_tl in nd1. apply nd1.
  * intros. apply (H name). simpl. right. apply H0.
  Qed.


Theorem from_intersection_leftNDL {i1 i2 : NoDupList} {i : Name} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->  In i i1.
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply from_intersection_left.
  Qed.

Theorem intersection_commutesNDL {i1 i2 : NoDupList} {i : Name} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->
  In i (myintersection (ndlist i2) (ndlist i1)).
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply intersection_commutes.
  Qed.



Definition from_intersection_rightNDL {i1 i2 : NoDupList} {i : Name} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->  In i i2.
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply from_intersection_right. 
  Qed.

Theorem intersection_eqNDL {i1 i2 : NoDupList} {i : Name} :
  In i (myintersection (ndlist i1) (ndlist i2)) <->  (In i i1 /\ In i i2).
  Proof.
    destruct i1 as [i1 nd1].
    destruct i2 as [i2 nd2].
    simpl in *.
    apply intersection_eq. 
  Qed.

Fixpoint inb (x : Name) (l : list Name) : bool :=
    match l with
    | [] => false
    | y :: ys => if EqDecN x y then true else inb x ys
    end.

Lemma inb_eq_in (x : Name) (l : list Name) : 
  match inb x l with
  | true => In x l
  | false => ~ In x l
  end.
  Proof.
  induction l.
  simpl. auto.
  simpl. destruct (EqDecN x a).
  left. auto.
  destruct (inb x l) eqn:H.
  right. apply IHl.
  unfold not.
  intros.
  destruct H0.
  auto. auto.
  Qed.

Lemma in_eq_inb (x : Name) (l : list Name) :
  In x l <-> inb x l = true.
  Proof. split. 
  - intros.
  unfold inb.
  induction l.
  elim H.
  simpl in *.
  destruct (EqDecN x a).
  reflexivity.
  destruct H. exfalso. apply n. symmetry. apply H.
  apply IHl. apply H.
  - intros. set (inb_eq_in x l).
  rewrite H in y. apply y.
  Qed.

Lemma in_eq_inb_neg (x : Name) (l : list Name) :
  ~ In x l <-> inb x l = false.
  Proof. split. 
  - intros.
  unfold inb.
  induction l.
  reflexivity.
  simpl in *.
  destruct (EqDecN x a).
  destruct H. 
  left. symmetry. apply e.
  apply IHl.
  apply Decidable.not_or in H.
  destruct H.
  apply H0. 
  - intros. set (inb_eq_in x l).
  rewrite H in y. apply y.
  Qed.

Definition not_in_intersection (i1 i2 : NoDupList) : NoDupList.
  Proof.
  exists 
  (filter
    (fun i => negb (inb i (intersectionNDL i1 i2)))
    (i1 ∪ i2)).
  apply NoDup_filter.
  apply NoDup_app_merge; 
  destruct i1; destruct i2; auto.
  Defined.

Open Scope bool_scope.

Definition not_in_intersection_inl (i1 i2 : NoDupList) : NoDupList.
  Proof.
  exists 
  (filter
    (fun i => negb (inb i (intersectionNDL i1 i2)) && inb i i1)
    (i1 ∪ i2)).
  apply NoDup_filter.
  apply NoDup_app_merge; 
  destruct i1; destruct i2; auto.
  Defined.

Theorem not_in_intersection_inl_ini1 (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inl i1 i2) -> In n i1.
  intros.
  destruct i1 as [i1 ndi1]. simpl in *.
  apply filter_In in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply in_eq_inb. apply H1.
  Qed. 

Theorem not_in_intersection_inl_notini2 (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inl i1 i2) -> ~ In n i2.
  intros.
  destruct i1 as [i1 ndi1]. simpl in *.
  apply filter_In in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  unfold not. intros.
  apply in_eq_inb in H1.
  apply Bool.negb_true_iff in H0.
  apply in_eq_inb_neg in H0.
  apply H0. apply in_both_in_intersection; auto.
  Qed. 

Theorem not_in_intersection_inl_OK (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inl i1 i2) -> In n i1 /\ ~ In n i2.
  intros. split.
  apply (not_in_intersection_inl_ini1 i1 i2); assumption.
  apply (not_in_intersection_inl_notini2 i1 i2); assumption.
  Qed.


Theorem merge_not_inl_and_inl (i1 i2 : NoDupList) : 
  permutation 
    i1
    (app_merge' (intersectionNDL i1 i2) (not_in_intersection_inl i1 i2)).
  unfold permutation.
  intros.
  split;intros; simpl in *.
  - destruct i1 as [i1 ndi1]. simpl in *.
    apply in_app_iff.
    destruct (inb name (myintersection i1 i2)) eqn:E.
    + left. induction (myintersection i1 i2) as [|inter qinter Hinter].
    discriminate E. simpl. simpl in E.
    destruct (EqDecN name inter). subst name. left. reflexivity. 
    right. apply Hinter. apply E.
    + right.
    apply filter_In.
    split. 
    * apply in_left_list. apply H.
    * apply Bool.andb_true_iff. split.
    apply Bool.negb_true_iff. apply E.
    apply in_eq_inb in H. apply H.
  - apply in_app_iff in H.
    destruct H.
    + apply from_intersection_left in H. apply H.
    + apply filter_In in H.
    destruct H. 
    apply Bool.andb_true_iff in H0.
    destruct H0.
    set (inb_eq_in name i1).
    rewrite H1 in y. apply y.
  Qed.


  Theorem disjoint_not_in_inter_inter (i1 i2 : NoDupList) : forall n : Name, In n (intersectionNDL i1 i2) -> In n (not_in_intersection_inl i1 i2) -> False.
  unfold intersectionNDL. simpl.
  intros n H H'.
  apply filter_In in H'.
  destruct H'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.negb_true_iff in H1.
  apply in_eq_inb in H. rewrite H in H1. discriminate H1.
  Qed.

End IntersectionNDL.

Global Notation "l1 ∩ l2" := (intersectionNDL l1 l2) (at level 50, left associativity).

Class PermutationNames (l1 l2 : NoDupList) := { pn : permutation l1 l2 }.

Definition PN_P {l1 l2 : NoDupList} (pn : PermutationNames l1 l2) : permutation l1 l2.
  Proof. destruct pn. apply pn0. Qed.

Definition P_NP {l1 l2 : NoDupList} (p : permutation l1 l2) : PermutationNames l1 l2.
  Proof. exists. apply p. Qed.

Definition permut_list_forward (l1 l2 : list Name) (p : permutation l1 l2)
  (nl1 : {name:Name|In name l1}) : {name:Name|In name l2}.
  Proof.
    destruct nl1.
    exists x.
    unfold permutation in p. 
    apply p in i. apply i.
  Defined.

Definition bij_permut_list (l1 l2 : list Name) (p : permutation l1 l2) :
  bijection {name:Name|In name l1} {name:Name|In name l2}.
  Proof.
    refine (mkBijection
    {name:Name|In name l1} {name:Name|In name l2}
    (permut_list_forward l1 l2 p)
    (permut_list_forward l2 l1 (symmetry p)) _ _
    ).
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    Unshelve. apply symmetric_permutation.
  Defined.

#[export] Instance permutation_distributive_PN {o3i1 o4i2 i1o3 i2o4}
  (p13 : PermutationNames (ndlist o3i1) (ndlist i1o3))
  (p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)) : 
  PermutationNames
     (app_merge_NoDupList o3i1 o4i2)
     (app_merge_NoDupList i1o3 i2o4).
  Proof.
  destruct p13 as [p13].
  destruct p24 as [p24].
  constructor.
  apply permutation_distributive; assumption.
  Defined.

#[export] Instance permutation_id_PN (l:NoDupList) : PermutationNames l l.
constructor. exact (permutation_id (ndlist l)).
Defined.

#[export] Instance permutation_id_am_PN (X:NoDupList) : PermutationNames X (app_merge_NoDupList X EmptyNDL).
constructor. rewrite <- merge_right_neutral'. exact (permutation_id (ndlist X)). 
Defined.

#[export] Instance permutation_id_am_l_PN (X:NoDupList) : PermutationNames X (app_merge_NoDupList EmptyNDL X).
constructor. rewrite merge_left_neutral. exact (permutation_id (ndlist X)).
Defined.

Lemma permutationtr {o1 o2 o3}:
permutation
    (app_merge_NoDupList EmptyNDL
       (app_merge_NoDupList (app_merge_NoDupList EmptyNDL (app_merge_NoDupList o1 o2)) o3))
    (app_merge_NoDupList EmptyNDL
       (app_merge_NoDupList o1 (app_merge_NoDupList EmptyNDL (app_merge_NoDupList o2 o3)))).
Proof. simpl. 
apply tr_permutation. 
Defined.

#[export] Instance permutation_id_am_l_PN_empty : PermutationNames
                                  (app_merge_NoDupList EmptyNDL EmptyNDL)
                                  EmptyNDL.
constructor. rewrite merge_left_neutral. exact (permutation_id []).
Defined.

#[export] Instance permutation_id_am_l_PN_empty_r : PermutationNames
                                  EmptyNDL
                                  (app_merge_NoDupList EmptyNDL EmptyNDL).
constructor. rewrite merge_left_neutral. exact (permutation_id []).
Defined.

#[export] Instance permutation_not_in_inter {o1 o2} : 
  PermutationNames o1 ((o1 ∩ o2) ∪ (not_in_intersection_inl o1 o2)).
  Proof.
  constructor. apply (merge_not_inl_and_inl o1 o2).
  Qed.

End Names.


