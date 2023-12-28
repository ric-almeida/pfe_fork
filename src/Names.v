
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Bijections.
Require Import MyBasics.

Require Import FunctionalExtensionality.

Set Printing All.


Import ListNotations.


Module Type Names.
Parameter Name : Type.
Parameter EqDecN : forall x y : Name, {x = y} + {x <> y}.

Record NoDupList : Type :=
mkNoDupList
  {
    ndlist :> list Name ;
    nd : NoDup ndlist ;
  }.

Definition EmptyNDL : NoDupList := {| ndlist := []; nd := NoDup_nil Name |}.


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

(* 
Theorem NoDup_app_merge (l1 : list Name) (l2 : list Name) :
NoDup l1 -> NoDup l2 -> NoDup (app_merge' l1 l2).

Mais pas 
Theorem NoDup_app_merge (l1 : list Name) (l2 : list Name) :
NoDup (app_merge' l1 l2). This <- is nodup
*)




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
Qed.

Lemma in_app_or_m_nod_dup : forall (l m:list Name) (a:Name), 
NoDup l -> NoDup m -> In a (app_merge' l m) -> In a l + In a m.
Proof.
    intros l m a ndl ndm H.
    destruct (in_dec EqDecN a m).
    - right. apply i. 
    - left. apply not_in_left in H; assumption.
Qed.

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


(* INTERESTING PART ABOUT NODUPLISTS *)

Definition app_NoDupList (l1 : NoDupList) (l2 : NoDupList) : NoDupList :=
{|
ndlist := app_merge' l1 l2 ;
nd := NoDup_app_merge l1 l2 (nd l1) (nd l2)
|}.


Theorem left_empty (i:NoDupList) :
forall name : Name,
  In name (app_NoDupList EmptyNDL i) <->
  In name i.
Proof. intros.
split; intros; simpl in *; apply H.
Qed.



Theorem woopsie : forall l1 l2, app_merge' (ndlist l1) (ndlist l2) = nodup EqDecN ((ndlist l1)++(ndlist l2)).
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
Admitted. 

(* PART ABOUT DISJOINT LISTS *)
Section DisjointLists.
Definition Disjoint (l1:NoDupList) (l2:NoDupList) : Prop :=
forall name, In name l1 -> ~ In name l2.

Theorem nodupmergedisjointlist (l1:NoDupList) (l2:NoDupList) :
Disjoint l1 l2 -> ndlist (list_to_NDL (l1 ++ l2)) = (ndlist l1) ++ (ndlist l2).
Proof.
unfold Disjoint.
intros.
destruct l1 as [l1 nd1].
destruct l2 as [l2 nd2].
simpl.
apply nodup_fixed_point. Abort.


End DisjointLists.






Section NameSubsets.


Definition NameSub (nl : NoDupList) : Type :=
  {name:Name | In name nl}.


Definition bij_list_forward (i1:NoDupList) (i2:NoDupList) : 
  (NameSub i1) + (NameSub i2) ->  NameSub (app_NoDupList i1 i2).
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
  NameSub (app_NoDupList i1 i2)
  ->
  (NameSub i1) + (NameSub i2).
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros Hn.
  apply in_app_or_m_nod_dup' in Hn; assumption.
  Defined.

Definition bij_list_names (i1:NoDupList) (i2:NoDupList) : 
  bijection ((NameSub i1) + (NameSub i2)) (NameSub (app_NoDupList i1 i2)).
  Proof.
  apply 
  (mkBijection _ _ 
  (bij_list_forward i1 i2) 
  (bij_list_backward i1 i2));
  destruct i1 as [i1 ndi1];
  destruct i2 as [i2 ndi2]; simpl.
  - apply functional_extensionality.
  intros.
  unfold bij_list_forward, funcomp, id. simpl. admit.
  - apply functional_extensionality.
  destruct x as [(na1, H1) | (na2, H2)].
  + unfold id. simpl. unfold funcomp. simpl. 
  Admitted.

(* 

Definition bij_list_forward' (i1:NoDupList) (i2:NoDupList) : 
  (NameSub i1) + (NameSub i2)
  ->
  NameSub (list_to_NDL (i1 ++ i2)).
  Proof.
  refine (fun name => match name with
                | inl (exist _ name' H1) => _
                | inr (exist _ name' H2) => _
                end).
    + exists (name'). unfold list_to_NDL.
      apply in_left_list; assumption. 
    + exists (name'). 
      apply in_right_list; assumption. 
    Defined.

Definition bij_list_backward (i1:NoDupList) (i2:NoDupList) :
  NameSub (app_NoDupList i1 i2)
  ->
  (NameSub i1) + (NameSub i2).
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros Hn.
  apply in_app_or_m_nod_dup' in Hn; assumption.
  Defined.

Definition bij_list_names (i1:NoDupList) (i2:NoDupList) : 
  bijection ((NameSub i1) + (NameSub i2)) (NameSub (app_NoDupList i1 i2)).
  Proof.
  apply 
  (mkBijection _ _ 
  (bij_list_forward i1 i2) 
  (bij_list_backward i1 i2));
  destruct i1 as [i1 ndi1];
  destruct i2 as [i2 ndi2]; simpl.
  - apply functional_extensionality.
  intros.
  unfold bij_list_forward, funcomp, id. simpl. admit.
  - apply functional_extensionality.
  destruct x as [(na1, H1) | (na2, H2)].
  + unfold id. simpl. unfold funcomp. simpl. 
  Admitted. *)



End NameSubsets.


End Names.