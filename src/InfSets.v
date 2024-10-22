Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-x".

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Bijections.
Require Import MyBasics.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.CRelationClasses.


Import ListNotations.



Module Type InfiniteParameter.
Parameter InfType : Type.
Parameter EqDecN : forall x y : InfType, {x = y} + {x <> y}.
Parameter InfProof: forall l:list InfType, exists n:InfType, ~ In n l.
Parameter DefaultInfType : InfType.
Parameter freshElInInfType : list InfType -> InfType. 
Parameter notInfreshElInInfType : forall l:list InfType, ~ In (freshElInInfType l) l. 
End InfiniteParameter.


Module FiniteSubset (NP: InfiniteParameter).
Include NP.

Section MergeList.
Fixpoint app_merge (l1 : list InfType) (l2 : list InfType) {struct l1} : list InfType :=  
    match l1 with
    | nil => l2
    | a :: l1' =>  
      if in_dec EqDecN a l2 then app_merge l1' l2
        else a :: app_merge l1' l2
  end.

Lemma merge_head {l1' l2' : list InfType} {a : InfType}:
  app_merge (a::l1') (a::l2') = app_merge l1' (a::l2').
  Proof.
      simpl.
      destruct (EqDecN a a).
      - reflexivity.
      - exfalso. apply n. reflexivity.
  Qed.

Lemma app_merge_empty_right (l1 : list InfType) :
  app_merge l1 [] = l1.
  Proof.
      induction l1.
      simpl. reflexivity.
      simpl. rewrite IHl1. reflexivity. 
  Qed.

Lemma app_merge_empty_left (l1 : list InfType) :
  app_merge [] l1 = l1.
  Proof.
      induction l1.
      simpl. reflexivity.
      simpl. reflexivity. 
  Qed.
End MergeList.

Section InList.
Lemma in_eq_m {a:InfType} {l}: 
  In a (app_merge [a] l).
  Proof.
      intros. simpl. destruct (in_dec EqDecN a l).
      apply i.
      constructor. reflexivity. 
  Qed.

Lemma in_cons_m : forall (a b:InfType) (l:list InfType), 
  In b l -> In b (app_merge [a] l).
  Proof. 
      intros. simpl. destruct (in_dec EqDecN a l).
      - apply H. 
      - apply in_cons. apply H.
  Qed.

Lemma in_head_right_list {a:InfType} {l1 l2}:
  In a (app_merge l1 (a::l2)).
  Proof.
      induction l1 as [|a1 l1' IHl1].
      - simpl. left. reflexivity.
      - simpl. destruct (EqDecN a a1).
      + apply IHl1.
      + destruct (in_dec EqDecN a1 l2).
      * apply IHl1.
      * apply in_cons. apply IHl1.
  Qed.

Theorem in_right_list : forall (b:InfType) (l1:list InfType) (l2:list InfType), 
  In b l2 -> In b (app_merge l1 l2).
  Proof. 
      intros.
      induction l1.
      - simpl. apply H.
      - simpl. destruct (in_dec EqDecN a l2).
      + apply IHl1.
      + simpl. right. apply IHl1. 
  Qed. 

Lemma in_head_left_list {a:InfType} {l1 l2}:
  In a (app_merge (a :: l1) l2).
  Proof.
      induction l1 as [|a1 l1' IHl1].
      - apply in_eq_m.
      - simpl. destruct (in_dec EqDecN a l2).
      + destruct (in_dec EqDecN a1 l2).
      * apply in_right_list. apply i.
      * apply in_cons. apply in_right_list. apply i.
      + constructor. reflexivity.
  Qed.
Theorem not_inr_not_interesting (a: InfType) (b:InfType) (l1:list InfType) (l2:list InfType) : 
  ~ In b l2 -> a <> b -> In b (app_merge l1 l2) -> In b (app_merge (a :: l1) l2).
  Proof.
      intros. simpl. 
      destruct (in_dec EqDecN a l2).
      - apply H1.
      - apply in_cons. apply H1.
  Qed.

Theorem inl_useless (a:InfType) (l1:list InfType) (l2:list InfType) : 
  In a l2 -> app_merge (a :: l1) l2 = app_merge l1 l2.
  Proof.
      intros.
      simpl.
      destruct (in_dec EqDecN a l2).
      - reflexivity.
      - exfalso. apply n. apply H.
  Qed. 

Theorem not_right (b:InfType) (l1:list InfType) (l2:list InfType) : 
  ~ In b l2 -> In b l1 -> In b (app_merge l1 l2).
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

Theorem in_left_list : forall (b:InfType) (l1:list InfType) (l2:list InfType), 
  In b l1 -> In b (app_merge l1 l2).
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
    
Lemma in_split_m (a:InfType) (l:list InfType) :
  In a l -> exists l1 l2, l = app_merge l1 (a :: l2).
  Proof. (* FALSE !! If l has dup, then app_merge will remove them *)
Abort.

Lemma in_or_app_m : forall (l m:list InfType) (a:InfType), 
  In a l \/ In a m -> In a (app_merge l m).
  Proof. 
      intros.
      destruct H.
      - apply in_left_list. apply H.
      - apply in_right_list. apply H.
  Qed.

Theorem not_in_cons_m (x a : InfType) (l : list InfType):
  ~ In x (app_merge [a] l) <-> x <> a /\ ~ In x l.
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
  ~ In a (app_merge l1 l2).
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

Theorem not_in_left {a:InfType} {l m} : 
  In a (app_merge l m) -> ~ In a m -> In a l.
  Proof.
      intros H H'.
      destruct (in_dec EqDecN a l).
      - apply i.
      - exfalso. apply (not_in_merge n H'). (*need comu?*)
      apply H.
  Qed. 

Theorem not_in_right {a:InfType} {l m} : 
  In a (app_merge l m) -> ~ In a l -> In a m.
  Proof.
      intros H H'.
      destruct (in_dec EqDecN a m).
      - apply i.
      - exfalso. apply (not_in_merge H' n). apply H.
  Qed.

Lemma in_app_or_m : forall (l m:list InfType) (a:InfType), 
  In a (app_merge l m) -> In a l \/ In a m.
  Proof.
      intros.
      destruct (in_dec EqDecN a m).
      - right. apply i. 
      - left. apply not_in_left in H; assumption.
  Defined.

Lemma not_in_merge_iff {a} {l1 l2}:
  (~ In a l1 /\ ~ In a l2) <->
  ~ In a (app_merge l1 l2).
  Proof. 
    split.
    - intros [H1 H2].
    apply not_in_merge; assumption.
    - intros. unfold not. split; intros. apply H. apply in_left_list. assumption.
    apply H. apply in_right_list. assumption. 
  Qed.

Lemma in_app_or_m_nod_dup : forall (l m:list InfType) (a:InfType), 
  NoDup l -> NoDup m -> In a (app_merge l m) -> In a l + In a m.
  Proof.
      intros l m a ndl ndm H.
      destruct (in_dec EqDecN a m).
      - right. apply i. 
      - left. apply not_in_left in H; assumption.
  Defined.

Lemma in_app_or_m_nod_dup' : forall (l m:list InfType), 
  NoDup l -> NoDup m -> {a:InfType | In a (app_merge l m)} -> {a | In a l} + {a | In a m}.
  Proof.
      intros l m ndl ndm H.
      destruct H.
      destruct (in_dec EqDecN x m).
      - right. exists x. apply i0. 
      - left. exists x. apply not_in_left in i; assumption.
  Qed.

Lemma in_app_iff {b:InfType} {l1 l2} :
  In b (app_merge l1 l2) <-> In b l1 \/ In b l2.
  Proof. 
      intros. split. 
      - apply in_app_or_m.
      - apply in_or_app_m.
  Qed.

Theorem in_app_merge_com {l1 l2 : list InfType} : forall a,
  In a (app_merge l1 l2) -> In a (app_merge l2 l1).
  Proof.
      intros.
      apply in_app_or_m in H.
      destruct H.
      - apply in_right_list; assumption.
      - apply in_left_list; assumption.
  Qed.

Theorem in_app_merge_comu {l1 l2 : list InfType} : forall a,
  In a (app_merge l1 l2) <-> In a (app_merge l2 l1).
  Proof.
      intros. split; apply in_app_merge_com.
  Qed.

Theorem in_app_merge_trans {l1 l2 l3 : list InfType} : forall a,
  In a (app_merge l1 (app_merge l2 l3)) -> In a (app_merge (app_merge l1 l2) l3).
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

Theorem in_app_merge_transi {l1 l2 l3 : list InfType} : forall a,
  In a (app_merge (app_merge l1 l2) l3) <-> In a (app_merge l1 (app_merge l2 l3)).
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
      - apply in_app_merge_trans.
  Defined.

Definition reflFinSub {r} : forall x : InfType,
  In x r <-> In x r.
  reflexivity. Defined.
End InList.


Section MyNoDupList.
Record NoDupList : Type :=
  mkNoDupList
  {
    ndlist :> list InfType ;
    nd : NoDup ndlist ;
  }.
Remark nodupproofirrelevant : forall l1 l2:NoDupList, 
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
Definition EmptyNDL : NoDupList := {| ndlist := []; nd := NoDup_nil InfType |}.
Definition OneelNDL (n : InfType): NoDupList.
  Proof. 
  eapply (mkNoDupList [n]).
  constructor; auto; constructor. 
  Defined.

Lemma NoDup_in_or_exclusive {a h:InfType} {t:list InfType} :
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

Lemma NoDup_in_or_exclusive' {a h:InfType} {t:list InfType} :
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

Lemma eq_means_cons_eq {a1 a2:InfType} {l1 l2} :
  a1 = a2 /\ l1 = l2 -> a1::l1 = a2::l2.
  Proof. 
      intros.
      destruct H. rewrite H. rewrite H0. reflexivity. 
  Qed.

Lemma NoDupFalse {a:InfType} {l1 l2} :
  ~ NoDup (a :: l1 ++ a :: l2). 
  Proof.
      unfold not. 
      intros nd.
      apply NoDup_cons_iff in nd. 
      destruct nd. apply H. apply in_or_app. right. constructor. reflexivity.
  Qed.

Lemma NoDup_id {a : InfType} {l1 l2} :
  NoDup (l1 ++ a :: l2) -> l1 ++ a :: l2 = app_merge l1 (a :: l2).
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
  NoDup (l1 ++ l2) -> l1 ++ l2 = app_merge l1 l2.
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

Lemma in_split_m_dup (a:InfType) (l:list InfType) :
  NoDup l -> In a l -> exists l1 l2, l = app_merge l1 (a :: l2).
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

Lemma rm_headNoDUP {a:InfType} {l}: 
  ~ In a l -> (NoDup (a::l) <-> NoDup l).
  Proof.
      intros.
      split.
      - intros. apply NoDup_cons_iff in H0.
      destruct H0 as [H0 H']. apply H'.
      - intros. constructor; assumption.
  Qed.

Theorem NoDup_app_merge (l1 : list InfType) (l2 : list InfType) :
  NoDup l1 -> NoDup l2 -> NoDup (app_merge l1 l2).
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

Lemma rearrangenodup {a a':InfType} {l}: 
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



Lemma app_merge_id {i1 i2}: 
  NoDup i1 -> NoDup i2 -> (forall x, In x i1 -> ~ In x i2) -> app_merge i1 i2 = i1 ++ i2.
  Proof.
  intros.
  induction i1.
  simpl. reflexivity.
  simpl. destruct (in_dec EqDecN a i2).
  - exfalso. specialize (H1 a). apply H1; auto. constructor. reflexivity.
  - rewrite IHi1; auto. apply nodup_tl in H. assumption.
  intros. apply H1. right. assumption. 
  Qed.


Lemma app_merge_cons_id {a} {l:NoDupList}: 
  NoDup l -> ~ In a l -> app_merge (OneelNDL a) l = a :: l.
  Proof.
  intros. 
  rewrite (@app_merge_id (OneelNDL a) l).
  + simpl. auto.
  + simpl. 
  constructor. 
  - auto.
  - constructor.
  + apply H.
  + intros. inversion H1. subst a. apply H0.
  elim H2.
  Qed.

End MyNoDupList.

Section MyPermutations.
Definition permutation (l1: list InfType) (l2: list InfType) := forall x, In x l1 <-> In x l2.
Definition permutation_id (l: list InfType) : permutation l l.
Proof. unfold permutation. intros. tauto. Defined.

Definition permutation_id' (l: list InfType) (l': list InfType) : l = l' -> permutation l l'.
Proof. intros. destruct H. exact (permutation_id l).
Defined. 



Theorem symmetric_permutation: Symmetric permutation.
Proof.
  constructor; unfold permutation in H; specialize (H x0); destruct H; assumption.
Qed.

Theorem transitive_permutation: Transitive permutation.
Proof.
  constructor; unfold permutation in *; specialize (H x0); destruct H; specialize (H0 x0); destruct H0; intros; auto.
Qed.

Theorem reflexive_permutation: Reflexive permutation.
Proof.
  constructor; unfold permutation in *; auto. 
Qed.
  
Definition tr_permutation {i1 i2 i3} : 
  permutation
    (app_merge (app_merge i1 i2) i3)
    (app_merge i1 (app_merge i2 i3)).
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

Lemma app_merge_cong {i1 i2 i3 i4}:  
  permutation i1 i2 -> permutation i3 i4 -> 
  permutation (app_merge i1 i3) (app_merge i2 i4).
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

End MyPermutations.


Definition app_merge_NoDupList (l1 : NoDupList) (l2 : NoDupList) : NoDupList :=
{|
ndlist := app_merge l1 l2 ;
nd := NoDup_app_merge l1 l2 (nd l1) (nd l2)
|}.

Notation "l1 ∪ l2" := (app_merge_NoDupList l1 l2) (at level 50, left associativity).

Section MyNDLTools.
Lemma app_merge_or {l1 l2 n} :
 In n (app_merge_NoDupList l1 l2) -> In n l1 \/ In n l2.
 Proof. apply in_app_iff. Qed.

Theorem left_empty (i:NoDupList) :
  forall x : InfType,
    In x (app_merge_NoDupList EmptyNDL i) <->
    In x i.
  Proof. intros.
      split; intros; simpl in *; apply H.
  Qed.

Theorem right_empty (i:NoDupList) :
  forall x : InfType,
    In x (app_merge_NoDupList i EmptyNDL) <->
    In x i.
  Proof. intros.
      split; intros; simpl in *. rewrite app_merge_empty_right in H. apply H. rewrite app_merge_empty_right. apply H.
  Qed.

Theorem eq_NDL (l1:list InfType) (l2:list InfType) 
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
  apply (eq_NDL (app_merge ndlist0 []) ndlist0).
  simpl. apply app_merge_empty_right.
  Qed.

Theorem merge_left_neutral : forall (l:NoDupList),
  app_merge_NoDupList EmptyNDL l = l.
  Proof. intros l. unfold EmptyNDL.
  unfold app_merge_NoDupList. 
  destruct l. simpl.
  apply (eq_NDL (app_merge [] ndlist0) ndlist0).
  simpl. apply app_merge_empty_left.
  Qed.

Theorem merge_right_neutral' : forall (l:NoDupList),
  ndlist l = ndlist (app_merge_NoDupList l EmptyNDL).
  Proof.
  symmetry.
  destruct l.
  simpl.
  apply  app_merge_empty_right.
  Qed.

Theorem permutation_distributive {o3i1 o4i2 i1o3 i2o4}
  (p13 : permutation (ndlist o3i1) (ndlist i1o3))
  (p24 : permutation (ndlist o4i2) (ndlist i2o4)) : 
  permutation
    (app_merge_NoDupList o3i1 o4i2)
    (app_merge_NoDupList i1o3 i2o4).
  Proof.
  unfold permutation in *.
  intros; split; intros; specialize (p13 x); specialize (p24 x); destruct p13; destruct p24; apply in_app_or_m in H; destruct H.
  - apply in_left_list. apply H0. apply H.
  - apply in_right_list. apply H2. apply H.
  - apply in_left_list. apply H1. apply H.
  - apply in_right_list. apply H3. apply H.  
  Defined.

Lemma permutation_union_commutes {i1 i2} : permutation (i1 ∪ i2) (i2 ∪ i1).
  Proof.
  unfold permutation.
  intros; split; intros; apply in_app_or_m in H; destruct H.
  - apply in_right_list. apply H.
  - apply in_left_list. apply H.
  - apply in_right_list. apply H.
  - apply in_left_list. apply H.
  Qed.

Lemma permutation_empty_union_commutes {o1 o2} : permutation (EmptyNDL ∪ (o1 ∪ o2)) (EmptyNDL ∪ (o2 ∪ o1)).
  Proof.
  unfold permutation.
  intros; split; intros; apply in_app_or_m in H; destruct H; try destruct H; apply in_app_or_m in H; destruct H.
  - apply in_right_list. apply in_right_list. apply H.
  - apply in_right_list. apply in_left_list. apply H.
  - apply in_right_list. apply in_right_list. apply H.
  - apply in_right_list. apply in_left_list. apply H.
  Qed.
End MyNDLTools.




Definition Disjoint (l1:NoDupList) (l2:NoDupList) : Prop :=
  forall x, In x l1 -> ~ In x l2.
Notation "l1 # l2" := (Disjoint l1 l2) (at level 50, left associativity).

Section DisjointLists.
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


Lemma disjoint_NoDup_app : forall (l1 l2 : list InfType),
  NoDup l1 -> NoDup l2 -> (forall a : InfType, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
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

Theorem not_in_both : forall l1 l2, forall n, 
  In n (ndlist l1) -> In n (ndlist l2) -> Disjoint l1 l2 -> False.
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
  - apply (not_in_both i1 i2 x H H0 dis_i12). 
  - apply (not_in_both i1 i3 x H H0 dis_i13). 
  Qed.

Class DisjointNDL (l1 l2 : NoDupList) := { disj : forall n, In n l1 -> In n l2 -> False }.
#[export] Instance disj_OneEl (n:InfType) (l : NoDupList) (not_in : ~ In n l):
  DisjointNDL l (OneelNDL n).
  Proof.
  constructor.
  intros n' Hn' H'.
  simpl in H'. destruct H'.
  - subst n. contradiction.
  - apply H.
  Qed.


#[export] Instance disj_left_neutral (l : NoDupList) : DisjointNDL EmptyNDL l.
  Proof.
  constructor.
  intros n Hn.
  elim (Hn).
  Qed.

#[export] Instance disj_right_neutral (l : NoDupList) : DisjointNDL l EmptyNDL.
  Proof.
  constructor.
  intros n _ Hn.
  elim (Hn).
  Qed.

#[export] Instance disj_app_right (l1 l2 l3 : NoDupList) (Disj12 : DisjointNDL l1 l2) (Disj13 : DisjointNDL l1 l3) : DisjointNDL l1 (l2 ∪ l3).
  Proof.
  constructor.
  intros n H1 H23.
  destruct Disj12. destruct Disj13.
  apply app_merge_or in H23.
  destruct H23. 
  * apply (disj0 n); try assumption.
  * apply (disj1 n); try assumption.
  Qed.

#[export] Instance disj_app_left (l1 l2 l3 : NoDupList) (Disj13 : DisjointNDL l1 l3) (Disj23 : DisjointNDL l2 l3) : DisjointNDL (l1 ∪ l2) l3.
  Proof.
  constructor.
  intros n H12 H3.
  destruct Disj13. destruct Disj23.
  apply app_merge_or in H12.
  destruct H12. 
  * apply (disj0 n); try assumption.
  * apply (disj1 n); try assumption.
  Qed.

Definition DN_D {l1 l2} : DisjointNDL l1 l2 -> Disjoint l1 l2.
  Proof. 
  intros.
  unfold Disjoint.
  destruct H as [H].
  unfold not.
  apply H.
  Qed.

Definition D_ND {l1 l2} : Disjoint l1 l2 -> DisjointNDL l1 l2.
  Proof. 
  intros.
  unfold Disjoint in H.
  unfold not in H.
  constructor.
  apply H.
  Qed.


End DisjointLists.


Global Notation "l1 # l2" := (DisjointNDL l1 l2) (at level 50, left associativity). 


Section FinSubsets.
Definition ListType (nl : NoDupList) : Type :=
  {x:InfType | In x nl}.
Remark nodupproofirrelevantns : forall l1 l2, 
    ndlist l1 = ndlist l2 -> ListType l1 = ListType l2.
    Proof. intros. unfold ListType. rewrite H. reflexivity. Qed. 

Definition bij_list_forward (i1:NoDupList) (i2:NoDupList) : 
  (ListType i1) + (ListType i2) ->  ListType (app_merge_NoDupList i1 i2).
  Proof.
  refine (fun x => match x with
                | inl (exist x' H1) => _
                | inr (exist x' H2) => _
                end).
    + exists (x'). 
      apply in_left_list; assumption. 
    + exists (x'). 
      apply in_right_list; assumption. 
    Defined.


Definition bij_list_backward (i1:NoDupList) (i2:NoDupList) :
  ListType (app_merge_NoDupList i1 i2)
  ->
  (ListType i1) + (ListType i2).
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros Hn.
  apply in_app_or_m_nod_dup' in Hn; assumption.
  Defined.

Definition bij_list_backward' (i1:NoDupList) (i2:NoDupList) {dis_i:Disjoint i1 i2}:
  ListType (app_merge_NoDupList i1 i2)
  ->
  (ListType i1) + (ListType i2).
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
  

Definition bij_list_ndl (i1:NoDupList) (i2:NoDupList) {dis_i:Disjoint i1 i2} : 
  bijection ((ListType i1) + (ListType i2)) (ListType (app_merge_NoDupList i1 i2)).
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
  + destruct ns1 as [x Hini1].
  destruct (in_dec EqDecN x i1).
  * apply f_equal. apply subset_eq_compat. reflexivity.
  * exfalso. apply n. apply Hini1.
  + destruct ns2 as [x Hini2].
  destruct (in_dec EqDecN x i1).
  * exfalso. 
  unfold Disjoint in dis_i. apply dis_i in i. apply i. apply Hini2.
  * apply f_equal. apply subset_eq_compat. reflexivity.
  Defined.
End FinSubsets.



Section IntersectionNDL.
Fixpoint myintersection (l1 : list InfType) (l2 : list InfType) : list InfType := 
  match l1 with
    | nil => []
    | a :: l1' =>  
      if in_dec EqDecN a l2 then a::myintersection l1' l2
        else myintersection l1' l2
  end.

Lemma in_both_in_intersection {i1 i2 : list InfType} {i : InfType} :
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



Definition from_intersection_left {i1 i2 : list InfType} {i : InfType} :
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



Theorem intersection_commutes {i1 i2 : list InfType} {i : InfType} :
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



Definition from_intersection_right {i1 i2 : list InfType} {i : InfType} :
  In i (myintersection i1 i2) ->  In i i2.
  Proof.
  intros Hin.
  apply intersection_commutes in Hin.
  apply from_intersection_left in Hin.
  apply Hin. 
  Qed.

Theorem intersection_eq {i1 i2 : list InfType} {i : InfType} :
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

Definition to_left {i1 i2 : NoDupList} (i : ListType(intersectionNDL i1 i2))
  : ListType i1.
  Proof.
    unfold ListType.
    destruct i.
    exists x.
    apply from_intersection_left in i. apply i.
  Defined.

Definition to_right {i1 i2 : NoDupList} (i : ListType(intersectionNDL i1 i2))
  : ListType i2.
  Proof.
    unfold ListType.
    destruct i.
    exists x.
    apply from_intersection_right in i. apply i.
  Defined.

Definition to_intersection {i1 i2 : NoDupList}
  (x:InfType) (ini1 : In x i1) (ini2 : In x i2) : 
    ListType (intersectionNDL i1 i2).
    Proof. 
    unfold ListType.
    exists x.
    unfold intersectionNDL.
    simpl.
    unfold myintersection.
    apply in_both_in_intersection; assumption.
    Defined.

Definition to_commute {i1 i2 : NoDupList}
  (x:ListType (intersectionNDL i1 i2)) : 
    ListType (intersectionNDL i2 i1).
    Proof. 
    unfold ListType in *.
    destruct x as [x H].
    exists x.
    apply intersection_commutes.
    apply H.
    Defined.

Lemma ListType_merge_proof_irrelevance {t q ndl} :
  ListType (OneelNDL t ∪ 
    {| ndlist := q; nd := nodup_tl t q ndl |}) = 
  ListType ({| ndlist := t :: q; nd := ndl |}).
  Proof.
  apply nodupproofirrelevantns. simpl.
  destruct (in_dec EqDecN t q).
  exfalso. rewrite (NoDup_cons_iff t q) in ndl.
  destruct ndl. contradiction.
  reflexivity.
  Qed.

Lemma Disjoint_NoDuPlist {a l ndl} :
  OneelNDL a # {| ndlist := l; nd := nodup_tl a l ndl |}. 
  Proof.
  constructor. simpl. intros n [Hc|Hc] InH. 
  subst a. rewrite (NoDup_cons_iff n l) in ndl.
  destruct ndl. contradiction. apply Hc.
  Qed.

  
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
  + exfalso. destruct H as [H]. unfold not in H. apply (H a); simpl; try auto; try assumption.
  + apply (IHi1 (nodup_tl a i1 nd1)). 
  constructor. intros. destruct H as [H]. 
  apply (H n0). simpl. right. apply H0.
  apply H1. 
  Qed.


Theorem from_intersection_leftNDL {i1 i2 : NoDupList} {i : InfType} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->  In i i1.
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply from_intersection_left.
  Qed.

Theorem intersection_commutesNDL {i1 i2 : NoDupList} {i : InfType} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->
  In i (myintersection (ndlist i2) (ndlist i1)).
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply intersection_commutes.
  Qed.



Definition from_intersection_rightNDL {i1 i2 : NoDupList} {i : InfType} :
  In i (myintersection (ndlist i1) (ndlist i2)) ->  In i i2.
  Proof.
  destruct i1 as [i1 nd1].
  destruct i2 as [i2 nd2].
  simpl in *.
  apply from_intersection_right. 
  Qed.

Theorem intersection_eqNDL {i1 i2 : NoDupList} {i : InfType} :
  In i (myintersection (ndlist i1) (ndlist i2)) <->  (In i i1 /\ In i i2).
  Proof.
    destruct i1 as [i1 nd1].
    destruct i2 as [i2 nd2].
    simpl in *.
    apply intersection_eq. 
  Qed.

Fixpoint inb (x : InfType) (l : list InfType) : bool :=
    match l with
    | [] => false
    | y :: ys => if EqDecN x y then true else inb x ys
    end.

Lemma inb_eq_in (x : InfType) (l : list InfType) : 
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

Lemma in_eq_inb (x : InfType) (l : list InfType) :
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

Lemma in_eq_inb_neg (x : InfType) (l : list InfType) :
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
  In n (not_in_intersection_inl i1 i2) <-> In n i1 /\ ~ In n i2.
  split. 
  -  intros. split.
  apply (not_in_intersection_inl_ini1 i1 i2); assumption.
  apply (not_in_intersection_inl_notini2 i1 i2); assumption.
  - intros [H1 nH2].
  unfold not_in_intersection_inl.
  simpl.
  apply filter_In.
  split.
  apply in_left_list. apply H1.
  apply Bool.andb_true_iff.
  split.
  apply Bool.negb_true_iff.
  apply in_eq_inb_neg.
  unfold not. intros. apply nH2.
  apply from_intersection_right in H. auto.
  apply in_eq_inb. auto.
  Qed.


Theorem merge_not_inl_and_inl (i1 i2 : NoDupList) : 
  permutation 
    i1
    (app_merge (intersectionNDL i1 i2) (not_in_intersection_inl i1 i2)).
  Proof.
    unfold permutation.
    intros.
    split;intros; simpl in *.
    - destruct i1 as [i1 ndi1]. simpl in *.
      apply in_app_iff.
      destruct (inb x (myintersection i1 i2)) eqn:E.
      + left. induction (myintersection i1 i2) as [|inter qinter Hinter].
      discriminate E. simpl. simpl in E.
      destruct (EqDecN x inter). subst x. left. reflexivity. 
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
      set (inb_eq_in x i1).
      rewrite H1 in y. apply y.
  Qed.


Theorem disjoint_not_in_inter_inter (i1 i2 : NoDupList) : forall n : InfType, In n (intersectionNDL i1 i2) -> In n (not_in_intersection_inl i1 i2) -> False.
  unfold intersectionNDL. simpl.
  intros n H H'.
  apply filter_In in H'.
  destruct H'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.negb_true_iff in H1.
  apply in_eq_inb in H. rewrite H in H1. discriminate H1.
  Qed.


Definition not_in_intersection_inr (i1 i2 : NoDupList) : NoDupList.
  Proof.
  exists 
  (filter
    (fun i => negb (inb i (intersectionNDL i1 i2)) && inb i i2)
    (i1 ∪ i2)).
  apply NoDup_filter.
  apply NoDup_app_merge; 
  destruct i1; destruct i2; auto.
  Defined.

Theorem not_in_intersection_inr_ini2 (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inr i1 i2) -> In n i2.
  intros.
  destruct i1 as [i1 ndi1]. simpl in *.
  apply filter_In in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply in_eq_inb. apply H1.
  Qed. 

Theorem not_in_intersection_inr_notini1 (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inr i1 i2) -> ~ In n i1.
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

Theorem not_in_intersection_inr_OK (i1 i2 : NoDupList) : 
  forall n, 
  In n (not_in_intersection_inr i1 i2) <-> In n i2 /\ ~ In n i1.
  split.
  - intros. split.
  apply (not_in_intersection_inr_ini2 i1 i2); assumption.
  apply (not_in_intersection_inr_notini1 i1 i2); assumption.
  - intros [H2 nH1].
  unfold not_in_intersection_inr.
  simpl.
  apply filter_In.
  split.
  apply in_right_list. apply H2.
  apply Bool.andb_true_iff.
  split.
  apply Bool.negb_true_iff.
  apply in_eq_inb_neg.
  unfold not. intros. apply nH1.
  apply from_intersection_left in H. auto.
  apply in_eq_inb. auto.
  Qed.


Theorem merge_not_inr_and_inr (i1 i2 : NoDupList) : 
  permutation 
    i2
    (app_merge (intersectionNDL i1 i2) (not_in_intersection_inr i1 i2)).
  Proof.
    unfold permutation.
    intros.
    split;intros; simpl in *.
    - destruct i1 as [i1 ndi1]. simpl in *.
      apply in_app_iff.
      destruct (inb x (myintersection i1 i2)) eqn:E.
      + left. induction (myintersection i1 i2) as [|inter qinter Hinter].
      discriminate E. simpl. simpl in E.
      destruct (EqDecN x inter). subst x. left. reflexivity. 
      right. apply Hinter. apply E.
      + right.
      apply filter_In.
      split. 
      * apply in_right_list. apply H.
      * apply Bool.andb_true_iff. split.
      apply Bool.negb_true_iff. apply E.
      apply in_eq_inb in H. apply H.
    - apply in_app_iff in H.
      destruct H.
      + apply from_intersection_right in H. apply H.
      + apply filter_In in H.
      destruct H. 
      apply Bool.andb_true_iff in H0.
      destruct H0.
      apply in_eq_inb.
      apply H1.
  Qed.


Theorem disjoint_not_in_inter_inter_inr (i1 i2 : NoDupList) : forall n : InfType, In n (intersectionNDL i1 i2) -> In n (not_in_intersection_inr i1 i2) -> False.
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

Section permutationsNDL.
Class PermutationNDL (l1 l2 : NoDupList) := { pn : permutation l1 l2 }.
Definition PN_P {l1 l2 : NoDupList} (pn : PermutationNDL l1 l2) : permutation l1 l2.
  Proof. destruct pn. apply pn0. Qed.

Definition P_NP {l1 l2 : NoDupList} (p : permutation l1 l2) : PermutationNDL l1 l2.
  Proof. exists. apply p. Qed.

Definition permut_list_forward (l1 l2 : list InfType) (p : permutation l1 l2)
  (nl1 : {x:InfType|In x l1}) : {x:InfType|In x l2}.
  Proof.
    destruct nl1.
    exists x.
    unfold permutation in p. 
    apply p in i. apply i.
  Defined.

Definition bij_permut_list (l1 l2 : list InfType) (p : permutation l1 l2) :
  bijection {x:InfType|In x l1} {x:InfType|In x l2}.
  Proof.
    refine (mkBijection
    {x:InfType|In x l1} {x:InfType|In x l2}
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
  (p13 : PermutationNDL (ndlist o3i1) (ndlist i1o3))
  (p24 : PermutationNDL (ndlist o4i2) (ndlist i2o4)) : 
  PermutationNDL
     (app_merge_NoDupList o3i1 o4i2)
     (app_merge_NoDupList i1o3 i2o4).
  Proof.
  destruct p13 as [p13].
  destruct p24 as [p24].
  constructor.
  apply permutation_distributive; assumption.
  Defined.

#[export] Instance permutation_id_PN (l:NoDupList) : PermutationNDL l l.
  constructor. exact (permutation_id (ndlist l)).
  Defined.

#[export] Instance permutation_id_am_PN (X:NoDupList) : PermutationNDL X (app_merge_NoDupList X EmptyNDL).
  constructor. rewrite <- merge_right_neutral'. exact (permutation_id (ndlist X)). 
  Defined.

#[export] Instance permutation_id_am_l_PN (X:NoDupList) : PermutationNDL X (app_merge_NoDupList EmptyNDL X).
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

#[export] Instance permutation_id_am_l_PN_empty : PermutationNDL
  (app_merge_NoDupList EmptyNDL EmptyNDL)
  EmptyNDL.
  constructor. rewrite merge_left_neutral. exact (permutation_id []).
  Defined.

#[export] Instance permutation_id_am_l_PN_empty_r : PermutationNDL
  EmptyNDL
  (app_merge_NoDupList EmptyNDL EmptyNDL).
  constructor. rewrite merge_left_neutral. exact (permutation_id []).
  Defined.

#[export] Instance permutation_not_in_inter {o1 o2} : 
  PermutationNDL o1 ((o1 ∩ o2) ∪ (not_in_intersection_inl o1 o2)).
  Proof.
  constructor. apply (merge_not_inl_and_inl o1 o2).
  Qed.


Lemma permutation_commute {i1 i2} : 
  permutation i1 i2 -> permutation i2 i1.
  unfold permutation. intros.
  split; destruct (H x); assumption.
  Qed.

  
Definition permutationtr' {o1 o2 o3}:
  permutation (o3 ∪ (o2 ∪ o1)) (o3 ∪ o2 ∪ o1).
  Proof. simpl. 
  apply (permutation_commute tr_permutation). 
  Defined.

#[export] Instance permutation_not_in_inter_i {i1 i2} :
  PermutationNDL
    (i1 ∩ i2 ∪ not_in_intersection_inl i1 i2)
    i1.
  Proof.
  constructor. 
  apply (permutation_commute (merge_not_inl_and_inl i1 i2)).
  Qed.

#[export] Instance permutation_not_in_inter_inr {o1 o2} : 
  PermutationNDL o2 (o1 ∩ o2 ∪ not_in_intersection_inr o1 o2).
  Proof.
  constructor. apply (merge_not_inr_and_inr o1 o2).
  Qed.

#[export] Instance permutation_not_in_inter_i_inr {i1 i2} :
  PermutationNDL
    (i1 ∩ i2 ∪ not_in_intersection_inr i1 i2) i2.
  Proof.
  constructor. 
  apply (permutation_commute (merge_not_inr_and_inr i1 i2)).
  Qed.  


Definition permutation_left_neutral {X:NoDupList} :
  permutation X (EmptyNDL ∪ X).
  Proof.
  unfold permutation.
  intros. split;intros.
  - apply in_right_list. apply H.
  - apply in_app_iff in H. destruct H.
  + elim H.
  + apply H.
  Qed.

Definition permutation_left_neutral_neutral {X:NoDupList} :
  permutation X (EmptyNDL ∪ (EmptyNDL ∪ X)).
  Proof.
  unfold permutation.
  intros. split;intros.
  - apply in_right_list. apply in_right_list. apply H.
  - apply in_app_iff in H. destruct H.
  + elim H.
  + apply in_app_iff in H. destruct H.
  * elim H.
  * apply H.
  Qed.

#[export] Instance permaxi {M N} {ndl : NoDup [M;N]} : 
PermutationNDL {| ndlist := [M;  N]; nd := ndl |}
(EmptyNDL ∪ (OneelNDL M ∪ OneelNDL N)).
constructor.
simpl.
destruct (EqDecN N M ).
subst M.
apply NoDup_cons_iff in ndl.
destruct ndl.
elim H. constructor. reflexivity.
apply permutation_id.
Qed. 

#[export] Instance oneelndl {n i} {Hn: ~In n (ndlist i)} :
  OneelNDL n # i.
  constructor.
  intros.
  inversion H.
  subst n.
  contradiction.
  apply H1.
  Qed.
  
End permutationsNDL.



End FiniteSubset.


