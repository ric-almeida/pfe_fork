
Require Import Coq.Lists.List.


Set Printing All.


Import ListNotations.



Module Names.
Variable Name : Type.
Variable EqDecN : forall x y : Name, {x = y} + {x <> y}.

Record NoDupList : Type :=
  {
    ndlist :> list Name ;
    nd : NoDup ndlist ;
  }.



Fixpoint app_merge' (l1 : list Name) (l2 : list Name) {struct l1} : list Name :=  match l1 with
    | nil => l2
    | a :: l1' =>  
      if in_dec EqDecN a l2 then 
      app_merge' l1' l2
        else
      a :: app_merge' l1' l2
  end.

Theorem app_merge'_com {l1 l2 : list Name} :
app_merge' l1 l2 = app_merge' l2 l1.
Proof.
induction l1 as [|a1 l1' IHl1].
- simpl. induction l2 as [|a2 l2' IHl2].
+ simpl. reflexivity.
+ simpl. rewrite <- IHl2. reflexivity.
- induction l2 as [|a2 l2' IHl2].
+ simpl. rewrite IHl1. simpl. reflexivity.
+ simpl. destruct (EqDecN a2 a1); destruct (EqDecN a1 a2).
++ rewrite IHl1. rewrite <- IHl2.
Abort.

Lemma app_merge'_empty_right (l1 : list Name) :
  app_merge' l1 [] = l1.
  Proof.
    induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity. 
  Qed.

Theorem in_eq_m {a:Name} {l}: 
In a (app_merge' [a] l).
Proof.
    intros. simpl. destruct (in_dec EqDecN a l).
    apply i.
    constructor. reflexivity. 
Qed.

Lemma in_app_or : forall (l m:list Name) (a:Name), 
In a (app_merge' l m) -> In a l \/ In a m.
Proof.
intros.
induction l.
- simpl in H. right. apply H.
- destruct (EqDecN a a0).
+ rewrite e. left. constructor. reflexivity.
+ apply in_cons. left.  destruct IHl.
+ Admitted. 
  

Theorem in_eq_list_m {a:Name} {l1 l2}:
In a l1 -> In a (app_merge' l1 l2).
Proof.
intros.
induction l1.
- exfalso. apply in_nil in H. apply H.
- destruct (EqDecN a1 a).
++ rewrite e. simpl. apply IHl1. 
apply in_inv in H. destruct H.
* 



Theorem in_cons : forall (a b:Name) (l:list Name), In b l -> In b (app_merge' [a] l).
Proof.
intros. simpl. destruct (in_dec EqDecN a l).
apply H. 
apply in_split in H.
destruct H as [l1 [l2 H]].
rewrite H.
apply (in_elt (a::l1)). Qed.

Theorem not_in_cons (x a : Name) (l : list Name):
~ In x (app_merge' [a] l) <-> x<>a /\ ~ In x l.
Proof. split.
- split.
+ unfold not. intros. apply H. rewrite H0. simpl.
destruct (in_dec EqDecN a l).
apply i.
constructor. reflexivity.
+ unfold not. intros. apply H. 
apply in_cons. apply H0.
- intros. unfold not. intros. destruct H.
simpl in H0. destruct (in_dec EqDecN a l).
apply H1. apply H0.
apply H1. apply in_inv in H0. destruct H0.
+ exfalso. apply H. symmetry. apply H0.
+ apply H0.
Qed. 
  
  
Lemma in_app_or : forall (l m:list Name) (a:Name), 
In a (app_merge' l m) -> In a l \/ In a m.
Proof.
intros.
induction l.
- simpl in H. right. apply H.
- destruct IHl.
+ Admitted. 
  
Lemma in_or_app : forall (l m:list Name) (a:Name), In a l \/ In a m -> In a (l ++ m).
Admitted. 
Lemma in_app_iff : forall l l' (a:Name), In a (l++l') <-> In a l \/ In a l'.
Admitted. 
Theorem in_split : forall x (l:list Name), In x l -> exists l1 l2, l = l1++x::l2.
Admitted. 
Lemma in_elt' : forall (x:Name) l1 l2, In x (l1 ++ x :: l2).
Admitted.  *)

Lemma in_elt' (l1: list Name) : forall (x:Name) l2, In x (l1 ++ x :: l2).
Proof. intros.
apply in_or_app.
right; left; reflexivity.
Qed.

  
Lemma dup_head_app_merge' {l1' l2' : list Name} {a : Name}:
app_merge' (a::l1') (a::l2') = app_merge' l1' (a::l2').
Proof.
    simpl.
    destruct (EqDecN a a).
    - reflexivity.
    - exfalso. apply n. reflexivity.
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

(* Lemma split_in {a a' : Name} {l1 l2}: 
In a' (a :: app_merge' l1 l2) <-> a = a' \/ In a l1 \/ In a l2.
Proof.
    split. Focus 2.
    - intros. destruct H as [H | [H' | H'']].
    * rewrite H. constructor. reflexivity. Focus 2.
    * apply H1'. apply H'.
    * apply H2. apply H''.
    - intros.
    apply in_inv in H. 
    destruct H as [H1 |  H1'].
    + left. apply H1.
    + simpl in H1'. Admitted. *)

Lemma in_merge {a} {l1 l2}:
In a l1 \/ In a l2 ->
In a (app_merge' l1 l2).
Proof.
intros [H | H].
- induction l1 as [|a1 l1' IHl1].
+ exfalso. apply in_nil in H. apply H.
+ destruct (EqDecN a1 a).
++ rewrite e. simpl. apply IHl1. 
apply in_inv in H. destruct H.
* 


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
**   
apply in_cons.
apply H.

Lemma no_dup_in_merge {a} {l1 l2}:
~ In a l1 -> ~ In a l2 ->
NoDup l1 -> NoDup l2 -> 
NoDup (a :: app_merge' l1 l2). 
Proof.
intros H1 H2 nd1 nd2.
constructor.
- apply not_in_merge; assumption.
induction l1 as [|a1 l1' IHl1].
- simpl.
constructor.
+ apply H2.
+ apply nd2. 
- simpl. destruct (in_dec EqDecN a1 l2).
+ apply IHl1.
++ unfold not in *. intros. apply H1. 
apply in_cons.
apply H.
++  apply NoDup_cons_iff in nd1.
destruct nd1 as [nd1' nd1''].
apply nd1''.
+ rewrite rearrangenodup.
rewrite rm_headNoDUP.  
++ apply IHl1.
*  apply not_in_cons in H1.
destruct H1 as [H1  H1'].
apply H1'.
* apply NoDup_cons_iff in nd1.
destruct nd1 as [nd1' nd1''].
apply nd1''.
++ apply not_in_cons in H1.
destruct H1 as [H1  H1'].
unfold not. intros. Admitted.
(* apply split_in in H.
destruct H as [H | [H' | H'']].
* apply H1. apply H.
* apply H1'. apply H'.
* apply H2. apply H''.
Qed. *)


Lemma NoDup_app_merge (l1 : list Name) (l2 : list Name) :
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
    apply not_in_merge; assumption.
    Qed.
    


(* Lemma NoDup_app_merge (l1 : list Name) (l2 : list Name) :
    NoDup l1 -> NoDup l2 -> NoDup (app_merge' l1 l2).
    Proof.
    intros nd1 nd2.
    induction l1 as [|a1 l1' IHl1]; induction l2 as [|a2 l2' IHl2] .
    - simpl. constructor.
    - simpl. constructor.
    + apply NoDup_cons_iff in nd2.
        destruct nd2 as [nd2' _].
        apply nd2'.
    + apply NoDup_cons_iff in nd2.
        destruct nd2 as [nd2' nd2''].
        apply nd2''.
    - simpl. rewrite app_merge'_empty_right. constructor.
    + apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' _].
        apply nd1'.
    + apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.
    - (*no link btw a1 and a2*) 
    destruct (In_dec EqDecN a1 (a2::l2')).
    +   apply in_inv in i. destruct i. (*In a1 l2*)
    ++  rewrite H. rewrite dup_head_app_merge'.
        rewrite <- H.
        apply IHl1. 
        apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.
    ++ rewrite a1_inl_app_merge'.
    +++ apply IHl1. 
        apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.  
    +++ apply H.
    + rewrite a1_not_inl_app_merge'. (* Not In a1 l2*)
    ++ simpl.  apply IHl1.
        apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.  
    ++ unfold not in n. destruct n.
    apply in_inv in n.

Lemma NoDup_app_merge (l1 : list Name) (l2 : list Name) :
    NoDup l1 -> NoDup l2 -> NoDup (app_merge l1 l2).
    Proof.
    intros nd1 nd2.
    induction l1 as [|a1 l1' IHl1]; induction l2 as [|a2 l2' IHl2] .
    - simpl. constructor.
    - simpl. constructor.
    + apply NoDup_cons_iff in nd2.
        destruct nd2 as [nd2' _].
        apply nd2'.
    + apply NoDup_cons_iff in nd2.
        destruct nd2 as [nd2' nd2''].
        apply nd2''.
    - rewrite app_merge_empty_right. constructor.
    + apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' _].
        apply nd1'.
    + apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.
    - (*no link btw a1 and a2*) 
    destruct (In_dec EqDecN a1 (a2::l2')).
    +   apply in_inv in i. destruct i.
    ++  rewrite H. rewrite dup_head_app_merge.
        rewrite <- H.
        apply IHl1. 
        apply NoDup_cons_iff in nd1.
        destruct nd1 as [nd1' nd1''].
        apply nd1''.
    ++  rewrite H. rewrite dup_head_app_merge.
    rewrite <- H.
    apply IHl1. 
    apply NoDup_cons_iff in nd1.
    destruct nd1 as [nd1' nd1''].
    apply nd1''.
    
    apply NoDup_cons_iff in nd2. constructor. simpl. *)
(* Lemma NoDupHeadBody {a a':Name} {l2_1' l2_2} : 
    NoDup ((a' :: l2_1') ++ a :: l2_2) -> a <> a'.
    Admitted. *)

(* Lemma app_merge'_body {l1' l2_2 : list Name} {a : Name} (l2_1 : list Name):
    NoDup (l2_1 ++ a :: l2_2) ->
    app_merge' (a :: l1') (l2_1 ++ a :: l2_2) = app_merge' l1' (l2_1 ++ a :: l2_2).
    Proof.
        intros nd2. 
        induction l2_1 as [|a' l2_1' IHl2]. (*if i do this I have to prove nodup -> a0 <> a*)
        - apply dup_head_app_merge'.
        - apply NoDupHeadBody in nd2.
        simpl.
        destruct (EqDecN a' a).
        + reflexivity.
        + destruct (in_dec EqDecN a (l2_1' ++ a :: l2_2)).
        ++ reflexivity.
        ++ exfalso. apply n0. 
        Search (in_app_or).
        apply in_or_app.
        right. constructor. reflexivity.
    Qed. *)


(* Lemma a1_inl_app_merge' {l1' l2' : list Name} {a1 a2 : Name}:
    In a1 l2' -> 
    app_merge' (a1::l1') (a2::l2') = app_merge' l1' (a2::l2').
    Proof.
    intros. Search ( _ = _ ++ _ :: _ ).
    apply in_split in H.
    destruct H as [l2_1 [l2_2 H']].
    rewrite H'.
    apply (app_merge'_body (a2::l2_1)).
    Admitted.  *)
    
(* Lemma a1_not_inl_app_merge' {l1' l2' : list Name} {a1 a2 : Name}:
    ~ In a1 l2' -> a1 <> a2 ->
    app_merge' (a1::l1') (a2::l2') = a1 :: app_merge' l1' (a2::l2').
    Proof.
    intros. Admitted. *)
    (* apply in_split in H.
    destruct H as [l2_1 [l2_2 H']].
    rewrite H'.
    apply (app_merge'_body (a2::l2_1)).
    Qed.  *)


    Fixpoint app_merge (l1 : list Name) (l2 : list Name) {struct l1} : list Name.
  Proof. 
    induction l1 as [| a l1'].
    - exact l2. (*l1 = [] and l2 nodup*)
    - destruct (In_dec EqDecN a l2) eqn:E.
    + (* In a l2 *)
      exact (app_merge l1' l2).
    + (* not In a l2 *)
      exact (a :: (app_merge l1' l2)).
  Defined.

  Lemma app_merge_empty_right (l1 : list Name) :
  app_merge l1 [] = l1.
  Proof.
    induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity. 
  Qed.

  Lemma dup_head_app_merge {l1' l2' : list Name} {a : Name}:
app_merge (a::l1') (a::l2') = app_merge l1' (a::l2').
    Proof.
        simpl.
        destruct (EqDecN a a).
        - reflexivity.
        - exfalso. apply n. reflexivity.
    Qed.  