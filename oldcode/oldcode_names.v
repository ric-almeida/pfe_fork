Fixpoint split_first_a (a:Name) (l:list Name) (acc : list Name): list Name * list Name :=
match l with 
| [] => (acc,[])
| h::t => match (EqDecN a h) with
    | left eq => (acc, t)
    | right noteq => split_first_a a t (acc ++ [h])
    end
end.

Lemma a_not_in_l1_split (a:Name) (l:list Name) :
~ In a (fst (split_first_a a l [])).
Proof.
    unfold not.
    intros.
    induction l as [| h t IH].
    - simpl in *. apply H.
    - simpl in *. destruct (EqDecN a h).
    + simpl in H. apply H.
    + apply IH. 
Admitted. 



Lemma not_in_cons {a h : Name} {l} :
a <> h -> ~ In a l -> ~ In a (h::l). 
Admitted.

Lemma in_split_not_in (a:Name) (l:list Name) : 
In a l -> exists l1 l2, ~ In a l1 /\ l = l1 ++ a :: l2.
Proof.
    intros.
    generalize dependent a.
    induction l as [| h t IH].
    - intros. inversion H.
    - intros.
    set (l12 := split_first_a a (h::t) []).
    destruct (EqDecN a h).
    + exists [].
        exists t.
        simpl. destruct e. auto.
    + exists (h::fst l12).
        exists (snd l12).
        split.
        * apply not_in_cons.
        ** apply n.
        ** unfold l12. apply (a_not_in_l1_split a).
        * destruct l12 as [l1 l2] eqn:E.
        apply IH in H.
        destruct H.
        destruct H.
        destruct H.
        exists (h :: x).
        exists x0.
        split.
        * unfold not. intros. apply H.  destruct H1.
        simpl.
        split.
        * unfold not. intros. destruct H1. 
        ** apply H. simpl.
        rewrite <- H.
        reflexivity.
Qed. 


Theorem reconstruct_split_first_a (a:Name) (l:list Name) : 
In a l -> 
l = fst (split_first_a a l []) ++ a :: snd (split_first_a a l []).
Proof.
intros.
induction l.
- exfalso. apply H.
- simpl. destruct (EqDecN a a0).
+ simpl. destruct e. reflexivity.
+ simpl. destruct H as [H | H]. {exfalso; apply n; symmetry; apply H. }
apply IHl in H. Admitted.


Theorem not_head_right_list {a2 b : Name} {l1 l2} :
b <> a2 -> In b (app_merge' l1 (a2 :: l2)) -> In b (app_merge' l1 l2).
Proof.
intros H H'.
destruct (in_dec EqDecN b (a2::l2)).
- apply in_right_list. destruct i. {exfalso. apply H; symmetry; apply H0. } apply H0.
- apply not_right.
+ unfold not. intros. apply n. apply in_cons. apply H0.
+ Admitted.

Theorem not_head_left_list {a h : Name} {t m} :
a <> h -> In a (app_merge' (h :: t) m) -> In a (app_merge' t m).
Proof.
intros.
destruct (in_dec EqDecN a (h::t)).
- apply in_left_list. destruct i. {exfalso. apply H. symmetry. apply H1. }
apply H1.
- Admitted.
 (* right. apply i. 
- left. induction l as [|h t IH].
+ exfalso. simpl in *. apply n. apply H.
+ destruct (EqDecN a h).
* destruct e. constructor. reflexivity.
* apply in_cons. apply IH.
apply (not_head_left_list n0 H).
Qed. *)


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


    Lemma no_dup_in_merge {a} {l1 l2}:
    ~ In a l1 -> ~ In a l2 ->
    NoDup l1 -> NoDup l2 -> 
    NoDup (a :: app_merge' l1 l2). 
    Proof.
    intros H1 H2 nd1 nd2.
    constructor.
    - apply not_in_merge; assumption.
    - 
    Admitted.


    (** SECTION APP_MERGE **)

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



    (* eq_comu *)
  Definition eq_comu {i1 i2: NoDupList} 
  (P : forall name : Name, In name i1 <-> In name i2) :
  forall name : Name, In name i2 <-> In name i1.
  Proof.
  intros. symmetry. apply P. Defined.

(* Definition eq_comu {i1 i2: NoDupList} 
  (P : forall name : Name, In name i1 <-> In name i2) :
  forall name : Name, In name i2 <-> In name i1.
  Proof.
  intros. symmetry. apply P. Defined. *)

Lemma eq_comu_plus {i1 i2: NoDupList} :
  (forall name : Name, In name i1 <-> In name i2) <->
  (forall name : Name, In name i2 <-> In name i1).
  Proof.
    split; intros H; exact (eq_comu H). Qed.

Lemma eq_comu_eq_commu {i1 i2: NoDupList} 
  (P : forall name : Name, In name i1 <-> In name i2) :
  eq_comu (eq_comu P) = P.
  Proof.
    unfold eq_comu. Admitted.

Lemma eq_comu_plus_plus {i1 i2: NoDupList} :
  forall name : Name, (In name i1 <-> In name i2) ->
  (In name i2 <-> In name i1).
  Proof.
    intros.
    split; intros H'.
    - rewrite <- H in H'. apply H'.
    - rewrite H in H'. apply H'. Qed.
(* 
Lemma eq_prop (H: P <-> Q) :
  {x | P x} = {y | Q y}
  <{}>


Lemma eq_commu_rewrite {x y : NoDupList}
  (bij : forall a, In a x <-> In a y ):
<{bij_id | eq_comu bij}> p = bij p. *)
Print eq_comu.
Check eq_comu.