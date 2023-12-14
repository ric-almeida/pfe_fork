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