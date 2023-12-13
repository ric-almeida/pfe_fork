
Fixpoint split_first_a (a:Name) (l:list Name) (acc : list Name): list Name * list Name :=
match l with 
| [] => (acc,[])
| h::t => match (EqDecN a h) with
    | left eq => (acc, t)
    | right noteq => split_first_a a t (acc ++ [h])
    end
end.

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


Lemma a_not_in_l1_split (a:Name) (l:list Name) :
~ In a (fst (split_first_a a l [])).
Proof.
unfold not.
intros.
induction l as [| h t IH].
- simpl in *. apply H.
- simpl in *. destruct (EqDecN a h).
+ simpl in H. apply H.
+ apply IH. Admitted. 

Lemma not_in_cons {a h : Name} {l} :
a <> h -> ~ In a l -> ~ In a (h::l). Admitted.