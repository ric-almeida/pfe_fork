Definition bij_list_forward {i1 i2} : 
  {name : Name | In name i1} + {name : Name | In name i2}
  ->
  {name : Name | In name (i1 ++ i2)}.
  Proof.
  refine (fun name => match name with
                | inl (exist _ name' H1) => _
                | inr (exist _ name' H2) => _
                end).
    + exists (name'). 
      apply in_or_app. left. apply H1.
    + exists (name'). 
      apply in_or_app. right. apply H2.
    Defined.


Definition bij_list_backward {i1 i2 : NoDupList} :
  {name : Name | In name (i1 ++ i2)}
  ->
  {name : Name | In name i1} + {name : Name | In name i2}.
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros [name Hn].
  apply in_app_or in Hn.
  destruct Hn.
  Admitted.


Definition mynoduptl  {a:Name} {l1: list Name}
  (nd1 : NoDup (a :: l1)) : NoDup l1.
  apply nodup_tl in nd1. apply nd1. Defined.
Locate in_dec.

Fixpoint app_mergeNoDup 
  (eq_dec : forall x y : Name, {x = y} + {x <> y})
  (l1 : list Name) (l2 : list Name) 
  (nd1 : NoDup l1) (nd2 : NoDup l2) : list Name.
  Proof. 
    induction l1 as [| a l1'].
    - exact l2. (*l1 = [] and l2 nodup*)
    - destruct (In_dec eq_dec a l2) eqn:E.
    + (* In a l2 *)
      set (nd1' := mynoduptl nd1).
      exact (app_mergeNoDup eq_dec l1' l2 nd1' nd2).
    + (* not In a l2 *)
      set (nd1' := NoDup_remove_1 [] l1' a nd1).
      simpl in nd1'.
      exact (a :: (app_mergeNoDup eq_dec l1' l2 (mynoduptl nd1) nd2)).
  Defined.

(*Definition noduptl {a:Name} {l1': list Name} (nd1 : NoDup (a :: l1')) : NoDup l1'.
  Proof. apply nodup_tl in nd1. apply nd1. Defined.
Locate nodup_tl.
Fixpoint app_mergeNoDup' 
  (eq_dec : forall x y : Name, {x = y} + {x <> y})
  (l1 : list Name) (l2 : list Name) 
  (nd1 : NoDup l1) (nd2 : NoDup l2) : list Name :=
  match l1 with
    | nil => l2
    | a :: l1' =>  
      if in_dec eq_dec a l2 then 
      app_mergeNoDup eq_dec l1' l2 (nodup_tl a l1') nd2
        else
      a :: app_mergeNoDup eq_dec l1' l2
  end.

  Proof. 
    induction l1 as [| a l1'].
    - exact l2. (*l1 = [] and l2 nodup*)
    - destruct (in_dec eq_dec a l2) eqn:E.
    + (* a in l2 *)
      set (nd1' := NoDup_remove_1 [] l1' a nd1).
      simpl in nd1'.
      exact (app_mergeNoDup eq_dec l1' l2 nd1' nd2).
    + (* a not in l2 *)
      set (nd1' := NoDup_remove_1 [] l1' a nd1).
      simpl in nd1'.
      exact (a :: (app_mergeNoDup eq_dec l1' l2 nd1' nd2)).
  Defined. *)

  Print app_mergeNoDup.

Lemma mergeemptyright 
  (eq_dec : forall x y : Name, {x = y} + {x <> y})
  (l1 : list Name) 
  (nd1 : NoDup l1) (nd2 : NoDup []):
  app_mergeNoDup eq_dec l1 [] nd1 nd2 = l1.
  Proof.
  induction l1.
  simpl. reflexivity.
  simpl. rewrite IHl1. reflexivity. Qed.

Lemma nodupcons {a:Name} {l1: list Name} :
NoDup (a :: l1) -> NoDup l1.
Proof. apply NoDup_cons_iff. Qed.

Lemma notinlnotinapp {a:Name} {l1 l2: list Name} {nd1 nd2} {eq_dec}:
~ In a l1 -> ~ In a l2 -> ~ In a (app_mergeNoDup eq_dec l1 l2 nd1 nd2).
Proof. Admitted.

Lemma root_not_in_left {l1 l2} {a a0} {nd1 nd2 nd1'} {eq_dec}: 
~ In a (a0::l2) 
-> (app_mergeNoDup eq_dec (a :: l1) (a0 :: l2) nd1 nd2)
= (a :: app_mergeNoDup eq_dec (l1) (a0 :: l2) nd1' nd2).
intros.
Admitted.

Theorem app_mergeNoDupNoDup (eq_dec : forall x y : Name, {x = y} + {x <> y})
  (l1 : list Name) (l2 : list Name) 
  (nd1 : NoDup l1) (nd2 : NoDup l2) : 
  NoDup (app_mergeNoDup eq_dec l1 l2 nd1 nd2).
  Proof.
    induction l1 as [|a1 l1' IHl1] eqn:E1; induction l2 as [|a2 l2' IHl2] eqn:E2.
    - simpl. constructor.
    - simpl. constructor.
    + apply NoDup_cons_iff in nd2.
      destruct nd2 as [nd2' _].
      apply nd2'.
    + apply NoDup_cons_iff in nd2.
      destruct nd2 as [nd2' nd2''].
      apply nd2''.
    - rewrite mergeemptyright. apply nd1.
    - (*shit, no link btw a and a0*) 
    destruct (In_dec eq_dec a1 (a2::l2')) eqn:E. Focus 2.
    + erewrite root_not_in_left. simpl. Search (NoDup (_::_)).
      ++ constructor.
        +++
      apply IHl1. Admitted. 
    (* with (nd1' := nd1).
      ++ 
    + assert (a = a0). {admit. }
    injection H.
    rewrite <- H in nd2.
    change (NoDup (app_mergeNoDup eq_dec (a :: l1) (a :: l2) nd1 nd2)).
    rewrite <-  H. simpl.
     pose nd1 as nd1'.
      apply nodupcons in nd1'.
      set (l2' := (a0 :: l2)). Admitted. *)

Variable eqdecName : forall x y : Name, {x = y} + {x <> y}.

Definition app_NoDupList (i1: NoDupList) (i2 : NoDupList) : NoDupList.
Proof.
  exists (app_mergeNoDup eqdecName (ndlist i1) (ndlist i2) (nd i1) (nd i2)).
  apply app_mergeNoDupNoDup.
  Defined.

  Definition bij_list_backward' {i1 i2 : NoDupList} (name:Name) :
  In name (app_NoDupList i1 i2)
  ->
  In name (ndlist i1) + In name (ndlist i2).
  Proof.
  destruct i1 as [i1 ndi1].
  destruct i2 as [i2 ndi2]. simpl.
  intros Hn.
  apply in_app_or_m_nod_dup in Hn; assumption.
  Defined.