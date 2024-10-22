Definition make_seq_ListTypenat (l:list nat) : list {n:nat| In n l}.
  Proof.
  (*eapply (
    map 
      (fun t => exist (fun name => In name l) t _)
      l
  ). Unshelve. simpl.

  refine (fold_left 
    (fun qt t => exist (fun name => In name l) t (or_introl erefl) :: qt) 
    l
    []).  *)
  simpl.
  induction l as [|tl ql IHl].
  - exact [].
  - Search (In _ _ -> In _ (_::_)).
  Check List.in_cons. Check exist.
    set (new_l := map 
      (fun n => match n with 
        | @exist _ _ tn hn => 
          @exist nat _ tn (@List.in_cons nat tl tn ql hn) end )
      IHl). simpl in new_l.
      simpl. eapply (@exist  nat _ tl _::new_l).
  Unshelve.
  simpl. left. reflexivity.
  Defined.

Eval compute in  (make_seq_ListTypenat (1::2::[])).  
Print make_seq_ListTypenat.


Definition add_t_to_subset_list {q} (t:Name) 
  (l:seq {n : Name | In n q}) : 
  seq {n : Name | In n (t::q)} :=
  map (fun n => match n with 
        | exist tn hn => 
            @exist _ _ tn (@List.in_cons _ t tn q hn) end )
      l.

Definition aux (n:Name) (l:list Name) (hin: In n l) := 
  @exist _ (fun n => In n l) n hin.

(* Definition make_seq_ListType (l:list Name) : list {n:Name| In n l}.
  Proof.
  simpl.
  induction l as [|tl ql IHl].
  - exact [].
  - apply (@exist _ _ tl (or_introl (erefl tl))::(add_t_to_subset_list tl IHl)).
  Defined.
Check list_rect.
  Print make_seq_ListType. *)

Definition make_seq_ListType (l:list Name) : list {n:Name| In n l}.
  Proof.
  simpl.
  induction l as [|tl ql IHl].
  - exact [].
  - apply (@exist _ _ tl (or_introl (erefl tl))::(add_t_to_subset_list tl IHl)).
  Defined.


Definition from_tlql_to_ql 
  {tl : Name}
  {ql : seq Name}
  {ndl : NoDup (tl :: ql)}
  (inner : ListType {| ndlist := tl :: ql; nd := ndl |})
  (Hinner : In (sval inner) ql) : 
  ListType {| ndlist := ql; nd := nodup_tl tl ql ndl |}.
  Proof.
  destruct inner as [iname Hiname]. exists iname. simpl in *.
  destruct Hiname. subst tl. apply Hinner. apply H. 
  Defined.

Lemma proj_eq_tlql 
  {tl : Name}
  {ql : seq Name}
  {ndl : NoDup (tl :: ql)}
  (inner : ListType {| ndlist := tl :: ql; nd := ndl |})
  (Hinner : In (sval inner) ql) : 
  sval (from_tlql_to_ql inner Hinner) = sval inner.
  Proof. 
  destruct inner. reflexivity.
  Qed.

(* Lemma add_t_to_subset_list_change_nothing {tl : Name} {ql : seq Name} {ndl : NoDup (tl :: ql)} (inner : ListType {| ndlist := tl :: ql; nd := ndl |})
  (Hinner : In (sval inner) ql ): 
  In (from_tlql_to_ql inner Hinner) (make_seq_ListType ql)
    ->
  In inner (add_t_to_subset_list (make_seq_ListType ql) tl). 
  Proof.
  destruct (from_tlql_to_ql inner Hinner) as [iname' Hiname'] eqn:E'.
  set (proj_eq_tlql inner Hinner). 
  simpl in *.
  setoid_rewrite E' in e.
  simpl in e.
  destruct inner as [iname Hiname] eqn:E.
  simpl in *.
  subst iname'. (*HERE start strategies*)
  destruct Hiname as [Hiname|Hiname].
  - exfalso. subst tl. clear E'. clear Hinner. clear E. clear inner.
  simpl in ndl. apply NoDup_cons_iff in ndl. 
  destruct ndl. apply H. apply Hiname'.
  - rewrite <- E'.
  clear E' Hiname' Hinner. 
  intros. 
  rewrite <- E.
  
  unfold add_t_to_subset_list.
  
  Admitted. *)


(* Lemma inter 
  (tl : Name)
  (ql : seq Name)
  (n : Name)
  (Hinner : In n ql) :
  In (exist ((In (A:=Name))^~ ql) n Hinner) (make_seq_ListType ql)
  ->
  In (exist ((In (A:=Name))^~ (tl :: ql)) n (or_intror Hinner))
    (add_t_to_subset_list (make_seq_ListType ql) tl).
  Proof. 
  intros. Check in_map.
  induction (make_seq_ListType ql); simpl in *.
  - apply H.
  - 


  Admitted. *)


(* Lemma wf_make_seq_ListType {l} (n:Name) (hin: In n l) : 
  In (exist _ n hin) (make_seq_ListType l).
  Proof.
  induction l as [|tl ql IHl].
  - elim hin.
  - destruct hin as [Hinner|Hinner].
  + left. subst tl. reflexivity. 
  + right. (*bc ndi*)  
  specialize (IHl Hinner).
  apply inter; assumption.
  Qed. *)


Lemma wf_make_seq_ListType {l} (inner:ListType l) : 
  In inner (make_seq_ListType (ndlist l)).
  Proof.
  destruct l as [l ndl].
  simpl in *.
  induction l as [|tl ql IHl].
  - exfalso. elim inner. intros. elim p.
  - simpl.  
  destruct (proj2_sig inner) as [Hinner|Hinner] eqn:Einner.
  + left. destruct inner. apply subset_eq_compat. apply Hinner.
  + right. (*bc ndi*)  
  specialize (IHl (nodup_tl tl ql ndl) (from_tlql_to_ql inner Hinner)).
  (* apply (add_t_to_subset_list_change_nothing inner Hinner IHl). *)
  Admitted.


  (*version with Prop, hard to say it's a finType because mathcomp knows subsets are finite if you give a pred (so a bool)*)
(* Definition get_edges_wo_idles {s i r o} (b:bigraph s i r o) := 
  {e : get_edge b | exists ip, get_link (bg:=b) ip = inr e}. *)

(* Lemma get_edges_wo_idles_enumP {s i r o} (b:bigraph s i r o): 
  Finite.axiom 
    (map (fun ip => match get_link (bg:=b) (ip) with 
      | inl o => 
      | inr e => e
      end) i). 

Proof. by case. Qed.
HB.instance Definition _ := isFinite.Build bool bool_enumP.
Lemma card_bool : #|{: bool}| = 2. Proof. by rewrite cardT enumT unlock. Qed. *)


(* Definition get_edges_wo_idles_ft {s i r o} (b:bigraph s i r o) : finType.
 Proof. 
  exists (get_edges_wo_idles b).
  Locate Finite.axioms_.
  Admitted.     *)

(* Definition get_edges_wo_idles {s i r o} (b:bigraph s i r o) := 
  {e : get_edge b | not_is_idle e}. *)

(* Check get_edges_wo_idles. it's a Type, but I can use it as a finType apparently :) *)



Fixpoint aux_is_lean {i p o e} {l: ListType i + p -> ListType o + e} e' :=
  match e' with 
  | [] => True 
  | e''::q => exists ip:ListType i + p, l ip = inr e'' /\ @aux_is_lean i p o e l q
  end.

Definition is_lean' {s i r o} (b:bigraph s i r o) :=
  @aux_is_lean 
    i 
    (Port (get_control (bg:=b))) 
    o 
    (get_edge b) 
    (get_link (bg:=b)) 
    (enum (get_edge b)).


Theorem lean_is_lean' {s i r o} (b:bigraph s i r o) :
  is_lean' (lean b).
  Proof.
  destruct b as [n e c p l ap].
  simpl.
  unfold is_lean,aux_is_lean.
  simpl.
  generalize e l.
  induction (enum e) eqn:E.
  (* - intros. E. auto.
  - rewrite E. simpl.
  rewrite E in IHl0. 
  simpl in IHl0.
  apply IHl0.
  esplit.
  Unshelve.
  2:{ }
   simpl. auto.
  intros [o'|e'].
  - admit. pcq en fait j'ai pas besoin que link soit surjective, juste surjective pour les edges *)
  - Abort.