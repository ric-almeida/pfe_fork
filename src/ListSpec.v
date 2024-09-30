
Require Import JMeq.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import PeanoNat.
Require Import Lia.
Require Import Compare_dec.
Require Import Basics.
Require Import List.

From mathcomp Require Import all_ssreflect.


Module Type ListSpec.

Parameter onto : forall [A : Type] (lA : list A), list { a : A | In a lA }.

Axiom onto_nil : forall {A : Type}, onto (@nil A) = nil.

Axiom onto_cons : forall [A : Type] (h : A) (t : list A),
  onto (h::t) = (exist (fun a => In a (h::t)) h (in_eq h t)) :: (map (fun (a_in_t : { a : A | In a t }) => let (a, Ha) := a_in_t in exist _ a (List.in_cons _ _ _ Ha)) (onto t)).

Axiom onto_Onto : forall [A : Type] (lA : list A) (a : { a : A | In a lA }), In a (onto lA).

End ListSpec.




Module MinIter : ListSpec.

Open Scope list_scope.

CoInductive stream (A : Type) :=
  mkstream { hd : A; tl : option (stream A) }.

Arguments hd [A]%type_scope _.
Arguments tl [A]%type_scope _.

Definition tl_rel {A : Type} := fun (s' s : option (stream A)) => match s with | None => False | Some s => @tl A s = s' end.

Record rlist (A : Type) :=
  mklist { str : option (stream A); acc : Acc tl_rel str }.

Definition list := rlist.

Arguments str [A]%type_scope _.
Arguments acc [A]%type_scope _.

Lemma eq_str : forall [A : Type] (l1 l2 : list A), str l1 = str l2 -> l1 = l2.
Proof.
intros A l1 l2.
destruct l1; destruct l2.
simpl.
intro H.
destruct H.
rewrite (proof_irrelevance _ acc0 acc1).
reflexivity.
Qed.

Lemma acc_nil : forall {A : Type}, Acc tl_rel (@None (stream A)).
Proof.
intro A.
apply Acc_intro.
contradiction.
Qed.

Definition nil {A : Type} : list A := mklist A None acc_nil.

Notation "[ ]" := (@nil _) (format "[ ]") : list_scope.

Lemma acc_cons : forall {A : Type} (t : A) {q : option (stream A)}, Acc tl_rel q -> Acc tl_rel (Some (mkstream A t q)).
Proof.
intros A t q Hq.
apply Acc_intro.
intros qq Hqq.
simpl in Hqq.
rewrite <- Hqq.
apply Hq.
Qed.

Definition cons [A : Type] : A -> list A -> list A := fun t q => mklist A (Some (mkstream A t (str q))) (acc_cons t (acc q)).

Notation "t ::: q" := (mklist _ (Some (mkstream _ t (str q))) (acc_cons t (acc q))) (at level 60, right associativity) : list_scope.

Notation "x :: y" := (@cons _ x y) (at level 60, right associativity) : list_scope.
Notation "[ x ]" := (@cons _ x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

Lemma nil_cons : forall [A : Type] [x : A] [l : list A],
       @nil A <> @cons A x l.
Proof.
intros A x l H.
injection H; clear H; intro H.
discriminate.
Qed.

Lemma injective_cons : forall [A : Type] [t1 t2 : A] [q1 q2 : list A],
                         cons t1 q1 = cons t2 q2 -> t1 = t2 /\ q1 = q2.
Proof.
intros A t1 t2 q1 q2 H.
injection H; clear H; intros Hq Ht.
split.
+ exact Ht.
+ destruct q1; destruct q2.
  simpl in * |- *.
  destruct Hq.
  rewrite (proof_irrelevance _ acc0 acc1).
  reflexivity.
Qed.

Lemma acc_tl : forall {A : Type} {t : A} {q : option (stream A)}, Acc tl_rel (Some (mkstream A t q)) -> Acc tl_rel q.
Proof.
intros A t q Htq.
inversion Htq.
apply H.
reflexivity.
Qed.

Definition destruct_list [A : Type] (l : list A) :
       {x : A & {tl : list A | l = @cons A x tl}} + {l = @nil A}.
Proof.
destruct l as (str, acc).
destruct str as [ (hd, tl) | ].
+ left.
  exists hd.
  exists (mklist _ tl (acc_tl acc)).
  unfold cons; simpl.
  rewrite (proof_irrelevance _ (@acc_cons A hd tl (@acc_tl A hd tl acc)) acc).
  reflexivity.
+ right.
  unfold nil.
  rewrite (proof_irrelevance _ acc_nil acc).
  reflexivity.
Defined.

Lemma tl_rel_tl : forall [A : Type] (s : stream A) (q : option (stream A)), tl_rel (tl s) (Some s).
Proof.
intros A s q.
reflexivity.
Qed.

Lemma stream_eta_conv : forall [A : Type] (s : stream A), s = mkstream A (hd s) (tl s).
Proof.
destruct s; reflexivity.
Qed.

Lemma list_eta_conv : forall [A : Type] (l : list A), l = mklist A (str l) (acc l).
Proof.
destruct l; reflexivity.
Qed.

Lemma cons_list_eta_conv : forall [A : Type] (s : stream A) (wf : Acc tl_rel (Some s)) (wf_tl : Acc tl_rel (tl s)),
                        mklist A (Some s) wf = cons (hd s) (mklist A (tl s) wf_tl).
Proof.
intros A s wf wf_tl.
destruct s.
unfold cons.
simpl.
rewrite (proof_irrelevance _ (@acc_cons A hd0 tl0 wf_tl) wf).
reflexivity.
Qed.




Fixpoint filter_rec [A : Type] (p : A -> bool) (os : option (stream A)) (wf : Acc tl_rel os) : list A :=
  match os as o return os = o -> list A with
  | None   => (fun _ => nil)
  | Some s => (fun Heq => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os')
    match wf with Acc_intro acc => acc end _ Heq in
    let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
    if p (hd s) then hd s ::: (filter_rec p (tl s) wf_tl)
    else           filter_rec p (tl s) wf_tl)
  end erefl.

Definition filter [A : Type] (p : A -> bool) (l : list A) := filter_rec p (str l) (acc l).

Lemma filter_nil : forall [A : Type] (p : A -> bool), filter p [] = [].
Proof.
intros A p.
unfold filter, nil.
destruct acc_nil.
simpl.
unfold nil.
rewrite (proof_irrelevance _ (Acc_intro None a) acc_nil).
reflexivity.
Qed.

Lemma filter_cons : forall [A : Type] (p : A -> bool) (h : A) (t : list A), filter p (h::t) = if p h then h::filter p t else filter p t.
Proof.
intros A p t q.
unfold filter.
unfold cons at 1.
simpl.
destruct acc_cons.
simpl.
destruct (p t).
+ unfold cons at 1.
  destruct q.
  simpl.
  rewrite (proof_irrelevance _ _ acc0).
  reflexivity.
+ destruct q.
  simpl.
  rewrite (proof_irrelevance _ acc0).
  reflexivity.
Qed.

Lemma filter_cons_ok : forall [A : Type] (p : A -> bool) (h : A) (t : list A), p h = true -> filter p (h::t) = h::filter p t.
Proof.
intros A p t q Ht.
unfold cons at 1.
destruct acc_cons.
unfold filter.
simpl.
destruct (p t).
+ unfold cons.
  rewrite (proof_irrelevance _ _ (acc q)).
  reflexivity.
+ discriminate.
Qed.

Lemma filter_cons_ko : forall [A : Type] (p : A -> bool) (h : A) (t : list A), p h = false -> filter p (h::t) = filter p t.
Proof.
intros A p t q Ht.
unfold cons at 1.
destruct acc_cons.
unfold filter.
simpl.
destruct (p t).
+ discriminate.
+ apply f_equal.
  apply proof_irrelevance.
Qed.

Fixpoint map_rec [A B : Type] (f : A -> B) (os : option (stream A)) (wf : Acc tl_rel os) : list B :=
  match os as o return os = o -> list B with
  | None   => (fun _ => nil)
  | Some s => (fun Heq => f (hd s) :::
                          match wf with
                          | Acc_intro _ acc => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os') acc _ Heq in
                                               let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
                                                 map_rec f (tl s) wf_tl
                          end)
  end eq_refl.

Definition map [A B : Type] (f : A -> B) (l : list A) := map_rec f (str l) (acc l).

Lemma map_nil : forall [A B : Type] (f : A -> B), map f [] = [].
Proof.
intros A B f.
unfold nil.
destruct acc_nil.
reflexivity.
Qed.

Lemma map_cons : forall [A B : Type] (f : A -> B) (h : A) (t : list A), map f (h :: t) = f h :: map f t.
Proof.
intros A B f h t.
unfold map, cons at 1.
simpl.
destruct acc_cons.
simpl.
unfold cons.
rewrite (proof_irrelevance _ _ (acc t)).
reflexivity.
Qed.

Fixpoint flat_map_rec [A B : Type] (f : A -> list B) (os : option (stream A)) (wf : Acc tl_rel os) : list B :=
  match os as o return os = o -> list B with
  | None   => (fun _ => nil)
  | Some s => (fun Heq => f (hd s) ++
                          match wf with
                          | Acc_intro _ acc => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os') acc _ Heq in
                                               let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
                                                 flat_map_rec f (tl s) wf_tl
                          end)
  end eq_refl.

Definition flat_map [A B : Type] (f : A -> list B) (l : list A) := flat_map_rec f (str l) (acc l).

Lemma flat_map_nil : forall [A B : Type] (f : A -> list B), flat_map f [] = [].
Proof.
intros A B f.
unfold nil.
destruct acc_nil.
reflexivity.
Qed.

Lemma flat_map_cons : forall [A B : Type] (f : A -> list B) (h : A) (t : list A), flat_map f (h :: t) = f h ++ flat_map f t.
Proof.
intros A B f h t.
unfold flat_map, cons at 1.
simpl.
destruct acc_cons.
simpl.
apply f_equal.
apply f_equal.
rewrite (proof_irrelevance _ _ (acc t)).
reflexivity.
Qed.

Definition eta_nil : forall [A : Type] [P : list A -> Type] [os : option (stream A)] [wf : Acc tl_rel os] (Heq : os = None)
  (H : P []), P {| str := os; acc := wf |}.
Proof.
intros A P os wf Heq.
subst.
unfold nil.
rewrite (proof_irrelevance _ acc_nil wf).
exact (fun x => x).
Defined.

Definition eta_cons : forall [A : Type] [P : list A -> Type] [os : option (stream A)] [s : stream A] [wf : Acc tl_rel os] [wf_tl : Acc tl_rel (tl s)] (Heq : os = Some s)
  (H : P (@hd A s :: {| str := @tl A s; acc := wf_tl |})), P {| str := os; acc := wf |}.
Proof.
intros A P os s wf wf_tl Heq H.
subst.
erewrite <- cons_list_eta_conv in H.
instantiate (1 := wf) in H.
exact H.
Defined.

Lemma eta_cons_id : forall [A B : Type] [s : stream A] [wf : Acc tl_rel (Some s)] [wf_tl : Acc tl_rel (tl s)]
  (H : (fun _ => B) (@hd A s :: {| str := @tl A s; acc := wf_tl |})), @eta_cons A (fun _ => B) (Some s) s wf wf_tl eq_refl H = H. (*P {| str := Some s; acc := wf |}.*)
Proof.
intros A B s wf wf_tl b.
simpl in b.
unfold eta_cons.
unfold eq_rect_r.
simpl.
destruct s.
simpl.
unfold cons.
simpl.
destruct eq_sym.
rewrite <- eq_rect_eq.
reflexivity.
Qed.

Fixpoint list_rect_rec [A : Type] (P : list A -> Type) (Pnil : P []) (Pcons : forall (a : A) [l : list A], P l -> P (a :: l))
                                  (os : option (stream A)) (wf : Acc tl_rel os) : P (mklist A os wf) :=
  match os as o return os = o -> P (mklist A os wf) with
  | None   => (fun Heq => eta_nil Heq Pnil)
  | Some s => (fun Heq => match wf with
                          | Acc_intro _ acc => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os') acc _ Heq in
                                               let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
                                                 eta_cons Heq (Pcons (hd s) (list_rect_rec P Pnil Pcons (tl s) wf_tl))
                          end)
  end eq_refl.

Definition list_rect [A : Type] (P : list A -> Type) (Pnil : P []) (Pcons : forall (a : A) (l : list A), P l -> P (a :: l)) (l : list A) :=
              eq_rect   (mklist A (str l) (acc l))
                        _
                        (list_rect_rec P Pnil Pcons (str l) (acc l))
                        l
                        (eq_sym (list_eta_conv l)).

Lemma list_rect_nil_JMeq : forall [A B : Type] (P : list A -> Type) (Pnil : P []) (Pnil' : B) (Pcons : forall (a : A) (l : list A), P l -> P (a :: l)),
                              JMeq Pnil Pnil' -> JMeq (list_rect P Pnil Pcons []) Pnil'.
Proof.
intros A B P Pnil Pnil' Pcons Heq.
unfold nil.
unfold list_rect.
simpl.
rewrite <- eq_rect_eq.
destruct acc_nil.
simpl.
unfold eta_nil.
unfold eq_rect_r.
rewrite <- eq_rect_eq.
rewrite (proof_irrelevance _ _ acc_nil).
rewrite <- eq_rect_eq.
exact Heq.
Qed.

Lemma list_rect_nil : forall [A : Type] (P : list A -> Type) (Pnil : P []) (Pcons : forall (a : A) (l : list A), P l -> P (a :: l)),
                        list_rect P Pnil Pcons [] = Pnil.
Proof.
intros.
apply JMeq_eq.
apply list_rect_nil_JMeq.
reflexivity.
Qed.

Lemma list_rect_cons_JMeq : forall [A : Type] [B : A -> list A -> Type] (P : list A -> Type) (Pnil : P []) (Pcons : forall (a : A) (l : list A), P l -> P (a :: l)) (Pcons' : forall (a : A) (l : list A), P l -> B a l) (h : A) (t : list A),
                              (forall h t (p : P t), JMeq (Pcons h t p) (Pcons' h t p)) -> JMeq (list_rect P Pnil Pcons (h::t)) (Pcons' h t (list_rect P Pnil Pcons t)).
Proof.
intros A B P Pnil Pcons Pcons' t q Heq.
unfold cons.
destruct acc_cons.
unfold list_rect.
simpl.
rewrite <- eq_rect_eq.
unfold eta_cons.
unfold eq_rect_r.
simpl.
unfold cons.
simpl.
destruct eq_sym.
rewrite <- eq_rect_eq.
destruct eq_sym.
rewrite <- eq_rect_eq.
rewrite (proof_irrelevance _ _ (acc q)).
apply (Heq t {| str := str q; acc := acc q |} (list_rect_rec P Pnil Pcons (str q) (acc q))).
Qed.

Lemma list_rect_cons : forall [A : Type] (P : list A -> Type) (Pnil : P []) (Pcons : forall (a : A) (l : list A), P l -> P (a :: l)) (h : A) (t : list A), list_rect P Pnil Pcons (h::t) = Pcons h t (list_rect P Pnil Pcons t).
Proof.
intros A P Pnil Pcons t q.
apply JMeq_eq.
eapply (list_rect_cons_JMeq P Pnil Pcons Pcons t q).
intros t' q' pt'.
reflexivity.
Qed.

Definition list_ind [A : Type] (P : list A -> Prop) := list_rect P.

Definition fold_right [A B : Type] (f : B -> A -> A) (e : A) (l : list B) : A := list_rect (fun _ => A) e (fun t _ Hq => f t Hq) l.

Lemma fold_right_nil : forall [A B : Type] (f : B -> A -> A) (e : A), fold_right f e [] = e.
Proof.
intros A B f e.
unfold nil.
destruct acc_nil.
unfold fold_right, list_rect.
simpl.
rewrite <- eq_rect_eq.
unfold eta_nil.
unfold eq_rect_r.
rewrite <- eq_rect_eq.
rewrite (proof_irrelevance _ _ acc_nil).
rewrite <- eq_rect_eq.
reflexivity.
Qed.

Lemma fold_right_cons : forall [A B : Type] (f : B -> A -> A) (e : A) (h : B) (t : list B), fold_right f e (h :: t) = f h (fold_right f e t).
Proof.
intros A B f e h t.
unfold fold_right, list_rect, cons at 1.
simpl.
rewrite <- eq_rect_eq.
rewrite <- list_eta_conv.
rewrite <- eq_rect_eq.
case_eq (acc_cons h (acc t)).
intros.
simpl.
rewrite (proof_irrelevance _ _ (acc t)).
apply eta_cons_id.
Qed.

(*
Lemma map_filter : forall [A B : Type] (p : B -> bool) (f : A -> B) (l : list A), filter p (map f l) = map f (filter (fun a => p (f a)) l).
Proof.
intros A B p f l.
pattern l.
apply list_ind.
+ rewrite map_nil.
  rewrite filter_nil.
  rewrite filter_nil.
  rewrite map_nil.
  reflexivity.
+ intros t q IHq.
  rewrite map_cons.
  case_eq (p (f t)); intro Hpft.
  - rewrite filter_cons_ok; [ | exact Hpft ].
    rewrite filter_cons_ok; [ | exact Hpft ].
    rewrite map_cons.
    f_equal.
    apply IHq.
  - rewrite filter_cons_ko; [ | exact Hpft ].
    rewrite filter_cons_ko; [ | exact Hpft ].
    apply IHq.
Qed.
*)

Lemma app_assoc : forall [A : Type] (l1 l2 l3 : list A), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
intros A l1 l2 l3.
pattern l1.
apply list_ind.
+ rewrite app_nil.
  rewrite app_nil.
  reflexivity.
+ intros t q IHq.
  rewrite app_cons.
  rewrite app_cons.
  rewrite app_cons.
  rewrite IHq.
  reflexivity.
Qed.


Fixpoint In_rec [A : Type] (a : A) (os : option (stream A)) (wf : Acc tl_rel os) : Prop :=
  match os as o return os = o -> Prop with
  | None   => (fun Heq => False)
  | Some s => (fun Heq => hd s = a \/
                          match wf with
                          | Acc_intro _ acc => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os') acc _ Heq in
                                               let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
                                                 In_rec a (tl s) wf_tl
                          end)
  end eq_refl.

Definition In [A : Type] (a : A) (l : list A) := In_rec a (str l) (acc l).

Lemma in_eq : forall [A : Type] (a : A) (l : list A), @In A a (a :: l).
Proof.
intros A a l.
unfold In.
destruct acc.
simpl.
left; reflexivity.
Qed.

Lemma in_cons : forall [A : Type] (a b : A) (l : list A), @In A b l -> @In A b (a :: l).
Proof.
unfold In.
intros A a b l H.
destruct (acc (a::l)) as (f).
simpl.
right.
rewrite (proof_irrelevance _ (f (@str A l) (@tl_rel_tl A {| hd := a; tl := @str A l |} (@str A l))) (acc l)).
apply H.
Qed.

Lemma in_nil : forall [A : Type] (a : A), ~ In a [].
Proof.
intros A a H.
unfold In in H.
destruct acc.
exact H.
Qed.

Lemma in_inv : forall [A : Type] (a b : A) (l : list A), In b (a :: l) -> a = b \/ In b l.
Proof.
intros A a b l.
intro H.
unfold In, cons in H.
destruct acc_cons.
simpl in H.
destruct H as [ H | H ].
+ left.
  exact H.
+ right.
  rewrite (proof_irrelevance _ _ (acc l)) in H.
  exact H.
Qed.

Lemma filter_In : forall [A : Type] (p : A -> bool) (x : A) (l : list A), In x (filter p l) <-> In x l /\ p x = true.
Proof.
intros A p x l.
pattern l.
apply list_ind.
+ rewrite filter_nil.
  intuition.
  elim (in_nil _ H).
+ intros t q IHq.
  case_eq (p t); intro Hpt.
  - rewrite filter_cons_ok; [ | exact Hpt].
    split.
    * intro Hx.
      destruct (in_inv _ _ _ Hx).
      ++ subst.
         split.
         -- apply in_eq.
         -- exact Hpt.
      ++ intuition.
         apply in_cons.
         assumption.
    * intros (Hx, Hpx).
      destruct (in_inv _ _ _ Hx).
      ++ subst.
         apply in_eq.
      ++ apply in_cons.
         intuition.
  - rewrite filter_cons_ko; [ | exact Hpt].
    split.
    * intro Hx.
      intuition.
      apply in_cons.
      assumption.
    * intros (Hx, Hpx).
      destruct (in_inv _ _ _ Hx).
      ++ subst.
         rewrite Hpt in Hpx.
         discriminate.
      ++ intuition.
Qed.

Lemma in_map : forall [A B : Type] (f : A -> B) (l : list A) (x : A),
       @In A x l -> @In B (f x) (@map A B f l).
Proof.
intros A B f l x.
apply (list_ind (fun l => @In A x l -> @In B (f x) (@map A B f l))).
+ intro H.
  elim (in_nil x H).
+ unfold In, map.
  intros t q IHq.
  destruct (acc (t::q)).
  simpl.
  intuition.
  - subst.
    apply in_eq.
  - rewrite (proof_irrelevance _ (a (@str A q) (@tl_rel_tl A {| hd := t; tl := @str A q |} (@str A q))) (@acc A q)).
    destruct acc_cons.
    simpl.
    right.
    rewrite (proof_irrelevance _ (a0 (@str B (@map_rec A B f (@str A q) (@acc A q))) 
                    (                 @tl_rel_tl B {| hd := f t; tl := @str B (@map_rec A B f (@str A q) (@acc A q)) |}
                                      (@str B (@map_rec A B f (@str A q) (@acc A q)))))
                                 (@acc B (@map_rec A B f (@str A q) (@acc A q)))).
    apply IHq.
    rewrite (proof_irrelevance _ (a (@str A q) (@tl_rel_tl A {| hd := t; tl := @str A q |} (@str A q))) (@acc A q)) in H0.
    apply H0.
Qed.

Lemma in_or_app : forall [A : Type] (l m : list A) (a : A), In a l \/ In a m -> In a (l ++ m).
Proof.
intros A l m a.
apply (list_ind (fun l => In a l \/ In a m -> In a (l ++ m))).
+ destruct 1 as [ H | H ].
  - elim (in_nil _ H).
  - unfold app.
    simpl.  
    destruct acc_nil.
    simpl.
    exact H.
+ intros t q IHq [ H | H ].
  - unfold cons, In in H.
    destruct (acc_cons t (acc q)).
    simpl in H.
    destruct H as [ H | H ].
    * subst.
      unfold app.
      simpl.
      destruct acc_cons.
      simpl.
      apply in_eq.
    * unfold app.
      simpl.
      destruct acc_cons.
      simpl.
      apply in_cons.
      unfold app in IHq.
      rewrite (proof_irrelevance _ _ (acc q)).
      apply IHq.
      left.
      unfold In.
      rewrite (proof_irrelevance _ _ (acc q)) in H.
      exact H.
  - unfold app.
    simpl.
    destruct acc_cons.
    simpl.
    apply in_cons.
    unfold app in IHq.
    rewrite (proof_irrelevance _ _ (acc q)).
    apply IHq.
    right.
    exact H.
Qed.

Lemma in_app_or : forall [A : Type] (l m : list A) (a : A), In a (l ++ m) -> In a l \/ In a m.
Proof.
intros A l m a.
apply (list_ind (fun l => In a (l ++ m) -> In a l \/ In a m)).
+ intro H.
  rewrite app_nil in H.
  right.
  exact H.
+ intros t q IHq H.
  rewrite app_cons in H.
  destruct (in_inv _ _ _ H) as [ H1 | H1 ].
  - subst.
    left.
    apply in_eq.
  - destruct (IHq H1) as [ H2 | H2 ].
    * left.
      apply in_cons.
      exact H2.
    * right.
      exact H2.
Qed.

Lemma in_flat_map : forall [A B : Type] (f : A -> list B) (l : list A) (y : B),
       @In B y (@flat_map A B f l) <->
       (exists x : A, @In A x l /\ @In B y (f x)).
Proof.
intros A B f l y.
apply (list_ind (fun l => @In B y (@flat_map A B f l) <-> (exists x : A, @In A x l /\ @In B y (f x)))).
+ split.
  - intro H.
    rewrite flat_map_nil in H.
    elim (in_nil _ H).
  - destruct 1 as (t, (H1, H2)).
    elim (in_nil _ H1).
+ intros t q IHq.
  split.
  - intro H.
    rewrite flat_map_cons in H.
    destruct (in_app_or _ _ _ H) as [ H1 | H1 ].
    * exists t.
      split.
      ++ apply in_eq.
      ++ exact H1.
    * intuition.
      destruct H3 as (a, (Hx1, Hx2)).
      exists a.
      split.
      ++ apply in_cons.
         exact Hx1.
      ++ exact Hx2.
  - intro H.
    destruct H as (a, (Ha1, Ha2)).
    rewrite flat_map_cons.
    apply in_or_app.
    destruct (in_inv _ _ _ Ha1) as [ Ha3 | Ha3 ].
    * subst.
      left.
      exact Ha2.
    * right.
      apply IHq.
      exists a.
      split.
      ++ exact Ha3.
      ++ exact Ha2.
Qed.

Lemma in_map_iff : forall [A B : Type] (f : A -> B) (l : list A) (y : B), In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
intros A B f l y.
pattern l.
apply list_ind.
+ split.
  - intro H.
    rewrite map_nil in H.
    elim (in_nil _ H).
  - destruct 1 as (a, (Ha1, Ha2)).
    elim (in_nil _ Ha2).
+ intros t q IHq.
  split.
  - intro H.
    rewrite map_cons in H.
    destruct (in_inv _ _ _ H) as [ H1 | H2 ].
    * exists t.
      split.
      ++ exact H1.
      ++ apply in_eq.
    * intuition.
      destruct H3 as (a, (Ha1, Ha2)).
      exists a.
      split.
      ++ exact Ha1.
      ++ apply in_cons.
         exact Ha2.
  - destruct 1 as (a, (Ha1, Ha2)).
    subst.
    apply in_map.
    exact Ha2.
Qed.

Lemma in_map_inv : forall {A B} (f : A -> B) a (lA : list A), Basics.InjectiveXT f -> In (f a) (map f lA) -> In a lA.
Proof.
intros A B f a lA Hinjf Hfa.
generalize (in_map_iff f lA (f a)).
intuition.
destruct H.
destruct H.
rewrite <- (Hinjf x a H).
assumption.
Qed.

Lemma in_dec : forall [A : Type], dec_eq A -> forall (a : A) (l : list A), decidable (In a l).
Proof.
intros A eqA a l.
pattern l.
apply list_rect.
+ right.
  exact (in_nil a).
+ intros t q IHq.
  destruct (eqA a t).
  - subst.
    left.
    apply in_eq.
  - destruct IHq.
    * left.
      apply in_cons.
      assumption.
    * right.
      intro H.
      apply n0.
      destruct (in_inv _ _ _ H).
      ++ symmetry in H0.
         contradiction.
      ++ assumption.
Qed.

Fixpoint nodup_rec [A : Type] (eqA : dec_eq A) (os1 : option (stream A)) (acc : list A) (wf1 : Acc tl_rel os1) { struct wf1 } : list A :=
  match os1 as o return os1 = o -> list A with
  | None    => (fun _   => nil)
  | Some s1 => (fun Heq => let acc1' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os')
                                                  match wf1 with Acc_intro _ acc1 => acc1 end _ Heq in
                           let wf1_tl := acc1' (tl s1) (tl_rel_tl s1 (tl s1)) in
                           let hd1 := hd s1 in
                           match in_dec eqA hd1 acc with
                           | left inacc     => nodup_rec eqA (tl s1) acc wf1_tl
                           | right notinacc => hd1 ::: (nodup_rec eqA (tl s1) (hd1::acc) wf1_tl)
                           end)
  end eq_refl.

Definition nodup [A : Type] (eqA : dec_eq A) (lA : list A) : list A := nodup_rec eqA (str lA) [] (acc lA).

Inductive NoDup (A : Type) : list A -> Prop :=
    NoDup_nil : NoDup A []
  | NoDup_cons : forall (x : A) [l : list A],
                 ~ In x l -> NoDup A l -> NoDup A (x :: l).

Arguments NoDup [A]%type_scope _%list.
Arguments NoDup_nil A%type_scope.
Arguments NoDup_cons [A]%type_scope x [l] _ _.

Lemma nodup_nil : forall [A : Type] (eqA : dec_eq A), @nodup A eqA [] = [].
Proof.
intros A eqA.
unfold nodup, nil.
destruct acc_nil.
simpl.
unfold nil.
rewrite (proof_irrelevance _ (Acc_intro None a) acc_nil).
reflexivity.
Qed.
(* not very useful
Lemma nodup_rec_cons_ok : forall [A : Type] (eqA : dec_eq A) (h : A) (t accA : list A),
                            ~In h accA -> @nodup_rec A eqA (str (h :: t)) accA (acc (h::t)) = h :: @nodup_rec A eqA (str t) (h::accA) (acc t).
Proof.
intros A eqA t q accA Ht.
simpl.
destruct acc_cons.
simpl.
destruct in_dec.
+ contradiction.
+ rewrite (proof_irrelevance _ _ (acc q)).
  reflexivity.
Qed.

Lemma nodup_rec_cons_ko : forall [A : Type] (eqA : dec_eq A) (h : A) (t accA : list A),
                            In h accA -> @nodup_rec A eqA (str (h :: t)) accA (acc (h::t)) = @nodup_rec A eqA (str t) accA (acc t).
Proof.
intros A eqA t q accA Ht.
simpl.
destruct acc_cons.
simpl.
destruct in_dec.
+ rewrite (proof_irrelevance _ _ (acc q)).
  reflexivity.
+ contradiction.
Qed.
*)
Lemma nodup_rec_in : forall [A : Type] (eqA : dec_eq A) (x : A) (lA : list A) (accA : list A),
                        In x (nodup_rec eqA (str lA) accA (acc lA)) <-> In x lA /\ ~In x accA.
Proof.
intros A eqA x lA.
pattern lA.
apply list_ind.
+ intro accA.
  simpl.
  destruct acc_nil.
  simpl.
  split.
  - intro H.
    elim (in_nil _ H).
  - destruct 1 as (H, H').
    elim (in_nil _ H).
+ intros t q IHq accA.
  split.
  - simpl.
    destruct acc_cons.
    simpl.
    destruct in_dec.
    * intro Hx.
      rewrite (proof_irrelevance _ _ (acc q)) in Hx.
      generalize (IHq accA).
      intuition.
      clear H.
      apply in_cons.
      assumption.
    * intro Hx.
      rewrite (proof_irrelevance _ _ (acc q)) in Hx.
      destruct (in_inv _ _ _ Hx).
      ++ subst.
         split.
         -- apply in_eq.
         -- assumption.
      ++ generalize (IHq (t::accA)).
         intuition.
         -- clear H0.
            apply in_cons.
            assumption.
         -- apply H3.
            apply in_cons.
            assumption.
  - destruct 1 as (Hx1, Hx2).
    simpl.
    destruct acc_cons.
    simpl.
    destruct in_dec.
    * rewrite (proof_irrelevance _ _ (acc q)).
      apply IHq.
      destruct (in_inv _ _ _ Hx1).
      ++ subst.
         contradiction.
      ++ intuition.
    * rewrite (proof_irrelevance _ _ (acc q)).
      destruct (in_inv _ _ _ Hx1).
      ++ subst.
         apply in_eq.
      ++ destruct (eqA x t).
         -- subst.
            apply in_eq.
         -- apply in_cons.
            apply IHq.
            split.
            ** assumption.
            ** intro Hx.
               destruct (in_inv _ _ _ Hx); intuition.
Qed.

Lemma nodup_In : forall [A : Type] (eqA : dec_eq A) (l : list A) (x : A), In x (nodup eqA l) <-> In x l.
Proof.
intros A eqA l x.
generalize (nodup_rec_in eqA x l []).
unfold nodup.
intuition.
apply H2.
apply in_nil.
Qed.

Lemma nodup_rec_NoDup : forall [A : Type] (eqA : dec_eq A) (lA : list A) (accA : list A), NoDup (nodup_rec eqA (str lA) accA (acc lA)).
Proof.
intros A eqA lA.
pattern lA.
apply list_ind.
+ intro accA.
  simpl.
  destruct acc_nil.
  apply NoDup_nil.
+ intros t q IHq accA.
  simpl.
  destruct acc_cons.
  simpl.
  destruct in_dec.
  - rewrite (proof_irrelevance _ _ (acc q)).
    apply IHq.
  - apply NoDup_cons.
    * rewrite (proof_irrelevance _ _ (acc q)).
      intro Ht.
      generalize (nodup_rec_in eqA t q (t::accA)).
      intuition.
      apply H2.
      apply in_eq.
    * rewrite (proof_irrelevance _ _ (acc q)).
      apply IHq.
Qed.

Lemma nodup_NoDup : forall [A : Type] (eqA : dec_eq A) (lA : list A), NoDup (nodup eqA lA).
Proof.
intros A eqA lA.
apply nodup_rec_NoDup.
Qed.

Lemma nodup_inv : forall [A : Type] (eqA : dec_eq A) (k l : list A) (a : A), nodup eqA k = a :: l -> ~ In a l.
Proof.
intros A eqA k l a H.
generalize (nodup_NoDup eqA k).
rewrite H.
intro Hal.
inversion Hal.
subst.
rewrite <- (eq_str _ _ H1).
assumption.
Qed.

Lemma nodup_rec_fixed_point : forall [A : Type] (eqA : dec_eq A) (lA accA : list A), NoDup lA -> (forall a, In a accA -> In a lA -> False) -> nodup_rec eqA (str lA) accA (acc lA) = lA.
Proof.
intros A eqA lA.
pattern lA.
apply list_ind.
+ intros accA _ Hdisj.
  simpl.
  destruct acc_nil.
  simpl.
  reflexivity.
+ intros t q IHq accA Htq Hdisj.
  inversion Htq.
  generalize (eq_str _ _ H0); clear H0; intro H0.
  subst.
  simpl.
  destruct acc_cons.
  simpl.
  destruct in_dec.
  - elim (Hdisj t).
    * assumption.
    * apply in_eq.
  - rewrite (proof_irrelevance _ _ (acc q)).
    rewrite IHq.
    * reflexivity.
    * assumption.
    * clear a.
      intros a Ha1 Ha2.
      destruct (eqA a t).
      ++ subst.
         contradiction.
      ++ apply (Hdisj a).
         -- destruct (in_inv _ _ _ Ha1).
            ** symmetry in H.
               contradiction.
            ** assumption.
         -- apply in_cons.
            assumption.
Qed.

Lemma nodup_fixed_point : forall [A : Type] (eqA : dec_eq A) (l : list A), NoDup l -> nodup eqA l = l.
Proof.
intros A eqA l Hl.
apply nodup_rec_fixed_point.
+ exact Hl.
+ intros a Ha.
  elim (in_nil _ Ha).
Qed.


Definition suffix [A : Type] (suf l : list A) := exists pre : list A, l = pre ++ suf.

Lemma suffix_refl : forall [A : Type] (lA :list A), suffix lA lA.
Proof.
intros A lA.
exists [].
rewrite app_nil.
reflexivity.
Qed.

Lemma stream_suffix_refl : forall [A : Type] (lA : list A), suffix (mklist A (str lA) (acc lA)) lA.
Proof.
intros A lA.
rewrite <- list_eta_conv.
apply suffix_refl.
Qed.

Lemma suffix_tl : forall [A : Type] (lA : list A) (h : A) (t : list A), suffix (h::t) lA -> suffix t lA.
Proof.
intros A lA t q Htq.
destruct Htq as (pre, Hpre).
exists (pre ++ [t]).
rewrite Hpre.
rewrite <- app_assoc.
rewrite app_cons.
rewrite app_nil.
reflexivity.
Qed.

Lemma suffix_cons : forall [A : Type] (hA : A) (tA : list A) (l : list A), suffix l tA -> suffix l (hA::tA).
Proof.
intros A hA tA l Htq.
destruct Htq as (pre, Hpre).
exists (hA::pre).
rewrite app_cons.
rewrite Hpre.
reflexivity.
Qed.

Lemma suffix_in : forall [A : Type] (lA : list A) (suf : list A) (a : A), suffix suf lA -> In a suf -> In a lA.
Proof.
intros A lA suf a H Ha.
destruct H as (pre, Hpre).
subst.
apply in_or_app.
right.
exact Ha.
Qed.

Lemma stream_in_eq : forall [A : Type] (os : option (stream A)) wf (s : stream A) (Heq : os = Some s), In (hd s) (mklist A os wf).
Proof.
intros A os wf s Heq.
subst.
destruct s.
simpl.
destruct wf.
unfold In.
simpl.
left.
reflexivity.
Qed.

Lemma stream_suffix : forall [A : Type] (lA : list A) (os : option (stream A)) wf (s : stream A) (wf_tl : Acc tl_rel (tl s)) (Heq : os = Some s),
                        suffix (mklist A os wf) lA -> suffix (hd s ::  mklist A (tl s) wf_tl) lA.
Proof.
intros A lA os wf s wf_tl Heq H.
subst.
destruct H as (pre, Hpre).
exists pre.
subst.
apply f_equal.
apply eq_str.
simpl.
rewrite <- stream_eta_conv.
reflexivity.
Qed.

Fixpoint onto_rec [A : Type] (lA : list A) (os : option (stream A)) (wf : Acc tl_rel os) (H : suffix (mklist A os wf) lA) { struct wf } : list { a : A | In a lA } :=
  match os as o return os = o -> list { a : A | In a lA } with
  | None   => (fun _   => nil)
  | Some s => (fun Heq => let acc' := eq_rect _ (fun os => forall os', tl_rel os' os -> Acc tl_rel os')
                                                match wf with Acc_intro _ acc => acc end _ Heq in
                          let wf_tl := acc' (tl s) (tl_rel_tl s (tl s)) in
                          let hd_in_s := stream_in_eq os wf _ Heq in
                          let H_tl := suffix_tl lA (hd s) (mklist A (tl s) wf_tl) (stream_suffix lA os wf s wf_tl Heq H) in
                          exist _ (hd s) (suffix_in lA _ (hd s) H hd_in_s) ::: (onto_rec lA (tl s) wf_tl H_tl))
  end eq_refl.

Definition onto [A : Type] (lA : list A) := onto_rec lA (str lA) (acc lA) (stream_suffix_refl lA).

Lemma onto_nil : forall {A : Type}, onto (@nil A) = nil.
Proof.
intro A.
unfold onto, nil.
simpl.
destruct acc_nil.
simpl.
apply list_eta_conv.
Qed.

Definition cons_cast [A : Type] (h : A) (t : list A) :=
                      { f : { a : A | In a t } -> { a : A | In a (h::t) } | forall a, proj1_sig (f a) = proj1_sig a }.

Definition cast [A : Type] (h : A) (t : list A) : cons_cast h t.
Proof.
exists (fun aHa => match aHa with exist _ a Ha => exist (fun a => In a (h::t)) a (in_cons _ _ _ Ha) end).
intros (a, Ha).
reflexivity.
Defined.

Lemma onto_rec_cons : forall [A : Type] (lA : list A) os wf s (Heq : os = Some s) H wf_tl H_hd H_tl,
                        onto_rec lA os wf H = (exist _ (hd s) H_hd) ::: onto_rec lA (tl s) wf_tl H_tl.
Proof.
intros.
destruct wf.
simpl.
destruct os as [ s' | ].
+ injection Heq.
  clear Heq; intro Heq; subst.
  rewrite <- eq_rect_eq.
  rewrite (proof_irrelevance _ _ H_hd).
  rewrite (proof_irrelevance _ _ wf_tl).
  rewrite (proof_irrelevance _ _ H_tl).
  reflexivity.
+ discriminate.
Qed.

Lemma onto_rec_cons_ref : forall [A : Type] (hA : A) (tA : list A) (f : cons_cast hA tA) (l : list A) os wf (Heq : l = mklist A os wf) Hht Ht,
                            onto_rec (hA::tA) os wf Hht = map (proj1_sig f) (onto_rec tA os wf Ht).
Proof.
intros A tA qA (f, Hf) l.
simpl.
pattern l.
apply list_ind.
+ intros os wf Heq Htq Hq.
  unfold nil in Heq.
  injection Heq.
  clear Heq; intro; subst.
  destruct wf.
  simpl.
  rewrite map_nil.
  reflexivity.
+ intros t q IHq os wf Heq Htq Hq.
  injection Heq.
  clear Heq; intro; subst.
  destruct wf.
  simpl.
  generalize map_cons.
  intro Hmap.
  unfold cons in Hmap.
  rewrite Hmap; clear Hmap.
  erewrite IHq.
  instantiate (1 := (suffix_tl qA t
            {| str := str q; acc := a (str q) (tl_rel_tl {| hd := t; tl := str q |} (str q)) |}
            (stream_suffix qA (Some {| hd := t; tl := str q |})
               (Acc_intro (Some {| hd := t; tl := str q |}) a) {| hd := t; tl := str q |}
               (a (str q) (tl_rel_tl {| hd := t; tl := str q |} (str q))) eq_refl Hq))).
  assert (forall (h h' : { a : A | In a (tA::qA) }) t, h = h' -> h:::t = h':::t) as H.
  - intros.
    subst.
    reflexivity.
  - apply H.
    generalize (Hf (exist (fun a0 : A => In a0 qA) t
     (suffix_in qA
        {|
          str := Some {| hd := t; tl := str q |};
          acc := Acc_intro (Some {| hd := t; tl := str q |}) a
        |} t Hq
        (stream_in_eq (Some {| hd := t; tl := str q |})
           (Acc_intro (Some {| hd := t; tl := str q |}) a) {| hd := t; tl := str q |} eq_refl)))).
    clear H; intro H.
    destruct f.
    simpl in H.
    subst.
    apply subset_eq_compat.
    reflexivity.
  - destruct q.
    simpl.
    apply eq_str.
    reflexivity.
Qed.

Lemma onto_cons_gen : forall [A : Type] (h : A) (t : list A) (f : cons_cast h t),
                        onto (h::t) = (exist (fun a => In a (h::t)) h (in_eq h t)) :: (map (proj1_sig f) (onto t)).
Proof.
intros A t q (f, Hf).
unfold onto, cons.
simpl.
apply eq_str.
simpl.
erewrite (onto_rec_cons (t:::q) _ (acc_cons t (acc q)) {| hd := t; tl := str q |}
                        eq_refl (stream_suffix_refl (t ::: q)) (acc q) (in_eq t q) (suffix_cons t q _ (stream_suffix_refl q))).
simpl.
apply f_equal.
apply f_equal.
erewrite (onto_rec_cons_ref t q (cast t q) (mklist A (str q) (acc q)) (str q) (acc q) eq_refl).
instantiate (1 := (stream_suffix_refl q)).
apply f_equal.
assert (proj1_sig (cast t q) = f).
+ apply functional_extensionality.
  destruct x as (a, Ha).
  simpl.
  generalize (Hf (exist (fun a0 : A => In a0 q) a Ha)); clear Hf; intro Hf.
  destruct f.
  simpl in Hf.
  subst.
  apply subset_eq_compat.
  reflexivity.
+ rewrite <- H.
  reflexivity.
Qed.

Lemma onto_cons : forall [A : Type] (h : A) (t : list A),
                    onto (h::t) = (exist (fun a => In a (h::t)) h (in_eq h t)) :: (map (fun (a_in_t : { a : A | In a t }) => let (a, Ha) := a_in_t in exist _ a (in_cons _ _ _ Ha)) (onto t)).
Proof.
intros A h t.
apply (onto_cons_gen h t (cast h t)).
Qed.

Lemma onto_Onto : forall [A : Type] (lA : list A) (a : { a : A | In a lA }), In a (onto lA).
Proof.
intros A lA (a, Ha).
revert Ha.
pattern lA.
apply list_ind.
+ intro Ha.
  elim (in_nil _ Ha).
+ intros t q IHq Ha.
  destruct (in_inv _ _ _ Ha).
  - subst.
    rewrite (onto_cons_gen a q (cast a q)).
    rewrite (proof_irrelevance _ (in_eq a q) Ha).
    apply in_eq.
  - rewrite (onto_cons_gen t q (cast t q)).
    apply in_cons.
    apply in_map_iff.
    exists (exist _ a H).
    split.
    * simpl.
      apply f_equal.
      apply proof_irrelevance.
    * apply IHq.
Qed.

End MinIter.

Module FullIter (Iter : ListSpec).

Export Iter.

Open Scope list_scope.

Lemma filter_map : forall [A B : Type] (p : B -> bool) (f : A -> B) (l : list A), filter p (map f l) = map f (filter (fun a => p (f a)) l).
Proof.
intros A B p f l.
pattern l.
apply list_ind.
+ rewrite map_nil.
  rewrite filter_nil.
  rewrite filter_nil.
  rewrite map_nil.
  reflexivity.
+ intros t q IHq.
  rewrite map_cons.
  case_eq (p (f t)); intro Hpft.
  - rewrite filter_cons_ok; [ | exact Hpft ].
    rewrite filter_cons_ok; [ | exact Hpft ].
    rewrite map_cons.
    f_equal.
    apply IHq.
  - rewrite filter_cons_ko; [ | exact Hpft ].
    rewrite filter_cons_ko; [ | exact Hpft ].
    apply IHq.
Qed.

Lemma app_length : forall [A : Type] (l l' : list A),
       length (l ++ l') = length l + length l'.
Proof.
intros A l.
pattern l.
apply list_ind.
+ intro l'.
  rewrite length_nil.
  rewrite app_nil.
  reflexivity.
+ intros t q IHq l'.
  rewrite length_cons.
  rewrite app_cons.
  rewrite length_cons.
  rewrite IHq.
  reflexivity.
Qed.

Lemma map_length : forall [A B : Type] (f : A -> B) (l : list A),
       length (map f l) = length l.
Proof.
intros A B f l.
pattern l.
apply list_ind.
+ rewrite map_nil.
  rewrite length_nil.
  rewrite length_nil.
  reflexivity.
+ intros t q IHq.
  rewrite length_cons.
  rewrite map_cons.
  rewrite length_cons.
  rewrite IHq.
  reflexivity.
Qed.

Lemma app_nil_right : forall [A : Type] (l : list A), app l [] = l.
Proof.
intros A l.
pattern l.
apply list_ind.
+ rewrite app_nil.
  reflexivity.
+ intros t q IHq.
  rewrite app_cons.
  f_equal.
  exact IHq.
Qed.

Lemma map_id : forall {A : Type}, @map A A id = id.
Proof.
intro A.
apply functional_extensionality.
intro l.
pattern l.
apply list_ind.
+ rewrite map_nil.
  reflexivity.
+ intros t q IHq.
  rewrite map_cons.
  unfold id.
  f_equal.
  exact IHq.
Qed.

Lemma map_comp : forall [A B C : Type] (f : A -> B) (g : B -> C),
       map g <o> map f = map (g <o> f).
Proof.
intros A B C f g.
apply functional_extensionality.
intro l.
pattern l.
apply list_ind.
+ unfold funcomp.
  rewrite map_nil.
  rewrite map_nil.
  rewrite map_nil.
  reflexivity.
+ unfold funcomp.
  intros t q IHq.
  rewrite map_cons.
  rewrite map_cons.
  rewrite map_cons.
  f_equal.
  exact IHq.
Qed.


Inductive Forall [A : Type] (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P []
  | Forall_cons : forall (x : A) [l : list A],
                  P x -> Forall P l -> Forall P (x :: l).

Arguments Forall_cons _ [P]%function_scope.

Inductive Exists [A : Type] (P : A -> Prop) : list A -> Prop :=
    Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l)
  | Exists_cons_tl : forall (x : A) [l : list A],
                     Exists P l -> Exists P (x :: l).

Arguments Exists_cons_tl _ [P]%function_scope.

Lemma Forall_dec : forall [A : Type] (P : A -> Prop), (forall a, decidable (P a)) -> forall l, decidable (Forall P l).
Proof.
intros A P Hdec l.
pattern l.
apply list_rect.
+ left.
  apply Forall_nil.
+ intros t q IHq.
  destruct (Hdec t).
  - destruct IHq.
    * left.
      apply Forall_cons; assumption.
    * right.
      intro H.
      apply n.
      inversion H.
      ++ elim (nil_cons H1).
      ++ destruct (injective_cons H0); subst.
         assumption.
  - right.
    intro H.
    apply n.
    inversion H.
    * elim (nil_cons H1).
    * destruct (injective_cons H0); subst.
      assumption.
Qed.

Lemma Exists_dec : forall [A : Type] (P : A -> Prop), (forall a, decidable (P a)) -> forall l, decidable (Exists P l).
Proof.
intros A P Hdec l.
pattern l.
apply list_rect.
+ right.
  intro H.
  inversion H.
  - eapply nil_cons.
    symmetry.
    eassumption.
  - eapply nil_cons.
    symmetry.
    eassumption.
+ intros t q IHq.
  destruct (Hdec t).
  - left.
    apply Exists_cons_hd.
    assumption.
  - destruct IHq.
    * left.
      apply Exists_cons_tl.
      assumption.
    * right.
      intro H.
      inversion H.
      ++ destruct (injective_cons H0); subst.
         contradiction.
      ++ destruct (injective_cons H0); subst.
         contradiction.
Qed.

Lemma Forall_impl : forall [A : Type] (P Q : A -> Prop), (forall a : A, P a -> Q a) -> forall l : list A, Forall P l -> Forall Q l.
Proof.
intros A P Q HPQ l.
pattern l.
apply list_ind.
+ intros _.
  apply Forall_nil.
+ intros t q IHq Htq.
  inversion Htq.
  - elim (nil_cons H0).
  - destruct (injective_cons H); subst.
    apply Forall_cons.
    * apply HPQ.
      assumption.
    * apply IHq.
      assumption.
Qed.

Lemma Forall_inv_tail : forall [A : Type] [P : A -> Prop] [a : A] [l : list A], Forall P (a :: l) -> Forall P l.
Proof.
intros A P a l H.
inversion H.
+ elim (nil_cons H1).
+ destruct (injective_cons H0); subst.
  assumption.
Qed.

Lemma Forall_inv : forall [A : Type] [P : A -> Prop] [a : A] [l : list A], Forall P (a :: l) -> P a.
Proof.
intros A P a l H.
inversion H.
+ elim (nil_cons H1).
+ destruct (injective_cons H0); subst.
  assumption.
Qed.

Lemma Forall_forall : forall [A : Type] (P : A -> Prop) (l : list A), Forall P l -> forall a, In a l -> P a.
Proof.
intros A P l.
pattern l.
apply list_ind.
+ intros _ a Ha.
  elim (in_nil _ Ha).
+ intros t q IHq Htq a Ha.
  inversion Htq.
  - elim (nil_cons H0).
  - destruct (injective_cons H); subst. 
    destruct (in_inv _ _ _ Ha).
    * subst.
      assumption.
    * exact (IHq H1 a H2).
Qed.

Lemma forall_Forall : forall [A : Type] (P : A -> Prop) (l : list A), (forall a, In a l -> P a) -> Forall P l.
Proof.
intros A P l.
pattern l.
apply list_ind.
+ intros _; apply Forall_nil.
+ intros t q IHq Htq.
  apply Forall_cons.
  - apply Htq.
    apply in_eq.
  - apply IHq.
    intros a' Ha'.
    apply Htq.
    apply in_cons.
    exact Ha'.
Qed.

Lemma Exists_exists : forall [A : Type] (P : A -> Prop) (l : list A), Exists P l -> exists a, In a l /\ P a.
Proof.
intros A P l.
pattern l.
apply list_ind.
+ intro H.
  inversion H.
  - eelim nil_cons.
    symmetry.
    eassumption.
  - eelim nil_cons.
    symmetry.
    eassumption.
+ intros t q IHq Htq.
  inversion Htq.
  - destruct (injective_cons H); subst.
    exists t.
    split.
    * apply in_eq.
    * assumption.
  - destruct (injective_cons H); subst.
    destruct (IHq H0) as (a, (Ha1, Ha2)).
    exists a.
    split.
    * apply in_cons.
      exact Ha1.
    * exact Ha2.
Qed.

Lemma exists_Exists : forall [A : Type] (P : A -> Prop) (l : list A), (exists a, In a l /\ P a) -> Exists P l.
Proof.
intros A P l.
pattern l.
apply list_ind.
+ destruct 1 as (a, (Ha1, _)).
  elim (in_nil _ Ha1).
+ intros t q IHq Htq.
  destruct Htq as (a, (Ha1, Ha2)).
  destruct (in_inv _ _ _ Ha1) as [ Ha3 | Ha3 ].
  - subst.
    apply Exists_cons_hd.
    exact Ha2.
  - apply Exists_cons_tl.
    apply IHq.
    exists a.
    split.
    * exact Ha3.
    * exact Ha2.
Qed.

Lemma Forall_Exists_neg : forall [A : Type] (P : A -> Prop) (l : list A), Forall (fun x : A => ~ P x) l <-> ~ Exists P l.
Proof.
intros A P l.
pattern l.
apply list_ind; intuition.
+ inversion H0.
  - eelim nil_cons.
    symmetry.
    eassumption.
  - eelim nil_cons.
    symmetry.
    eassumption.
+ apply Forall_nil.
+ inversion H; [ eelim nil_cons; eassumption | ].
  destruct (injective_cons H3); subst.
  clear H H3.
  inversion H2.
  - destruct (injective_cons H); subst.
    contradiction.
  - destruct (injective_cons H); subst.
    apply H0.
    * assumption.
    * assumption.
+ apply Forall_cons.
  - intro Ha.
    apply H.
    apply Exists_cons_hd.
    exact Ha.
  - apply H1.
    intro Hl.
    apply H.
    apply Exists_cons_tl.
    exact Hl.
Qed.


Lemma nodup_hd : forall {A} (t : A) (q : list A), NoDup (t::q) -> ~In t q.
Proof.
intros A t q Htq.
inversion Htq.
+ elim (nil_cons H0).
+ destruct (injective_cons H); subst.
  assumption.
Qed.

Lemma nodup_tl : forall {A} (t : A) (q : list A), NoDup (t::q) -> NoDup q.
Proof.
intros A t q Htq.
inversion Htq.
+ elim (nil_cons H0).
+ destruct (injective_cons H).
  subst.
assumption.
Qed.

Lemma nodup_filter : forall [A : Type] (p : A -> bool) (l : list A), NoDup l -> NoDup (filter p l).
Proof.
intros A p l.
pattern l.
apply list_ind.
+ rewrite filter_nil.
  trivial.
+ intros t q IHq Htq.
  inversion Htq.
  - elim (nil_cons H0).
  - destruct (injective_cons H); subst.
    case_eq (p t); intro Hpt.
    * rewrite filter_cons_ok.
      ++ apply NoDup_cons.
         -- intro Ht.
            generalize (filter_In p t q).
            intuition.
         -- intuition.
      ++ exact Hpt.
    * rewrite filter_cons_ko.
      ++ intuition.
      ++ exact Hpt.
Qed.

Lemma nodup_map : forall {A B} (f : A -> B) (lA : list A), InjectiveXT f -> NoDup lA -> NoDup (map f lA).
Proof.
intros A B f lA Hinjf.
pattern lA.
apply list_ind.
+ rewrite map_nil.
  intros _.
  apply NoDup_nil.
+ intros t q IHq Htq.
  rewrite map_cons.
  inversion Htq; subst; clear Htq.
  - elim (nil_cons H0).
  - destruct (injective_cons H); clear H; subst.
    apply NoDup_cons.
    * intro Hft.
      apply H0.
      exact (in_map_inv f t q Hinjf Hft).
    * apply IHq.
      assumption.
Qed.

Lemma nodup_map_inv : forall {A B} (f : A -> B) (lA : list A), NoDup (map f lA) -> NoDup lA.
Proof.
intros A B f lA.
pattern lA.
apply list_ind.
+ rewrite map_nil.
  intros _.
  apply NoDup_nil.
+ intros t q IHq H.
  rewrite map_cons in H.
  inversion H.
  - elim (nil_cons H1).
  - destruct (injective_cons H0); subst.
    apply NoDup_cons.
    * intro H'.
      apply H1.
      apply in_map.
      exact H'.
    * intuition.
Qed.

Lemma nodup_app : forall {A} (l1 l2 : list A), NoDup l1 -> NoDup l2 -> Forall (fun a1 => ~In a1 l2) l1 -> NoDup (l1 ++ l2).
Proof.
intros A l1 l2 Hl1 Hl2 Hl12.
revert Hl1 Hl12.
pattern l1.
apply list_ind.
+ rewrite app_nil.
  auto.
+ intros t q IHq Htq1 Htq2.
  rewrite app_cons.
  inversion Htq1.
  - elim (nil_cons H0).
  - destruct (injective_cons H); subst.
    inversion Htq2; [ elim (nil_cons H3) | destruct (injective_cons H2); subst ].
    apply NoDup_cons.
    * intro Htq3.
      destruct (in_app_or _ _ _ Htq3).
      ++ contradiction.
      ++ contradiction.
    * apply IHq.
      ++ assumption.
      ++ assumption.
Qed.

Lemma nodup_flat_map : forall {A B} (lA : list A) (f : A -> list B),
  NoDup lA -> (forall a, NoDup (f a)) -> (forall a1 a2, a1 <> a2 -> Forall (fun a1 => ~In a1 (f a2)) (f a1)) -> NoDup (flat_map f lA).
Proof.
intros A B lA f HlA Hf1 Hf2.
revert HlA.
pattern lA.
apply list_ind.
+ intros _.
  rewrite flat_map_nil.
  apply NoDup_nil.
+ intros t q IHq HlA.
  rewrite flat_map_cons.
  apply nodup_app.
  - apply Hf1.
  - apply IHq.
    inversion HlA.
    * elim (nil_cons H0).
    * destruct (injective_cons H); subst.
      assumption.
  - apply Forall_Exists_neg.
    intro Hft.
    destruct (Exists_exists _ _ Hft) as (a, (Ha1, Ha2)).
    generalize (in_flat_map f q a).
    intuition.
    clear H0.
    destruct H as (a', (Ha1', Ha2')).
    assert (t <> a') as Hta'.
    * inversion HlA.
      ++ eelim nil_cons.
         eassumption.
      ++ intro Hta'.
         destruct (injective_cons H); subst.
         contradiction.
    * generalize (Hf2 t a' Hta').
      intro Hf.
      generalize (Forall_forall (fun a1 : B => In a1 (f a') -> False) (f t)).
      intuition.
      apply (H0 a Ha1 Ha2').
Qed.

Lemma onto_NoDup : forall {A} (lA : list A), NoDup lA -> NoDup (onto lA).
Proof.
intros A lA.
pattern lA.
apply list_ind.
+ rewrite onto_nil.
  intros _.
  apply NoDup_nil.
+ intros t q IHq Htq.
  inversion Htq.
  - elim (nil_cons H0).
  - destruct (injective_cons H).
    subst.
    rewrite onto_cons.
    apply NoDup_cons.
    * intro Ht.
      apply H0.
      generalize (in_map_iff (fun a_in_t : {a : A | In a q} =>
           let (a, Ha) := a_in_t in
           exist (fun a0 : A => In a0 (t :: q)) a
             (in_cons t a q Ha)) (onto q) (exist (fun a : A => In a (t :: q)) t (in_eq t q))).
      intuition.
      clear H H3 H0.
      destruct H5 as ((a, Ha), (Heq, Haq)).
      inversion Heq; subst.
      exact Ha.
    * apply nodup_map.
      ++ intros (a1, Ha1) (a2, Ha2) Ha12.
         inversion Ha12; subst.
         apply subset_eq_compat.
         reflexivity.
      ++ apply IHq.
         assumption.
Qed.


Lemma nth_error_In : forall [A : Type] (l : list A) (n : nat) [x : A], nth_error l n = Some x -> In x l.
Proof.
intros A l n x.
revert n.
pattern l.
apply list_ind.
+ intro n.
  rewrite nth_error_nil.
  intro H.
  discriminate.
+ intros t q IHq n Htq.
  destruct n as [ | n'].
  - rewrite nth_error_cons_hd in Htq.
    injection Htq; clear Htq; intro Htq; subst.
    apply in_eq.
  - apply in_cons.
    apply (IHq n').
    rewrite nth_error_cons_tl in Htq.
    exact Htq.
Qed.

Lemma In_nth_error : forall [A : Type] (l : list A) (x : A), In x l -> exists (n : nat), nth_error l n = Some x.
Proof.
intros A l x.
pattern l.
apply list_rect.
+ intro H.
  elim (in_nil _ H).
+ intros t q IHq Htq.
  destruct (in_inv _ _ _ Htq).
  - subst.
    exists 0.
    rewrite nth_error_cons_hd.
    reflexivity.
  - destruct (IHq H) as (n, Hn).
    exists (S n).
    rewrite nth_error_cons_tl.
    exact Hn.
Qed.

Lemma nth_error_None : forall [A : Type] (l : list A) (n : nat),
       nth_error l n = None <-> length l <= n.
Proof.
intros A l.
pattern l.
apply list_ind.
+ intros n.
  rewrite length_nil.
  rewrite nth_error_nil.
  intuition.
+ intros t q IHq n.
  rewrite length_cons.
  destruct n as [ | n' ].
  - rewrite nth_error_cons_hd.
    intuition.
    * discriminate.
    * lia.
  - rewrite nth_error_cons_tl.
    generalize (IHq n').
    intuition.
Qed.

Lemma nth_error_Some : forall [A : Type] (l : list A) (n : nat),
       nth_error l n <> None <-> n < length l.
Proof.
intros A l n.
generalize (nth_error_None l n).
+ destruct (le_lt_dec (length l) n) as [Hn | Hn].
  - intuition.
    lia.
  - intuition.
    lia.
Qed.

Lemma position_in : forall [A : Type] (eqA : dec_eq A) (a : A) (l :list A),
  In a l -> position eqA a l < length l.
Proof.
intros A eqA a l.
pattern l.
apply list_ind.
+ intro H.
  elim (in_nil _ H).
+ intros t q IHq Htq.
  rewrite length_cons.
  destruct (eqA a t).
  - subst.
    rewrite position_cons_hd.
    auto with arith.
  - rewrite position_cons_tl.
    * destruct (in_inv _ _ _ Htq).
      ++ symmetry in H.
         contradiction.
      ++ intuition.
    * assumption.
Qed.

Lemma position_notin : forall {A} (eqA : dec_eq A) (a : A) (l :list A),
  ~In a l -> position eqA a l = length l.
Proof.
intros A eqA a l.
pattern l.
apply list_ind.
+ rewrite position_nil.
  rewrite length_nil.
  reflexivity.
+ intros t q IHq Htq.
  rewrite length_cons.
  destruct (eqA a t).
  - subst.
    elim Htq.
    apply in_eq.
  - rewrite position_cons_tl.
    * apply f_equal.
      apply IHq.
      intro H.
      apply Htq.
      apply in_cons.
      exact H.
    * assumption.
Qed.

Lemma length_nth_in_cons_tl : forall [A : Type] t q (l : list A) (n : nat) (Heq : l = t::q) (H : S n < length l), n < length q.
Proof.
intros.
rewrite Heq in H.
rewrite length_cons in H.
exact (Arith_prebase.lt_S_n _ _ H).
Qed.

Lemma nth_in_nil : forall [A : Type] (l : list A) (n : nat) (Heq : l = []), ~(n < length l).
Proof.
intros.
intro H.
rewrite Heq in H.
rewrite length_nil in H.
elim (Nat.nlt_0_r n H).
Qed.

Fixpoint nth_in [A : Type] (l : list A) (n : nat) : n < length l -> A :=
  match destruct_list l with
  | inleft (existT _ t (exist _ q Htq)) => match n with
                                           | O    => (fun H => t)
                                           | S n' => (fun H => nth_in q n' (length_nth_in_cons_tl t q l n' Htq H))
                                           end
  | inright Hnil                        => (fun H => False_rect A (nth_in_nil l n Hnil H))
  end.

Lemma nth_in_nth_error : forall [A : Type] (l : list A) (n : nat) (Hn : n < length l), 
  nth_error l n = Some (nth_in l n Hn).
Proof.
intros A l.
pattern l.
apply list_ind.
+ intros n Hn.
  cut False; [ contradiction | ].
  rewrite length_nil in Hn.
  exact (Nat.nlt_0_r n Hn).
+ intros t q IHq n.
  destruct n as [ | n' ].
  - intro Hn.
    simpl.
    destruct destruct_list as [ (t', (q', Htq')) | Hnil ].
    * rewrite nth_error_cons_hd.
      destruct (injective_cons Htq'); subst.
      reflexivity.
    * eelim nil_cons.
      symmetry.
      apply Hnil.
  - intro Hn.
    simpl.
    destruct destruct_list as [ (t', (q', Htq')) | Hnil ].
    * rewrite nth_error_cons_tl.
      destruct (injective_cons Htq'); subst.
      erewrite (IHq n').
      reflexivity.
    * eelim nil_cons.
      symmetry.
      apply Hnil.
Qed.

Lemma nth_in_cons_hd : forall [A : Type] (t : A) (q : list A) (H : 0 < length (t::q)),
  nth_in (t::q) 0 H = t.
Proof.
intros.
simpl.
destruct destruct_list as [ (t', (q', Htq)) | Hnil ].
+ destruct (injective_cons Htq); subst.
  reflexivity.
+ eelim nil_cons.
  symmetry.
  apply Hnil.
Qed.

Lemma nth_in_cons_tl : forall [A : Type] (t : A) (q : list A) n (Hn : n < length q) (HSn : S n < length (t::q)),
  nth_in (t::q) (S n) HSn = nth_in q n Hn.
Proof.
intros.
simpl.
destruct destruct_list as [ (t', (q', Htq)) | Hnil ].
+ destruct (injective_cons Htq); subst.
  rewrite (proof_irrelevance _ _ Hn).
  reflexivity.
+ eelim nil_cons.
  symmetry.
  apply Hnil.
Qed.

Lemma nth_in_in : forall [A : Type] (l : list A) (n : nat) (Hn : n < length l), 
  In (nth_in l n Hn) l.
Proof.
intros A l.
pattern l.
apply list_ind.
+ intros n Hn.
  elim (Nat.nlt_0_r n).
  rewrite length_nil in Hn.
  exact Hn.
+ intros t q IHq n Hn.
  destruct n as [ | n' ].
  - rewrite nth_in_cons_hd.
    apply in_eq.
  - apply in_cons.
    assert (n' < length q) as Hn'.
    * rewrite length_cons in Hn.
      exact (Arith_prebase.lt_S_n _ _ Hn).
    * erewrite nth_in_cons_tl.
      instantiate (1 := Hn').
      apply IHq.
Qed.

Lemma nth_error_position_in : forall {A} (eqA : dec_eq A) (a : A) (l : list A),
  In a l -> nth_error l (position eqA a l) = Some a.
Proof.
intros A eqA a l.
pattern l.
apply list_ind.
+ intro H.
  elim (in_nil _ H).
+ intros t q IHq Htq.
  destruct (eqA a t).
  - subst.
    rewrite position_cons_hd.
    rewrite nth_error_cons_hd.
    reflexivity.
  - destruct (in_inv _ _ _ Htq).
    * symmetry in H.
      contradiction.
    * rewrite position_cons_tl.
      ++ rewrite nth_error_cons_tl.
         exact (IHq H).
      ++ assumption.
Qed.

Lemma nth_error_position_notin : forall {A} (eqA : dec_eq A) (a : A) (l : list A),
  ~In a l -> nth_error l (position eqA a l) = None.
Proof.
intros A eqA a l.
pattern l.
apply list_ind.
+ intros _.
  rewrite position_nil.
  rewrite nth_error_nil.
  reflexivity.
+ intros t q IHq Htq.
  destruct (eqA a t).
  - subst.
    elim (Htq (in_eq t q)).
  - rewrite position_cons_tl; [ | assumption].
    rewrite nth_error_cons_tl.
    apply IHq.
    intro H.
    apply Htq.
    apply in_cons.
    exact H.
Qed.

Lemma position_nth_in : forall [A : Type] (eqA : dec_eq A) (l : list A) (Hinj : NoDup l) (n : nat) (Hn : n < length l),
  position eqA (nth_in l n Hn) l = n.
Proof.
intros A eqA l.
pattern l.
apply list_ind.
+ intros _ n Hn.
  eelim (Nat.nlt_0_r n).
  rewrite length_nil in Hn.
  exact Hn.
+ intros t q IHq Htq n Hn.
  destruct n as [ | n' ].
  - rewrite nth_in_cons_hd.
    apply position_cons_hd.
  - assert (n' < length q) as Hn'.
    * rewrite length_cons in Hn.
      exact (Arith_prebase.lt_S_n _ _ Hn).
    * erewrite nth_in_cons_tl.
      instantiate (1 := Hn').
      generalize (nth_in_in q n' Hn').
      set (a := (@nth_in A q n' Hn')).
      intro Ha.
      inversion Htq.
      ++ elim (nil_cons H0).
      ++ destruct (injective_cons H); subst.
         destruct (eqA a t).
         -- subst.
            contradiction.
         -- rewrite position_cons_tl; [ | assumption ].
            apply f_equal.
            apply IHq.
            assumption.
Qed.

Definition InjectiveList { N : Type } (l : list N) := forall i j, i < length l -> nth_error l i = nth_error l j -> i = j.

Lemma sym_injective : forall A (lA : list A) i j (Hij : nth_error lA i = nth_error lA j), i < length lA -> j < length lA.
Proof.
intros A lA i j Hij Hi.
generalize (nth_error_Some lA i).
generalize (nth_error_Some lA j).
intros HlAj HlAi.
rewrite Hij in HlAi.
intuition.
Qed.

Lemma injective_nodup : forall A (lA : list A), InjectiveList lA -> NoDup lA.
Proof.
intros A lA.
pattern lA.
apply list_ind.
+ intros _; apply NoDup_nil.
+ intros t q IHq Htq.
  apply NoDup_cons.
  - intro Ha.
    destruct (In_nth_error _ _ Ha) as (i, Hi).
    assert (0 = S i); [ | discriminate].
    apply Htq.
    * rewrite length_cons.
      apply Nat.lt_0_succ.
    * symmetry.
      rewrite nth_error_cons_hd.
      rewrite nth_error_cons_tl.
      exact Hi.
  - apply IHq.
    intros i j Hi Hij.
    assert (S i = S j) as Hij'.
    * apply Htq.
      ++ rewrite length_cons.
         apply Arith_prebase.lt_n_S_stt.
         exact Hi.
      ++ rewrite nth_error_cons_tl.
         rewrite nth_error_cons_tl.
         exact Hij.
    * auto.
Qed.

Lemma nodup_injective : forall A (lA : list A), NoDup lA -> InjectiveList lA.
Proof.
intros A lA HA.
induction HA.
+ intros i j Hi.
  rewrite length_nil in Hi.
  elim (Nat.nlt_0_r _ Hi).
+ intros i j Hi Hij.
  destruct i as [|i']; destruct j as [|j'].
  - reflexivity.
  - symmetry in Hij.
    rewrite nth_error_cons_hd in Hij.
    rewrite nth_error_cons_tl in Hij.
    elim (H (nth_error_In _ _ Hij)).
  - rewrite nth_error_cons_hd in Hij.
    rewrite nth_error_cons_tl in Hij.
    elim (H (nth_error_In _ _ Hij)).
  - f_equal.
    apply IHHA.
    * rewrite length_cons in Hi.
      apply Arith_prebase.lt_S_n.
      exact Hi.
    * rewrite nth_error_cons_tl in Hij.
      rewrite nth_error_cons_tl in Hij.
      exact Hij.
Qed.

Lemma in_map_inv_exists : forall {A B} (f : A -> B) b (lA : list A), In b (map f lA) -> exists a, f a = b /\ In a lA.
Proof.
intros A B f b lA Hb.
apply in_map_iff.
exact Hb.
Qed.

End FullIter.