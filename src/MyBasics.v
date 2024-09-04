(** Basic definitions and facts
  Deals with
  - functions, 
  - (iterated) sequential and parallel composition,
  - void, unit, sum, product types
  - finite subsets [0..n) of nat
*)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import PeanoNat.
Require Import List.
Require Import Arith.
Require Import JMeq.


Set Warnings "-notation-overridden".

Definition decidable (P : Prop) := { P } + { ~P }.

Definition dec_eq A := forall (a a' : A), decidable (a = a').

Definition InjectiveXT { A B : Type } (f : A -> B) := forall x y, f x = f y -> x = y.

Definition SurjectiveXT { A B : Type } (f : A -> B) := forall b, { a : A | b = f a }.

Definition SurjectiveList { N : Type } (l : list N) := forall n : N, In n l.

Definition InjectiveXTList { N : Type } (l : list N) := forall i j, i < length l -> nth_error l i = nth_error l j -> i = j.

Inductive closure {N I O : Type} (p : (N+I) -> (N+O)) (ni : N+I) : (N+O) -> Prop :=
  | One  : closure p ni (p ni)
  | Add  : forall n', closure p ni (inl n') -> closure p ni (p (inl n')).

Definition FiniteChild {N I O} (p : N+I -> N+O) := forall n, Acc (fun n n' => p (inl n) = inl n') n.

Definition FiniteParent {N I O} (p : N+I -> N+O) := forall n, Acc (fun n' n => p (inl n) = inl n') n.

Definition Acyclic {N I O} (p : N+I -> N+O) := forall ni no, closure p ni no -> forall n, ni = inl n -> ~ no = inl n.

Lemma eq_sigT_intro : forall {A} {P : A -> Type} {x y : A} {Px : P x} (Hxy : x = y), 
  existT P x Px = existT P y (eq_rect x P Px y Hxy).
  Proof.
  intros A P x y Px Hxy.
  unfold eq_rect.
  destruct Hxy.
  reflexivity.
  Qed.

Lemma eq_rect_exist : forall {A B} {Q : A -> B -> Prop} {a a' : A} (Haa' : a = a') (b : B) (Hb : Q a b),
  @eq_rect A a (fun a => { b : B | Q a b}) (exist (Q a) b Hb) a' Haa' = exist (Q a') b (@eq_rect A a (fun a => Q a b) Hb a' Haa').
Proof.
intros A B Q a a' Haa' b Hb.
destruct Haa'.
simpl.
reflexivity.
Qed.

Lemma eq_rect_existT : forall {A B} {Q : A -> B -> Type} {a a' : A} (Haa' : a = a') (b : B) (Hb : Q a b),
                        @eq_rect A a (fun a => { b : B & Q a b}) (existT (Q a) b Hb) a' Haa' = existT (Q a') b (@eq_rect A a (fun a => Q a b) Hb a' Haa').
Proof.
intros A B Q a a' Haa' b Hb.
destruct Haa'.
simpl.
reflexivity.
Qed.

Lemma eq_rect_pi : forall {A} {P : A -> Type} {x y : A} {Px : P x} {H H' : x = y},
  eq_rect x P Px y H = eq_rect x P Px y H'.
  Proof.
  intros A P x y Px H H'.
  rewrite (proof_irrelevance (x = y) H H').
  reflexivity.
  Qed.

Lemma eq_rect_compose : forall {A} {P : A -> Type} {x y z : A} {Px : P x} {Hxy : x = y} {Hyz : y = z} {Hxz : x = z},
  eq_rect y P (eq_rect x P Px y Hxy) z Hyz = eq_rect x P Px z Hxz.
  Proof.
  intros A P x y z Px Hxy Hyz Hxz.
  unfold eq_rect.
  destruct Hxy.
  destruct Hyz.
  rewrite (proof_irrelevance (x = x) Hxz eq_refl).
  reflexivity.
  Qed.

Lemma eq_rect_map : forall {A B} {P : B -> Type} {f : A -> B} {a a' : A} {Pa : P (f a)} {Haa' : a = a'} {Hfaa' : f a = f a'},
  eq_rect a (fun a => P (f a)) Pa a' Haa' = eq_rect (f a) P Pa (f a') Hfaa'.
  Proof.
  intros A B P f a a' Pa Haa' Hfaa'.
  unfold eq_rect.
  destruct Haa'.
  rewrite (proof_irrelevance (f a = f a) Hfaa' eq_refl).
  reflexivity.
  Qed.

Lemma eq_rect_image_1 : forall {A} {P : A -> Type} {f : forall a, P a} {a a' : A} {Haa' : a = a'},
  @eq_rect A a P (f a) a' Haa' = f a'.
  Proof.
  intros A P f a a' Haa'.
  destruct Haa'.
  reflexivity.
  Qed.

Lemma eq_rect_image_2 : forall {A} {P Q : A -> Type} {f : forall a, (P a -> Q a)} {a a' : A} {Pa : P a} {Haa' : a = a'},
  @eq_rect A a Q (f a Pa) a' Haa' = f a' (@eq_rect A a P Pa a' Haa').
  Proof.
  intros A P Q f a a' Pa Haa'.
  destruct Haa'.
  reflexivity.
  Qed.

Definition lt_n_S_stt := fun n m => (proj1 (Nat.succ_lt_mono n m)).

Lemma injective_list_tl : forall A t (q : list A), 
  InjectiveXTList (t::q) -> InjectiveXTList q.
  Proof.
  intros A t q Htq i j Hi Hij.
  assert (S i = S j) as Heq; [ | injection Heq; auto ].
  apply Htq.
  + simpl.
    apply lt_n_S_stt.
    exact Hi.
  + simpl.
    exact Hij.
  Qed.

Lemma injective_list_hd : forall A t (q : list A), InjectiveXTList (t::q) -> ~In t q.
  Proof.
  intros A t q Hinj Hin.
  destruct (In_nth_error _ _ Hin) as (i, Hi).
  symmetry in Hi.
  generalize (Hinj 0 (S i) (Nat.lt_0_succ _) Hi).
  discriminate.
  Qed.

Lemma nodup_tl : forall {A} (t : A) (q : list A), NoDup (t::q) -> NoDup q.
  Proof.
  intros A t q Htq.
  inversion Htq.
  assumption.
  Qed.

Lemma in_map_inv : forall {A B} (f : A -> B) a (lA : list A), InjectiveXT f -> In (f a) (map f lA) -> In a lA.
  Proof.
  intros A B f a lA Hinjf Hfa.
  generalize (in_map_iff f lA (f a)).
  
  intros.
  destruct H.
  apply H in Hfa.
  destruct H. apply H0. apply Hfa.
  destruct H.
  rewrite <- (Hinjf x a H).
  assumption.
  Qed.

Lemma in_map_inv_exists : forall {A B} (f : A -> B) b (lA : list A), In b (map f lA) -> exists a, f a = b /\ In a lA.
  Proof.
  induction lA; simpl.
  + contradiction.
  + intros. destruct H.
    - exists a.
      auto.
    - apply IHlA in H.
      destruct H as (a', Ha').
      exists a'.
      destruct Ha'.
      split; auto.
  Qed.

Lemma nodup_map : forall {A B} (f : A -> B) (lA : list A), InjectiveXT f -> NoDup lA -> NoDup (map f lA).
  Proof.
  induction lA; simpl.
  + intros.
    apply NoDup_nil.
  + intros Hinjf HalA.
    inversion HalA; subst; clear HalA.
    apply NoDup_cons.
    intro Hin_fa.
    apply H1.
    apply (in_map_inv f a lA Hinjf).
    exact Hin_fa.
    apply (IHlA Hinjf).
    assumption.
  Qed.

Lemma nodup_app : forall {A} (l1 l2 : list A), NoDup l1 -> NoDup l2 -> Forall (fun a1 => ~In a1 l2) l1 -> NoDup (l1 ++ l2).
  Proof.
  induction l1; simpl.
  + auto.
  + intros l2 Hal1 Hl2 Hal1l2.
    inversion Hal1.
    subst.
    apply NoDup_cons.
    - intro Hal1l2'.
      destruct (in_app_or l1 l2 a Hal1l2').
      * contradiction.
      * inversion Hal1l2.
        contradiction.
    - apply IHl1.
      * assumption.
      * assumption.
      * inversion Hal1l2.
        assumption.
  Qed.

Lemma nodup_flat_map : forall {A B} (lA : list A) (f : A -> list B),
  NoDup lA -> (forall a, NoDup (f a)) -> (forall a1 a2, a1 <> a2 -> Forall (fun a1 => ~In a1 (f a2)) (f a1)) -> NoDup (flat_map f lA).
  Proof.
  intros A B lA f.
  induction lA; simpl.
  + intros.
    apply NoDup_nil.
  + intros HlA Hf1 Hf2.
    apply nodup_app.
    - apply Hf1.
    - apply IHlA.
      * inversion HlA.
        assumption.
      * exact Hf1.
      * exact Hf2.
    - apply Forall_Exists_neg.
      intro Hfa.
      generalize (Exists_exists (fun x : B => In x (flat_map f lA)) (f a)).
      intuition.
      clear H0.
      destruct H as (b, (Hb1, Hb2)).
      generalize (in_flat_map f lA b).
      intuition.
      clear H0.
      destruct H as (a', (Ha1', Ha2')).
      assert (a <> a') as Haa'.
      * inversion HlA.
        intro Haa'.
        subst.
        contradiction.
      * generalize (Hf2 a a' Haa').
        intro Hf.
        generalize (Forall_forall (fun a1 : B => In a1 (f a') -> False) (f a)).
        intuition.
        clear H0.
        apply (H b Hb1 Ha2').
  Qed.

Lemma nth_error_some : forall A (lA : list A) i (Hi : i < length lA), exists a, nth_error lA i = Some a.
  Proof.
  intros A lA i Hi.
  generalize (nth_error_Some lA i).
  intuition.
  destruct (nth_error lA i).
  + exists a.
    reflexivity.
  + elim H.
    reflexivity.
  Qed.

Lemma nth_error_none : forall A (lA : list A) i (Hi : length lA <= i), nth_error lA i = None.
  Proof.
  intros A lA i Hi.
  generalize (nth_error_None lA i).
  intuition.
  Qed.

Lemma dec_Forall : forall A (P : A -> Prop), (forall a, decidable (P a)) -> forall l, decidable (Forall P l).
  Proof.
  induction l; simpl.
  + left.
    auto.
  + destruct (X a).
    - destruct IHl.
      * left.
        auto.
      * right.
        intro H.
        apply n.
        inversion H.
        assumption.
    - right.
      intro H.
      apply n.
      inversion H.
      assumption.
  Qed.

Lemma dec_Exists : forall A (P : A -> Prop), (forall a, decidable (P a)) -> forall l, decidable (Exists P l).
  Proof.
  induction l; simpl.
  + right.
    intro H.
    inversion H.
  + destruct (X a).
    - left.
      auto.
    - destruct IHl.
      * left.
        auto.
      * right.
        intro H.
        inversion H.
        ++ contradiction.
        ++ contradiction.
  Qed.

Lemma injective_in_map_inv : forall A B (f : A -> B) a l, InjectiveXT f -> In (f a) (map f l) -> In a l.
  Proof.
  intros A B f a l Hinjf.
  induction l.
  + auto.
  + simpl.
    intuition.
  Qed.

Inductive void : Type := .

Definition void_univ_embedding' {A : Type} : void -> A.
  Proof.
  intro v.
  elim v.
  Defined.

Definition fin (n : nat) := { p | p < n }.

Theorem le_S_n' : forall n m : nat, S n <= S m -> n <= m.
Proof. {apply Nat.succ_le_mono. } Qed.

Theorem le_lt_or_eq_dec : forall {n m : nat}, n <= m -> { n = m } + { n < m }.
  Proof.
  induction n.
  destruct m.
  left.
  reflexivity.
  right.
  apply Nat.lt_0_succ.
  intros.
  destruct m.
  elim (Nat.nle_succ_0 _ H).
  destruct (IHn _ (le_S_n' _ _ H)).
  left.
  apply f_equal.
  assumption.
  right.
  rewrite <- Nat.succ_lt_mono.
  assumption.
  Qed.

Definition fin_0_univ_embedding {A : Type} : fin 0 -> A.
  Proof.
  intro f.
  destruct f as (p, Hp).
  elim (Nat.nlt_0_r p Hp).
  Defined.
Definition id {A : Type} := fun (x : A) => x.

Definition funcomp {A B C : Type} (f : B -> C) (g : A -> B) := fun x => f (g x).

Notation "f <o> g" := (funcomp f g) (at level 50).

Lemma funcomp_simpl : forall {A B C} (f : A -> B) (g : B -> C) a, (g <o> f) a = g (f a).
  Proof.
  reflexivity.
  Qed.

Lemma map_comp : forall A B C (f :A -> B) (g : B -> C), (map g) <o> (map f) = map (g <o> f).
  Proof.
  intros A B C f g.
  apply functional_extensionality.
  unfold funcomp, id.
  induction x; simpl.
  + reflexivity.
  + rewrite IHx.
    reflexivity.
  Qed.

Lemma map_id : forall A, map (@id A) = @id (list A).
  Proof.
  intros A.
  apply functional_extensionality.
  unfold id.
  induction x; simpl.
  + reflexivity.
  + rewrite IHx.
    reflexivity.
  Qed.

Theorem id_left_neutral : forall {A B : Type} (f : A -> B), id <o> f = f.
  Proof.
  intros A B f.
  reflexivity.
  Qed.

Theorem id_right_neutral : forall {A B : Type} (f : A -> B), f <o> id = f.
  Proof.
  intros A B f.
  reflexivity.
  Qed.

Theorem comp_assoc : forall {A B C D : Type} (h : A-> B) (g : B -> C) (f : C -> D), (f <o> g) <o> h = f <o> (g <o> h).
  Proof.
  intros.
  apply functional_extensionality.
  intros.
  reflexivity.
  Qed.

Theorem comp_left_simpl : forall {A B C : Type} (f : B -> C) (g h : A -> B), g = h -> f <o> g = f <o> h.
  Proof.
  intros.
  rewrite H.
  reflexivity.
  Qed.

Theorem comp_right_simpl : forall {A B C : Type} (f : A -> B) (g h : B -> C), g = h -> g <o> f = h <o> f.
  Proof.
  intros.
  rewrite H.
  reflexivity.
  Qed.

(** parallel is used to define the parent and link function of two juxtapositionned bigraphs *)
Definition parallel {A B C D : Type} (p : A -> B) (q : C -> D) (ac : A+C) : B+D :=
 match ac with
 | inl a => inl (p a)
 | inr c => inr (q c)
 end.

Definition parallel_bis {A B C D : Type} (p : A -> B) (q : C -> D) (ac : A+C) : B+D :=
  match ac with
  | inl a => inl (p a)
  | inr c => inr (q c)
  end.



Notation "f ||| g" := (parallel f g) (at level 67).
Theorem parallel_id : forall {A B : Type}, parallel id id = (id : A+B -> A+B).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as [ a | b].
  reflexivity.
  reflexivity.
  Qed.

Theorem parallel_compose : forall {A B C E F G : Type} (p : A -> B) (q : B -> C) (r : E -> F) (s : F -> G),
   (parallel q s) <o> (parallel p r) = parallel (q <o> p) (s <o> r).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as [a | e].
  reflexivity.
  reflexivity.
  Qed.

Definition product {A B C D : Type} (p : A -> B) (q : C -> D) (ac : A*C) : B*D :=
 match ac with
 | (a, c) => (p a, q c)
 end.

Theorem product_id : forall {A B : Type}, product id id = (id : A*B -> A*B).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as (a, b).
  reflexivity.
  Qed.

Theorem product_compose : forall {A B C E F G : Type} (p : A -> B) (q : B -> C) (r : E -> F) (s : F -> G),
   (product q s) <o> (product p r) = product (q <o> p) (s <o> r).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as (a, e).
  reflexivity.
  Qed.

Definition inject {P Q I M O : Type} : (P+Q)+I -> (P+I) + (Q+M) :=
 fun pqi =>
 match pqi with
 | inl (inl p) => inl (inl p)
 | inl (inr q) => inr (inl q)
 | inr i       => inl (inr i)
 end.


(* Definition extract {A B C : Type} : (A+C) -> (B+A)+C :=
 fun ac =>
 match ac with
 | inl a => inl (inr a)
 | inr c => inr c
 end.

Definition sequence {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O) : (P+Q)+I -> (P+Q)+O :=
 fun pqi =>
  match parallel pp pq (@inject P Q I M O pqi) with
  | inl (inl p) => inl (inl p)
  | inl (inr m) => extract (pq (inr m))
  | inr qo      => extract qo
  end. *)


Definition extract1 {E1 E2 O1 : Type} (eo : E1+O1) : (E1+E2)+O1 :=
 match eo with
 | inl e => inl (inl e)
 | inr o => inr o
 end.

Definition rearrange {P1 E1 E2 O1 I1: Type} (sl1 : P1+I1 -> E1+O1) (e_oi : E2+I1) : (E1+E2)+O1 :=
  match e_oi with 
  | inl e => inl (inr e)
  | inr oi => extract1 (sl1 (inr oi))
  end.

(* R2 = S1 *)
(* O2 = I1 *)
Definition sequence {P1 P2 E1 E2 O1 I1 I2 : Type} 
  (sl2 : P2+I2 -> E2+I1) (sl1 : P1+I1 -> E1+O1) 
    (p1p2i2 : (P1+P2)+I2) : (E1+E2)+O1 :=
  match p1p2i2 with 
  | inl (inl p1) => extract1 (sl1 (inl p1))
  | inl (inr p2) => rearrange sl1 (sl2 (inl p2))
  | inr i2 =>       rearrange sl1 (sl2 (inr i2))
  end. 

Definition switch_link {I P O E} (l: I + P -> O + E) (pi: P + I) : E + O :=
  match pi with  
  | inl p => 
    match l (inr p) with 
    | inl o => inr o
    | inr e => inl e
    end
  | inr i => 
    match l (inl i) with 
    | inl o => inr o
    | inr e => inl e
    end
  end.

  
(* Definition extract2 {O1 O2 E1 E2 : Type} (oe : O1+E1) : O1 + (E1+E2) :=
  match oe with
  | inl n => inl (inl n)
  | inr r => inr r
  end.

Definition rearrange2 {N1 S1 R1 N2 S2 : Type} (p1 : N1+S1 -> N1+R1) (n_rs : N2+S1) : (N1+N2)+R1 :=
  match n_rs with 
  | inl n => inl (inr n)
  | inr rs => extract1 (p1 (inr rs))
  end.

(* R2 = S1 *)
Definition sequence2 {N1 S1 R1 N2 S2 : Type} 
  (p2 : N2+S2 -> N2+S1) (p1 : N1+S1 -> N1+R1) 
    (n1n2s2 : (N1+N2)+S2) : (N1+N2)+R1 :=
  match n1n2s2 with 
  | inl (inl n1) => extract1 (p1 (inl n1))
  | inl (inr n2) => @rearrange N1 S1 R1 N2 S2 p1 (p2 (inl n2))
  | inr s2 =>       @rearrange N1 S1 R1 N2 S2 p1 (p2 (inr s2))
  end.  *)


Notation "f >> g" := (sequence f g) (at level 70).

Definition sequence_id {I : Type} : (void+I) -> (void+I) := fun x => x.

(* Theorem sequence_closure_left : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (p p' : P),
  closure (pp >> pq) (inl (inr p)) (inl (inr p')) -> closure pp (inl p) (inl p').
  Proof.
  intros P Q I M O pp pq p p'.  Admitted. 
  remember (inl (inl p')) as llp'.
  intro H.
  revert p' Heqllp'.
  induction H; intros.
  unfold sequence in Heqllp'.
  unfold parallel in Heqllp'.
  unfold inject in Heqllp'.
  case_eq (pp (inl p)); intros.
  rewrite H in Heqllp'.
  injection Heqllp'; intro; subst.
  rewrite <- H.
  apply One.
  rewrite H in Heqllp'.
  destruct (pq (inr m)).
  discriminate.
  discriminate.
  destruct n' as [p'' | q'].
  unfold sequence in Heqllp'.
  unfold parallel in Heqllp'.
  unfold inject in Heqllp'.
  case_eq (pp (inl p'')); intros.
  rewrite H0 in Heqllp'.
  injection Heqllp'; intro; subst.
  rewrite <- H0.
  apply Add.
  apply IHclosure.
  reflexivity.
  rewrite H0 in Heqllp'.
  destruct (pq (inr m)).
  discriminate.
  discriminate.
  unfold sequence in Heqllp'.
  unfold parallel in Heqllp'.
  unfold inject in Heqllp'.
  destruct (pq (inl q')).
  discriminate.
  discriminate.
  Qed. *)

Theorem sequence_closure_left_inv : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (p p' : P),
  closure pp (inl p) (inl p') -> closure (pp >> pq) (inl (inr p)) (inl (inr p')).
  Proof.
  intros P Q I M O pp pq p p'.
  remember (inl p') as lp'.
  intro H.
  revert p' Heqlp'.
  induction H; intros.
  assert ((pp >> pq) (inl (inr p)) = inl (inr p')).
  unfold sequence.
  unfold parallel.
  unfold inject.
  rewrite Heqlp'.
  reflexivity.
  rewrite <- H.
  apply One.
  assert ((pp >> pq) (inl (inr n')) = inl (inr p')).
  unfold sequence.
  unfold parallel.
  unfold inject.
  rewrite Heqlp'.
  reflexivity.
  rewrite <- H0.
  apply Add.
  apply IHclosure.
  reflexivity.
  Qed.

Theorem sequence_right : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q : Q),
  (pp >> pq) (inl (inl q)) = extract1 (pq (inl q)).
  Proof.
  intros.
  reflexivity.
  Qed.

(* Theorem sequence_closure_right_impossible : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q : Q) (p : P),
  ~closure (pp >> pq) (inl (inl q)) (inl (inr p)).
  Proof.
  intros.
  intro H.
  remember (inl (inr p)) as p'.
  revert p Heqp'.
  induction H; intros.
  unfold sequence in Heqp'.
  unfold parallel in Heqp'.
  unfold inject in Heqp'.
  unfold extract1 in Heqp'.
  destruct (pq (inl q)).
  discriminate.
  discriminate.
  destruct n' as [p' | q']. Admitted.
  apply (IHclosure p').
  reflexivity.
  unfold sequence in Heqp'.
  unfold parallel in Heqp'.
  unfold inject in Heqp'.
  unfold extract in Heqp'.
  destruct (pq (inl q')).
  discriminate.
  discriminate.
  Qed. *)

(* Theorem sequence_closure_right : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q q' : Q),
  closure (pp >> pq) (inl (inl q)) (inl (inl q')) -> closure pq (inl q) (inl q').
  Proof.
  intros P Q I M O pp pq q q'.
  remember (inl (inl q')) as lrq'.
  intro H.
  revert q' Heqlrq'.
  induction H; intros.
  unfold sequence in Heqlrq'.
  unfold parallel in Heqlrq'.
  unfold inject in Heqlrq'.
  unfold extract1 in Heqlrq'.
  case_eq (pq (inl q)); intros.
  rewrite H in Heqlrq'.
  injection Heqlrq'.
  clear Heqlrq'; intro; subst.
  rewrite <- H.
  apply One.
  rewrite H in Heqlrq'.
  discriminate.
  destruct n' as [p' | q'']. Admitted.
  elim (sequence_closure_right_impossible pp pq _ _ H). 
  rewrite sequence_right in Heqlrq'.
  unfold extract in Heqlrq'.
  revert Heqlrq'.
  case_eq (pq (inl q'')); intros.
  injection Heqlrq'.
  clear Heqlrq'; intro; subst.
  rewrite <- H0.
  eapply Add.
  apply IHclosure.
  reflexivity.
  discriminate.
  Qed. *)

(* Theorem sequence_closure_right_inv : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q q' : Q),
  closure pq (inl q) (inl q') -> closure (pp >> pq) (inl (inl q)) (inl (inl q')).
  Proof.
  intros P Q I M O pp pq q q'.
  remember (inl q') as lq'.
  intro H.
  revert q' Heqlq'.
  induction H; intros.
  generalize (sequence_right pp pq q); intro H.
  rewrite Heqlq' in H.
  simpl in H.
  rewrite <- H. Admitted.
  apply One.
  generalize (sequence_right pp pq n'); intro H'.
  rewrite Heqlq' in H'.
  simpl in H'.
  rewrite <- H'.
  apply Add.
  apply IHclosure.
  reflexivity.
  Qed. *)

Definition pair {A B C} (p : A -> B) (q : A -> C) : A -> B*C :=
 fun a => (p a, q a).

Definition choice {A B C} (p : A -> C) (q : B -> C) : A+B -> C :=
 fun ab => match ab with
  | inl a => p a
  | inr b => q b
 end.

Definition collapse {A} : A + A -> A := fun a => match a with inl a => a | inr a => a end.

Definition duplicate {A} : A -> A*A := fun a => (a, a).

(* Lemma pair_alt : forall {A B C} (p : A -> B) (q : A -> C), pair p q = (product p q) <o> duplicate.
  Proof.
  reflexivity.
  Qed.

Lemma choice_alt : forall {A B C} (p : A -> C) (q : B -> C), choice p q = collapse <o> (parallel p q).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x;reflexivity.
  Qed. *)

Definition tensor {P Q I O J L : Type} (pp : P+I -> P+O) (pq : Q+J -> Q+L) : (P+Q)+(I+J) -> (P+Q)+(O+L) :=
 fun pq_ij =>
  match pq_ij with
  | inl (inl p) => match pp (inl p) with
                   | inl p' => inl (inl p')
                   | inr o' => inr (inl o')
                   end
  | inl (inr q) => match pq (inl q) with
                   | inl q' => inl (inr q')
                   | inr l' => inr (inr l')
                   end
  | inr (inl i) => match pp (inr i) with
                   | inl p' => inl (inl p')
                   | inr o' => inr (inl o')
                   end
  | inr (inr j) => match pq (inr j) with
                   | inl q' => inl (inr q')
                   | inr l' => inr (inr l')
                   end
  end.

Notation "f ** g" := (tensor f g) (at level 65).

Theorem closure_transitive : forall {N I O : Type} (pp : N+I -> N+O) ni n' no,
  closure pp ni (inl n') -> closure pp (inl n') no -> closure pp ni no.
  Proof.
  intros N I O pp ni n'.
  remember (inl n') as m.
  remember (@inl N I n') as m'.
  intros no Hm Hm'.
  revert Hm n' Heqm Heqm' Hm.
  revert m.
  induction Hm'; intros.
  rewrite Heqm'.
  eapply Add.
  rewrite <- Heqm.
  exact Hm0.
  apply Add.
  eapply IHHm'.
  apply Hm0.
  apply Heqm.
  exact Heqm'.
  exact Hm.
  Qed.

Theorem closure_first_step : forall {N I O : Type} (pp : N+I -> N+O) ni  no,
  closure pp ni no -> pp ni = no \/ exists n' : N, pp ni = inl n' /\ closure pp (inl n') no.
  Proof.
  intros.
  induction H; intros.
  left.
  reflexivity.
  destruct IHclosure.
  right.
  exists n'.
  split.
  assumption.
  apply One.
  destruct H0.
  destruct H0.
  right.
  exists x.
  split.
  assumption.
  apply Add.
  assumption.
  Qed.

Theorem closure_last_step : forall {N I O : Type} (pp : N+I -> N+O) ni no,
  closure pp ni no -> pp ni = no \/ exists n' : N, pp (inl n') = no /\ closure pp ni (inl n').
  Proof.
  intros.
  inversion_clear H.
  left.
  reflexivity.
  right.
  exists n'.
  split.
  reflexivity.
  assumption.
  Qed.

Theorem acyclic_antisymmetric : forall {N I O : Type} (pp : N+I -> N+O) n,
  ~closure pp (inl n) (inl n) -> forall n', closure pp (inl n) (inl n') -> ~closure pp (inl n') (inl n).
  Proof.
  intros.
  intro.
  apply H.
  apply (closure_transitive pp _ n' _).
  assumption.
  assumption.
  Qed.

Theorem antisymmetric_acyclic : forall {N I O : Type} (pp : N+I -> N+O) n,
  (forall n', closure pp (inl n) (inl n') -> ~closure pp (inl n') (inl n)) -> ~closure pp (inl n) (inl n).
  Proof.
  intros.
  intro.
  apply (H n H0 H0).
  Qed.

(* Théorèmes faux 
  Theorem finite_parent_child : forall { N I O : Type} (pp : N+I -> N+O),
    FiniteParent pp -> FiniteChild pp.
  Proof.
  intros until pp.
  intro HC.
  intro n.
  induction (HC n) as (x,Hterm,Hind).
  case_eq (pp (inl x)).
  + intros p_x Hp_x.
    generalize (Hind p_x Hp_x).
    clear Hind; intro Hind_p_x.
    inversion Hind_p_x.
    exact (H x Hp_x).
  + intros o Ho.

  Qed.

  Theorem finite_child_parent : forall { N I O : Type} (pp : N+I -> N+O),
    FiniteChild pp -> FiniteParent pp.
  Proof.
  intros until pp.
  intro HC.
  intro n.
  induction (HC n) as (x,_,Hind).
  apply Acc_intro.

  Admitted.
  Qed.
*)

Theorem finite_child_acyclic : forall {N I O : Type} (pp : N+I -> N+O),
  FiniteChild pp -> forall n, ~closure pp (inl n) (inl n).
  Proof.
  unfold FiniteChild.
  intros N I O pp H n.
  induction (H n).
  intro H2.
  eelim H1.
  destruct (closure_last_step _ _ _ H2).
  apply H3.
  destruct H3.
  destruct H3.
  elim (H1 x0).
  assumption.
  eapply closure_transitive.
  rewrite <- H3.
  apply One.
  assumption.
  assumption.
  Qed.

Theorem finite_parent_acyclic : forall {N I O : Type} (pp : N+I -> N+O),
  FiniteParent pp -> forall n, ~closure pp (inl n) (inl n).
  Proof.
  unfold FiniteParent.
  intros N I O pp H n.
  induction (H n).
  intro H2.
  eelim H1.
  destruct (closure_first_step _ _ _ H2).
  apply H3.
  destruct H3.
  destruct H3.
  elim (H1 x0).
  assumption.
  eapply closure_transitive.
  apply H4.
  rewrite <- H3.
  apply One.
  assumption.
  Qed.

Theorem finite_child_tensor_left : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2) n1,
  Acc (fun n n' => p1 (inl n) = inl n') n1 -> Acc (fun n n' => (tensor p1 p2) (inl n) = inl n') (inl n1).
  Proof.
  intros until p2.
  intros n1 Hp1n1.
  induction Hp1n1 as (n1, _, Hindn1').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
    apply Hindn1'.
    simpl in Hn1'.
    destruct (p1 (inl n1')); congruence.
  + intro Hn2'.
    simpl in Hn2'.
    destruct (p2 (inl n2')); congruence.
  Qed.

Theorem finite_child_tensor_right : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2) n2,
  Acc (fun n n' => p2 (inl n) = inl n') n2 -> Acc (fun n n' => (tensor p1 p2) (inl n) = inl n') (inr n2).
  Proof.
  intros until p2.
  intros n2 Hp2n2.
  induction Hp2n2 as (n2, _, Hindn2').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
    simpl in Hn1'.
    destruct (p1 (inl n1')); congruence.
  + intro Hn2'.
    apply Hindn2'.
    simpl in Hn2'.
    destruct (p2 (inl n2')); congruence.
  Qed.

Theorem finite_child_tensor : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2),
  FiniteChild p1 -> FiniteChild p2 -> FiniteChild (tensor p1 p2).
  Proof.
  intros until p2.
  intros Hp1 Hp2 n.
  destruct n as [n1 | n2].
  + apply finite_child_tensor_left.
    apply Hp1.
  + apply finite_child_tensor_right.
    apply Hp2.
  Qed.

Theorem finite_parent_tensor_left : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2) n1,
  Acc (fun n' n => p1 (inl n) = inl n') n1 -> Acc (fun n' n => (tensor p1 p2) (inl n) = inl n') (inl n1).
  Proof.
  intros until p2.
  intros n1 Hp1n1.
  induction Hp1n1 as (n1, _, Hindn1').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
    apply Hindn1'.
    simpl in Hn1'.
    destruct (p1 (inl n1)); congruence.
  + intro Hn2'.
    simpl in Hn2'.
    destruct (p1 (inl n1)); congruence.
  Qed.

Theorem finite_parent_tensor_right : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2) n2,
  Acc (fun n' n => p2 (inl n) = inl n') n2 -> Acc (fun n' n => (tensor p1 p2) (inl n) = inl n') (inr n2).
  Proof.
  intros until p2.
  intros n2 Hp2n2.
  induction Hp2n2 as (n2, _, Hindn2').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
    simpl in Hn1'.
    destruct (p2 (inl n2)); congruence.
  + intro Hn2'.
    apply Hindn2'.
    simpl in Hn2'.
    destruct (p2 (inl n2)); congruence.
  Qed.

Theorem finite_parent_tensor : forall {N1 I1 O1 N2 I2 O2 : Type} (p1 : N1+I1 -> N1+O1) (p2 : N2+I2 -> N2+O2),
  FiniteParent p1 -> FiniteParent p2 -> FiniteParent (tensor p1 p2).
  Proof.
  intros until p2.
  intros Hp1 Hp2 n.
  destruct n as [n1 | n2].
  + apply finite_parent_tensor_left.
    apply Hp1.
  + apply finite_parent_tensor_right.
    apply Hp2.
  Qed.

Theorem finite_parent_inout : forall { N I O I' O' } (p : N+I -> N+O) (fi : I' -> I) (fo : O -> O'),
  FiniteParent p -> FiniteParent ((id ||| fo) <o> p <o> (id ||| fi)).
Proof.
intros N I O I' O' p fi fo H n.
induction (H n) as (n', _, Hind).
apply Acc_intro.
intros n'' Hn''.
unfold parallel, id, funcomp in Hn''.
generalize (Hind n''); clear Hind; intro Hind.
destruct (p (inl n')).
+ apply Hind.
  injection Hn''.
  congruence.
+ discriminate.
Qed.

(* Theorem acyclic_sequence : forall {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O),
  (forall p, ~closure pp (inl p) (inl p)) -> (forall q, ~closure pq (inl q) (inl q)) -> forall p_q, ~closure (pp >> pq) (inl p_q) (inl p_q).
  Proof.
  intros P Q I M O pp pq Hpp Hpq p_q Hp_q.
  destruct p_q as [p | q].
  elim (Hpq p). Admitted.
  (* eapply sequence_closure_left.
  eassumption.
  elim (Hpq q).
  eapply sequence_closure_right.
  eassumption.
  Qed. *)

Theorem finite_child_sequence_left : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n1,
  Acc (fun n n' => p1 (inl n) = inl n') n1 -> Acc (fun n n' => (sequence p1 p2) (inl n) = inl n') (inr n1).
  Proof.
  intros until p2.
  intros n1 Hp1n1.
  induction Hp1n1 as (n1, _, Hindn1').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'. Admitted.
    (* apply Hindn1'.
    unfold sequence in Hn1'.
    simpl in Hn1'.
    destruct (p1 (inl n1')).
    - congruence.
    - unfold extract in Hn1'.
      destruct (p2 (inr m)); congruence.
  + intro Hn2'.
    unfold sequence in Hn2'.
    simpl in Hn2'.
    unfold extract in Hn2'.
    destruct (p2 (inl n2')); congruence.
  Qed. *)

Theorem finite_child_sequence_right : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n2,
  FiniteChild p1 -> Acc (fun n n' => p2 (inl n) = inl n') n2 -> Acc (fun n n' => (sequence p1 p2) (inl n) = inl n') (inl n2).
  Proof.
  intros until p2.
  intros n2 Hp1 Hp2n2.
  induction Hp2n2 as (n2, _, Hindn2').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'. Admitted.
    (* apply finite_child_sequence_left.
    apply Hp1.
  + intro Hn2'.
    apply Hindn2'.
    unfold sequence in Hn2'.
    simpl in Hn2'.
    unfold extract in Hn2'.
    destruct (p2 (inl n2')); congruence.
  Qed. *)

Theorem finite_child_sequence : forall {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O),
  FiniteChild pp -> FiniteChild pq -> FiniteChild (sequence pp pq).
  Proof.
  intros until pq.
  intros Hpp Hpq n.
  destruct n as [np | nq].
  + apply finite_child_sequence_right.
    apply Hpp.
    apply Hpq.
  + apply finite_child_sequence_left.
    apply Hpp.
  Qed. *)

Theorem finite_parent_sequence_right : forall {N1 N2 S1 S2 R1 : Type} (p1 : N1+S1 -> N1+R1) (p2 : N2+S2 -> N2+S1) (n1:N1),
  Acc (fun n' n => p1 (inl n) = inl n') n1 -> Acc (fun n' n => (sequence p2 p1) (inl n) = inl n') (inl n1).
  Proof.
  intros until p2.
  intros n1 Hp1n1.
  induction Hp1n1 as (n1, _, Hindn1').
  apply Acc_intro.
  destruct y as [n1' | n2']. 
  + intro Hn1'.
    unfold sequence in Hn1'.
    unfold rearrange in Hn1'.
    unfold extract1 in Hn1'.
    destruct (p1 (inl n1)); apply Hindn1'. inversion Hn1'. f_equal. discriminate Hn1'.
  + intro Hn2'.
    unfold sequence in Hn2'.
    unfold rearrange in Hn2'.
    unfold extract1 in Hn2'.
    destruct (p1 (inl n1)).
    ++ discriminate Hn2'. 
    ++ discriminate Hn2'.
  Qed.

Theorem finite_parent_sequence_left : forall {N1 N2 S1 S2 R1 : Type} (p1 : N1+S1 -> N1+R1) (p2 : N2+S2 -> N2+S1) (n2:N2),
  Acc (fun n' n => p2 (inl n) = inl n') n2 -> FiniteParent p1 -> Acc (fun n' n => (sequence p2 p1) (inl n) = inl n') (inr n2).
  Proof.
  intros until p2.
  intros n2 Hp2n2 Hp1.
  induction Hp2n2 as (n2, _, Hindn2').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn2'.
    apply finite_parent_sequence_right.
    unfold sequence in Hn2'.
    unfold rearrange in Hn2'.
    unfold extract1 in Hn2'.
    destruct (p2 (inl n2)).
    - congruence.
    - apply Hp1.
  + intro Hn1'.
    apply Hindn2'.
    unfold sequence in Hn1'.
    unfold rearrange in Hn1'.
    unfold extract1 in Hn1'.
    destruct (p2 (inl n2)).
    - congruence.
    - destruct (p1 (inr s)); congruence.  
  Qed. 


Theorem finite_parent_sequence : forall {N1 N2 S1 S2 R1 : Type} (p1 : N1+S1 -> N1+R1) (p2 : N2+S2 -> N2+S1),
  FiniteParent p1 -> FiniteParent p2 -> FiniteParent (sequence p2 p1).
  Proof.
  intros until p2.
  intros Hp1 Hp2 n.
  destruct n as [n1 | n2].
  + apply finite_parent_sequence_right.
    apply Hp1.
  + apply finite_parent_sequence_left.
    apply Hp2.
    apply Hp1.
  Qed.



Lemma and_implies_or : 
  forall (A B : Prop), A /\ B -> A \/ B.
  Proof.
    intros A B H.
    destruct H as [Ha Hb].
    left.
    apply Ha.
  Qed.

