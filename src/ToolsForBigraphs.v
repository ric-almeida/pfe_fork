(*
  bigraph = structural forest + hypergraph
            + interfaces + transition rule
*)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import List.
Require Import Euclid.
Require Import Lists.List.
Require Import Arith.
Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Require Import MyBasics.
Import ListNotations. 

Set Warnings "-notation-overridden".

Section parametric.
  Variable T : Type.
Theorem nth_error_map : forall U (f : T -> U) ls n,
    nth_error (map f ls) n = match nth_error ls n with
                               | None => None
                               | Some x => Some (f x)
                             end.
  Proof.
    induction ls; destruct n; simpl; auto.
  Qed.


  End parametric.
Definition decidable (P : Prop) := { P } + { ~P }.

Definition InjectiveXT { A B : Type } (f : A -> B) := forall x y, f x = f y -> x = y.

Inductive closure {N I O : Type} (p : (N+I) -> (N+O)) (ni : N+I) : (N+O) -> Prop :=
| One  : closure p ni (p ni)
| Add  : forall n', closure p ni (inl n') -> closure p ni (p (inl n')).

Definition FiniteChild {N I O} (p : N+I -> N+O) := forall n, Acc (fun n n' => p (inl n) = inl n') n.

Definition FiniteParent {N I O} (p : N+I -> N+O) := forall n, Acc (fun n' n => p (inl n) = inl n') n.

Definition Acyclic {N I O} (p : N+I -> N+O) := forall ni no, closure p ni no -> forall n, ni = inl n -> ~ no = inl n.

Definition SurjectiveList { N : Type } (l : list N) := forall n : N, In n l.

Definition InjectiveXTList { N : Type } (l : list N) := forall i j, i < length l -> nth_error l i = nth_error l j -> i = j.

Definition Finite (N : Type) : Type := { l : list N | SurjectiveList l /\ InjectiveXTList l }.

Record forest (N I O : Type) : Type := mkForest
{
  parent  : (N + I) -> (N + O);
  acyclic : Acyclic parent;
  finite  : FiniteParent parent
}.

Inductive void : Type := .

Definition void_univ_embedding {A : Type} : void -> A.
Proof.
intro v.
elim v.
Defined.

Definition id {A : Type} := fun (x : A) => x.

Definition funcomp {A B C : Type} (f : B -> C) (g : A -> B) := fun x => f (g x).

Notation "f <o> g" := (funcomp f g) (at level 50).

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

Definition parallel {A B C D : Type} (p : A -> B) (q : C -> D) (ac : A+C) : B+D :=
 match ac with
 | inl a => inl (p a)
 | inr c => inr (q c)
 end.

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

Definition extract {A B C : Type} : (A+C) -> (B+A)+C :=
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
  end.

Notation "f >> g" := (sequence f g) (at level 70).

Definition sequence_id {I : Type} : (void+I) -> (void+I) := fun x => x.

Theorem sequence_closure_left : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (p p' : P),
                                  closure (pp >> pq) (inl (inl p)) (inl (inl p')) -> closure pp (inl p) (inl p').
Proof.
intros P Q I M O pp pq p p'.
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
Qed.

Theorem sequence_closure_left_inv : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (p p' : P),
                                  closure pp (inl p) (inl p') -> closure (pp >> pq) (inl (inl p)) (inl (inl p')).
Proof.
intros P Q I M O pp pq p p'.
remember (inl p') as lp'.
intro H.
revert p' Heqlp'.
induction H; intros.
assert ((pp >> pq) (inl (inl p)) = inl (inl p')).
unfold sequence.
unfold parallel.
unfold inject.
rewrite Heqlp'.
reflexivity.
rewrite <- H.
apply One.
assert ((pp >> pq) (inl (inl n')) = inl (inl p')).
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
                           (pp >> pq) (inl (inr q)) = extract (pq (inl q)).
Proof.
intros.
reflexivity.
Qed.

Theorem sequence_closure_right_impossible : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q : Q) (p : P),
                                             ~closure (pp >> pq) (inl (inr q)) (inl (inl p)).
Proof.
intros.
intro H.
remember (inl (inl p)) as p'.
revert p Heqp'.
induction H; intros.
unfold sequence in Heqp'.
unfold parallel in Heqp'.
unfold inject in Heqp'.
unfold extract in Heqp'.
destruct (pq (inl q)).
discriminate.
discriminate.
destruct n' as [p' | q'].
apply (IHclosure p').
reflexivity.
unfold sequence in Heqp'.
unfold parallel in Heqp'.
unfold inject in Heqp'.
unfold extract in Heqp'.
destruct (pq (inl q')).
discriminate.
discriminate.
Qed.

Theorem sequence_closure_right : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q q' : Q),
                                   closure (pp >> pq) (inl (inr q)) (inl (inr q')) -> closure pq (inl q) (inl q').
Proof.
intros P Q I M O pp pq q q'.
remember (inl (inr q')) as lrq'.
intro H.
revert q' Heqlrq'.
induction H; intros.
unfold sequence in Heqlrq'.
unfold parallel in Heqlrq'.
unfold inject in Heqlrq'.
unfold extract in Heqlrq'.
case_eq (pq (inl q)); intros.
rewrite H in Heqlrq'.
injection Heqlrq'.
clear Heqlrq'; intro; subst.
rewrite <- H.
apply One.
rewrite H in Heqlrq'.
discriminate.
destruct n' as [p' | q''].
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
Qed.

Theorem sequence_closure_right_inv : forall {P Q I M O : Type} (pp : P+I ->P+M) (pq : Q+M -> Q+O) (q q' : Q),
                                       closure pq (inl q) (inl q') -> closure (pp >> pq) (inl (inr q)) (inl (inr q')).
Proof.
intros P Q I M O pp pq q q'.
remember (inl q') as lq'.
intro H.
revert q' Heqlq'.
induction H; intros.
generalize (sequence_right pp pq q); intro H.
rewrite Heqlq' in H.
simpl in H.
rewrite <- H.
apply One.
generalize (sequence_right pp pq n'); intro H'.
rewrite Heqlq' in H'.
simpl in H'.
rewrite <- H'.
apply Add.
apply IHclosure.
reflexivity.
Qed.

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



Record bijection (A B : Type) := mkBijection
{
 forward  : A -> B;
 backward : B -> A;
 fob_id   : forward <o> backward = id;
 bof_id   : backward <o> forward = id;
}.


Definition bijection_inv {A B} (bij : bijection A B) : bijection B A :=
 (mkBijection B A (bij.(backward A B)) (bij.(forward A B)) (bij.(bof_id A B)) (bij.(fob_id A B))).


Definition bijection_id {A} : bijection A A :=
 (mkBijection A A id id eq_refl eq_refl).

Theorem bij_void_sum_neutral : forall {A}, bijection (void+A) A.
Proof.
intro A.
apply (mkBijection (void+A) A
        (fun va => match va with | inr a => a | inl v => match v with end end)
        (fun a => inr a)).
apply functional_extensionality.
intro x.
reflexivity.
apply functional_extensionality.
destruct x.
elim v.
reflexivity.
Defined.

Theorem bij_sum_comm : forall {A B}, bijection (A+B) (B+A).
Proof.
intros A B.
apply (mkBijection (A+B) (B+A)
        (fun ab => match ab with | inr b => inl b | inl a => inr a end)
        (fun ab => match ab with | inr b => inl b | inl a => inr a end)).
apply functional_extensionality.
destruct x; reflexivity.
apply functional_extensionality.
destruct x; reflexivity.
Defined.

Theorem bij_sum_assoc : forall {A B C}, bijection ((A+B)+C) (A+(B+C)).
Proof.
intros A B C.
apply (mkBijection ((A+B)+C) (A+(B+C))
        (fun ab_c => match ab_c with | inl (inl a) => inl a | inl (inr b) => inr (inl b) | inr c => inr (inr c) end)
        (fun a_bc => match a_bc with | inl a => inl (inl a) | inr (inl b) => inl (inr b) | inr (inr c) => inr c end)).
apply functional_extensionality.
destruct x as [a | [b | c]].
reflexivity.
reflexivity.
reflexivity.
apply functional_extensionality.
destruct x as [[a | b] | c].
reflexivity.
reflexivity.
reflexivity.
Defined.

Theorem bij_void_prod_absorbing : forall {A : Type}, bijection (void*A) void.
Proof.
intros.
apply (mkBijection (void*A) void (fun va => match va with (v, a) => void_univ_embedding v end) void_univ_embedding).
apply functional_extensionality.
destruct x.
apply functional_extensionality.
destruct x as ([], _).
Defined.

Theorem bij_unit_prod_neutral : forall {A}, bijection (unit*A) A.
Proof.
intro A.
apply (mkBijection (unit*A) A
        (fun va => match va with (u, a) => a end)
        (fun a => (tt, a))).
apply functional_extensionality.
intro x.
reflexivity.
apply functional_extensionality.
destruct x.
elim u.
reflexivity.
Defined.

Theorem bij_prod_comm : forall {A B}, bijection (A*B) (B*A).
Proof.
intros A B.
apply (mkBijection (A*B) (B*A)
        (fun ab => match ab with (a, b) => (b, a) end)
        (fun ab => match ab with (a, b) => (b, a) end)).
apply functional_extensionality.
destruct x; reflexivity.
apply functional_extensionality.
destruct x; reflexivity.
Defined.

Theorem bij_prod_assoc : forall {A B C}, bijection ((A*B)*C) (A*(B*C)).
Proof.
intros A B C.
apply (mkBijection ((A*B)*C) (A*(B*C))
        (fun ab_c => match ab_c with ((a, b), c) => (a, (b, c)) end)
        (fun a_bc => match a_bc with (a, (b, c)) => ((a, b), c) end)).
apply functional_extensionality.
destruct x as (a, (b, c)).
reflexivity.
apply functional_extensionality.
destruct x as ((a, b), c).
reflexivity.
Defined.

Theorem bij_distrib : forall {A B C}, bijection (A*(B+C)) (A*B+A*C).
Proof.
intros A B C.
apply (mkBijection (A*(B+C)) (A*B+A*C)
        (fun ab_c  => match ab_c  with | (a, inl b) => inl (a, b) | (a, inr c) => inr (a, c) end)
        (fun ab_ac => match ab_ac with | inl (a, b) => (a, inl b) | inr (a, c) => (a, inr c) end)).
apply functional_extensionality.
destruct x as [(a, b) | (a, c)].
reflexivity.
reflexivity.
apply functional_extensionality.
destruct x as (a, [ b | c]).
reflexivity.
reflexivity.
Defined.

Theorem bij_compose : forall {A B C}, bijection B C -> bijection A B -> bijection A C.
Proof.
intros A B C bij_BC bij_AB.
apply (mkBijection A C (bij_BC.(forward B C) <o> bij_AB.(forward A B)) (bij_AB.(backward A B) <o> bij_BC.(backward B C))).
rewrite -> comp_assoc.
rewrite <- (comp_assoc (backward B C bij_BC)).
rewrite bij_AB.(fob_id A B).
rewrite id_left_neutral.
apply bij_BC.(fob_id B C).
rewrite -> comp_assoc.
rewrite <- (comp_assoc (forward A B bij_AB)).
rewrite bij_BC.(bof_id B C).
rewrite id_left_neutral.
apply bij_AB.(bof_id A B).
Defined.

Notation "f <O> g" := (bij_compose f g)( at level 60).

Require Import ProofIrrelevance.

Theorem bij_eq : forall {A B} (bij1 bij2 : bijection A B), bij1.(forward A B) = bij2.(forward A B) -> bij1.(backward A B) = bij2.(backward A B) -> bij1 = bij2.
Proof.
intros.
destruct bij1.
destruct bij2.
simpl in * |- *.
subst.
rewrite (proof_irrelevance _ fob_id0 fob_id1).
rewrite (proof_irrelevance _ bof_id0 bof_id1).
reflexivity.
Qed.

Theorem bij_id_left_neutral : forall {A B} (bij_AB : bijection A B), bijection_id <O> bij_AB = bij_AB.
Proof.
intros.
destruct bij_AB.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_id_right_neutral : forall {A B} (bij_AB : bijection A B), bij_AB <O> bijection_id = bij_AB.
Proof.
intros.
destruct bij_AB.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_assoc : forall {A B C D} (bij_AB : bijection A B) (bij_BC : bijection B C) (bij_CD : bijection C D),
                      (bij_CD <O> bij_BC) <O> bij_AB = bij_CD <O> (bij_BC <O> bij_AB).
Proof.
intros.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_involution : forall {A B} (bij_AB : bijection A B), bijection_inv (bijection_inv bij_AB) = bij_AB.
Proof.
intros.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_inv_left_simpl : forall {A B} (bij_AB : bijection A B), bijection_inv bij_AB <O> bij_AB = bijection_id.
Proof.
intros.
destruct bij_AB.
unfold bij_compose.
apply bij_eq.
assumption.
assumption.
Qed.

Theorem bij_inv_right_simpl : forall {A B} (bij_AB : bijection A B), bij_AB <O> bijection_inv bij_AB = bijection_id.
Proof.
intros.
destruct bij_AB.
unfold bij_compose.
apply bij_eq.
assumption.
assumption.
Qed.

Theorem bij_inv_comp : forall {A B C} (bij_AB : bijection A B) (bij_BC : bijection B C),
                        bijection_inv (bij_BC <O> bij_AB) = (bijection_inv bij_AB) <O> (bijection_inv bij_BC).
Proof.
intros.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Definition bij_sum_compose : forall {A B C D : Type}, bijection A B -> bijection C D -> bijection (A+C) (B+D).
Proof.
intros A B C D bij_AB bij_CD.
apply (mkBijection (A+C) (B+D) (parallel bij_AB.(forward A B) bij_CD.(forward C D)) (parallel bij_AB.(backward A B) bij_CD.(backward C D))).
rewrite parallel_compose.
rewrite bij_AB.(fob_id A B).
rewrite bij_CD.(fob_id C D).
apply parallel_id.
rewrite parallel_compose.
rewrite bij_AB.(bof_id A B).
rewrite bij_CD.(bof_id C D).
apply parallel_id.
Defined.

Notation "f <+> g" := (bij_sum_compose f g) (at level 70).

Theorem bij_inv_sum :forall {A B C D : Type} (bij_AB : bijection A B) (bij_CD : bijection C D),
                      bijection_inv (bij_AB <+> bij_CD) = ((bijection_inv bij_AB) <+> (bijection_inv bij_CD)).
Proof.
intros A B C D bij_AB bij_CD.
destruct bij_AB.
destruct bij_CD.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Definition bij_prod_compose : forall {A B C D : Type}, bijection A B -> bijection C D -> bijection (A*C) (B*D).
Proof.
intros A B C D bij_AB bij_CD.
apply (mkBijection (A*C) (B*D) (product bij_AB.(forward A B) bij_CD.(forward C D)) (product bij_AB.(backward A B) bij_CD.(backward C D))).
rewrite product_compose.
rewrite bij_AB.(fob_id A B).
rewrite bij_CD.(fob_id C D).
apply product_id.
rewrite product_compose.
rewrite bij_AB.(bof_id A B).
rewrite bij_CD.(bof_id C D).
apply product_id.
Defined.

Notation "f <*> g" := (bij_prod_compose f g) (at level 65).

Theorem bij_inv_prod :forall {A B C D : Type} (bij_AB : bijection A B) (bij_CD : bijection C D),
                      bijection_inv (bij_AB <*> bij_CD) = ((bijection_inv bij_AB) <*> (bijection_inv bij_CD)).
Proof.
intros A B C D bij_AB bij_CD.
destruct bij_AB.
destruct bij_CD.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

(******** Section Cecile ********)
Lemma bijection_forward_equals_inv_backward {A B} (bij : bijection A B) :
    bij.(forward A B) = (bijection_inv bij).(backward B A).
    Proof. unfold bijection_inv. simpl. reflexivity. Qed.

  Lemma bijection_forward_inv_equals_backward {A B} (bij : bijection A B) :
    (bijection_inv bij).(forward B A) = bij.(backward A B).
    Proof. unfold bijection_inv. simpl. reflexivity. Qed.
  
  Lemma bof_a_eq_a {A B} (bij : bijection A B) (a:A) :
    a = backward A B bij (forward A B bij a).
    Proof. change (a = (backward A B bij <o> forward A B bij) a). rewrite (bof_id A B bij). 
    unfold id. reflexivity. Qed.

  Lemma fob_a_eq_a {A B} (bij : bijection A B) (b:B) :
    b = forward A B bij (backward A B bij b).
    Proof. change (b = (forward A B bij <o> backward A B bij) b). rewrite (fob_id A B bij). 
    unfold id. reflexivity. Qed. 

  Theorem bij_preserve_equality {A B} (bij : bijection A B) (x:A) (y:A) :
    x = y <-> bij.(forward A B) x = bij.(forward A B) y.
    Proof. split.
    - intros. rewrite H. reflexivity.
    - intros. 
      set (x' := bij.(forward A B) x).
      assert (x = bij.(backward A B) x').
      + change (x = backward A B bij (bij.(forward A B) x)). apply bof_a_eq_a.
      + rewrite H0 in H. rewrite <- fob_a_eq_a in H.
        rewrite H in H0. rewrite <- (@bof_a_eq_a A B bij) in H0. apply H0. Qed.
  
  (* Theorem bij_preserve_equality {A} (bij : bijection A A) (a:A) (b:A) :
    a = b <-> bij.(forward A A) a = bij.(forward A A) b.
    Proof. split.
    - intros. rewrite H. reflexivity.
    - intros. 
      set (x := bij.(forward A A) a).
      assert (a = bij.(backward A A) x).
      + change (a = backward A A bij (bij.(forward A A) a)). apply bof_a_eq_a.
      + rewrite H0 in H. rewrite <- fob_a_eq_a in H.
        rewrite H in H0. rewrite <- (@bof_a_eq_a A A bij) in H0. apply H0. Qed.
     *)
  Lemma fx_eq_by {A B} (bij:bijection A B) (a:A) (b:B) :
    a = backward A B bij b <-> b = forward A B bij a.
    Proof. split.
    - intros. rewrite H. apply fob_a_eq_a. 
    - intros. rewrite H. apply bof_a_eq_a. Qed. 

(**********************)


Definition fin (n : nat) := { p | p < n }.

Require Import PeanoNat.
Require Import Lia.

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

Theorem bij_fin_zero : bijection (fin 0) void.
Proof.
apply (mkBijection (fin 0) void fin_0_univ_embedding void_univ_embedding).
apply functional_extensionality.
intro v.
elim v.
apply functional_extensionality.
intro x.
destruct x as (p, Hp).
elim (Nat.nlt_0_r p Hp).
Defined.

Theorem lt_S_n' : forall n m : nat, S n < S m -> n < m. 
Proof. apply Nat.succ_lt_mono. Qed. 

Theorem bij_fin_one : bijection (fin 1) unit.
Proof.
apply (mkBijection (fin 1) unit (fun _ => tt) (fun _ => exist _ 0 (Nat.lt_succ_diag_r 0))).
apply functional_extensionality.
destruct x.
reflexivity.
apply functional_extensionality.
destruct x as (zero, Hzero).
unfold funcomp.
unfold id.
apply subset_eq_compat.
destruct zero.
reflexivity.
elim (Nat.nlt_0_r _ (lt_S_n' _ _ Hzero)).
Defined.

Definition inj_fin_two (f : fin 2) : bool.
destruct f as ([ | _], _).
exact true.
exact false.
Defined.

Definition surj_fin_two (b : bool) : fin 2.
case b.
exists 0.
exact Nat.lt_0_2.
exists 1.
exact Nat.lt_1_2.
Defined.

Theorem bij_fin_two : bijection (fin 2) bool.
Proof.
apply (mkBijection (fin 2) bool inj_fin_two surj_fin_two).
unfold inj_fin_two.
unfold surj_fin_two.
unfold funcomp.
unfold id.
apply functional_extensionality.
destruct x.
reflexivity.
reflexivity.
apply functional_extensionality.
destruct x as ([ | k], Hk).
apply subset_eq_compat.
reflexivity.
apply subset_eq_compat.
destruct k.
reflexivity.
elim (Nat.nlt_0_r _ (lt_S_n' _ _ (lt_S_n' _ _ Hk))).
Defined.

Theorem bij_bool : bijection bool (unit+unit).
Proof.
apply (mkBijection bool (unit+unit) (fun b => match b with true => inl tt | false => inr tt end) (fun uu => match uu with inl _ => true | inr _ => false end)).
apply functional_extensionality.
destruct x as [() | ()].
reflexivity.
reflexivity.
apply functional_extensionality.
destruct x.
reflexivity.
reflexivity.
Defined.

Definition inj_fin_Sn {n : nat} (f : fin (S n)) : unit + fin n.
Proof.
destruct f as ([ | p], Hp).
left.
exact tt.
right.
exists p.
apply lt_S_n'.
exact Hp.
Defined.

Definition surj_fin_Sn {n : nat} (f : unit + fin n) : fin (S n).
Proof.
destruct f as [u | (p, Hp)].
exists 0.
apply Nat.lt_0_succ.
exists (S p).
rewrite <- Nat.succ_lt_mono.
exact Hp.
Defined.

Theorem bij_fin_Sn : forall {n : nat}, bijection (fin (S n)) (unit + fin n).
Proof.
intro n.
apply (mkBijection (fin (S n)) (unit + fin n) inj_fin_Sn surj_fin_Sn).
apply functional_extensionality.
destruct x as [() | (p, Hp)].
reflexivity.
unfold inj_fin_Sn.
unfold surj_fin_Sn.
unfold funcomp.
unfold id.
apply f_equal.
apply subset_eq_compat.
reflexivity.
apply functional_extensionality.
destruct x as ([ | p], Hp).
unfold inj_fin_Sn.
unfold surj_fin_Sn.
unfold funcomp.
unfold id.
apply subset_eq_compat.
reflexivity.
unfold inj_fin_Sn.
unfold surj_fin_Sn.
unfold funcomp.
unfold id.
apply subset_eq_compat.
reflexivity.
Defined.

Require Import Orders.

Definition inj_fin_add {n p : nat} (f : fin (n+p)) : fin n + fin p.
Proof.
destruct f as (k, Hk).
destruct (Nat.ltb_spec0 k n).
left.
exists k.
assumption.
right.
exists (k - n).
lia.
Defined.

Definition surj_fin_add {n p : nat} (f : fin n + fin p) : fin (n + p).
Proof.
destruct f as [(k, Hk) | (k, Hk)].
exists k.
lia.
exists (n + k).
lia.
Defined.

Theorem bij_fin_sum : forall {n p :nat}, bijection (fin (n+p)) ((fin n)+(fin p)).
Proof.
intros n p.
apply (mkBijection _ _ inj_fin_add surj_fin_add).
apply functional_extensionality.
unfold inj_fin_add.
unfold surj_fin_add.
unfold funcomp.
unfold id.
destruct x as [(k, Hk) | (k, Hk)].
destruct (Nat.ltb_spec0 k n).
apply f_equal.
apply subset_eq_compat.
reflexivity.
destruct (Nat.ltb_spec0 (n + k) n).
contradiction.
contradiction.
destruct (Nat.ltb_spec0 (n + k) n).
lia.
apply f_equal.
apply subset_eq_compat.
lia.
apply functional_extensionality.
unfold inj_fin_add.
unfold surj_fin_add.
unfold funcomp.
unfold id.
destruct x as (k, Hk).
destruct (Nat.ltb_spec0 k n).
apply subset_eq_compat.
reflexivity.
apply subset_eq_compat.
lia.
Defined.

Definition inj_fin_mul {n p : nat} (f : fin (n*p)) : fin n * fin p.
Proof.
destruct f as (k, Hk).
split.
exists (k / p).
apply Nat.Div0.div_lt_upper_bound.
rewrite Nat.mul_comm.
assumption.

exists (k mod p).
apply Nat.mod_upper_bound.
intro H.
rewrite H in Hk.
apply (Nat.nlt_0_r k).
rewrite (mult_n_O n).
assumption.
Defined.

Definition surj_fin_mul {n p : nat} (f : fin n * fin p) : fin (n * p).
Proof.
destruct f as ((d, Hd), (m, Hm)).
exists (d * p + m).
assert (1 + d <= n).
exact Hd.
apply Nat.lt_le_trans with (m := d*p+1*p).
apply Nat.add_lt_mono_l.
simpl.
rewrite Nat.add_0_r.
exact Hm.
rewrite <- Nat.mul_add_distr_r.
apply Nat.mul_le_mono_r.
rewrite Nat.add_comm.
exact H.
Defined.

Theorem le_plus_minus' : forall n m : nat, n <= m -> m = n + (m - n).
Proof. 
intros. simpl. rewrite Nat.add_comm. 
rewrite Nat.sub_add; auto. 
Qed.

Theorem bij_fin_prod : forall {n p :nat}, bijection (fin (n*p)) ((fin n)*(fin p)).
Proof.
intros n p.
apply (mkBijection _ _ inj_fin_mul surj_fin_mul).
apply functional_extensionality.
unfold inj_fin_mul.
unfold surj_fin_mul.
unfold funcomp.
unfold id.
destruct x as ((a, Ha), (b, Hb)).
assert (forall P Q (a b : P) (c d : Q), a=b -> c=d -> (a,c)=(b,d)).
intros; subst; reflexivity.
apply H.
apply subset_eq_compat.
rewrite Nat.div_add_l.
assert (b / p = 0).
apply Nat.div_small.
exact Hb.
rewrite H0.
apply Nat.add_0_r.
intro Hp; rewrite Hp in Hb.
elim (Nat.nlt_0_r _ Hb).
apply subset_eq_compat.
rewrite Nat.add_comm.
rewrite Nat.Div0.mod_add.
apply Nat.mod_small.
exact Hb.
apply functional_extensionality.
unfold inj_fin_mul.
unfold surj_fin_mul.
unfold funcomp.
unfold id.
destruct x as (a, Ha).
apply subset_eq_compat.
rewrite Nat.Div0.mod_eq.
rewrite Nat.mul_comm.
rewrite <- le_plus_minus'.
reflexivity.
apply Nat.Div0.mul_div_le.
Qed.
(*
induction n; intros.
simpl.
apply @bij_compose with (B := (void * fin p)%type).
apply bij_prod_compose.
apply bijection_inv.
apply bij_fin_zero.
apply bijection_id.
apply @bij_compose with (B := void).
apply bijection_inv.
apply bij_void_prod_absorbing.
apply bij_fin_zero.
simpl.
apply @bij_compose with (B := (fin p + fin (n*p))%type).
apply @bij_compose with (B := ((unit + fin n) * fin p)%type).
apply bij_prod_compose.
apply bijection_inv.
apply bij_fin_Sn.
apply bijection_id.
apply @bij_compose with (B := ((fin p*unit) + (fin p*fin n))%type).
apply @bij_compose with (B := (fin p * (unit + fin n))%type).
apply bij_prod_comm.
apply bijection_inv.
apply bij_distrib.
apply bij_sum_compose.
apply @bij_compose with (B := (unit * fin p)%type).
apply bij_prod_comm.
apply bijection_inv.
apply bij_unit_prod_neutral.
apply @bij_compose with (B := (fin n * fin p)%type).
apply bij_prod_comm.
apply IHn.
apply bij_fin_sum.
*)

Definition bij_transform {N M I O : Type} (bij : bijection N M) (f : N+I -> N+O) : M+I -> M+O :=
 (parallel bij.(forward N M) id) <o> f <o> (parallel bij.(backward N M) id).

Theorem bij_transform_bij_id : forall {N I O : Type} (f : N+I -> N+O), bij_transform bijection_id f = f.
Proof.
intros.
unfold bij_transform.
simpl.
rewrite parallel_id.
rewrite parallel_id.
reflexivity.
Qed.

Theorem bij_transform_bij_compose : forall {N M P I O : Type} (bij_NM : bijection N M) (bij_MP : bijection M P) (f : N+I -> N+O),
                                  bij_transform bij_MP (bij_transform bij_NM f) = bij_transform (bij_MP <O> bij_NM) f.
Proof.
intros.
destruct bij_NM.
destruct bij_MP.
unfold bij_transform.
simpl.
rewrite <- comp_assoc.
rewrite <- comp_assoc.
rewrite parallel_compose.
rewrite id_left_neutral.
rewrite comp_assoc.
apply comp_left_simpl.
apply parallel_compose.
Qed.

Theorem bij_transform_inv : forall {N M I O : Type} (bij_NM : bijection N M) (f : N+I -> N+O) (g : M+I -> M+O),
                              f = bij_transform (bijection_inv bij_NM) g -> bij_transform bij_NM f = g.
Proof.
intros.
rewrite H.
rewrite bij_transform_bij_compose.
rewrite bij_inv_right_simpl.
apply bij_transform_bij_id.
Qed.

Theorem bij_transform_id : forall {A I : Type} (bij_AA : bijection A A), bij_transform bij_AA id = (id : A+I -> A+I).
Proof.
intros.
destruct bij_AA.
unfold bij_transform.
simpl.
rewrite id_right_neutral.
rewrite parallel_compose.
rewrite fob_id0.
rewrite parallel_id.
reflexivity.
Qed.

Theorem bij_transform_sequence : forall {A B C D M I O : Type} (f : A+I -> A+M) (g : B+M -> B+O) (bij_AC : bijection A C) (bij_BD : bijection B D),
                                  (bij_transform bij_AC f) >> (bij_transform bij_BD g) = bij_transform (bij_AC <+> bij_BD) (f >> g).
Proof.
intros.
destruct bij_AC.
destruct bij_BD.
unfold bij_transform.
unfold parallel.
unfold sequence.
apply functional_extensionality.
destruct x as [[c | d] | i].
simpl.
unfold parallel.
unfold funcomp.
unfold id.
simpl.
destruct (f (inl (backward0 c))).
reflexivity.
unfold extract.
simpl.
destruct (g (inr m)).
reflexivity.
reflexivity.
unfold extract.
unfold parallel.
unfold funcomp.
simpl.
unfold parallel.
destruct (g (inl (backward1 d))).
reflexivity.
reflexivity.
unfold parallel.
unfold funcomp.
unfold id.
simpl.
destruct (f (inr i)).
reflexivity.
unfold extract.
destruct (g (inr m)).
reflexivity.
reflexivity.
Qed.

Theorem sequence_id_left_neutral : forall {N I O} (f : N+I -> N+O),
                                    sequence_id >> f = bij_transform (bijection_inv bij_void_sum_neutral) f.
Proof.
intros.
apply functional_extensionality.
destruct x as [[v | n] | i].
elim v.
reflexivity.
reflexivity.
Qed.

Theorem sequence_id_right_neutral : forall {N I O} (f : N+I -> N+O),
                                     f >> sequence_id = bij_transform (bij_sum_comm <O> (bijection_inv bij_void_sum_neutral)) f.
Proof.
intros.
apply functional_extensionality.
destruct x as [[n | v] | i].
reflexivity.
elim v.
reflexivity.
Qed.

Theorem sequence_assoc : forall {A B C I O P Q} (f : A+I -> A+O) (g : B+O -> B+P) (h : C+P -> C+Q),
                          (f >> g) >> h = bij_transform (bijection_inv bij_sum_assoc) (f >> (g >> h)).
Proof.
intros.
apply functional_extensionality.
unfold bij_transform.
unfold funcomp.
unfold parallel.
unfold sequence.
destruct x as [[[a | b] | c] | i].
simpl.
destruct (f (inl a)).
reflexivity.
unfold extract.
destruct (g (inr o)).
reflexivity.
destruct (h (inr p)).
reflexivity.
reflexivity.
simpl.
unfold extract.
destruct (g (inl b)).
reflexivity.
destruct (h (inr p)).
reflexivity.
reflexivity.
simpl.
unfold extract.
destruct (h (inl c)).
reflexivity.
reflexivity.
simpl.
unfold id.
destruct (f (inr i)).
reflexivity.
unfold extract.
destruct (g (inr o)).
reflexivity.
destruct (h (inr p)).
reflexivity.
reflexivity.
Qed.

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

Theorem acyclic_sequence : forall {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O),
  (forall p, ~closure pp (inl p) (inl p)) -> (forall q, ~closure pq (inl q) (inl q)) -> forall p_q, ~closure (pp >> pq) (inl p_q) (inl p_q).
Proof.
intros P Q I M O pp pq Hpp Hpq p_q Hp_q.
destruct p_q as [p | q].
elim (Hpp p).
eapply sequence_closure_left.
eassumption.
elim (Hpq q).
eapply sequence_closure_right.
eassumption.
Qed.

Theorem finite_child_sequence_left : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n1,
  Acc (fun n n' => p1 (inl n) = inl n') n1 -> Acc (fun n n' => (sequence p1 p2) (inl n) = inl n') (inl n1).
Proof.
intros until p2.
intros n1 Hp1n1.
induction Hp1n1 as (n1, _, Hindn1').
apply Acc_intro.
destruct y as [n1' | n2'].
+ intro Hn1'.
  apply Hindn1'.
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
Qed.

Theorem finite_child_sequence_right : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n2,
  FiniteChild p1 -> Acc (fun n n' => p2 (inl n) = inl n') n2 -> Acc (fun n n' => (sequence p1 p2) (inl n) = inl n') (inr n2).
Proof.
intros until p2.
intros n2 Hp1 Hp2n2.
induction Hp2n2 as (n2, _, Hindn2').
apply Acc_intro.
destruct y as [n1' | n2'].
+ intro Hn1'.
  apply finite_child_sequence_left.
  apply Hp1.
+ intro Hn2'.
  apply Hindn2'.
  unfold sequence in Hn2'.
  simpl in Hn2'.
  unfold extract in Hn2'.
  destruct (p2 (inl n2')); congruence.
Qed.

Theorem finite_child_sequence : forall {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O),
  FiniteChild pp -> FiniteChild pq -> FiniteChild (sequence pp pq).
Proof.
intros until pq.
intros Hpp Hpq n.
destruct n as [np | nq].
+ apply finite_child_sequence_left.
  apply Hpp.
+ apply finite_child_sequence_right.
  apply Hpp.
  apply Hpq.
Qed.

Theorem finite_parent_sequence_right : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n2,
  Acc (fun n' n => p2 (inl n) = inl n') n2 -> Acc (fun n' n => (sequence p1 p2) (inl n) = inl n') (inr n2).
Proof.
intros until p2.
intros n2 Hp2n2.
induction Hp2n2 as (n2, _, Hindn2').
apply Acc_intro.
destruct y as [n1' | n2'].
+ intro Hn1'.
  unfold sequence in Hn1'.
  simpl in Hn1'.
  unfold extract in Hn1'.
  destruct (p2 (inl n2)); congruence.
+ intro Hn2'.
  apply Hindn2'.
  unfold sequence in Hn2'.
  simpl in Hn2'.
  unfold extract in Hn2'.
  destruct (p2 (inl n2)); congruence.
Qed.

Theorem finite_parent_sequence_left : forall {N1 I1 M N2 O2 : Type} (p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n1,
  Acc (fun n' n => p1 (inl n) = inl n') n1 -> FiniteParent p2 -> Acc (fun n' n => (sequence p1 p2) (inl n) = inl n') (inl n1).
Proof.
intros until p2.
intros n1 Hp1n1 Hp2.
induction Hp1n1 as (n1, _, Hindn1').
apply Acc_intro.
destruct y as [n1' | n2'].
+ intro Hn1'.
  apply Hindn1'.
  unfold sequence in Hn1'.
  simpl in Hn1'.
  destruct (p1 (inl n1)).
  - congruence.
  - unfold extract in Hn1'.
    destruct (p2 (inr m)); congruence.
+ intro Hn2'.
  apply finite_parent_sequence_right.
  apply Hp2.
Qed.

Theorem finite_parent_sequence : forall {P Q I M O : Type} (pp : P+I -> P+M) (pq : Q+M -> Q+O),
  FiniteParent pp -> FiniteParent pq -> FiniteParent (sequence pp pq).
Proof.
intros until pq.
intros Hpp Hpq n.
destruct n as [np | nq].
+ apply finite_parent_sequence_left.
  apply Hpp.
  apply Hpq.
+ apply finite_parent_sequence_right.
  apply Hpq.
Qed.

Theorem finite_void : Finite void.
Proof.
exists nil.
split.
+ destruct 1.
+ intros i j Hi.
  simpl in Hi.
  inversion Hi.
Qed.

Theorem finite_unit : Finite unit.
Proof.
exists (cons tt nil).
split.
+ intro t.
  destruct t.
  apply in_eq.
+ intros i j Hi.
  simpl in Hi.
  inversion Hi.
  - subst.
    simpl.
    generalize (nth_error_Some (tt::nil) j).
    intros Hj1 Hj2.
    assert (j < length (tt :: nil)).
    rewrite <- Hj2 in Hj1.
    apply Hj1.
    discriminate.
    simpl in H.
    destruct j; auto.
    lia.
  - lia. 
Qed.

Definition inj_fin_n_Sn : forall {n}, fin n -> fin (S n).
Proof.
intros n (x, Hx).
exists x.
lia.
Defined.

Definition first_fin_Sn : forall n, fin (S n).
Proof.
intro n.
exists n.
lia.
Defined.

Theorem first_fin_Sn_n : forall n, proj1_sig (first_fin_Sn n) = n.
Proof.
intro n.
reflexivity.
Qed.

Theorem inj_fin_n_Sn_id : forall n (x : fin n), proj1_sig (inj_fin_n_Sn x) = proj1_sig x.
Proof.
intros n (x, Hx).
reflexivity.
Qed.

Theorem inj_inj_fin_n_Sn : forall n, InjectiveXT (@inj_fin_n_Sn n).
Proof.
intros until y.
destruct x as (x, Hx); destruct y as (y, Hy).
simpl; intro Hxy.
apply subset_eq_compat.
generalize (proj1_sig_eq Hxy); clear Hxy; intro Hxy; exact Hxy.
Qed.

Lemma in_eq' : forall T a b (q : list T), a = b -> In a (cons b q).
Proof.
intros.
rewrite H.
apply in_eq.
Qed.

Lemma inj_option_map : forall A B (f : A -> B), InjectiveXT f -> InjectiveXT (option_map f).
Proof.
intros until y.
destruct x as [x'|]; destruct y as [y'|]; simpl; try discriminate.
+ intro Hxy'; injection Hxy'; clear Hxy'; intro Hxy'.
  rewrite (H _ _ Hxy'); reflexivity.
+ reflexivity.
Qed.

Lemma injective_nodup : forall A (lA : list A), InjectiveXTList lA -> NoDup lA.
Proof.
intros A lA HlA.
induction lA.
+ apply NoDup_nil.
+ apply NoDup_cons.
  - intro Ha.
    destruct (In_nth_error _ _ Ha) as (i, Hi).
    assert (0 = S i); [|discriminate].
    apply HlA.
    * simpl; lia.
    * symmetry; exact Hi.
  - apply IHlA.
    intros i j Hi Hij.
    assert (S i = S j); [|lia].
    apply HlA.
    * simpl; lia.
    * exact Hij.
Qed.

Lemma nodup_injective : forall A (lA : list A), NoDup lA -> InjectiveXTList lA.
Proof.
intros A lA HA.
induction HA.
+ intros i j Hi.
  simpl in Hi; lia.
+ intros i j Hi Hij.
  destruct i as [|i']; destruct j as [|j']; simpl in Hi; simpl in Hij.
  - reflexivity.
  - symmetry in Hij.
    elim (H (nth_error_In _ _ Hij)).
  - elim (H (nth_error_In _ _ Hij)).
  - f_equal.
    apply IHHA.
    * lia.
    * exact Hij.
Qed.

Lemma nth_error_nil : forall A (i : nat), nth_error (@nil A) i = None.
Proof.
destruct i; reflexivity.
Qed.



Theorem finite_fin : forall n, Finite (fin n).
Proof.
induction n.
+ exists nil.
  split.
  - destruct 1.
    inversion l.
  - intros i j Hi.
    inversion Hi.
+ destruct IHn as (ln, (Hln1, Hln2)).
  exists (cons (first_fin_Sn n) (List.map inj_fin_n_Sn ln)).
  split.
  - intros (x, Hx).
    assert (x = n \/ x < n).
    * lia.
    * destruct H as [H1 | H2].
      ++ subst.
         unfold first_fin_Sn.
         apply in_eq'.
         apply subset_eq_compat.
         reflexivity.
      ++ apply in_cons.
         apply in_map_iff.
         exists (exist (fun p => p < n) x H2).
         split.
         -- apply subset_eq_compat.
            reflexivity.
         -- apply Hln1.
  - intros i j Hi.
    simpl in Hi.
    rewrite map_length in Hi.
    destruct i as [|i']; destruct j as  [|j']; simpl.
    * reflexivity.
    * rewrite nth_error_map.
      case_eq (nth_error ln j'); simpl.
      ++ intros x Hj' H.
         injection H; clear H; intro H.
         unfold first_fin_Sn in H. 
         unfold inj_fin_n_Sn in H.
         destruct x as (x, Hx).
         generalize (proj1_sig_eq H); simpl; clear H; intro H.
         lia.
      ++ discriminate.
    * rewrite nth_error_map.
      case_eq (nth_error ln i'); simpl.
      ++ intros x Hi' H.
         injection H; clear H; intro H.
         unfold first_fin_Sn in H. 
         unfold inj_fin_n_Sn in H.
         destruct x as (x, Hx).
         generalize (proj1_sig_eq H); simpl; clear H; intro H.
         lia.
      ++ discriminate.
    * rewrite nth_error_map.
      rewrite nth_error_map.
      intro H.
      apply f_equal.
      apply Hln2.
      ++ lia.
      ++ apply (inj_option_map _ _ _ (@inj_inj_fin_n_Sn n)).
         exact H.
Qed.

Lemma inj_inl : forall A B, InjectiveXT (@inl A B).
Proof.
intros A B x y Hxy.
injection Hxy.
exact (fun H => H).
Qed.

Lemma inj_inr : forall A B, InjectiveXT (@inr A B).
Proof.
intros A B x y Hxy.
injection Hxy.
exact (fun H => H).
Qed.

Theorem finite_sum : forall A B, Finite A -> Finite B -> Finite (A+B).
Proof.
intros A B HA HB.
destruct HA as (lA, (HA1, HA2)); destruct HB as (lB, (HB1, HB2)).
exists ((map inl lA) ++ (map inr lB)).
split.
+ intro n.
  apply in_or_app.
  destruct n as [a|b].
  - left; apply in_map; apply HA1.
  - right; apply in_map; apply HB1.
+ intros i j Hi.
  rewrite app_length in Hi.
  rewrite map_length in Hi.
  rewrite map_length in Hi.
  assert (i < length lA \/ i >= length lA); try lia.
  assert (j < length lA \/ j >= length lA); try lia.
  destruct H as [Hi1|Hi2]; destruct H0 as [Hj1|Hj2].
  - rewrite nth_error_app1.
    rewrite nth_error_app1.
    rewrite nth_error_map.
    rewrite nth_error_map.
    intro Hij.
    apply HA2.
    exact Hi1.
    eapply inj_option_map.
    eapply inj_inl.
    * exact Hij.
    * rewrite map_length.
      exact Hj1.
    * rewrite map_length.
      exact Hi1.
  - rewrite nth_error_app1.
    * rewrite nth_error_app2.
      ++ rewrite nth_error_map.
         rewrite nth_error_map.
         case_eq (nth_error lA i); simpl.
         -- intros a Ha.
            destruct nth_error in |-*.
            ** discriminate.
            ** discriminate.
         -- intro H.
            assert (i >= length lA).
            ** apply nth_error_None.
               exact H.
            ** lia.
      ++ rewrite map_length.
         exact Hj2.
    * rewrite map_length.
      exact Hi1.
  - rewrite nth_error_app2.
    * rewrite nth_error_app1.
      ++ rewrite nth_error_map.
         rewrite nth_error_map.
         case_eq (nth_error lA j); simpl.
         -- intros a Ha.
            destruct nth_error in |-*.
            ** discriminate.
            ** discriminate.
         -- intro H.
            assert (j >= length lA).
            ** apply nth_error_None.
               exact H.
            ** lia.
      ++ rewrite map_length.
         exact Hj1.
    * rewrite map_length.
      exact Hi2.
  - rewrite nth_error_app2.
    * rewrite nth_error_app2.
      ++ rewrite nth_error_map.
         rewrite nth_error_map.
         intro Hij.
         assert (i - length (map (@inl A B) lA) = j - length (map (@inl A B) lA)).
         ** apply HB2.
            +++ rewrite map_length.
                lia.
            +++ eapply inj_option_map.
                --- eapply inj_inr.
                --- exact Hij.
         ** rewrite map_length in H.
            lia.
      ++ rewrite map_length.
         exact Hj2.
    * rewrite map_length.
      exact Hi2.
Qed.

Lemma inj_proj1_sig : forall A (P : A -> Prop), InjectiveXT (@proj1_sig A P).
Proof.
intros A P (a1, H1) (a2, H2) H12.
apply subset_eq_compat.
exact H12.
Qed.

Lemma sym_injective : forall A (lA : list A) i j (Hij : nth_error lA i = nth_error lA j), i < length lA -> j < length lA.
Proof.
intros A lA i j Hij Hi.
generalize (nth_error_Some lA i).
generalize (nth_error_Some lA j).
intros HlAj HlAi.
rewrite Hij in HlAi.
intuition.
Qed.

Theorem finite_disjoint_union : forall A (P : A -> Prop) (DecP : forall a, decidable (P a)), 
  Finite { a : A | P a } -> Finite { a : A | ~(P a) } -> Finite A.
Proof.
intros A P DecP (lP, (HlP1, HlP2)) (lnP, (HlnP1, HlnP2)).
exists ((map (@proj1_sig _ _) lP) ++ (map (@proj1_sig _ _) lnP)).
split.
+ intro a.
  apply in_or_app.
  destruct (DecP a) as [HPa | HnPa].
  - left.
    assert (a = proj1_sig (exist P a HPa)) as Ha.
    * reflexivity.
    * rewrite Ha.
      apply in_map.
      apply (HlP1 (exist P a HPa)).
  - right.
    assert (a = proj1_sig (exist (fun a => ~(P a)) a HnPa)) as Ha.
    * reflexivity.
    * rewrite Ha.
      apply in_map.
      apply (HlnP1 (exist _ a HnPa)).
+ intros i j Hi Hij.
  generalize (sym_injective _ _ _ _ Hij Hi).
  intro Hj.
  rewrite app_length in *.
  rewrite map_length in *.
  rewrite map_length in *.
  assert (i < length lP \/ length lP <= i) as Hi'; [lia|].
  assert (j < length lP \/ length lP <= j) as Hj'; [lia|].
  destruct Hi' as [Hi' | Hi']; destruct Hj' as [Hj' | Hj'].
  - rewrite nth_error_app1 in Hij; [|rewrite map_length; exact Hi'].
    rewrite nth_error_app1 in Hij; [|rewrite map_length; exact Hj'].
    rewrite nth_error_map in Hij.
    rewrite nth_error_map in Hij.
    apply (HlP2 i j Hi').
    exact (inj_option_map _ _ _ (inj_proj1_sig _ _) _ _ Hij).
  - rewrite nth_error_app1 in Hij; [|rewrite map_length; exact Hi'].
    rewrite nth_error_app2 in Hij; [|rewrite map_length; exact Hj'].
    rewrite nth_error_map in Hij.
    rewrite nth_error_map in Hij.
    rewrite map_length in Hij.
    generalize (nth_error_Some lP i).
    generalize (nth_error_Some lnP (j - length lP)).
    destruct (nth_error lP i) as [(a,Pa) | ]; [simpl | intuition].
    destruct (nth_error lnP (j - length lP)) as [(b,Pb) | ]; [ | intuition; try discriminate].
    intros _ _.
    injection Hij; intro; subst; contradiction.
  - rewrite nth_error_app2 in Hij; [|rewrite map_length; exact Hi'].
    rewrite nth_error_app1 in Hij; [|rewrite map_length; exact Hj'].
    rewrite nth_error_map in Hij.
    rewrite nth_error_map in Hij.
    rewrite map_length in Hij.
    generalize (nth_error_Some lnP (i - length lP)).
    generalize (nth_error_Some lP j).
    destruct (nth_error lP j) as [(b,Pb) | ]; [simpl | intuition].
    destruct (nth_error lnP (i - length lP)) as [(a,Pa) | ]; [ | intuition; try discriminate].
    intros _ _.
    injection Hij; intro; subst; contradiction.
  - rewrite nth_error_app2 in Hij; [|rewrite map_length; exact Hi'].
    rewrite nth_error_app2 in Hij; [|rewrite map_length; exact Hj'].
    rewrite nth_error_map in Hij.
    rewrite nth_error_map in Hij.
    rewrite map_length in Hij.
    assert (i - length lP < length lnP) as Hi''; [lia|].
    assert (i - length lP = j - length lP); [|lia].
    apply (HlnP2 (i - length lP) (j - length lP) Hi'').
    exact (inj_option_map _ _ _ (inj_proj1_sig _ _) _ _ Hij).
Qed.

Definition cross_product { A B } (lA : list A) (lB : list B) : list (A * B) :=
  List.flat_map (fun a => List.map (fun b => (a, b)) lB) lA.

Definition option_bind { A B } (a : option A) (f : A -> option B) : option B :=
  match a with
  | None   => None
  | Some a => f a
  end.

Theorem cross_product_nil_right : forall A B (lA : list A), cross_product lA (@nil B) = nil.
Proof.
induction lA.
+ reflexivity.
+ simpl.
  exact IHlA.
Qed.

Theorem length_cross_product : forall A B (lA : list A) (lB : list B),
  length (cross_product lA lB) = length lA * length lB.
Proof.
induction lA; intro lB; simpl.
+ reflexivity.
+ rewrite app_length.
  rewrite IHlA.
  rewrite map_length.
  reflexivity.
Qed.

Theorem nth_error_cross_product : forall { A B } (lA : list A) (lB : list B) i j (Hj : j < length lB),
  option_bind (nth_error lA i) (fun a => option_bind (nth_error lB j) (fun b => Some (a, b)))
  = nth_error (cross_product lA lB) ((length lB) * i + j).
Proof.
intros A B lA lB.
induction lA; simpl; intros i j Hj.
+ rewrite nth_error_nil.
  rewrite nth_error_nil.
  reflexivity.
+ destruct i as [|i']; simpl.
  - rewrite nth_error_app1.
    * rewrite Nat.mul_0_r.
      rewrite nth_error_map.
      simpl.
      destruct (nth_error lB j); reflexivity.
    * rewrite Nat.mul_0_r.
      rewrite map_length.
      exact Hj.
  - rewrite nth_error_app2.
    * rewrite map_length.
      assert (length lB * S i' + j - length lB = length lB * i' + j) as H; [lia|].
      rewrite H.
      apply IHlA.
      exact Hj.
    * rewrite map_length.
      lia.
Qed.

Theorem nth_error_cross_product_inv : forall { A B } (lA : list A) (lB : list B) (HlB : length lB > 0) i,
  nth_error (cross_product lA lB) i =
  let (q, r, Hr, Hqr) := eucl_dev (length lB) HlB i
  in option_bind (nth_error lA q) (fun a => option_bind (nth_error lB r) (fun b => Some (a, b))).
Proof.
intros A B lA lB HlB i.
destruct (eucl_dev (length lB) HlB i) as (q,r, Hr, Hqr).
rewrite nth_error_cross_product.
+ rewrite Hqr.
  rewrite Nat.mul_comm.
  reflexivity.
+ exact Hr.
Qed.

Theorem finite_prod : forall A B, Finite A -> Finite B -> Finite (A*B).
Proof.
intros A B (lA, (HlA1, HlA2)) (lB, (HlB1, HlB2)).
exists (cross_product lA lB).
split.
+ intro ab.
  destruct ab as (a, b).
  apply in_flat_map.
  exists a.
  intuition.
  apply in_map.
  intuition.
+ intros i j Hi Hij.
  generalize (sym_injective _ _ _ _ Hij Hi).
  intro Hj.
  rewrite length_cross_product in Hi.
  rewrite length_cross_product in Hj.
  assert (length lB = 0 \/ length lB > 0) as HlB; [lia|].
  destruct HlB as [HlB | HlB].
  - rewrite HlB in Hi.
    rewrite Nat.mul_0_r in Hi.
    lia.
  - rewrite (nth_error_cross_product_inv lA lB HlB) in Hij.
    rewrite (nth_error_cross_product_inv lA lB HlB) in Hij.
    destruct (eucl_dev (length lB) HlB i) as (qi, ri, Hri, Hqri).
    destruct (eucl_dev (length lB) HlB j) as (qj, rj, Hrj, Hqrj).
    subst.
    rewrite Nat.add_comm in Hi.
    generalize (Nat.add_lt_cases ri (qi * length lB) 0 (length lA * length lB) Hi).
    intro Hqi; destruct Hqi as [Hqi | Hqi]; [lia |].
    assert (qi < length lA) as Hqi'; [apply (Nat.mul_lt_mono_pos_r _ _ _ HlB); exact Hqi|].
    rewrite Nat.add_comm in Hj.
    generalize (Nat.add_lt_cases rj (qj * length lB) 0 (length lA * length lB) Hj).
    intro Hqj; destruct Hqj as [Hqj | Hqj]; [lia |].
    assert (qj < length lA) as Hqj'; [apply (Nat.mul_lt_mono_pos_r _ _ _ HlB); exact Hqj|].
    clear Hqi Hqj.
    generalize (nth_error_None lA qi).
    case_eq (nth_error lA qi); [intros ai Hai _ | intuition; lia].
    generalize (nth_error_None lA qj).
    case_eq (nth_error lA qj); [intros aj Haj _ | intuition; lia].
    generalize (nth_error_None lB ri).
    case_eq (nth_error lB ri); [intros bi Hbi _ | intuition; lia].
    generalize (nth_error_None lB rj).
    case_eq (nth_error lB rj); [intros bj Hbj _ | intuition; lia].
    rewrite Hai in Hij.
    rewrite Haj in Hij.
    rewrite Hbi in Hij.
    rewrite Hbj in Hij.
    injection Hij; clear Hij; intros Haij Hbij.
    subst.
    assert (qi = qj) as Hqij.
    * apply (HlA2 qi qj Hqi').
      congruence.
    * subst.
      assert (ri = rj) as Hrij.
      ++ apply (HlB2 ri rj Hri).
         congruence.
      ++ congruence.
Qed.

Definition filter_pred { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) : list { a : A | P a } :=
  fold_right (fun a r => match DecP a with left Pa => (exist (fun a => P a) a Pa) :: r | right _ => r end) nil lA.

Theorem filter_pred_flat_map : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A),
  filter_pred P DecP lA = flat_map (fun a => match DecP a with left Pa => (exist (fun a => P a) a Pa)::nil | right nPa => nil end) lA.
Proof.
induction lA; simpl.
+ reflexivity.
+ destruct (DecP a).
  - rewrite <- IHlA.
    simpl.
    reflexivity.
  - rewrite <- IHlA.
    simpl.
    reflexivity. 
Qed.

Theorem filter_pred_length : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A),
  length (filter_pred P DecP lA) <= length lA.
Proof.
induction lA; simpl.
+ auto.
+ destruct (DecP a).
  - simpl.
    lia.
  - lia.
Qed.

Definition nth_error_filter_pred : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) i,
  i < length (filter_pred P DecP lA)
  -> { j | i <= j /\ j < length lA /\ option_map (@proj1_sig A P) (nth_error (filter_pred P DecP lA) i) = nth_error lA j }.
Proof.
induction lA; simpl.
+ intro i; lia.
+ intros i Hi.
  destruct (DecP a).
  - destruct i as [|i'].
    * exists 0.
      simpl.
      split; try split.
      ++ apply le_n.
      ++ lia.
      ++ reflexivity.
    * assert (i' < length (filter_pred P DecP lA)).
      ++ simpl in Hi; lia.
      ++ destruct (IHlA i' H) as (j, (Hij, (Hj, Hij'))).
         exists (S j).
         split; try split.
         -- lia.
         -- lia.
         -- exact Hij'.
  - destruct (IHlA i Hi) as (j, (Hij, (Hj, Hij'))).
    exists (S j).
    split; try split.
    * lia.
    * lia.
    * simpl.
      exact Hij'.
Defined.

Definition nth_error_filter_pred_fun_v0 { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) i (Hi :  i < length (filter_pred P DecP lA)) : nat.
Proof.
revert i Hi.
induction lA; intros i Hi; simpl.
+ elim (Nat.nlt_0_r i Hi).
+ simpl in Hi.
  destruct (DecP a).
  - destruct i as [|i'].
    * exact 0.
    * exact (S (IHlA i' (lt_S_n' _ _ Hi))).
  - exact (S (IHlA i Hi)).
Defined.

Lemma filter_pred_ok : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (a : A) (Pa : P a) (lA : list A),
  filter_pred P DecP (cons a lA) = cons (exist (fun a => P a) a Pa) (filter_pred P DecP lA).
Proof.
intros.
simpl.
destruct (DecP a).
+ apply equal_f.
  apply f_equal.
  apply subset_eq_compat.
  reflexivity.
+ elim (n Pa).
Qed.

Lemma filter_pred_ko : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (a : A) (nPa : ~ (P a)) (lA : list A),
  filter_pred P DecP (cons a lA) = filter_pred P DecP lA.
Proof.
intros.
simpl.
destruct (DecP a).
+ elim (nPa p).
+ reflexivity.
Qed.

Fixpoint nth_error_filter_pred_fun_v1 { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) { struct lA } : forall i (Hi :  i < length (filter_pred P DecP lA)), nat :=
  match lA return forall i (Hi : i < length (filter_pred P DecP lA)), nat with
  | nil      => (fun i Hi => False_rec _ (Nat.nlt_0_r i Hi))
  | cons a q => (fun i    => match DecP a with
                             | left  Pa  => match i return i < length (filter_pred P DecP (cons a q)) -> nat with
                                            | O    => (fun _  => 0)
                                            | S i' => (fun Hi => let Hi' := lt_S_n' _ _ (eq_rect _ (fun l => (S i') < length l) Hi _ (filter_pred_ok P DecP a Pa q))
                                                                 in S (nth_error_filter_pred_fun_v1 P DecP q i' Hi'))
                                            end
                             | right nPa => (fun Hi => let Hi := eq_rect _ (fun l => i < length l) Hi _ (filter_pred_ko P DecP a nPa q)
                                            in S (nth_error_filter_pred_fun_v1 P DecP q i Hi))
                             end
                )
  end.

Fixpoint nth_error_filter_pred_fun_v2 { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) i { struct lA } : nat :=
  match lA with
  | nil      => 0 (* inaccessible *)
  | cons a q => match DecP a with
                | left  Pa  => match i with
                               | O    => 0
                               | S i' => S (nth_error_filter_pred_fun_v2 P DecP q i')
                               end
                | right nPa => S (nth_error_filter_pred_fun_v2 P DecP q i)
                end
  end.

Theorem nth_error_filter_pred_spec : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A) i (Hi : i < length (filter_pred P DecP lA)),
  let j := nth_error_filter_pred_fun_v2 P DecP lA i
  in  i <= j /\ j < length lA /\ option_map (@proj1_sig A P) (nth_error (filter_pred P DecP lA) i) = nth_error lA j.
Proof.
induction lA; simpl.
+ intros i Hi; elim (Nat.nlt_0_r _ Hi).
+ destruct (DecP a); simpl; intros i Hi.
  - destruct i as [|i']; simpl.
    * split; auto. split; auto. apply Nat.lt_0_succ. 
    * destruct (IHlA i' (lt_S_n' _ _ Hi)) as (Hij', (Hj, Hij'')).
      split; auto. 
      ** apply le_n_S. assumption.
      ** split ; auto. apply lt_n_S_stt. assumption.
  - destruct (IHlA i Hi). destruct H0.
    split; auto. split; auto. apply lt_n_S_stt. assumption. 
Qed.

Theorem length_head {A:Type} : forall t:A, forall q, length (t::q) = S (length q).
Proof.
intros.
change (length ([t] ++ q) = S (length q)).
rewrite app_length.
simpl.
reflexivity.
Qed.

Theorem inj_nth_error_filter_pred : forall { A : Type } (P : A -> Prop) (DecP : forall a, decidable (P a)) (lA : list A),
  forall i (Hi : i < length (filter_pred P DecP lA)) j (Hj : j < length (filter_pred P DecP lA)), nth_error_filter_pred_fun_v2 P DecP lA i = nth_error_filter_pred_fun_v2 P DecP lA j -> i = j.
Proof.
induction lA; simpl.
+ intros.
  elim (Nat.nlt_0_r _ Hi).
+ intros i Hi j Hj HlA.
  destruct (DecP a).
  - destruct i as [|i']; destruct j as [|j']; auto.
    * discriminate HlA.
    * discriminate HlA.
    * apply eq_S. apply IHlA.
    ** apply lt_S_n'. rewrite length_head in Hi. apply Hi.
    ** apply lt_S_n'. rewrite length_head in Hj. apply Hj.
    ** apply eq_add_S. assumption.
  - apply IHlA; intuition.
Qed.

Theorem finite_subset : forall { A : Type } (P : A -> Prop), Finite A -> (forall a, decidable (P a)) -> Finite { a : A | P a }.
Proof.
intros A P (lA, (HlA1, HlA2)) HP.
exists (filter_pred P HP lA).
split.
+ intros (x, Hx).
  rewrite filter_pred_flat_map.
  apply in_flat_map.
  exists x.
  split.
  - apply (HlA1 x).
  - destruct (HP x).
    * apply in_eq'.
      apply subset_eq_compat.
      reflexivity.
    * contradiction.
+ intros x y Hx Hxy.
  assert (y < length (filter_pred P HP lA)) as Hy.
  - apply nth_error_Some.
    intro Hy.
    rewrite Hy in Hxy.
    revert Hx.
    apply Nat.le_ngt.
    apply nth_error_None.
    exact Hxy.
  - generalize (nth_error_filter_pred_spec P HP lA x Hx).
    generalize (nth_error_filter_pred_spec P HP lA y Hy).
    simpl.
    intros (Hyy', (Hy', Hyy'')) (Hxx', (Hx', Hxx'')).
    apply (inj_nth_error_filter_pred P HP lA x Hx y Hy).
    apply (HlA2 _ _ Hx').
    rewrite <- Hxx''.
    rewrite <- Hyy''.
    rewrite Hxy.
    reflexivity.
Qed.

Definition dec_eq A := forall (a a' : A), decidable (a = a').

Theorem finite_dec_exists : forall A (P : A -> Prop), Finite A -> (forall a, decidable (P a)) -> decidable (exists a, P a).
Proof.
intros A P FA DecP.
destruct (finite_subset P FA DecP) as (lPA, (HlPA, _)).
destruct lPA.
+ apply right.
  intros (a, Pa).
  apply (in_nil (HlPA (exist P a Pa))).
+ apply left.
  destruct s.
  exists x.
  exact p.
Qed.

Lemma Forall_forall : forall A (P : A -> Prop) (l : list A), Forall P l -> forall a, In a l -> P a.
Proof.
induction l; simpl; intros Hl x Hx.
+ elim Hx.
+ inversion Hl; subst.
  destruct Hx as [Hxa | Hxl].
  - subst; assumption.
  - apply IHl; assumption.
Qed.

Lemma forall_Forall : forall A (P : A -> Prop) (l : list A), (forall a, In a l -> P a) -> Forall P l.
Proof.
induction l; simpl; intros Hl.
+ apply Forall_nil.
+ apply Forall_cons.
  - apply Hl.
    left.
    reflexivity.
  - apply IHl.
    intros a' Ha'.
    apply Hl.
    right.
    exact Ha'.
Qed.

Definition spec_image { A B } (f : A -> B) lA := fun b => exists a, In a lA /\ b = f a.

Lemma spec_image_image : forall { A B } (f : A -> B) lA a, In a lA -> spec_image f lA (f a).
Proof.
intros.
exact (ex_intro (fun a' => In a' lA /\ f a = f a') a (conj H refl_equal)).
Qed.

Definition spec_image_list { A B } (f : A -> B) lA lB := forall prA, Forall (spec_image f (prA++lA)) lB.

Definition spec_image_list_nil { A B } (f : A -> B): spec_image_list f nil nil.
Proof.
intro prA.
apply Forall_nil.
Defined.

Definition spec_image_list_shift { A B } (f : A -> B) a qA lB (spec : spec_image_list f qA lB) : spec_image_list f (cons a qA) lB.
Proof.
intro prA.
assert (prA ++ a :: qA = (prA ++ (a :: nil)) ++ qA).
+ rewrite <- app_assoc.
  reflexivity.
+ rewrite H.
  apply spec.
Defined.


Section ListsMoi.

  Variable A : Type.
Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
Proof.
  intros x l1 l2. unfold In. simpl. Admitted.
  
End ListsMoi.

Definition spec_image_list_cons { A B } (f : A -> B) a qA lB (spec : spec_image_list f qA lB) : spec_image_list f (cons a qA) (cons (f a) lB).
Proof.
intro prA.
apply Forall_cons.
+ apply spec_image_image.
  apply in_elt.
+ apply spec_image_list_shift.
  apply spec.
Defined.

Definition spec_domain { A B } (f : A -> B) lB := fun a => In (f a) lB.

Definition spec_domain_list { A B } (f : A -> B) lB lA := Forall (spec_domain f lB) lA.

Definition spec_domain_list_nil { A B } (f : A -> B): spec_domain_list f nil nil.
Proof.
apply Forall_nil.
Defined.

Definition spec_domain_list_shift { A B } (f : A -> B) lB a qA (Ha : In (f a) lB) (spec : spec_domain_list f lB qA) : spec_domain_list f lB (cons a qA).
Proof.
apply Forall_cons.
+ exact Ha.
+ apply spec.
Defined.

Definition spec_domain_list_cons { A B } (f : A -> B) lB a qA (Ha : ~In (f a) lB) (spec : spec_domain_list f lB qA) : spec_domain_list f (cons (f a) lB) (cons a qA).
Proof.
apply Forall_cons.
+ apply in_eq.
+ eapply Forall_impl.
  - intros a' Ha'.
    apply in_cons.
    apply Ha'.
  - exact spec.
Defined.

Definition spec_injective_list_nil { B } : InjectiveXTList (@nil B).
Proof.
intros i j Hi.
elim (Nat.nlt_0_r _ Hi).
Defined.

Definition spec_injective_list_cons { B } (lB : list B) b (Hb : ~In b lB) (spec : InjectiveXTList lB) : InjectiveXTList (cons b lB).
Proof.
intros i j Hi.
destruct i as [|i']; destruct j as [|j']; simpl.
+ reflexivity.
+ intro Hj'.
  symmetry in Hj'.
  elim (Hb (nth_error_In _ _ Hj')).
+ intro Hi'.
  elim (Hb (nth_error_In _ _ Hi')).
+ intro Hij'.
  f_equal.
  apply spec.
  - simpl in Hi.
    lia.
  - exact Hij'. 
Defined.

Record SpecImage { A B } (f : A -> B) (lA : list A) (lB : list B) : Prop := {
  inj : InjectiveXTList lB;
  img : spec_image_list f lA lB;
  dom : spec_domain_list f lB lA;
}.

Definition SpecImageNil { A B } (f : A -> B) := {|
  inj := spec_injective_list_nil;
  img := spec_image_list_nil f;
  dom := spec_domain_list_nil f;
|}.

Definition SpecImageShift { A B } (f : A -> B) a (qA : list A) (lB : list B) (Ha : In (f a) lB) (spec : SpecImage f qA lB) : SpecImage f (cons a qA) lB:= {|
  inj := spec.(inj _ _ _);
  img := spec_image_list_shift f a qA lB spec.(img _ _ _);
  dom := spec_domain_list_shift f lB a qA Ha spec.(dom _ _ _);
|}.

Definition SpecImageCons { A B } (f : A -> B) a (qA : list A) (lB : list B) (Ha : ~In (f a) lB) (spec : SpecImage f qA lB) : SpecImage f (cons a qA) (cons (f a) lB):= {|
  inj := spec_injective_list_cons lB (f a) Ha spec.(inj _ _ _);
  img := spec_image_list_cons f a qA lB spec.(img _ _ _);
  dom := spec_domain_list_cons f lB a qA Ha spec.(dom _ _ _);
|}.

Fixpoint image A B (f : A -> B) (eqB : dec_eq B) (lA : list A) { struct lA } : { lB : list B | SpecImage f lA lB } :=
  match lA return { lB : list B | SpecImage f lA lB } with
  | nil      => exist (SpecImage f nil) nil (SpecImageNil f)
  | cons a q => let (imgq, Hspecq) := image A B f eqB q in
                let imga := f a in
                match in_dec eqB imga imgq with
                | left  Infa  => exist (SpecImage f (cons a q))
                                  imgq
                                  (SpecImageShift f a q imgq Infa Hspecq)
                | right nInfa => exist (SpecImage f (cons a q))
                                  (cons (f a) imgq)
                                  (SpecImageCons f a q imgq nInfa Hspecq)
                end
  end.

Definition conversion_forall : forall { A B C } (P : C -> B -> A -> Prop) b (l : list A) (Hl : forall c, Forall (P c b) l), list { a : A | forall c, P c b a }.
Proof.
intros A B C P b l Hl.
generalize (fun c => Forall_forall A (P c b) l (Hl c)); clear Hl; intro Hl.
induction  l.
+ exact nil.
+ eapply cons.
  - exists a.
    intro c.
    apply Hl.
    apply in_eq.
  - apply IHl.
    intros c a' Ha'.
    apply Hl.
    apply in_cons.
    exact Ha'.
Defined.

Theorem conversion_forall_nil : forall { A B C } (P : C -> B -> A -> Prop) b (Hnil : forall c, Forall (P c b) nil),
  conversion_forall P b nil Hnil = nil.
Proof.
reflexivity.
Qed.

Theorem conversion_forall_cons : forall A B C (P : C -> B -> A -> Prop) b a (Ha : forall c, P c b a) (l : list A) (Hl : forall c, Forall (P c b) l) (Hal : forall c, Forall (P c b) (cons a l)),
  conversion_forall P b (cons a l) Hal = (exist _ a Ha) :: (conversion_forall P b l Hl).
Proof.
intros A B C P b a Ha l Hl Hal.
unfold conversion_forall.
simpl.
f_equal.
+ apply subset_eq_compat.
  reflexivity.
+ f_equal.
  apply functional_extensionality_dep; intro c.
  apply functional_extensionality_dep; intro a'.
  apply functional_extensionality_dep; intro Ha'.
  apply proof_irrelevance.
Qed.

Theorem conversion_forall_id : forall { A B C } (P : C -> B -> A -> Prop) b (l : list A) (Hl : forall c, Forall (P c b) l),
  List.map (@proj1_sig _ (fun a => forall c, P c b a)) (conversion_forall P b l Hl) = l.
Proof.
intros A B C P b l Hl.
induction l.
+ reflexivity.
+ assert (forall c, Forall (P c b) l) as Hl'.
  - intro c.
    apply (Forall_inv_tail (Hl c)).
  - rewrite <- (IHl Hl') at 2.
    rewrite conversion_forall_cons with (Hl := Hl') (Ha := fun c => Forall_inv (Hl c)).
    simpl.
    reflexivity.
Qed.

Theorem nth_error_conversion_forall : forall { A B C } (P : C -> B -> A -> Prop) b i (l : list A) (Hl : forall c, Forall (P c b) l),
  nth_error l i = option_map (@proj1_sig _ (fun a => forall c, P c b a)) (nth_error (conversion_forall P b l Hl) i).
Proof.
intros A B C P b i l Hl.
revert i.
induction l.
+ rewrite conversion_forall_nil.
  intro i.
  rewrite nth_error_nil.
  rewrite nth_error_nil.
  reflexivity.
+ destruct i as [|i'].
  - reflexivity.
  - assert (forall c, Forall (P c b) l) as Hl'.
    * intro c.
      apply (Forall_inv_tail (Hl c)).
    * rewrite conversion_forall_cons with (Hl := Hl') (Ha := fun c => Forall_inv (Hl c)).
      simpl.
      apply (IHl Hl').
Qed.

Theorem in_conversion_forall : forall { A B C } (P : C -> B -> A -> Prop) b a (Pa : forall c, P c b a) (l : list A) (Hl : forall c, Forall (P c b) l),
  In a l -> In (exist _ a Pa) (conversion_forall P b l Hl).
Proof.
intros A B C P b a Pa l Hl Hal.
induction l.
+ auto.
+ destruct Hal as [Hal | Hal].
  - subst.
    left.
    apply subset_eq_compat.
    reflexivity.
  - assert (forall c, Forall (P c b) l) as Hl'.
    * intro c.
      eapply Forall_inv_tail.
      apply Hl.
    * rewrite conversion_forall_cons with (Hl := Hl') (Ha := fun c => Forall_inv (Hl c)).
      apply in_cons.
      exact (IHl Hl' Hal).
Qed.

Theorem inj_conversion_forall : forall { A B C } (P : C -> B -> A -> Prop) b (l : list A) (Hl : forall c, Forall (P c b) l),
  InjectiveXTList l -> InjectiveXTList (conversion_forall P b l Hl).
Proof.
intros A B C P b l Hl HIl i j Hi Hij.
apply HIl.
+ rewrite <- (conversion_forall_id P b l Hl).
  rewrite map_length.
  exact Hi.
+ rewrite (nth_error_conversion_forall P b i l Hl).
  rewrite (nth_error_conversion_forall P b j l Hl).
  f_equal.
  exact Hij.
Qed.

Definition image_dep A B (f : A -> B) (eqB : dec_eq B) (lA : list A) :=
  let (lB, Hspec) := image A B f eqB lA
  in conversion_forall (fun pr lA b => spec_image f (pr ++ lA) b) lA lB Hspec.(img _ _ _).

Theorem surj_image : forall A B (f : A -> B) (eqB : dec_eq B) (lA : list A), SurjectiveList (image_dep A B f eqB lA).
Proof.
intros A B f eqB lA (b, Pb).
unfold image_dep.
destruct (image A B f eqB lA) as (img, (Hinj, Himg, Hdom)).
apply (in_conversion_forall (fun c lA b => spec_image f (c ++ lA) b) lA b Pb img Himg).
destruct (Pb nil) as (a, (HalA, Hb)).
subst.
apply (Forall_forall _ _ _ Hdom).
exact HalA.
Qed.

Theorem inj_image : forall A B (f : A -> B) (eqB : dec_eq B) (lA : list A), InjectiveXTList (image_dep A B f eqB lA).
Proof.
unfold image_dep.
intros A B f eqB lA.
destruct (image A B f eqB lA) as (img, (Hinj, Himg, Hdom)).
apply (inj_conversion_forall (fun pr lA b => spec_image f (pr++lA) b)).
exact Hinj.
Qed.

Theorem finite_image : forall A B (f : A -> B) (eqB : dec_eq B), Finite A -> Finite { b : B | exists a, b = f a }.
Proof.
intros A B f eqB (lA, (HlA1, _)).
generalize (surj_image A B f eqB lA).
generalize (inj_image A B f eqB lA).
set (img := image_dep A B f eqB lA).
intros Himg1 Himg2.
unfold image_dep in img.
destruct (image A B f eqB lA) as (lB, (Hinj, Himg, Hdom)).
assert ((fun b => exists a, b = f a) = (fun b => forall c, spec_image f (c++lA) b)).
+ apply functional_extensionality.
  intro b.
  apply propositional_extensionality.
  unfold spec_image. (*firstorder.*)
  intuition.
  ++ edestruct H. exists x. split. 
    +++ unfold SurjectiveList in HlA1.
    specialize (HlA1 x). apply in_or_app. right. assumption.
    +++ apply H0. 
  ++ edestruct H. exists x. apply H0. 
+ rewrite H.
  exists img.
  intuition.
  Unshelve.
  apply lA.
Qed.



