(*
  bigraph = structural forest + hypergraph
            + interfaces + transition rule
*)

Require Import FunctionalExtensionality.

Inductive closure {N I O : Type} (p : (N+I) -> (N+O)) (ni : N+I) : (N+O) -> Prop :=
| One  : closure p ni (p ni)
| Add  : forall n', closure p ni (inl n') -> closure p ni (p (inl n')).

Definition FiniteChild {N I O} (p : N+I -> N+O) := forall n, Acc (fun n n' => p (inl n) = inl n') n.
(*n' père de n*)
Definition FiniteParent {N I O} (p : N+I -> N+O) := forall n, Acc (fun n' n => p (inl n) = inl n') n.

Definition Acyclic {N I O} (p : N+I -> N+O) := forall ni no, closure p ni no -> forall n, ni = inl n -> ~ no = inl n.

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
destruct (IHn _ (Le.le_S_n _ _ H)).
left.
apply f_equal.
assumption.
right.
apply Lt.lt_n_S.
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
elim (Nat.nlt_0_r _ (Lt.lt_S_n _ _ Hzero)).
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
Search (~ _ < 0).
elim (Nat.nlt_0_r _ (Lt.lt_S_n _ _ (Lt.lt_S_n _ _ Hk))).
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
apply Lt.lt_S_n.
exact Hp.
Defined.

Definition surj_fin_Sn {n : nat} (f : unit + fin n) : fin (S n).
Proof.
destruct f as [u | (p, Hp)].
exists 0.
apply Nat.lt_0_succ.
exists (S p).
apply Lt.lt_n_S.
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
apply Nat.div_lt_upper_bound.
intro H.
rewrite H in Hk.
apply (Nat.nlt_0_r k).
rewrite (mult_n_O n).
assumption.
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
apply Plus.plus_lt_compat_l.
simpl.
rewrite Nat.add_0_r.
exact Hm.
rewrite <- Nat.mul_add_distr_r.
apply Nat.mul_le_mono_r.
rewrite Nat.add_comm.
exact H.
Defined.

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
rewrite Nat.mod_add.
Search (_ mod _ = _).
apply Nat.mod_small.
exact Hb.
intro Hp.
rewrite Hp in Hb.
elim (Nat.nlt_0_r _ Hb).
apply functional_extensionality.
unfold inj_fin_mul.
unfold surj_fin_mul.
unfold funcomp.
unfold id.
destruct x as (a, Ha).
apply subset_eq_compat.
rewrite Nat.mod_eq.
rewrite Nat.mul_comm.
rewrite <- Minus.le_plus_minus.
reflexivity.
apply Nat.mul_div_le.
intro Hp; rewrite Hp in Ha; rewrite Nat.mul_0_r in Ha; elim (Nat.nlt_0_r _ Ha).
intro Hp; rewrite Hp in Ha; rewrite Nat.mul_0_r in Ha; elim (Nat.nlt_0_r _ Ha).
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
  destruct (p2 (inl n2')). ++ congruence. ++ congruence.
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

Theorem finite_parent_sequence_right : forall {N1 I1 M N2 O2 : Type} 
(p1 : N1+I1 -> N1+M) (p2 : N2+M -> N2+O2) n2,
  Acc (fun n' n => p2 (inl n) = inl n') n2 -> 
  Acc (fun n' n => (sequence p1 p2) (inl n) = inl n') (inr n2).
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
  destruct (p2 (inl n2)). ++ congruence. ++ congruence.
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
