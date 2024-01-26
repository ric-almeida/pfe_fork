(*
  Bijections between void, unit, sum, product, function and finite types
*)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import MyBasics.
Require Import PeanoNat.
Require Import Lia.
Require Import List.
Require Import Coq.Numbers.Natural.Abstract.NDiv0.
Require Import Arith.

Set Warnings "-notation-overridden".

Record bijection (A B : Type) := mkBijection
{
 forward  :> A -> B;
 backward : B -> A;
 fob_id   : forward <o> backward = id;
 bof_id   : backward <o> forward = id;
}.

Arguments backward {A B}.
Arguments forward  {A B}.

Notation "bij ⁻¹" := (backward bij) (at level 55).

Theorem bij_injective : forall {A B} (bij : bijection A B), InjectiveXT bij.(forward).
Proof.
destruct bij.
intros a1 a2 Hfa12.
simpl in Hfa12.
assert (a1 = id a1) as H; [reflexivity | rewrite H; clear H].
assert (a2 = id a2) as H; [reflexivity | rewrite H; clear H].
rewrite <- bof_id0.
unfold funcomp.
apply f_equal.
apply Hfa12.
Qed.

Theorem bij_surjective : forall {A B} (bij : bijection A B), SurjectiveXT bij.(backward).
Proof.
destruct bij.
simpl.
intro a.
exists (forward0 a).
assert (a = id a) as H; [reflexivity | rewrite H at 1; clear H].
rewrite <- bof_id0.
reflexivity.
Qed.

Definition injective_bij_forward {A B} (f : A -> B) (Hinjf : InjectiveXT f) : A -> { b : B & { a : A | b = f a } }.
Proof.
intro a.
exists (f a).
exists a.
reflexivity.
Defined.

Definition injective_bij_backward {A B} (f : A -> B) (Hinjf : InjectiveXT f) : { b : B & { a : A | b = f a } } -> A.
Proof.
destruct 1 as (_, (a, _)).
exact a.
Defined.

Theorem injective_bij : forall {A B} (f : A -> B), InjectiveXT f -> bijection A { b : B & { a : A | b = f a } }.
Proof.
intros A B f Hinjf.
apply (mkBijection _ _ (injective_bij_forward f Hinjf) (injective_bij_backward f Hinjf)); unfold injective_bij_forward, injective_bij_backward, funcomp, id; apply functional_extensionality.
+ destruct x as (b, (a, Hab)).
  rewrite Hab.
  reflexivity.
+ reflexivity.
Qed.

Definition bijection_inv {A B} (bij : bijection A B) : bijection B A :=
 (mkBijection B A bij.(backward) bij.(forward) (bij.(bof_id A B)) (bij.(fob_id A B))).

Definition bij_id {A} : bijection A A :=
 (mkBijection A A id id eq_refl eq_refl).

Theorem bij_inv_id : forall {A}, bijection_inv (@bij_id A) = @bij_id A.
Proof.
intro A.
reflexivity.
Qed.

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

Theorem bij_void_sum_neutral_r : forall {A}, bijection (A + void) A.
Proof.
intro A.
apply (mkBijection (A+void) A
        (fun va => match va with | inl a => a | inr v => match v with end end)
        (fun a => inl a)).
apply functional_extensionality.
intro x.
reflexivity.
apply functional_extensionality.
destruct x.
reflexivity.
elim v.
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
apply (mkBijection A C (bij_BC.(forward) <o> bij_AB.(forward)) (bij_AB.(backward) <o> bij_BC.(backward))).
rewrite -> comp_assoc.
rewrite <- (comp_assoc (backward bij_BC)).
rewrite bij_AB.(fob_id A B).
rewrite id_left_neutral.
apply bij_BC.(fob_id B C).
rewrite -> comp_assoc.
rewrite <- (comp_assoc (forward bij_AB)).
rewrite bij_BC.(bof_id B C).
rewrite id_left_neutral.
apply bij_AB.(bof_id A B).
Defined.

Notation "f <O> g" := (bij_compose f g)( at level 60).

Lemma bij_compose_forward_simpl : forall {A B C} (bij_AB : bijection A B) (bij_BC : bijection B C) a, (bij_BC <O> bij_AB) a = bij_BC (bij_AB a).
Proof.
reflexivity.
Qed.

Lemma bij_compose_backward_simpl : forall {A B C} (bij_AB : bijection A B) (bij_BC : bijection B C) c,
                                      backward (bij_BC <O> bij_AB) c = backward bij_AB (backward bij_BC c).
Proof.
reflexivity.
Qed.

Theorem bij_eq : forall {A B} (bij1 bij2 : bijection A B), bij1.(forward) = bij2.(forward) -> bij1.(backward) = bij2.(backward) -> bij1 = bij2.
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

Definition sum_shuffle {A B C D} : (A+B)+(C+D) -> (A+C)+(B+D) :=
  (fun abcd => match abcd with
               | inl (inl a) => inl (inl a)
               | inl (inr b) => inr (inl b)
               | inr (inl c) => inl (inr c)
               | inr (inr d) => inr (inr d) end).

Theorem bij_sum_shuffle : forall {A B C D}, bijection ((A+B)+(C+D)) ((A+C)+(B+D)).
Proof.
intros A B C D.
apply (mkBijection _ _ (@sum_shuffle A B C D) (@sum_shuffle A C B D)). 
+ apply functional_extensionality.
  destruct x as [[a|c]|[b|d]]; reflexivity.
+ apply functional_extensionality.
  destruct x as [[a|b]|[c|d]]; reflexivity.
Defined.

Theorem bij_sum_shuffle_involution : forall {A B C D}, bijection_inv (@bij_sum_shuffle A B C D) = (@bij_sum_shuffle A C B D).
Proof.
intros A B C D.
apply bij_eq.
+ apply functional_extensionality.
  destruct x as [[a|c]|[b|d]]; reflexivity.
+ apply functional_extensionality.
  destruct x as [[a|b]|[c|d]]; reflexivity.
Qed.

Theorem sum_shuffle_parallel_comm : forall {A B C D E F G H} (f1 : A -> B) (f2 : C -> D) (f3 : E -> F) (f4 : G -> H),
  sum_shuffle <o> (parallel (parallel f1 f2) (parallel f3 f4)) = (parallel (parallel f1 f3) (parallel f2 f4)) <o> sum_shuffle.
Proof.
intros.
apply functional_extensionality.
destruct x as [[a | c] | [e | g]]; unfold funcomp; simpl; reflexivity.
Qed.

Theorem bij_id_left_neutral : forall {A B} (bij_AB : bijection A B), bij_id <O> bij_AB = bij_AB.
Proof.
intros.
destruct bij_AB.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_id_right_neutral : forall {A B} (bij_AB : bijection A B), bij_AB <O> bij_id = bij_AB.
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

Theorem bij_inv_left_simpl : forall {A B} (bij_AB : bijection A B), bijection_inv bij_AB <O> bij_AB = bij_id.
Proof.
intros.
destruct bij_AB.
unfold bij_compose.
apply bij_eq.
assumption.
assumption.
Qed.

Theorem bij_inv_right_simpl : forall {A B} (bij_AB : bijection A B), bij_AB <O> bijection_inv bij_AB = bij_id.
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

(** Fait le parralèle  *)
Definition bij_sum_compose : forall {A B C D : Type}, bijection A B -> bijection C D -> bijection (A+C) (B+D).
Proof.
intros A B C D bij_AB bij_CD.
apply 
(mkBijection (A+C) (B+D) 
(parallel (@forward  A B bij_AB) (@forward  C D bij_CD)) 
(parallel (@backward A B bij_AB) (@backward C D bij_CD))).
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
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_sum_compose_id : forall {A B}, bij_sum_compose (@bij_id A) (@bij_id B) = bij_id.
Proof.
intros A B.
apply bij_eq.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Theorem bij_sum_compose_compose : forall {A B C D E F : Type} (bij_AB : bijection A B) (bij_BC : bijection B C) (bij_DE : bijection D E) (bij_EF : bijection E F),
  (bij_BC <+> bij_EF) <O> (bij_AB <+> bij_DE) = ((bij_BC <O> bij_AB) <+> (bij_EF <O> bij_DE)).
Proof.
intros A B C D E F bji_AB bij_BC bij_DE bij_EF.
apply bij_eq.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.


Definition bij_prod_compose : forall {A B C D : Type}, bijection A B -> bijection C D -> bijection (A*C) (B*D).
Proof.
intros A B C D bij_AB bij_CD.
apply (mkBijection (A*C) (B*D) 
(product (forward bij_AB) (forward bij_CD)) (product (backward bij_AB) (backward bij_CD))).
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
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_prod_compose_id : forall {A B}, bij_prod_compose (@bij_id A) (@bij_id B) = bij_id.
Proof.
intros A B.
apply bij_eq.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Theorem bij_prod_compose_compose : forall {A B C D E F : Type} (bij_AB : bijection A B) (bij_BC : bijection B C) (bij_DE : bijection D E) (bij_EF : bijection E F),
          bij_prod_compose bij_BC bij_EF <O> bij_prod_compose bij_AB bij_DE = bij_prod_compose (bij_BC <O> bij_AB) (bij_EF <O> bij_DE).
Proof.
intros A B C D E F bji_AB bij_BC bij_DE bij_EF.
apply bij_eq.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Definition bij_fun_compose : forall {A B C D : Type}, 
bijection A B -> 
bijection C D -> 
bijection (A -> C) (B -> D).
Proof.
intros A B C D bij_AB bij_CD.
apply (mkBijection (A->C) (B->D) 
(fun f_AC => (forward bij_CD) <o> f_AC <o> (backward bij_AB)) 
(fun f_BD => (@backward C D bij_CD) <o> f_BD <o> (@forward A B bij_AB))).
+ apply functional_extensionality.
intro f_BD.
apply functional_extensionality.
intro b.
generalize bij_CD.(fob_id C D).
generalize bij_AB.(fob_id A B).
unfold funcomp.
intros HAB HCD.
rewrite (equal_f HAB).
rewrite (equal_f HCD).
reflexivity.
+ apply functional_extensionality.
intro f_AC.
apply functional_extensionality.
intro a.
generalize bij_CD.(bof_id C D).
generalize bij_AB.(bof_id A B).
unfold funcomp.
intros HAB HCD.
rewrite (equal_f HAB).
rewrite (equal_f HCD).
reflexivity.
Defined.

Notation "f -->> g" := (bij_fun_compose f g) (at level 75).

Theorem bij_inv_fun :forall {A B C D : Type} (bij_AB : bijection A B) (bij_CD : bijection C D),
                      bijection_inv (bij_AB -->> bij_CD) = ((bijection_inv bij_AB) -->> (bijection_inv bij_CD)).
Proof.
intros A B C D bij_AB bij_CD.
apply bij_eq.
reflexivity.
reflexivity.
Qed.

Theorem bij_fun_compose_id : forall {A B}, bij_fun_compose (@bij_id A) (@bij_id B) = bij_id.
Proof.
intros A B.
apply bij_eq.
+ apply functional_extensionality.
  intros x.
  apply functional_extensionality.
  reflexivity.
+ apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  reflexivity.
Qed.

Theorem bij_fun_compose_compose : forall {A B C D E F : Type} (bij_AB : bijection A B) (bij_BC : bijection B C) (bij_DE : bijection D E) (bij_EF : bijection E F),
  ((bij_BC -->> bij_EF) <O> (bij_AB -->> bij_DE)) = ((bij_BC <O> bij_AB) -->> (bij_EF <O> bij_DE)).
Proof.
intros A B C D E F bji_AB bij_BC bij_DE bij_EF.
apply bij_eq.
+ apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  reflexivity.
+ apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  reflexivity.
Qed.

Theorem bij_fun_hcompose : forall {A B C D E F : Type} (bij_AB : bijection A B) (bij_CD : bijection C D) (bij_EF : bijection E F) (ac : A -> C) (ce : C -> E),
                              (bij_CD -->> bij_EF) ce <o> (bij_AB -->> bij_CD) ac = (bij_AB -->> bij_EF) (ce <o> ac).
Proof.
intros A B C D E F bij_AB bij_CD bij_EF ac ce.
simpl.
repeat rewrite comp_assoc.
repeat apply comp_left_simpl.
repeat rewrite <- comp_assoc.
erewrite comp_right_simpl.
+ instantiate (1 := ac).
  reflexivity.
+ erewrite comp_right_simpl.
  - instantiate (1 := id).
    reflexivity.
  - apply (bof_id _ _ bij_CD).
Qed.


Definition bij_subset_forward {A B : Type} {P : A -> Prop} {Q : B -> Prop} 
(bij_AB : bijection A B) 
(HEqPQ : forall a, P a <-> Q (forward bij_AB a)) : 
{a:A | P a} -> {b:B | Q b}.
Proof.
apply 
(fun aPa => match aPa with (exist _ a Pa) => exist Q ((forward bij_AB) a) (proj1 ((HEqPQ a)) Pa) end).
Defined.

Definition bij_subset_backward {A B : Type} {P : A -> Prop} {Q : B -> Prop} (bij_AB : bijection A B) (HEqPQ : forall a, P a <-> Q (forward bij_AB a)) : (@sig B Q) -> (@sig A P).
Proof.
refine (fun bQb => match bQb with (exist _ b Qb) => exist P (bij_AB.(backward) b) _ end).
apply HEqPQ.
generalize (equal_f (fob_id _ _ bij_AB) b).
unfold funcomp.
intro H.
rewrite H.
exact Qb.
Defined.

Definition bij_subset_compose : forall {A B : Type} {P : A -> Prop} {Q : B -> Prop} (bij_AB : bijection A B), (forall a, P a <-> Q (bij_AB a)) -> bijection (@sig A P) (@sig B Q).
Proof.
intros A B P Q bij_AB HEqPQ.
apply (mkBijection _ _ (bij_subset_forward bij_AB HEqPQ) (bij_subset_backward bij_AB HEqPQ)).
+ apply functional_extensionality.
  destruct x as (b, Qb).
  apply subset_eq_compat.
  generalize (equal_f (fob_id _ _ bij_AB) b).
  auto.
+ apply functional_extensionality.
  destruct x as (a, Pa).
  apply subset_eq_compat.
  generalize (equal_f (bof_id _ _ bij_AB) a).
  auto.
Defined.

Notation "<{ f | g }>" := (bij_subset_compose f g).

Lemma adjunction_equiv {A B : Type} {P : A -> Prop} {Q : B -> Prop} (bij_AB : bijection A B) :
  (forall a, P a <-> Q (forward bij_AB a)) -> (forall b, Q b <-> P (backward bij_AB b)).
Proof.
intros EqPQ b.
apply iff_sym.
assert (b = id b) as Hb.
+ reflexivity.
+ rewrite Hb at 2.
  rewrite <- (equal_f (fob_id _ _ bij_AB) b).
  exact (EqPQ (backward bij_AB b)).
Qed.

Theorem bij_inv_subset :forall {A B : Type} {P : A -> Prop} {Q : B -> Prop} (bij_AB : bijection A B) (EqPQ : forall a, P a <-> Q (bij_AB a)),
  bijection_inv (<{bij_AB | EqPQ}>) = <{(bijection_inv bij_AB) | (adjunction_equiv bij_AB EqPQ)}>.
Proof.
intros A B P Q bij_AB EqPQ.
apply bij_eq.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
Qed.

Theorem bij_subset_compose_id : forall {A : Type} {P : A -> Prop} 
  (EqPP : forall a, P a <-> P (bij_id a)),
  <{bij_id | EqPP}> = bij_id.
Proof.
intros A P EqPP.
apply bij_eq.
+ simpl.
  apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
+ simpl.
  apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
Qed.

Fail Theorem bij_subset_compose_id' : forall {A : Type} {P : A -> Prop} {Q : A -> Prop}
  (EqPQ : forall a, P a <-> Q (bij_id a)),
  <{bij_id | EqPQ}> = bij_id.
  (* TODO: FIX *)

Theorem bij_subset_compose_id'' : forall {A : Type} {P : A -> Prop} {Q : A -> Prop}
  (EqPQ : forall a, P a <-> Q (bij_id a)),
  forall a:{x : A | P x}, Q (proj1_sig a).
  Proof. intros. simpl in EqPQ. unfold id in EqPQ. apply EqPQ.
  destruct a. simpl. apply p. Qed.

Theorem bij_subset_compose_id''' : forall {A : Type} {P : A -> Prop} {Q : A -> Prop}
  (EqPQ : forall a, P a <-> Q (bij_id a)),
  forall a:A, P a <-> Q a.
  Proof. intros. simpl in EqPQ. unfold id in EqPQ. apply EqPQ. Qed.

Theorem bij_subset_compose_id'''' : forall {A : Type} {P : A -> Prop} {Q : A -> Prop}
  (EqPQ : forall a, P a <-> Q (bij_id a)),
  forall a:{x : A | P x}, P (proj1_sig a) <-> Q (proj1_sig a).
  Proof. intros. simpl in EqPQ. unfold id in EqPQ. apply EqPQ. Qed.


Theorem bij_subset_compose_compose : forall {A B C} {P : A -> Prop} {Q : B -> Prop} {R : C -> Prop}
  (bij_AB : bijection A B) (bij_BC : bijection B C)
  (EqPQ : forall a, P a <-> Q (bij_AB a))
  (EqQR : forall b, Q b <-> R (bij_BC b)),
  <{bij_BC | EqQR}> <O> <{bij_AB | EqPQ}> = <{(bij_BC <O> bij_AB) | (fun a => iff_trans (EqPQ a) (EqQR (bij_AB a)))}>.
Proof.
intros A B C P Q R bij_AB bij_BC EqPQ EqQR.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
Qed.

Theorem bij_subset_compose_compose_id : forall {A} {P : A -> Prop} {Q : A -> Prop} {R : A -> Prop}
  (EqPQ : forall a, P a <-> Q (bij_id a))
  (EqQR : forall b, Q b <-> R (bij_id b)),
  <{bij_id | EqQR}> <O> <{bij_id | EqPQ}> = <{(bij_id) | (fun a => iff_trans (EqPQ a) (EqQR (bij_id a)))}>.
Proof.
intros A P Q R EqPQ EqQR.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
+ apply functional_extensionality.
  destruct x.
  apply subset_eq_compat.
  reflexivity.
Qed.

Definition bij_rew_forward {A} {P : A -> Type} {a b : A} (Hab : a = b) : (P a) -> (P b) := fun pa => eq_rect a P pa b Hab.

Lemma bij_rew : forall {A} {P : A -> Type} {a b : A}, a = b -> bijection (P a) (P b).
Proof.
intros A P a b Hab.
apply (mkBijection _ _ (bij_rew_forward Hab) (bij_rew_forward (eq_sym Hab))).
+ apply functional_extensionality.
  intro Pb.
  unfold bij_rew_forward, funcomp, id.
  erewrite eq_rect_compose.
  instantiate (1 := eq_refl).
  reflexivity.
+ apply functional_extensionality.
  intro Pa.
  unfold bij_rew_forward, funcomp, id.
  erewrite eq_rect_compose.
  instantiate (1 := eq_refl).
  reflexivity.
Defined.

Lemma bij_rew_id : forall {A} {P : A -> Type} {a : A} (Haa : a = a), (@bij_rew A P a a Haa) = bij_id.
Proof.
intros A P a Haa.
apply bij_eq; simpl.
+ apply functional_extensionality.
  intro Pa.
  rewrite (proof_irrelevance (a = a) Haa eq_refl).
  reflexivity.
+ apply functional_extensionality.
  intro Pa.
  rewrite (proof_irrelevance (a = a) Haa eq_refl).
  reflexivity.
Qed.

Lemma bij_inv_rew : forall {A} {P : A -> Type} {a b : A} (Hab : a = b), bijection_inv (@bij_rew A P a b Hab) = @bij_rew A P b a (eq_sym Hab).
Proof.
intros A P a b Hab.
apply bij_eq; simpl.
+ reflexivity.
+ apply f_equal.
  destruct Hab.
  reflexivity.
Qed.

Lemma bij_rew_compose : forall {A} {P : A -> Type} {a b c : A} (Hab : a = b) (Hbc : b = c),
  (@bij_rew A P b c Hbc) <O> (@bij_rew A P a b Hab) = @bij_rew A P a c (eq_trans Hab Hbc).
Proof.
intros A P a b c Hab Hbc.
apply bij_eq; simpl.
+ apply functional_extensionality.
  intro Pa.
  destruct Hab.
  destruct Hbc.
  reflexivity.
+ apply functional_extensionality.
  intro Pc.
  destruct Hab.
  destruct Hbc.
  reflexivity.
Qed.

Lemma bij_rew_sum : forall {A} {P Q : A -> Type} {a b : A} (Hab : a = b),
  (@bij_rew A P a b Hab) <+> (@bij_rew A Q a b Hab) = @bij_rew A (fun a => P a + Q a)%type a b Hab.
Proof.
intros A P Q a b Hab.
destruct Hab.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Lemma bij_rew_prod : forall {A} {P Q : A -> Type} {a b : A} (Hab : a = b),
  (@bij_rew A P a b Hab) <*> (@bij_rew A Q a b Hab) = @bij_rew A (fun a => P a * Q a)%type a b Hab.
Proof.
intros A P Q a b Hab.
destruct Hab.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x; reflexivity.
+ apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Lemma bij_rew_fun : forall {A} {P Q : A -> Type} {a b : A} (Hab : a = b),
  ((@bij_rew A P a b Hab) -->> (@bij_rew A Q a b Hab)) = @bij_rew A (fun a => P a -> Q a)%type a b Hab.
Proof.
intros A P Q a b Hab.
destruct Hab.
apply bij_eq; simpl.
+ apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  reflexivity.
+ apply functional_extensionality.
  intro x.
  apply functional_extensionality.
  reflexivity.
Qed.

Definition adjunction_bij {A B : Type} {P : A -> Type} {Q : B -> Type} (bij_AB : bijection A B) :
  (forall a, bijection (P a) (Q (bij_AB a))) -> (forall b, bijection (Q b) (P (backward bij_AB b))).
Proof.
intros bij_PQ b.
apply bijection_inv.
eapply bij_compose.
+ eapply bij_rew.
  generalize (equal_f (fob_id _ _ bij_AB) b).
  intro Hb.
  apply Hb.
+ exact (bij_PQ (backward bij_AB b)).
Defined.

Definition bij_dep_prod_2_forward {A} {P Q : A -> Type} (bij_PQ : forall a, bijection (P a) (Q a)) : (forall a, P a) -> (forall a, Q a).
Proof.
intros HP a.
exact (forward (bij_PQ a) (HP a)).
Defined.

Lemma bij_dep_prod_2_compose : forall {A} {P Q : A -> Type}, (forall a, bijection (P a) (Q a)) -> bijection (forall a, P a) (forall a, Q a).
Proof.
intros A P Q bij_PQ.
apply (mkBijection _ _ (bij_dep_prod_2_forward bij_PQ) (bij_dep_prod_2_forward (fun a => bijection_inv (bij_PQ a)))).
+ apply functional_extensionality.
  intro HQ.
  apply functional_extensionality_dep.
  intro a.
  unfold funcomp, id.
  unfold bij_dep_prod_2_forward.
  generalize (f_equal (forward) (bij_inv_right_simpl (bij_PQ a))).
  intro H.
  unfold bij_compose, bij_id in H.
  simpl in H.
  unfold funcomp, id in H.
  unfold bijection_inv.
  simpl.
  rewrite (equal_f H (HQ a)).
  reflexivity.
+ apply functional_extensionality.
  intro HP.
  apply functional_extensionality_dep.
  intro a.
  unfold funcomp, id.
  unfold bij_dep_prod_2_forward.
  generalize (f_equal (forward) (bij_inv_left_simpl (bij_PQ a))).
  intro H.
  unfold bij_compose, bij_id in H.
  simpl in H.
  unfold funcomp, id in H.
  unfold bijection_inv.
  simpl.
  rewrite (equal_f H (HP a)).
  reflexivity.
Defined.

Definition bij_dep_prod_1_forward {A B} {P : B -> Type} (bij_AB : bijection A B) : (forall a, P (bij_AB a)) -> (forall b, P b).
Proof.
exact (fun HPa b => eq_rect (bij_AB (backward bij_AB b)) P (HPa (backward bij_AB b)) b (equal_f (fob_id _ _ bij_AB) b)).
Defined.

Definition bij_dep_prod_1_backward {A B} {P : B -> Type} (bij_AB : bijection A B) : (forall b, P b) -> (forall a, P (bij_AB a)).
Proof.
exact (fun HPb a => HPb (bij_AB a)).
Defined.

Lemma bij_dep_prod_1_compose : forall {A B} {P : B -> Type} (bij_AB : bijection A B), bijection (forall a, P (bij_AB a)) (forall b, P b).
Proof.
intros A B P bij_AB.
apply (mkBijection _ _ (bij_dep_prod_1_forward bij_AB) (bij_dep_prod_1_backward bij_AB)).
+ apply functional_extensionality.
  intro HPb.
  apply functional_extensionality_dep.
  intro b.
  unfold bij_dep_prod_1_forward, bij_dep_prod_1_backward, funcomp, id.
  apply eq_rect_image_1.
+ apply functional_extensionality.
  intro HPa.
  apply functional_extensionality_dep.
  intro a.
  unfold bij_dep_prod_1_forward, bij_dep_prod_1_backward, funcomp, id.
  erewrite <- eq_rect_map.
  instantiate (1 := equal_f (bof_id _ _ bij_AB) a).
  rewrite eq_rect_image_1.
  reflexivity.
Defined.

Definition bij_dep_prod_compose : forall {A B : Type} {P : A -> Type} {Q : B -> Type} (bij_AB : bijection A B),
  (forall a, bijection (P a) (Q (bij_AB a))) -> bijection (forall a: A, P a) (forall b : B, Q b).
Proof.
intros A B P Q bij_AB bij_PQ.
apply (@bij_compose _ (forall a : A, Q (bij_AB a)) _).
+ apply (bij_dep_prod_1_compose bij_AB).
+ apply (bij_dep_prod_2_compose bij_PQ).
Defined.

Notation "<'forall' f , g >" := (bij_dep_prod_compose f g).


Theorem bij_inv_dep_prod : forall {A B : Type} {P : A -> Type} {Q : B -> Type} (bij_AB : bijection A B)
  (bij_PQ : forall a, bijection (P a) (Q (bij_AB a))),
  bijection_inv (bij_dep_prod_compose bij_AB bij_PQ) = bij_dep_prod_compose (bijection_inv bij_AB) (adjunction_bij bij_AB bij_PQ).
Proof.
intros A B P Q bij_AB bij_PQ.
apply bij_eq; simpl.
+ apply functional_extensionality.
  intro x.
  unfold bij_dep_prod_2_forward, bij_dep_prod_1_backward, bij_dep_prod_1_forward, funcomp, id.
  apply functional_extensionality_dep.
  intro a.
  simpl.
  unfold funcomp, id.
  unfold bij_rew_forward, eq_rect_r.
  erewrite <- eq_rect_map.
  instantiate (1 := (eq_sym (equal_f (bof_id A B bij_AB) a))).
  rewrite <- (@eq_rect_image_2 _ _ _ (fun a p => backward (bij_PQ a) p) a (backward bij_AB (bij_AB a)) _ _).
  erewrite eq_rect_compose.
  instantiate (1 := eq_refl).
  reflexivity.
+ apply functional_extensionality.
  intro x.
  unfold bij_dep_prod_2_forward, bij_dep_prod_1_backward, bij_dep_prod_1_forward, funcomp, id.
  apply functional_extensionality_dep.
  intro b.
  simpl.
  unfold funcomp, id.
  unfold bij_rew_forward, eq_rect_r.
  reflexivity.
Qed.

Theorem bij_dep_prod_compose_id : forall {A : Type} {P : A -> Type}, bij_dep_prod_compose (@bij_id A) (fun a => @bij_id (P a)) = bij_id.
Proof.
intros A P.
apply bij_eq.
+ simpl.
  apply functional_extensionality.
  intro x.
  unfold bij_dep_prod_1_forward, bij_dep_prod_2_forward, funcomp, id.
  simpl.
  apply functional_extensionality_dep.
  intro a.
  unfold id.
  reflexivity.
+ simpl.
  apply functional_extensionality.
  intro x.
  reflexivity.
Qed.

Theorem bij_dep_prod_compose_compose : forall {A B C} {P : A -> Type} {Q : B -> Type} {R : C -> Type}
                                   (bij_AB : bijection A B) (bij_BC : bijection B C)
                                   (bij_PQ : forall a, bijection (P a) (Q (bij_AB a)))
                                   (bij_QR : forall b, bijection (Q b) (R (bij_BC b))),
         (bij_dep_prod_compose bij_BC bij_QR) <O> (bij_dep_prod_compose bij_AB bij_PQ)  = bij_dep_prod_compose (bij_BC <O> bij_AB) (fun a => (bij_QR (bij_AB a)) <O> (bij_PQ a)).
Proof.
intros A B C P Q R bij_AB bij_BC bij_PQ bij_QR.
apply bij_eq; simpl.
+ apply functional_extensionality.
  intro x.
  unfold bij_dep_prod_1_forward, bij_dep_prod_2_forward, funcomp, id.
  unfold bijection_inv.
  simpl.
  unfold funcomp, id.
  apply functional_extensionality_dep.
  intro c.
(*
  erewrite (@eq_rect_pi _ _ (bij_BC (bij_AB (backward bij_AB (backward bij_BC c))))).
  erewrite (@eq_rect_pi _ _ (bij_BC (backward bij_BC c))).
  erewrite (@eq_rect_pi _ _ (bij_AB (backward bij_AB (backward bij_BC c)))).
*)
  rewrite <- (@eq_rect_image_2 _ _ _ (fun b p => bij_QR b p)).
  erewrite (@eq_rect_map _ _ R (bij_BC)).
  instantiate (1 := f_equal bij_BC (equal_f (fob_id A B bij_AB) ((bij_BC ⁻¹) c))).
  assert (bij_BC (bij_AB (backward bij_AB (backward bij_BC c))) = c) as H.
  - transitivity (bij_BC (backward bij_BC c)).
    * apply f_equal.
      exact (equal_f (fob_id _ _ bij_AB) (backward bij_BC c)).
    * exact (equal_f (fob_id _ _ bij_BC) c).
  - erewrite eq_rect_compose.
    instantiate (1 := H).
    apply f_equal.
    apply proof_irrelevance.
+ apply functional_extensionality.
  intro x.
  unfold bij_dep_prod_1_backward, bij_dep_prod_2_forward, funcomp, id.
  apply functional_extensionality_dep.
  intro a.
  unfold bijection_inv.
  simpl.
  reflexivity.
Qed.


Definition bij_dep_sum_2_forward {A} {P Q : A -> Type} (bij_PQ : forall a, bijection (P a) (Q a)) : (@sigT A P) -> (@sigT A Q).
Proof.
exact (fun aPa => let (a, Pa) := aPa in existT Q a (bij_PQ a Pa)).
Defined.

Lemma bij_dep_sum_2_compose : forall {A} {P Q : A -> Type}, (forall a, bijection (P a) (Q a)) -> bijection (@sigT A P) (@sigT A Q).
Proof.
intros A P Q bij_PQ.
apply (mkBijection _ _ (bij_dep_sum_2_forward bij_PQ) (bij_dep_sum_2_forward (fun a => bijection_inv (bij_PQ a)))).
+ unfold bij_dep_sum_2_forward, funcomp, id.
  apply functional_extensionality.
  intros (a, Qa).
  apply f_equal.
  unfold bijection_inv.
  simpl.
  generalize (equal_f (fob_id _ _ (bij_PQ a)) Qa).
  auto.
+ unfold bij_dep_sum_2_forward, funcomp, id.
  apply functional_extensionality.
  intros (a, Pa).
  apply f_equal.
  unfold bijection_inv.
  simpl.
  generalize (equal_f (bof_id _ _ (bij_PQ a)) Pa).
  auto.
Defined.

Definition bij_dep_sum_1_forward {A B} {P : A -> Type} (bij_AB : bijection A B) : (@sigT A P) -> (@sigT B (P <o> (backward bij_AB))).
Proof.
exact (fun aPa => let (a, Pa) := aPa in @existT B (P <o> (backward bij_AB)) (bij_AB a) (eq_rect_r P Pa (equal_f (bof_id _ _ bij_AB) a))).
Defined.

Definition bij_dep_sum_1_backward {A B} {P : A -> Type} (bij_AB : bijection A B) : (@sigT B (P <o> (backward bij_AB))) -> (@sigT A P).
Proof.
exact (fun bPbijinvb => let (b, Pbijinvb) := bPbijinvb in @existT A P (backward bij_AB b) Pbijinvb).
Defined.

Lemma bij_dep_sum_1_compose : forall {A B} {P : A -> Type} (bij_AB : bijection A B), bijection (@sigT A P) (@sigT B (P <o> (backward bij_AB))).
Proof.
intros A B P bij_AB.
apply (mkBijection _ _ (bij_dep_sum_1_forward bij_AB) (bij_dep_sum_1_backward bij_AB)).
+ apply functional_extensionality.
  intros (b, Pbijinvb).
  unfold bij_dep_sum_1_forward, bij_dep_sum_1_backward, funcomp, id.
  symmetry.
  assert (b = forward bij_AB (backward bij_AB b)) as Hb.
  - generalize (equal_f (fob_id _ _ bij_AB) b).
    auto.
  - generalize (@eq_sigT_intro B (fun x : B => P (backward bij_AB x)) b (forward bij_AB (backward bij_AB b)) Pbijinvb Hb).
    intro H.
    rewrite H; clear H.
    apply f_equal.
    unfold eq_rect_r.
    apply eq_rect_map.
+ apply functional_extensionality.
  intros (a, Pa).
  unfold bij_dep_sum_1_forward, bij_dep_sum_1_backward, funcomp, id.
  symmetry.
  assert (a = backward bij_AB (forward bij_AB a)) as Ha.
  - generalize (equal_f (bof_id _ _ bij_AB) a).
    auto.
  - generalize (@eq_sigT_intro A P a (backward bij_AB (forward bij_AB a)) Pa Ha).
    intro H.
    rewrite H; clear H.
    apply f_equal.
    unfold eq_rect_r.
    apply f_equal.
    unfold eq_sym.
    apply proof_irrelevance.
Defined.

Definition bij_sigT_compose : forall {A B : Type} {P : A -> Type} {Q : B -> Type} (bij_AB : bijection A B),
  (forall a, bijection (P a) (Q (bij_AB a))) -> bijection (@sigT A P) (@sigT B Q).
Proof.
intros A B P Q bij_AB bij_PQ.
apply (@bij_compose _ {a : A & Q (bij_AB a) } _).
+ apply bijection_inv.
  apply (bij_dep_sum_1_compose (bijection_inv bij_AB)).
+ apply (bij_dep_sum_2_compose bij_PQ).
Defined.

Notation "<{ f & g }>" := (bij_sigT_compose f g).


Theorem bij_inv_sigT : forall {A B : Type} {P : A -> Type} {Q : B -> Type} (bij_AB : bijection A B)
  (bij_PQ : forall a, bijection (P a) (Q (bij_AB a))),
  bijection_inv (bij_sigT_compose bij_AB bij_PQ) = bij_sigT_compose (bijection_inv bij_AB) (adjunction_bij bij_AB bij_PQ).
Proof.
intros A B P Q bij_AB bij_PQ.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x.
  unfold bij_dep_sum_2_forward, bij_dep_sum_1_backward, bij_dep_sum_1_forward, funcomp, id.
  apply f_equal.
  simpl.
  unfold funcomp, id.
  apply f_equal.
  unfold bij_rew_forward, eq_rect_r.
  reflexivity.
+ apply functional_extensionality.
  destruct x.
  unfold bij_dep_sum_2_forward, bij_dep_sum_1_backward, bij_dep_sum_1_forward, funcomp, id.
  apply f_equal.
  simpl.
  unfold funcomp, id.
  unfold bij_rew_forward, eq_rect_r.
  erewrite <- eq_rect_map.
  instantiate (1 := equal_f (bof_id _ _ bij_AB) x).
  rewrite (@eq_rect_image_2 _ _ _  (fun x p => forward (bij_PQ x) p) (backward bij_AB (forward bij_AB x)) x).
  apply f_equal.
  erewrite eq_rect_compose.
  instantiate (1 := eq_refl).
  reflexivity.
Qed.

Theorem bij_sigT_compose_id : forall {A : Type} {P : A -> Type}, bij_sigT_compose (@bij_id A) (fun a => @bij_id (P a)) = bij_id.
Proof.
intros A P.
apply bij_eq.
+ simpl.
  apply functional_extensionality.
  destruct x.
  reflexivity.
+ simpl.
  apply functional_extensionality.
  destruct x.
  unfold bij_dep_sum_1_forward, bij_dep_sum_2_forward, funcomp, id.
  simpl.
  symmetry.
  apply eq_sigT_intro.
Qed.

Theorem bij_sigT_compose_compose : forall {A B C} {P : A -> Type} {Q : B -> Type} {R : C -> Type}
                                   (bij_AB : bijection A B) (bij_BC : bijection B C)
                                   (bij_PQ : forall a, bijection (P a) (Q (bij_AB a)))
                                   (bij_QR : forall b, bijection (Q b) (R (bij_BC b))),
         <{ bij_BC & bij_QR }> <O> <{ bij_AB & bij_PQ }>  = <{ bij_BC <O> bij_AB & (fun a => (bij_QR (bij_AB a)) <O> (bij_PQ a)) }>.
Proof.
intros A B C P Q R bij_AB bij_BC bij_PQ bij_QR.
apply bij_eq; simpl.
+ apply functional_extensionality.
  destruct x.
  unfold bij_dep_sum_1_backward, bij_dep_sum_2_forward, funcomp, id.
  assert (backward (@bijection_inv B C bij_BC) (backward (@bijection_inv A B bij_AB) x) = backward (@bijection_inv A C (bij_BC <O> bij_AB)) x) as Hx.
  - reflexivity.
  - apply (eq_existT_curried Hx).
    revert Hx.
    unfold bijection_inv; simpl.
    unfold funcomp; simpl.
    intro Hx.
    rewrite (proof_irrelevance _ Hx eq_refl).
    reflexivity.
+ apply functional_extensionality.
  destruct x.
  unfold bij_dep_sum_1_forward, bij_dep_sum_2_forward, funcomp, id.
  unfold bijection_inv.
  simpl.
  unfold funcomp, id.
  apply f_equal.
  apply f_equal.
  unfold eq_rect_r.
  rewrite (@eq_rect_image_2 _ _ _ (fun x p => backward (bij_QR x) p) (backward bij_BC x) (bij_AB (backward bij_AB (backward bij_BC x)))).
  apply f_equal.
  erewrite (@eq_rect_map _ _ R (forward bij_BC) (backward bij_BC x)).
  instantiate (1 := f_equal (forward bij_BC) (eq_sym (equal_f (fob_id A B bij_AB) (backward bij_BC x)))).
  erewrite eq_rect_compose.
  apply f_equal.
  reflexivity.
Qed.


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
Proof.
apply Nat.succ_lt_mono.
Qed.

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
apply Hk.
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

Fixpoint position {A} (eqA : dec_eq A) (a : A) (l : list A) : nat :=
  match l with
  | nil  => 0 (* unreachable *)
  | t::q => if eqA t a then 0 else S (position eqA a q)
  end.

Theorem position_in : forall {A} (eqA : dec_eq A) (a : A) (l :list A),
  In a l -> position eqA a l < length l.
Proof.
induction l; simpl.
+ contradiction.
+ destruct eqA.
  - subst. intros. apply Nat.lt_0_succ.
  - intros. destruct H.
  * exfalso; apply n; apply H.
  * apply IHl in H. apply lt_n_S_stt. assumption.
Qed.

Theorem position_notin : forall {A} (eqA : dec_eq A) (a : A) (l :list A),
  ~In a l -> position eqA a l = length l.
Proof.
induction l; simpl.
+ reflexivity.
+ destruct eqA.
  - subst.
    intuition.
  - intuition.
Qed.

Definition nth_error_in {T} (n : nat) (l : list T) (H : n < length l) : T.
Proof.
generalize (nth_error_None l n); intro Hnth.
destruct (nth_error l n) as [t | ].
+ exact t.
+ intuition.
  lia.
Defined.

Theorem nth_error_in_nth_error : forall {T} n (l : list T) (Hn : n < length l), 
  nth_error l n = Some (nth_error_in n l Hn).
Proof.
intros.
unfold nth_error_in.
generalize (nth_error_None l n).
generalize (nth_error l n) as ln.
destruct ln.
+ reflexivity.
+ intro H.
  assert (length l <= n).
  - intuition.
  - lia.
Qed.

Theorem nth_error_in_hd : forall {T} (t : T) (q : list T) (H : 0 < length (t::q)),
  nth_error_in 0 (t::q) H = t.
Proof.
intros.
reflexivity.
Qed.

Theorem nth_error_in_tl : forall {T} n (t : T) (q : list T) (Hn : n < length q) (HSn : S n < length (t::q)),
  nth_error_in (S n) (t::q) HSn = nth_error_in n q Hn.
Proof.
intros.
assert (Some (nth_error_in (S n) (t :: q) HSn) = Some (nth_error_in n q Hn)).
+ rewrite <- nth_error_in_nth_error.
  rewrite <- nth_error_in_nth_error.
  reflexivity.
+ injection H.
  auto.
Qed.

Theorem position_nth_error_in : forall {A} (eqA : dec_eq A) n (l : list A) (Hinj : InjectiveXTList l) (Hn : n < length l),
  position eqA (nth_error_in n l Hn) l = n.
Proof.
induction n; intros l Hinjl Hn; simpl.
+ destruct l; simpl.
  - reflexivity.
  - rewrite nth_error_in_hd.
    destruct eqA.
    * reflexivity.
    * contradiction.
+ destruct l.
  - simpl in Hn.
    lia.
  - rewrite (nth_error_in_tl _ _ _ (lt_S_n' _ _ Hn) Hn).
    simpl.
    rewrite IHn.
    * destruct eqA.
      ++ generalize (@f_equal _ _ Some _ _ e); clear e; intro Ha.
         rewrite <- nth_error_in_nth_error in Ha.
         assert (nth_error (a::l) (S n) = nth_error (a::l) 0).
         -- simpl.
            symmetry.
            exact Ha.
         -- generalize (Hinjl _ _ Hn H).
            auto.
      ++ reflexivity.
    * intros i j Hi Hij.
      generalize (Hinjl (S i) (S j)); simpl.
      intro H.
      apply Nat.succ_inj.
      apply H.
      ++ lia.
      ++ exact Hij.
Qed.

Theorem nth_error_position_in : forall {A} (eqA : dec_eq A) (a : A) (l : list A),
  In a l -> nth_error l (position eqA a l) = Some a.
Proof.
induction l; simpl.
+ contradiction.
+ destruct eqA.
  - subst.
    reflexivity.
  - intuition.
Qed.

Theorem nth_error_position_notin : forall {A} (eqA : dec_eq A) (a : A) (l : list A),
  ~In a l -> nth_error l (position eqA a l) = None.
Proof.
induction l; simpl.
+ reflexivity.
+ destruct eqA.
  - subst.
    intuition.
  - intuition.
Qed.


Definition bij_transform {N M I O : Type} (bij : bijection N M) (f : N+I -> N+O) : M+I -> M+O :=
 (parallel (forward bij) id) <o> f <o> (parallel (backward bij) id).

Theorem bij_transform_bij_id : forall {N I O : Type} (f : N+I -> N+O), bij_transform bij_id f = f.
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

(*
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
Qed.*)

Theorem bij_subset : forall {A} (P : A -> Prop), (forall a, P a) -> bijection A { a : A | P a }.
Proof.
intros A P HP.
apply (mkBijection _ _ (fun a => exist P a (HP a)) (fun a => proj1_sig a)); unfold funcomp, id; apply functional_extensionality.
+ destruct x as (a, Ha).
  apply subset_eq_compat.
  reflexivity.
+ reflexivity.
Defined.

Definition forward_subset_subset {A} (P : A -> Prop) (Q : {a | P a} -> Prop) : { b : { a | P a } | Q b } -> { a : A | P a /\ forall (Ha : P a), Q (exist P a Ha) }.
Proof.
destruct 1 as ((a, Pa), Qb).
exists a.
split.
+ exact Pa.
+ intro Ha.
  erewrite subset_eq_compat.
  - apply Qb.
  - reflexivity.
Defined.

Definition backward_subset_subset {A} (P : A -> Prop) (Q : {a | P a} -> Prop) : { a : A | P a /\ forall (Ha : P a), Q (exist P a Ha) } -> { b : { a | P a } | Q b }.
Proof.
destruct 1 as (a, (Pa, Qa)).
exists (exist P a Pa).
apply Qa.
Defined.

Theorem bij_subset_subset : forall {A} (P : A -> Prop) (Q : {a | P a} -> Prop),
  bijection { b : { a | P a } | Q b } { a : A | P a /\ forall (Ha : P a), Q (exist P a Ha) }.
Proof.
intros A P Q.
apply (mkBijection _ _ (forward_subset_subset P Q) (backward_subset_subset P Q)); unfold funcomp, id; apply functional_extensionality.
+ destruct x as (a, (Pa, Qa)).
  simpl.
  apply subset_eq_compat.
  reflexivity.
+ destruct x as ((a, Pa), Qa).
  simpl.
  apply subset_eq_compat.
  reflexivity.
Qed.

Theorem bij_subset_equiv : forall {A} (P : A -> Prop) (Q : A -> Prop),
  (forall a, P a <-> Q a) -> bijection { a : A | P a } { a : A | Q a }.
Proof.
intros A P Q Heq.
assert (forall a, P a -> Q a) as HPQ; [firstorder |].
assert (forall a, Q a -> P a) as HQP; [firstorder |].
apply (mkBijection _ _ (fun a => match a with exist _ a Ha => exist Q a (HPQ a Ha) end) (fun a => match a with exist _ a Ha => exist P a (HQP a Ha) end)); unfold funcomp, id; apply functional_extensionality.
+ destruct x as (a, Qa); simpl.
  apply subset_eq_compat.
  reflexivity.
+ destruct x as (a, Pa).
  apply subset_eq_compat.
  reflexivity.
Qed.


Definition rearrange_sum {A B C D : Type} (abcd : (A+B)+(C+D)) : ((A+C)+(B+D)) :=
  match abcd with
  | inl (inl a) => inl (inl a)
  | inl (inr b) => inr (inl b)
  | inr (inl c) => inl (inr c)
  | inr (inr d) => inr (inr d) 
  end.


Definition bij_sum_rearrange {I J K}
  (bik :bijection I K) 
  (bjk :bijection J K):  
  bijection (I+J) K.
Proof.
  apply (mkBijection 
    (I + J) 
    K 
    (fun ij => match ij with 
      | inl i => bik i
      | inr j => bjk j
      end
    )
    (fun k => inl (bik⁻¹ k) )).
  - unfold funcomp.
    destruct bik. 
    unfold funcomp in fob_id0. 
    simpl. 
    apply fob_id0.
  - unfold funcomp.
    apply functional_extensionality.
    intros [i | j];
    destruct bjk;
    unfold funcomp in fob_id0;
    simpl; unfold id. 
Abort.


Theorem equality_bij {A B} (bij1 : bijection A B) (bij2 : bijection A B): 
  bij1 = bij2 <-> (forward bij1) = (forward bij2) /\ (backward bij1) = (backward bij2).
  Proof. 
  split.
  - intros. rewrite H. split; reflexivity.
  - intros.  destruct bij1 as [f1 b1 fob1 bof1], bij2 as [f2 b2 fob2 bof2].
  simpl in H.
  destruct H.
  destruct H.
  destruct H0.
  assert (fob2 = fob1). { destruct fob1. auto. simpl in fob2.
  Abort.

  Lemma tensor_alt : forall {N1 I1 O1 N2 I2 O2} (f1 : N1 + I1 -> N1 + O1) (f2 : N2 + I2 -> N2 + O2), 
  f1 ** f2 = (bij_sum_shuffle <o> (parallel f1 f2) <o> (bijection_inv bij_sum_shuffle)).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as [[n1|n2]|[i1|i2]]; reflexivity.
  Qed.

  Theorem bijidObijid {A}: @bij_id A <O> bij_id = bij_id.
  Proof. apply bij_eq.
  -  unfold bij_compose,funcomp,parallel,bij_id,id. simpl. reflexivity.
  -  unfold bij_compose,funcomp,parallel,bij_id,id. simpl. reflexivity. 
  Qed.

  Theorem bij_eq_comp_id {A} : @bij_id A <O> bij_id = bij_id.
  Proof.
  unfold bij_compose. simpl. unfold bij_id. apply bij_eq. 
  - simpl. auto.
  - simpl. auto. 
  Qed.