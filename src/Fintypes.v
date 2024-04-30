(*
  Finite types 
*)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import List.
Require Import Euclid.
Require Import Arith.
Require Import Compare_dec PeanoNat.
Require Import Lia.

Import ListNotations.

Require Import MyBasics.
Require Import Bijections.

Definition Finite (N : Type) : Type := { l : list N | SurjectiveList l /\ InjectiveXTList l }.

Definition cardinal {T} (F : Finite T) := List.length (proj1_sig F).

Lemma injective_some : forall {A}, @InjectiveXT A _ Some.
Proof.
intros A x y Hxy.
injection Hxy.
exact (fun eq => eq).
Qed.

Theorem bij_Finite_fin : forall {T} (eqT : dec_eq T) (F : Finite T), bijection T (fin (cardinal F)).
Proof.
intros T eqT F.
destruct F as (l, (Hl1, Hl2)).
unfold cardinal; simpl.
apply (mkBijection _ _ (fun t => exist (fun p => p < length l) (position eqT t l) (position_in eqT t l (Hl1 t)))
                       (fun np => let (n, Hn) := np in nth_error_in n l Hn)).
+ apply functional_extensionality.
  destruct x as (n, Hn).
  unfold id, funcomp.
  apply subset_eq_compat.
  apply position_nth_error_in.
  exact Hl2.
+ apply functional_extensionality.
  intro x.
  unfold id, funcomp.
  apply injective_some.
  rewrite <- nth_error_in_nth_error.
  rewrite nth_error_position_in.
  - reflexivity.
  - apply Hl1.
Defined.

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

Theorem finite_bool : Finite bool.
Proof.
exists (false::true::[]).
split.
+ intro b.
  destruct b.
  - apply in_cons.
    apply in_eq.
  - apply in_eq.
+ intros i j Hi.
  destruct i; simpl.
  - destruct j; simpl.
    * reflexivity.
    * intro H.  
      destruct j; simpl.
      ++ discriminate.
      ++ simpl in H.
         destruct j; discriminate.
  - destruct j; simpl.
    * destruct i; simpl.
      ++ discriminate.
      ++ destruct i; discriminate.
    * destruct i; simpl.
      ++ destruct j; simpl.
         -- reflexivity.
         -- destruct j; discriminate.
      ++ simpl in Hi; lia.
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

Theorem nth_error_map {T:Type}: forall U (f : T -> U) ls n,
    nth_error (map f ls) n = match nth_error ls n with
                               | None => None
                               | Some x => Some (f x)
                             end.
  Proof.
    induction ls; destruct n; simpl; auto.
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


Theorem lt_S_n' : forall n m : nat, S n < S m -> n < m.
Proof. apply Nat.succ_lt_mono. Qed.

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
    * split. ** auto. ** split. *** apply Nat.lt_0_succ. *** reflexivity. 
    * destruct (IHlA i' (lt_S_n' _ _ Hi)) as (Hij', (Hj, Hij'')).
      split.
      ** apply le_n_S. assumption.
      ** split. 
      *** apply le_n_S. assumption.
      *** auto.
  - destruct (IHlA i Hi).
    split.
    ** apply Nat.le_le_succ_r. assumption.
    ** split. 
    *** destruct H0; auto. apply lt_n_S_stt. assumption.
    *** destruct H0; auto.
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

Theorem dec_image : forall A B (f : A -> B), Finite A -> dec_eq B -> forall b, decidable (exists a, b = f a).
Proof.
intros A B f FA eqB b.
apply finite_dec_exists.
+ exact FA.
+ intros a.
  apply eqB.
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

Lemma in_elt {A:Type} : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
Proof.
intros.
induction l1.
- simpl. left. reflexivity.
- apply (in_cons a). auto.
Qed.

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
  unfold spec_image.
  firstorder.
  exists x.
  split. 
  * unfold SurjectiveList in HlA1.
  specialize (HlA1 x). apply in_or_app. right. assumption. 
  * assumption.
+ rewrite H.
  exists img.
  intuition.
Qed.

Theorem finite_empty_subset : forall A (P : A -> Prop), (forall a, ~(P a)) -> Finite { a : A | P a }.
Proof.
intros A P HnP.
exists [].
split.
+ destruct 1.
  elim (HnP x p).
+ intros i j Hi.
  simpl in Hi.
  lia.
Qed.

Theorem finite_subset_inv : forall A (P : A -> Prop), (forall a, P a) -> Finite { a : A | P a } -> Finite A.
Proof.
intros A P HP FA.
apply (finite_disjoint_union _ P).
+ intros a.
  left.
  apply HP.
+ exact FA.
+ apply finite_empty_subset.
  intuition.
Qed.

Theorem finite_bij : forall A B (bij : bijection A B), Finite A -> Finite B.
Proof.
intros A B bij (lA, (HlA1, HlA2)).
exists (map (forward bij) lA).
split.
+ intro b.
  apply (injective_in_map_inv _ _ (backward bij)).
  - assert (backward bij = forward (bijection_inv bij)).
    * destruct bij.
      reflexivity.
    * rewrite H.
      apply bij_injective.
  - generalize (map_comp A B A (forward bij) (backward bij)).
    rewrite bij.(bof_id A B).
    unfold funcomp.
    intro H.
    rewrite (equal_f H lA).
    rewrite map_id.
    apply HlA1.
+ intros i j Hi.
  rewrite nth_error_map.
  rewrite nth_error_map.
  intro H.
  apply HlA2.
  - rewrite map_length in Hi.
    exact Hi.
  - revert H.
    generalize (nth_error lA i).
    generalize (nth_error lA j).
    intros o1 o2 Ho12.
    apply (inj_option_map A B (forward bij) (bij_injective bij)).
    exact Ho12.
Qed.

Theorem finite_surjective : forall A B (f : A -> B), dec_eq B -> SurjectiveXT f -> Finite A -> Finite B.
Proof.
intros A B f HeqB Hsurjf FA.
apply (finite_subset_inv _ (fun a => exists b, a = f b)).
+ intro b.
  destruct (Hsurjf b).
  exists x.
  assumption.
+ apply finite_image.
  - exact HeqB.
  - exact FA.
Qed.


Module Old.

Definition subset_in_list {A} := fun l => { a : A | In a l }.

Definition subset_nil {A} : @subset_in_list A [] -> bool :=
 fun a => let (a, H) := a in (False_rec bool (@in_nil _ a H)).

Definition subset_cons {A} (eqA : dec_eq A) (t : A) (pt : bool) {q : list A} (Htq : NoDup (t::q)) (pq : subset_in_list q -> bool) : subset_in_list (t::q) -> bool :=
  fun a => let (a, Ha_tq) := a in
    match eqA t a with
    | left  _    => pt
    | right Hneq => let Ha_q :=
                    match Ha_tq with
                    | or_introl Heq => False_ind (In a q) (Hneq Heq)
                    | or_intror a_q => a_q
                    end in
                    pq (exist (fun a => In a q) a Ha_q)
    end.

Definition subset_tl {A} {t : A} {q : list A} (ptq : subset_in_list (t::q) -> bool) : subset_in_list q -> bool :=
  fun a => let (a, Ha_q) := a in
    ptq (exist (fun a => In a (t::q)) a (in_cons t a q Ha_q)).

Lemma cancel_tl_cons : forall {A} (eqA : dec_eq A) {t : A} {pt : bool} {q : list A} (Htq : NoDup (t::q)) (pq : subset_in_list q -> bool),
  subset_tl (subset_cons eqA t pt Htq pq) = pq.
Proof.
intros A eqA t pt q Htq pq.
apply functional_extensionality.
destruct x as (a, Ha).
simpl.
destruct eqA.
+ subst.
  inversion Htq.
  contradiction.
+ apply f_equal.
  apply subset_eq_compat.
  reflexivity.
Qed.

Lemma cancel_cons_tl : forall {A} (eqA : dec_eq A) {t : A} {q : list A} (Htq : NoDup (t::q)) (p : subset_in_list (t::q) -> bool),
  subset_cons eqA t (p (exist (fun x => In x (t::q)) t (in_eq t q))) Htq (subset_tl p) = p.
Proof.
intros A eqA t q Htq p.
apply functional_extensionality.
destruct x as (a, Ha).
simpl.
destruct eqA; subst.
+ erewrite subset_eq_compat.
  - apply eq_refl.
  - reflexivity.
+ inversion Ha; subst.
  - contradiction.
  - erewrite subset_eq_compat.
    * apply eq_refl.
    * reflexivity.
Qed.

Lemma disjoint_subset_cons : forall {A} (eqA : dec_eq A) (t : A) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : subset_in_list q -> bool),
  subset_cons eqA t true Htq1 pq1 <> subset_cons eqA t false Htq2 pq2.
Proof.
intros A eqA t q Htq1 Htq2 pq1 pq2 Heq.
generalize (equal_f Heq (exist (fun a => In a (t::q)) t (in_eq t q))); simpl.
destruct eqA.
+ discriminate.
+ auto.
Qed.

Lemma injective_subset_cons : forall {A} (eqA : dec_eq A) (t : A) (pt : bool) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : subset_in_list q -> bool),
  subset_cons eqA t pt Htq1 pq1 = subset_cons eqA t pt Htq2 pq2 -> pq1 = pq2.
Proof.
intros A eqA t pt q Htq1 Htq2 pq1 pq2 Heq.
apply functional_extensionality.
destruct x as (a, Ha).
generalize (equal_f Heq (exist (fun a => In a (t::q)) a (in_cons t a q Ha))).
simpl.
destruct eqA.
+ inversion Htq1.
  subst.
  contradiction.
+ erewrite <- subset_eq_compat.
  intro H.
  apply H.
  reflexivity.
Qed.

Fixpoint powerset {A} (eqA : dec_eq A) (lA : list A) : NoDup lA -> list (subset_in_list lA -> bool) :=
  match lA with
  | []   => (fun _ => [subset_nil])
  | t::q => (fun Htq => let pq := powerset eqA q (nodup_tl t q Htq) in
              (map (subset_cons eqA t false Htq) pq) ++ (map (subset_cons eqA t true Htq) pq))
  end.

Theorem nodup_powerset : forall A (eqA : dec_eq A) (lA : list A) (HlA : NoDup lA), NoDup (powerset eqA lA HlA).
Proof.
induction lA; simpl.
+ intros _.
  apply NoDup_cons.
  - apply in_nil.
  - apply NoDup_nil.
+ intro HlA.
  inversion HlA.
  subst.
  apply nodup_app.
  - apply nodup_map.
    * unfold InjectiveXT.
      intros p q Heq.
      exact (injective_subset_cons eqA a false HlA HlA p q Heq).
    * apply IHlA.
  - apply nodup_map.
    * unfold InjectiveXT.
      intros p q Heq.
      exact (injective_subset_cons eqA a true HlA HlA p q Heq).
    * apply IHlA.
  - apply forall_Forall.
    intros p Hp1 Hp2.
    generalize (in_map_iff (subset_cons eqA a false HlA) (powerset eqA lA (nodup_tl a lA HlA)) p).
    intuition.
    clear H0.
    destruct H as (q, (Hq1, Hq2)).
    generalize (in_map_iff (subset_cons eqA a true HlA) (powerset eqA lA (nodup_tl a lA HlA)) p).
    intuition.
    clear H0.
    destruct H as (r, (Hr1, Hr2)).
    eapply disjoint_subset_cons.
    transitivity p.
    apply Hr1.
    symmetry.
    apply Hq1.
Qed.

Theorem surjective_powerset : forall {A} (eqA : dec_eq A) (lA : list A) (HlA : NoDup lA), SurjectiveList (powerset eqA lA HlA).
Proof.
induction lA; simpl.
+ intros _ p.
  assert (p = subset_nil).
  - apply functional_extensionality.
    intros (a ,Ha).
    elim (in_nil Ha).
  - subst.
    apply in_eq.
+ intros HlA p.
  apply in_or_app.
  case_eq (p (exist (fun x => In x (a::lA)) a (in_eq a lA))); intro Hpa.
  - right.
    generalize (in_map_iff (subset_cons eqA a true HlA) (powerset eqA lA (nodup_tl a lA HlA)) p).
    intuition.
    apply H1.
    exists (subset_tl p).
    split.
    * rewrite <- Hpa.
      apply cancel_cons_tl.
    * apply (IHlA (nodup_tl a lA HlA)).
  - left.
    generalize (in_map_iff (subset_cons eqA a false HlA) (powerset eqA lA (nodup_tl a lA HlA)) p).
    intuition.
    apply H1.
    exists (subset_tl p).
    split.
    * rewrite <- Hpa.
      apply cancel_cons_tl.
    * apply (IHlA (nodup_tl a lA HlA)).
Qed.

Theorem finite_powerset : forall A, dec_eq A -> Finite A -> Finite (A -> bool).
Proof.
intros A eqA (lA, (HlA1, HlA2)).
apply (finite_bij (subset_in_list lA -> bool) (A -> bool)).
+ apply bij_fun_compose.
  - apply bijection_inv.
    apply bij_subset.
    apply HlA1.
  - apply bij_id.
+ exists (powerset eqA lA (injective_nodup _ _ HlA2)).
  split.
  - apply surjective_powerset.
  - apply nodup_injective.
    apply nodup_powerset.
Qed.

Theorem finite_subset_equiv : forall A (P Q : A -> Prop), (forall a, P a <-> Q a) -> Finite { a : A | Q a } -> Finite { a : A | P a }.
Proof.
intros A P Q HPQ FQA.
eapply finite_bij.
+ apply bijection_inv.
  apply bij_subset_equiv.
  apply HPQ.
+ exact FQA.
Qed.

Theorem finite_subset_incl : forall A (P Q : A -> Prop), (forall a, P a -> Q a) -> (forall a, decidable (P a)) -> Finite { a : A | Q a } -> Finite { a : A | P a }.
Proof.
intros A P Q HPQ HdecP FQA.
assert (forall a, P a <-> (Q a /\ forall (Ha : Q a), ((P <o> (@proj1_sig A _)) (exist Q a Ha)))).
+ firstorder.
+ eapply finite_bij.
  - apply bijection_inv.
    apply (bij_subset_equiv _ _ H).
  - eapply finite_bij.
    * apply bij_subset_subset.
    * apply finite_subset.
      ++ exact FQA.
      ++ destruct a as (a, Ha).
         unfold funcomp.
         simpl.
         apply HdecP.
Qed.

End Old.

Definition subset_in_list {A} := fun l => { a : A | In a l }.

Definition subset_nil {A B} : @subset_in_list A [] -> B :=
 fun a => let (a, H) := a in (False_rect B (@in_nil _ a H)).

Definition subset_cons {A B} (eqA : dec_eq A) (t : A) (pt : B) {q : list A} (Htq : NoDup (t::q)) (pq : subset_in_list q -> B) : subset_in_list (t::q) -> B :=
  fun a => let (a, Ha_tq) := a in
    match eqA t a with
    | left  _    => pt
    | right Hneq => let Ha_q :=
                    match Ha_tq with
                    | or_introl Heq => False_ind (In a q) (Hneq Heq)
                    | or_intror a_q => a_q
                    end in
                    pq (exist (fun a => In a q) a Ha_q)
    end.

Definition subset_tl {A B} {t : A} {q : list A} (ptq : subset_in_list (t::q) -> B) : subset_in_list q -> B :=
  fun a => let (a, Ha_q) := a in
    ptq (exist (fun a => In a (t::q)) a (in_cons t a q Ha_q)).

Lemma cancel_tl_cons : forall {A B} (eqA : dec_eq A) {t : A} {pt : B} {q : list A} (Htq : NoDup (t::q)) (pq : subset_in_list q -> B),
  subset_tl (subset_cons eqA t pt Htq pq) = pq.
Proof.
intros A B eqA t pt q Htq pq.
apply functional_extensionality.
destruct x as (a, Ha).
simpl.
destruct eqA.
+ subst.
  inversion Htq.
  contradiction.
+ apply f_equal.
  apply subset_eq_compat.
  reflexivity.
Qed.

Lemma cancel_cons_tl : forall {A B} (eqA : dec_eq A) {t : A} {q : list A} (Htq : NoDup (t::q)) (p : subset_in_list (t::q) -> B),
  subset_cons eqA t (p (exist (fun x => In x (t::q)) t (in_eq t q))) Htq (subset_tl p) = p.
Proof.
intros A B eqA t q Htq p.
apply functional_extensionality.
destruct x as (a, Ha).
simpl.
destruct eqA; subst.
+ erewrite subset_eq_compat.
  - apply eq_refl.
  - reflexivity.
+ inversion Ha; subst.
  - contradiction.
  - erewrite subset_eq_compat.
    * apply eq_refl.
    * reflexivity.
Qed.

Lemma injective_subset_cons_1 : forall {A B} (eqA : dec_eq A) (t : A) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : subset_in_list q -> B),
  forall b1 b2, subset_cons eqA t b1 Htq1 pq1 = subset_cons eqA t b2 Htq2 pq2 -> b1 = b2.
Proof.
intros A B eqA t q Htq1 Htq2 pq1 pq2 b1 b2 Heq.
generalize (equal_f Heq (exist (fun a => In a (t::q)) t (in_eq t q))); simpl.
destruct eqA.
+ auto.
+ elim n.
  reflexivity.
Qed.

Lemma injective_subset_cons : forall {A B} (eqA : dec_eq A) (t : A) (pt : B) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : subset_in_list q -> B),
  subset_cons eqA t pt Htq1 pq1 = subset_cons eqA t pt Htq2 pq2 -> pq1 = pq2.
Proof.
intros A B eqA t pt q Htq1 Htq2 pq1 pq2 Heq.
apply functional_extensionality.
destruct x as (a, Ha).
generalize (equal_f Heq (exist (fun a => In a (t::q)) a (in_cons t a q Ha))).
simpl.
destruct eqA.
+ inversion Htq1.
  subst.
  contradiction.
+ erewrite <- subset_eq_compat.
  intro H.
  apply H.
  reflexivity.
Qed.

Fixpoint power {A B} (eqA : dec_eq A) (lA : list A) (lB : list B) : NoDup lA -> list (subset_in_list lA -> B) :=
  match lA with
  | []   => (fun _   => [@subset_nil A B])
  | t::q => (fun Htq => let pq := power eqA q lB (nodup_tl t q Htq) in
              flat_map (fun p => map (fun pt => subset_cons eqA t pt Htq p) lB) pq)
  end.

Theorem nodup_power : forall A B (eqA : dec_eq A) (lA : list A) (lB : list B) (HlA : NoDup lA), NoDup lB -> NoDup (power eqA lA lB HlA).
Proof.
induction lA; simpl.
+ intros _ _ _.
  apply NoDup_cons.
  - apply in_nil.
  - apply NoDup_nil.
+ intros lB HlA HlB.
  inversion HlA.
  subst.
  apply nodup_flat_map.
  - apply IHlA.
    exact HlB.
  - intro p.
    apply nodup_map.
    * unfold InjectiveXT.
      intros b1 b2 Heq.
      eapply injective_subset_cons_1.
      apply Heq.
    * exact HlB.
  - intros p q Hnpq.
    apply forall_Forall.
    intros p' Hp1' Hp2'.
    generalize (in_map_iff (fun pt : B => subset_cons eqA a pt HlA p) lB p').
    intuition.
    clear H0.
    destruct H as (b, (Hb1, Hb2)).
    generalize (in_map_iff (fun pt : B => subset_cons eqA a pt HlA q) lB p').
    intuition.
    clear H0.
    destruct H as (b', (Hb1', Hb2')).
    apply Hnpq.
    eapply injective_subset_cons.
    etransitivity.
    * apply Hb1.
    * symmetry.
      assert (b = b').
      ++ eapply injective_subset_cons_1.
         etransitivity.
         -- apply Hb1.
         -- symmetry.
            apply Hb1'.
      ++ subst.
         apply Hb1'.
Qed.

Theorem surjective_power : forall {A B} (eqA : dec_eq A) (lA : list A) (lB : list B) (HlA : NoDup lA), SurjectiveList lB -> SurjectiveList (power eqA lA lB HlA).
Proof.
induction lA; simpl.
+ intros _ _ _ p.
  assert (p = subset_nil).
  - apply functional_extensionality.
    intros (a ,Ha).
    elim (in_nil Ha).
  - subst.
    apply in_eq.
+ intros lB HlA HlB p.
  apply in_flat_map.
  exists (subset_tl p).
  split.
  - apply IHlA.
    exact HlB.
  - apply in_map_iff.
    exists (p (exist (fun x => In x (a::lA)) a (in_eq a lA))).
    split.
    * apply cancel_cons_tl.
    * apply HlB.
Qed.

Theorem finite_power : forall {A B}, dec_eq A -> Finite A -> Finite B -> Finite (A -> B).
Proof.
intros A B eqA (lA, (HlA1, HlA2)) (lB, (HlB1, HlB2)).
apply (finite_bij (subset_in_list lA -> B) (A -> B)).
+ apply bij_fun_compose.
  - apply bijection_inv.
    apply bij_subset.
    apply HlA1.
  - apply bij_id.
+ exists (power eqA lA lB (injective_nodup _ _ HlA2)).
  split.
  - apply surjective_power.
    exact HlB1.
  - apply nodup_injective.
    apply nodup_power.
    apply injective_nodup.
    exact HlB2.
Qed.

Definition subset_dep_prod_nil {A} {B : A -> Type} : forall a : @subset_in_list A [], B (proj1_sig a) :=
 fun aHa => let (a, H) := aHa in (False_rect (B (proj1_sig aHa)) (@in_nil _ a H)).

Definition subset_dep_prod_cons {A B} (eqA : dec_eq A) (t : A) (pt : B t) {q : list A} (Htq : NoDup (t::q)) (pq : forall a : subset_in_list q, B (proj1_sig a)) : forall a : subset_in_list (t::q), B (proj1_sig a) :=
  fun aHa => match aHa with
             | exist _ a Ha_tq => match eqA t a with
                                  | left  Heq  => eq_rect t _ pt a Heq
                                  | right Hneq => let Ha_q :=
                                                  match Ha_tq with
                                                  | or_introl Heq => False_ind (In a q) (Hneq Heq)
                                                  | or_intror a_q => a_q
                                                  end in
                                                  pq (exist (fun a => In a q) a Ha_q)
                                  end
             end.

Definition subset_dep_prod_tl {A} {B : A -> Type} {t : A} {q : list A} (ptq : forall a : subset_in_list (t::q), B (proj1_sig a)) : forall a : subset_in_list q, B (proj1_sig a) :=
  fun aHa => match aHa with
             | exist _ a Ha_q => ptq (exist (fun a => In a (t::q)) a (in_cons t a q Ha_q))
             end.

Lemma cancel_dep_prod_tl_cons : forall {A} {B : A -> Type} (eqA : dec_eq A) {t : A} {pt : B t} {q : list A} (Htq : NoDup (t::q)) (pq : forall a : subset_in_list q, B (proj1_sig a)),
  subset_dep_prod_tl (subset_dep_prod_cons eqA t pt Htq pq) = pq.
Proof.
intros A B eqA t pt q Htq pq.
apply functional_extensionality_dep.
destruct x as (a, Ha).
simpl.
destruct eqA.
+ subst.
  inversion Htq.
  contradiction.
+ assert (match in_cons t a q Ha with
     | or_introl Heq => False_ind (In a q) (n Heq)
     | or_intror a_q => a_q
     end = Ha).
  - apply proof_irrelevance.
  - rewrite H.
    reflexivity.
Qed.

Lemma cancel_dep_prod_cons_tl : forall {A} {B : A -> Type} (eqA : dec_eq A) {t : A} {q : list A} (Htq : NoDup (t::q)) (p : forall a : subset_in_list (t::q), B (proj1_sig a)),
  subset_dep_prod_cons eqA t (p (exist (fun x => In x (t::q)) t (in_eq t q))) Htq (subset_dep_prod_tl p) = p.
Proof.
intros A B eqA t q Htq p.
apply functional_extensionality_dep.
destruct x as (a, Ha).
simpl.
destruct eqA; subst.
+ rewrite <- eq_rect_eq. 
  rewrite (proof_irrelevance _ (in_eq a q) Ha).
  reflexivity.
+ inversion Ha; subst.
  - contradiction.
  - rewrite (proof_irrelevance _ (in_cons t a q
        match Ha with
        | or_introl Heq => False_ind (In a q) (n Heq)
        | or_intror a_q => a_q
        end) Ha).
    reflexivity.
Qed.

Lemma injective_subset_dep_prod_cons_1 : forall {A} {B : A -> Type} (eqA : dec_eq A) (t : A) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : forall a : subset_in_list q, B (proj1_sig a)),
  forall b1 b2, subset_dep_prod_cons eqA t b1 Htq1 pq1 = subset_dep_prod_cons eqA t b2 Htq2 pq2 -> b1 = b2.
Proof.
intros A B eqA t q Htq1 Htq2 pq1 pq2 b1 b2 Heq.
generalize (equal_f_dep Heq (exist (fun a => In a (t::q)) t (in_eq t q))); simpl.
destruct eqA.
+ intro H.
  rewrite <- eq_rect_eq in H.
  rewrite <- eq_rect_eq in H.
  exact H.
+ elim n.
  reflexivity.
Qed.

Lemma injective_subset_dep_prod_cons : forall {A} {B : A -> Type} (eqA : dec_eq A) (t : A) (pt : B t) {q : list A} (Htq1 Htq2 : NoDup (t::q)) (pq1 pq2 : forall a : subset_in_list q, B (proj1_sig a)),
  subset_dep_prod_cons eqA t pt Htq1 pq1 = subset_dep_prod_cons eqA t pt Htq2 pq2 -> pq1 = pq2.
Proof.
intros A B eqA t pt q Htq1 Htq2 pq1 pq2 Heq.
apply functional_extensionality_dep.
destruct x as (a, Ha).
generalize (equal_f_dep Heq (exist (fun a => In a (t::q)) a (in_cons t a q Ha))).
simpl.
destruct eqA.
+ inversion Htq1.
  subst.
  contradiction.
+ assert (match in_cons t a q Ha with
     | or_introl Heq0 => False_ind (In a q) (n Heq0)
     | or_intror a_q => a_q
     end = Ha) as H.
  - apply proof_irrelevance.
  - rewrite H.
    auto.
Qed.

Fixpoint dep_prod {A} {B : A -> Type} (eqA : dec_eq A) (lA : list A) (laB : forall a, list (B a)) : NoDup lA -> list (forall a : subset_in_list lA, B (proj1_sig a)) :=
  match lA with
  | []   => (fun _   => [@subset_dep_prod_nil A B])
  | t::q => (fun Htq => let pq := dep_prod eqA q laB (nodup_tl t q Htq) in
              flat_map (fun p => map (fun pt => subset_dep_prod_cons eqA t pt Htq p) (laB t)) pq)
  end.

Theorem nodup_dep_prod : forall {A} {B : A -> Type} (eqA : dec_eq A) (lA : list A) (laB : forall a, list (B a)) (HlA : NoDup lA), (forall a, NoDup (laB a)) -> NoDup (dep_prod eqA lA laB HlA).
Proof.
induction lA; simpl.
+ intros _ _ _.
  apply NoDup_cons.
  - apply in_nil.
  - apply NoDup_nil.
+ intros laB HlA HlaB.
  inversion HlA.
  subst.
  apply nodup_flat_map.
  - apply IHlA.
    exact HlaB.
  - intro p.
    apply nodup_map.
    * unfold InjectiveXT.
      intros b1 b2 Heq.
      eapply injective_subset_dep_prod_cons_1.
      apply Heq.
    * exact (HlaB a).
  - intros p q Hnpq.
    apply forall_Forall.
    intros p' Hp1' Hp2'.
    generalize (in_map_iff (fun pt : B a => subset_dep_prod_cons eqA a pt HlA p) (laB a) p').
    intuition.
    clear H0.
    destruct H as (b, (Hb1, Hb2)).
    generalize (in_map_iff (fun pt : B a => subset_dep_prod_cons eqA a pt HlA q) (laB a) p').
    intuition.
    clear H0.
    destruct H as (b', (Hb1', Hb2')).
    apply Hnpq.
    eapply injective_subset_dep_prod_cons.
    etransitivity.
    * apply Hb1.
    * symmetry.
      assert (b = b').
      ++ eapply injective_subset_dep_prod_cons_1.
         etransitivity.
         -- apply Hb1.
         -- symmetry.
            apply Hb1'.
      ++ subst.
         apply Hb1'.
Qed.

Theorem surjective_dep_prod : forall {A} {B : A -> Type} (eqA : dec_eq A) (lA : list A) (laB : forall a, list (B a)) (HlA : NoDup lA), (forall a, SurjectiveList (laB a)) -> SurjectiveList (dep_prod eqA lA laB HlA).
Proof.
induction lA; simpl.
+ intros _ _ _ p.
  assert (p = subset_dep_prod_nil).
  - apply functional_extensionality_dep.
    intros (a ,Ha).
    elim (in_nil Ha).
  - subst.
    apply in_eq.
+ intros lB HlA HlaB p.
  apply in_flat_map.
  exists (subset_dep_prod_tl p).
  split.
  - apply IHlA.
    exact HlaB.
  - apply in_map_iff.
    exists (p (exist (fun x => In x (a::lA)) a (in_eq a lA))).
    split.
    * apply cancel_dep_prod_cons_tl.
    * apply HlaB.
Qed.

Theorem finite_dep_prod : forall {A} {B : A -> Type} (eqA : dec_eq A), Finite A -> (forall a, Finite (B a)) -> Finite (forall a, B a).
Proof.
intros A B eqA (lA, (HlA1, HlA2)) FaB.
apply (finite_bij (forall a : subset_in_list lA, B (proj1_sig a)) (forall a, B a)).
+ apply bijection_inv.
  apply (bij_dep_prod_compose (bij_subset (fun a => In a lA) HlA1)).
  intro a.
  exact bij_id.
+ exists (dep_prod eqA lA (fun a => proj1_sig (FaB a)) (injective_nodup _ _ HlA2)).
  split.
  - apply surjective_dep_prod.
    intro a.
    destruct (FaB a) as (lB, (HlB1, HlB2)).
    exact HlB1.
  - apply nodup_injective.
    apply nodup_dep_prod.
    intro a.
    apply injective_nodup.
    destruct (FaB a) as (lB, (HlB1, HlB2)).
    exact HlB2.
Qed.


Definition subset_dep_sum_cons_hd {A} {B : A -> Type} (t : A) (q : list A) (b : B t) : { a : subset_in_list (t::q) & B (proj1_sig a) } :=
  existT _ (exist _ t (in_eq t q)) b.

Definition subset_dep_sum_cons_tl {A} {B : A -> Type} (t : A) (q : list A) (pq : { a : subset_in_list q & B (proj1_sig a) }) : { a : subset_in_list (t::q) & B (proj1_sig a) }.
destruct pq as ((a, Ha), ba).
exists (exist _ a (in_cons t a q Ha)).
exact ba.
Defined.

Fixpoint dep_sum {A} {B : A -> Type} (lA : list A) (laB : forall a, list (B a)) : list ({ a : subset_in_list lA & B (proj1_sig a) }) :=
  match lA with
  | []   => []
  | t::q => let pq := dep_sum q laB in
              (map (fun b => subset_dep_sum_cons_hd t q b) (laB t)) ++ (map (fun p => subset_dep_sum_cons_tl t q p) pq)
  end.

Lemma injective_subset_dep_sum_cons_hd : forall {A} {B : A -> Type} (a : A) (lA : list A), InjectiveXT (fun b : B a => subset_dep_sum_cons_hd a lA b).
Proof.
intros A B a lA b1 b2 H.
unfold subset_dep_sum_cons_hd in H.
generalize (projT2_eq H).
simpl.
intro H'.
rewrite <- eq_rect_eq in H'.
exact H'.
Qed.

Lemma injective_subset_dep_sum_cons_tl : forall {A} {B : A -> Type} (a : A) (lA : list A),
  InjectiveXT (fun p : {a0 : subset_in_list lA & B (proj1_sig a0)} => subset_dep_sum_cons_tl a lA p).
Proof.
intros A B a lA p1 p2 H.
destruct p1 as ((a1, Ha1), ba1).
destruct p2 as ((a2, Ha2), ba2).
simpl in H.
generalize (projT1_eq H).
simpl.
intro H'.
inversion H'.
subst.
clear H'.
rewrite (proof_irrelevance _ Ha1 Ha2).
apply f_equal.
rewrite (proof_irrelevance _ Ha1 Ha2) in H.
simpl in ba1, ba2.
generalize (projT2_eq H).
simpl.
rewrite <- eq_rect_eq.
auto.
Qed.

Lemma eq_subset_dep_sum_cons_hd :  forall {A} {B : A -> Type} (a : A) (lA : list A) (b : B a), proj1_sig (projT1 (subset_dep_sum_cons_hd a lA b)) = a.
Proof.
intros A B a lA b.
reflexivity.
Qed.

Lemma in_subset_dep_sum_cons_tl : forall {A} {B : A -> Type} (t : A) (q : list A) (pq : { a : subset_in_list q & B (proj1_sig a) }),
  In (proj1_sig (projT1 (subset_dep_sum_cons_tl t q pq))) q.
Proof.
intros A B t q pq.
destruct pq as ((a, Ha), ba).
exact Ha.
Qed.
 
Theorem nodup_dep_sum : forall {A} {B : A -> Type} (lA : list A) (laB : forall a, list (B a)) (HlA : NoDup lA), (forall a, NoDup (laB a)) -> NoDup (dep_sum lA laB).
Proof.
induction lA; simpl.
+ intros _ _ _ .
  apply NoDup_nil.
+ intros laB HlA HlaB.
  apply nodup_app.
  - apply nodup_map.
    * apply injective_subset_dep_sum_cons_hd.
    * apply HlaB.
  - apply nodup_map.
    * apply injective_subset_dep_sum_cons_tl.
    * apply IHlA.
      inversion HlA.
      assumption.
      exact HlaB.
  - apply forall_Forall.
    intros ((a', Ha'), ba') Ha1' Ha2'.
    simpl in * |- *.
    generalize (in_map_inv_exists _ _ _ Ha1').
    clear Ha1'; intro Ha1'.
    destruct Ha1' as (b, (Hb1, _)).
    generalize (eq_subset_dep_sum_cons_hd a lA b).
    rewrite Hb1.
    simpl.
    clear Hb1 b.
    intro Haa'.
    subst.
    generalize (in_map_inv_exists _ _ _ Ha2').
    clear Ha2'; intro Ha2'.
    destruct Ha2' as (((a'', Ha''), ba''),(Ha1'', Ha2'')).
    generalize (in_subset_dep_sum_cons_tl a lA (existT (fun a : subset_in_list lA => B (proj1_sig a)) (exist (fun a : A => In a lA) a'' Ha'') ba'')).
    rewrite Ha1''.
    simpl.
    clear Ha1'' Ha2''.
    intro Ha.
    inversion HlA.
    contradiction.
Qed.

Theorem surjective_dep_sum : forall {A} {B : A -> Type} (lA : list A) (laB : forall a, list (B a)), (forall a, SurjectiveList (laB a)) -> SurjectiveList (dep_sum lA laB).
Proof.
intros A B lA laB HlaB.
induction lA; simpl.
+ intros ((a, Ha), ba).
  elim (in_nil Ha).
+ intros ((a', Ha'), ba').
  apply in_or_app.
  destruct Ha' as [Ha'| Ha'].
  - subst.
    left.
    apply in_map_iff.
    exists ba'.
    split.
    * unfold subset_dep_sum_cons_hd.
      rewrite (proof_irrelevance _ (in_eq a' lA) (or_introl eq_refl)).
      reflexivity.
    * apply HlaB.
  - right.
    simpl in ba'.
    assert (existT (fun a0 : subset_in_list (a :: lA) => B (@proj1_sig _ (fun a1 : A => a = a1 \/ @In A a1 lA) a0)) (exist (fun a0 : A => a = a0 \/ In a0 lA) a' (or_intror Ha')) ba'
            = subset_dep_sum_cons_tl a lA (existT (fun a0 : subset_in_list lA => B (proj1_sig a0)) (exist (fun a0 : A => In a0 lA) a' Ha') ba')) as H.
    * simpl.
      rewrite (proof_irrelevance _ (or_intror Ha') (in_cons a a' lA Ha')).
      reflexivity.
    * simpl.
      rewrite H.
      apply in_map.
      apply IHlA.
Qed.

Theorem finite_dep_sum : forall {A} {B : A -> Type}, Finite A -> (forall a, Finite (B a)) -> Finite ({ a : A & B a }).
Proof.
intros A B (lA, (HlA1, HlA2)) FaB.
apply (finite_bij { a : subset_in_list lA & B (proj1_sig a) } {a : A & B a }).
+ apply bijection_inv.
  apply (bij_sigT_compose (bij_subset (fun a => In a lA) HlA1)).
  intro a.
  exact bij_id.
+ exists (dep_sum lA (fun a => proj1_sig (FaB a))).
  split.
  - apply surjective_dep_sum.
    intro a.
    destruct (FaB a) as (lB, (HlB1, HlB2)).
    exact HlB1.
  - apply nodup_injective.
    apply nodup_dep_sum.
    * apply injective_nodup.
      exact HlA2.
    * intro a.
      destruct (FaB a) as (lB, (HlB1, HlB2)).
      apply injective_nodup.
      exact HlB2.
Qed.

