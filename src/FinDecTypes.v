(** Finite Decidable Types *)

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import List.
Require Import Euclid.
Require Import Lists.List.
Require Import Arith.
Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Require Import Lia.

Import ListNotations. 
Require Import MyBasics.


Definition Finite (N : Type) : Type := { l : list N | SurjectiveList l /\ InjectiveXTList l }.


Record FinDecType : Type :=
    {
      type : Type ;
      finite_type : Finite type ;
      dec_type : EqDec type
    }.

(** Decidability of = on some commmon finite types*)
Section decidability.
Lemma dec_eq_void : dec_eq void.
  Proof.
  unfold dec_eq, decidable.
  decide equality.
  Qed.

Lemma dec_eq_unit : dec_eq unit.
  Proof.
  unfold dec_eq, decidable.
  decide equality.
  Qed.

Lemma dec_eq_bool : dec_eq bool.
  Proof.
  unfold dec_eq, decidable.
  decide equality.
  Qed.

Lemma dec_eq_nat : dec_eq nat.
  Proof.
  unfold dec_eq, decidable.
  decide equality.
  Qed.

Lemma dec_eq_sum : forall {A B}, dec_eq A -> dec_eq B -> dec_eq (A + B).
  Proof.
  unfold dec_eq, decidable.
  decide equality.
  Qed.

Lemma dec_eq_subset : forall {A} (P : A -> Prop), dec_eq A -> dec_eq { a : A | P a }.
  Proof.
  unfold dec_eq, decidable.
  intros A P Heqaa' a a'.
  destruct a as (a, Ha); destruct a' as (a', Ha').
  destruct (Heqaa' a a') as [Haa' |Hnaa'].
  + left.
    apply subset_eq_compat.
    assumption.
  + right.
    intro H.
    apply Hnaa'.
    injection H.
    auto.
  Qed.

Lemma dec_eq_fin : forall {n}, dec_eq (fin n).
  Proof.
  unfold dec_eq, decidable.
  intro n.
  destruct a as (a, Ha).
  destruct a' as (a', Ha').
  destruct (dec_eq_nat a a') as [Heqa' | Hneqaa'].
  + subst.
    left.
    apply subset_eq_compat.
    reflexivity.
  + right.
    intro H.
    apply Hneqaa'.
    injection H.
    auto.
  Qed.

End decidability.

(** Finiteness of some commmon finite types*)
Section finiteness.
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

Lemma inj_option_map : forall A B (f : A -> B), InjectiveXT f -> InjectiveXT (option_map f).
  Proof.
  intros until y.
  destruct x as [x'|]; destruct y as [y'|]; simpl; try discriminate.
  + intro Hxy'; injection Hxy'; clear Hxy'; intro Hxy'.
    rewrite (H _ _ Hxy'); reflexivity.
  + reflexivity.
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

Lemma in_eq' : forall T a b (q : list T), a = b -> In a (cons b q).
  Proof.
  intros.
  rewrite H.
  apply in_eq.
  Qed.

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

Theorem lt_S_n' : forall n m : nat, S n < S m -> n < m.
  Proof. apply Nat.succ_lt_mono. Qed.

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

Definition first_fin_Sn : forall n, fin (S n).
  Proof.
  intro n.
  exists n.
  lia.
  Defined.


Definition inj_fin_n_Sn : forall {n}, fin n -> fin (S n).
  Proof.
  intros n (x, Hx).
  exists x.
  lia.
  Defined.

Theorem first_fin_Sn_n : forall n, proj1_sig (first_fin_Sn n) = n.
  Proof.
  intro n.
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

End finiteness.


(** Commmon finite types*)
Definition voidfd :=
  {|
    type        := void;
    dec_type    := dec_eq_void;
    finite_type := finite_void
  |}.

Definition findec_unit :=
  {|
    type        := unit;
    dec_type    := dec_eq_unit;
    finite_type := finite_unit
  |}.

Definition findec_bool :=
  {|
    type        := bool;
    dec_type    := dec_eq_bool;
    finite_type := finite_bool
  |}.

Definition findec_sum (A B : FinDecType) :=
 {|
    type        := (type A) + (type B);
    dec_type    := dec_eq_sum (dec_type A) (dec_type B);
    finite_type := finite_sum _ _ (finite_type A) (finite_type B)
  |}.

Definition findec_subset (A : FinDecType) (P : (type A) -> Prop) (HdecP : forall a, decidable (P a)) :=
 {|
    type        := { a : (type A) | P a };
    dec_type    := dec_eq_subset P (dec_type A);
    finite_type := finite_subset P (finite_type A) HdecP
  |}.

Definition findec_fin (n : nat) :=
 {|
    type        := fin n;
    dec_type    := @dec_eq_fin n;
    finite_type := finite_fin n 
  |}.


