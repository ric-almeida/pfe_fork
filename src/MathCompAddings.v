Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".

Require Import Arith.

Require Import List.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finfun. 



Definition void_univ_embedding {A : Type} : void -> A.
  Proof.
  intro v.
  elim v.
  Defined.


Definition nlt_0_it : forall p, p<0 -> False. 
  intros p Hp.
  (* apply is_true_lt in Hp. *)
  (* apply Nat.nlt_0_r in Hp. apply Hp. *)
  unfold is_true in Hp. 
  set (nHp := ltn0 p).
  exfalso.
  apply Bool.diff_true_false.
  auto.
  Qed.

Lemma lt1_eq0 x : x < 1 -> x = 0.
Proof.
  move=> Hx.
  case: x Hx => [| n] //.
Qed.


Definition ordinal_0_univ_embedding {A : Type} : ordinal 0 -> A.
  Proof.
  intro f.
  destruct f as (p, Hp).
  elim (nlt_0_it p Hp).
  Qed.


Lemma minus_lt : forall s m n, s - m < n -> s < n + m.
  Proof.
  move=> s m n H.
  destruct n.
  - exfalso. apply (nlt_0_it (s-m) H).
  - rewrite ltn_psubLR in H. 
  * rewrite addnC. apply H.
  * apply ltn0Sn. 
  Qed.


Definition replace_in_H : forall {r r' : nat} (Hrr' : r' = r) (m : nat) (Hrm : m < r'), m <r.
Proof.
intros. destruct Hrr'. auto. 
Qed. 

Lemma eq_rect_ordinal : forall {r r' : nat} (Hrr' : r' = r) (m : nat) (Hrm' : m < r'),
  @eq_rect nat r' 
  ordinal
  (@Ordinal r' m Hrm')
  r 
  Hrr' = 
  @Ordinal r m (replace_in_H Hrr' m Hrm').
Proof.
intros.
destruct Hrr'.
simpl.
apply val_inj.
reflexivity.
Qed. 

(* Lemma eq_rect_ordinal_open {node:finType} {ctrl:node -> nat} : 
  forall {n n':node} {port} (H : port < ctrl n) (H' : port < ctrl n')
  (Hnn' : n = n'),
  eq_rect 
    n
    (fun y => 'I_(ctrl y))
    (Ordinal (n:=ctrl n) (m:=port) H)
    n'
    Hnn' = Ordinal (n:=ctrl n') (m:=port) H'.
  Proof.
  intros.
  simpl.
  Admitted. *)


Lemma Ordinal_proof_irrelevance : forall (s m : nat) (i0 i1 : m < s),
  Ordinal i0 = Ordinal i1.
Proof.
  intros s m i0 i1.
  apply val_inj.
  reflexivity.
Qed.

Lemma Ordinal_proof_irrelevance' {s m: nat} (s' m' : nat) {i0 i1}:
  s'=s -> m = m' ->
  nat_of_ord (Ordinal (n:=s) (m:=m) i0) = nat_of_ord (Ordinal (n:=s') (m:=m') i1).
Proof.
  intros. subst s'. subst m'.
  reflexivity.
Qed.

Lemma lt_ge_contradiction : forall m s : nat, (m < s) -> (s <= m) -> False.
Proof.
  move=> m s Hlt Hge.
  apply ltn_geF in Hlt.
  apply Bool.diff_true_false.
  rewrite <- Hlt.
  rewrite <- Hge.
  reflexivity.
Qed.

Lemma ord_same_value : forall s m m' H H', m=m'->
@Ordinal s m H =
@Ordinal s m' H'.
Proof.
  intros.
  apply val_inj. simpl.
  apply H0.
Qed.

Lemma leq_addl_trans s1 s2 m : s1 + s2 <= m -> s1 <= m.
Proof.
  move=> H.
  apply: leq_trans H.
  rewrite addnC.
  apply leq_addl.
Qed.

Lemma lt_addl_trans s1 s2 m : s1 + s2 < m -> s1 < m.
Proof.
  move=> H.
  apply: leq_trans H.
  rewrite addnC.
  apply leq_addl.
Qed.

Lemma not_s_lt : forall a b, a + b < a -> False.
Proof. 
intros.
assert (a + b < a + 0).
rewrite addn0. apply H.
rewrite ltn_add2l in H0.
apply (nlt_0_it b H0).
Qed.

Lemma eq_sum_r : forall m n p s : nat, 
  m = p -> n = s -> m + n = p + s.
Proof.
  intros.
  subst m. subst n. reflexivity.
Qed.

Lemma eq_sum_l : forall m n p s : nat, 
  n = s -> m = p ->  m + n = p + s.
Proof.
  intros.
  subst m. subst n. reflexivity.
Qed.

Lemma eq_sum_l_0 : forall m n p s : nat, 
  n = 0 ->  m + n = m.
Proof.
  intros.  subst n. rewrite addn0. reflexivity.
Qed.

Lemma eq_sum_r_0 : forall m n p s : nat, 
  n = 0 ->  n + m = m.
Proof.
  intros.  subst n. rewrite addnC. rewrite addn0. reflexivity.
Qed.


Lemma minus_plus : forall x y, x - y + y = x.
Proof.
Abort.



Lemma plus_minus : forall x y, x + y - y = x.
Proof. 
  intros.
  rewrite subDnAC.
  rewrite subnn.
  rewrite addnC.
  rewrite addn0.
  reflexivity.
  apply leqnn.
  Qed.

Lemma add1_leq_false r : r + 1 <= r -> False.
Proof.
  intros.
  induction r.
  rewrite leqn0 in H.
  rewrite addnC in H. rewrite addn0 in H. discriminate H.
  apply IHr.
  rewrite addSn in H.
  apply ltnSE in H. apply H.
  Qed.

Lemma in_or_app_mc {Name} : forall (l1 l2 : seq Name) (inner : Name),
  In inner ((l1 ++ (inner :: l2)%SEQ)%list).
  Proof.
  intros l1 l2 inner.
  apply in_or_app.
  right. constructor. reflexivity. 
Qed.

