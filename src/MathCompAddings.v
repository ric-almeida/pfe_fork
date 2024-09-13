Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".

Require Import Arith.

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


Definition ordinal_0_univ_embedding {A : Type} : ordinal 0 -> A.
  Proof.
  intro f.
  destruct f as (p, Hp).
  elim (nlt_0_it p Hp).
  Qed.


Lemma minus_lt : forall s m n, s - m < n -> s < n + m.
  Proof.
  move=> s m n H.
  assert (H2: s = (s - m) + m). rewrite <- addnBn.
  Admitted. 
  (* symmetry. 
  apply subnKC.
  - simpl. Search (_ = _ - _ + _). reflexivity. rewrite  //; apply: ltnW; apply: ltn_trans H; rewrite addnC addnK.
  rewrite H2.
  apply: leq_addl.
  intros.
  induction m.
  Search (_ + 0 = _).
  simpl in *. *)

Lemma minus_lt_iff : forall s m n, s > m -> s < m + n -> s - m < m + n.
  Proof.
  move=> s m n H H'.
  Admitted. 


Definition replace_in_H : forall {r r' : nat} (Hrr' : r' = r) (m : nat) (Hrm : m < r'), m <r.
Proof.
intros. destruct Hrr'. auto. Qed. 

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

Lemma Ordinal_proof_irrelevance : forall (s m : nat) (i0 i1 : m < s),
  Ordinal i0 = Ordinal i1.
Proof.
  intros s m i0 i1.
  apply val_inj.
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


Lemma not_s_lt : forall a b, a + b < a -> False.
Proof. 
Admitted.