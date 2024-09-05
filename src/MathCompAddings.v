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