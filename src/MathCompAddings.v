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