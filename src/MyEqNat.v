Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import Bijections.


From mathcomp Require Import all_ssreflect.

Class MyEqNat (x y : nat) := { eqxy : x = y }. 
#[export] Instance MyEqNat_refl (x:nat) : MyEqNat x x.
  Proof. 
  constructor. reflexivity. 
  Qed.

#[export] Instance MyEqNat_add {s1 s2 r3 r4} (eqs2r4 : MyEqNat s2 r4) (eqs1r3 : MyEqNat s1 r3) : 
  MyEqNat (s1 + s2) (r3 + r4).
  Proof. 
  constructor. destruct eqs2r4 as [eqs2r4].
  destruct eqs1r3 as [eqs1r3].
  subst s1.
  subst s2. reflexivity.
  Qed.

#[export] Instance MyEqNat_add_bis {s1 r3 s2 r4} (eqs2r4 : MyEqNat s2 r4) (eqs1r3 : MyEqNat s1 r3) : 
  MyEqNat (s1 + s2) (r3 + r4).
  Proof. 
  constructor. destruct eqs2r4 as [eqs2r4].
  destruct eqs1r3 as [eqs1r3].
  subst s1.
  subst s2. reflexivity.
  Qed.

#[export] Instance MyEqNat_r_neutral {a} : 
  MyEqNat (a+0) a.
  Proof. 
  constructor. 
  apply addn0.
  Qed.
