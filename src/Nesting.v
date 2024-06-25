Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import ParallelProduct.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.

(** Nesting operator *)
Module NestingBig (s : SignatureParameter) (n : NamesParameter).
Module pp := ParallelProduct s n.
Include pp.

Definition nest  {s1 r1 s2 r2 : nat} {o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  {eqs1r2 : MyEqNat s1 r2}
  (* {p : PermutationNames i1 EmptyNDL} *)
  (* : bigraph s2 i2 r1 (app_merge_NoDupList o1 o2)  *)
  := ((bigraph_id 0 o2) || b1) <<o>> b2.


Global Notation "G '<.>' F" := (nest G F) (at level 50, left associativity).

(* Lemma id_union'' : forall X Y:NoDupList, 
  bigraph_equality
  (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
  ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (bigraph_identity (s := 0) (i := app_merge_NoDupList X Y) (p := P_NP (permutation_id (app_merge_NoDupList X Y))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
    + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
    + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Lemma my_id_union : forall X Y:NoDupList, 
  bigraph_packed_equality
    (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
    ((bigraph_identity (i := X)) || (bigraph_identity (i := Y))).
  Proof.
    intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ).
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
  + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
  + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Theorem testimportant {I X Y}
  (F : bigraph 1 I 1 X) (G : bigraph 1 EmptyNDL 1 Y) :
  bigraph_packed_equality F G -> bigraph_packed_equality F F.
  Proof. 
    intros H. 
    rewrite H. auto. reflexivity. 
  Qed. 

Theorem intermediaire_rewrie {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  (b3 : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2))
  {up : UnionPossible b1 b2} :
  bigraph_packed_equality (b1 || b2) b3
  <-> bigraph_packed_equality ((packing b1) || (packing b2)) b3.
  split. auto. auto. Qed. 

Theorem intermediaire_rewrie' {s1 r1 s2 r2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: PermutationNames o2i1 i1o2} {eqsr : MyEqNat s1 r2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 r2 o2i1) 
  (b3 : bigraph s2 i2 r1 o1)
  {up : UnionPossible b1 b2} :
  bigraph_packed_equality (b1 <<o>> b2) b3
  <-> bigraph_packed_equality ((packing b1) <<o>> (packing b2)) b3.
  split. auto. auto. Qed. 

Lemma my_id_union' : forall X Y:NoDupList, 
  bigraph_packed_equality
    (@packing O (app_merge_NoDupList X Y) O (app_merge_NoDupList X Y) (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y))))))
    (packing ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))).
  intros X Y.
    unfold bigraph_id. unfold bigraph_identity.
    unfold bigraph_parallel_product.
    simpl.
    unfold link_juxt, parallel, funcomp.
    simpl.
    unfold findec_sum. simpl.
    unfold join.
    unfold sum_shuffle.
    refine 
      (BigEq 0 0 0 0 (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (app_merge_NoDupList X Y)
        (@bigraph_identity O (app_merge_NoDupList X Y) (app_merge_NoDupList X Y) (permutation_id_PN (@reverse_coercion NoDupList (list Name) (app_merge_NoDupList X Y) (ndlist (app_merge_NoDupList X Y)))))
        ((bigraph_identity (i := X)) || (bigraph_identity (i := Y)))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        eq_refl
        (permutation_id (app_merge_NoDupList X Y))
        (bijection_inv bij_void_sum_neutral)
        (bijection_inv bij_void_sum_neutral)
        (fun n => void_univ_embedding n) _ _ _
      ). 
  + apply functional_extensionality.
      intros [ x | x ]; destruct x. 
  + apply functional_extensionality.
      intros [[x | x] | p]; try (destruct x).
      unfold fin in p. destruct p. exfalso. apply PeanoNat.Nat.nlt_0_r in l. apply l.
  + rewrite bij_subset_compose_id. simpl.
    apply functional_extensionality.
    intros [[i H]|x].
    * unfold id, parallel, funcomp. simpl. unfold in_app_or_m_nod_dup.
    destruct (in_dec EqDecN i Y); f_equal; apply subset_eq_compat; reflexivity.
    * destruct x. destruct x as [x | x]; destruct x.
  Qed.

Print my_id_union'.  *)

Lemma nest_arity_associative : forall {s1 r1 o1 s2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 EmptyNDL r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3},
  forall n,
  Arity (get_control ((b1 <.> b2) <.>  b3) n) =
  Arity (get_control (b1 <.> (b2 <.> b3)) (bij_nesting_assoc n)).
  Proof.
  intros until n.
  destruct n as [[v|[[v|a']|b']] | c']; try elim v; reflexivity.
  Qed. 


Theorem nest_associative : forall {s1 r1 o1 s2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph s2 EmptyNDL r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {eqs1r2 : MyEqNat s1 r2} {eqs2r3 : MyEqNat s2 r3},
  bigraph_equality 
    ((b1 <.> b2) <.>  b3)
    (b1 <.> (b2 <.> b3)).
  Proof.
    intros.
    refine (BigEq _ _ _ _ _ _ _ _ ((b1 <.> b2) <.> b3) (b1 <.> (b2 <.> b3))
    (reflexivity s3)
    (permutation_id i3)
    (eq_refl)
    (permutation_commute tr_permutation)
    bij_nesting_assoc
    bij_nesting_assoc
    (fun n12_3 => bij_rew (P := fin) (nest_arity_associative b1 b2 b3 n12_3)) _ _ _ 
    ).
    + apply functional_extensionality. simpl.
      destruct x as [[v|a']|[[v|b']|c']]; try elim v; try reflexivity.
    + apply functional_extensionality. rewrite bij_rew_id. 
      intros [[[v|a']|[[v|b']|c']] | s1_23']; simpl; unfold funcomp; simpl; try (elim v).
      - unfold extract1, parallel, sum_shuffle. 
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold inj_fin_add, bij_rew_forward, surj_fin_add, id.
        destruct f.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r1 r1 _ (0 + (0 + x)) _).
        apply subset_eq_compat. reflexivity.
      - unfold extract1, parallel, sum_shuffle. 
        unfold rearrange.
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold extract1, inj_fin_add, bij_rew_forward, surj_fin_add, id, rearrange.
        destruct f. 
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ (0 + x) _).
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ (0 + x) _).
        destruct (PeanoNat.Nat.ltb_spec0 (0 + x) 0).
        lia.
        erewrite <- (parent_proof_irrelevant b1 (0 + x - 0) (0 + x - 0) (ZifyClasses.rew_iff_rev (0 + x - 0 < s1) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0))) (BinInt.Z.of_nat s1)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x - 0) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n0 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m)) Znat.Nat2Z.inj_sub_max (0 + x) (BinInt.Z.of_nat (0 + x)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl) s1 (BinInt.Z.of_nat s1) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0)))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0)) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat 0)) (BinInt.Z.of_nat s1) VarMap.Empty) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0))) (VarMap.Elt (BinInt.Z.of_nat (0 + x))))) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0))) (ZifyClasses.rew_iff (0 + x < 0 + s1) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x) (BinInt.Z.of_nat (0 + x)) eq_refl (0 + s1) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl s1 (BinInt.Z.of_nat s1) eq_refl)) (eq_rect r2 (fun a : nat => 0 + x < a) (ZifyClasses.rew_iff_rev (0 + x < 0 + r2) (BinInt.Z.lt (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl x (BinInt.Z.of_nat x) eq_refl) (0 + r2) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl)) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xO BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xI BinNums.xH) |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xO BinNums.xH)); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xI BinNums.xH)) |} tt)) [] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat x)) (BinInt.Z.of_nat 0) (VarMap.Elt (BinInt.Z.of_nat r2)))) (ZifyClasses.rew_iff (x < r2) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat r2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl) l))) s1 (eq_sym eqxy))) (ZifyClasses.rew_iff (~ 0 + x < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0)) (ZifyClasses.not_morph (0 + x < 0) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x)) (BinInt.Z.of_nat 0)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x) (BinInt.Z.of_nat (0 + x)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl)) n)))).
        destruct get_parent; try reflexivity.
        destruct f.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r1 r1 _ (0 + (0 + x0)) _).
        f_equal. apply subset_eq_compat. lia.
        lia. 
      - unfold extract1, parallel, sum_shuffle. 
        unfold rearrange.
        destruct get_parent; try reflexivity.
        f_equal. 
        unfold extract1, inj_fin_add, bij_rew_forward, surj_fin_add, id, rearrange,sequence.
        destruct f. 
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r3 s2 _ x _).
        destruct (PeanoNat.Nat.ltb_spec0 x 0).
        lia.
        unfold rearrange.
        erewrite <- (parent_proof_irrelevant b2 (x - 0) (x - 0) (ZifyClasses.rew_iff_rev (x - 0 < s2) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (BinInt.Z.of_nat s2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (x - 0) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n0 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl) s2 (BinInt.Z.of_nat s2) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat 0)) (BinInt.Z.of_nat s2) VarMap.Empty) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (VarMap.Elt (BinInt.Z.of_nat x)))) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (ZifyClasses.rew_iff (x < 0 + s2) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl (0 + s2) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s2)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl s2 (BinInt.Z.of_nat s2) eq_refl)) (eq_rect r3 (fun a : nat => x < a) l s2 (eq_sym eqxy))) (ZifyClasses.rew_iff (~ x < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) (ZifyClasses.not_morph (x < 0) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl)) n)))).
        destruct get_parent; try reflexivity.
        unfold extract1. destruct f.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ x0 _).
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ (0+x0) _).
        destruct (PeanoNat.Nat.ltb_spec0 x0 0).
        destruct (PeanoNat.Nat.ltb_spec0 (0 + x0) 0).
        lia.
        lia.
        destruct (PeanoNat.Nat.ltb_spec0 (0 + x0) 0).
        lia.
        erewrite <- (parent_proof_irrelevant' b1 (x0 - 0) (0 + x0 - 0) ((ZifyClasses.rew_iff_rev (0 + x0 - 0 < s1) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (BinInt.Z.of_nat s1)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0 - 0) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n2 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n2 m)) Znat.Nat2Z.inj_sub_max (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl) s1 (BinInt.Z.of_nat s1) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat 0)) (BinInt.Z.of_nat s1) VarMap.Empty) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (VarMap.Elt (BinInt.Z.of_nat (0 + x0))))) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (ZifyClasses.rew_iff (0 + x0 < 0 + s1) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl (0 + s1) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl s1 (BinInt.Z.of_nat s1) eq_refl)) (eq_rect r2 (fun a : nat => 0 + x0 < a) (ZifyClasses.rew_iff_rev (0 + x0 < 0 + r2) (BinInt.Z.lt (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x0)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x0)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl x0 (BinInt.Z.of_nat x0) eq_refl) (0 + r2) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl)) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xO BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xI BinNums.xH) |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xO BinNums.xH)); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xI BinNums.xH)) |} tt)) [] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat x0)) (BinInt.Z.of_nat 0) (VarMap.Elt (BinInt.Z.of_nat r2)))) (ZifyClasses.rew_iff (x0 < r2) (BinInt.Z.lt (BinInt.Z.of_nat x0) (BinInt.Z.of_nat r2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x0 (BinInt.Z.of_nat x0) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl) l0))) s1 (eq_sym eqxy))) (ZifyClasses.rew_iff (~ 0 + x0 < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) (ZifyClasses.not_morph (0 + x0 < 0) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl)) n1))))).
        destruct get_parent; try reflexivity.
        destruct f.
        f_equal. apply subset_eq_compat. lia.
        lia. 
        lia.
      - unfold extract1, parallel, sum_shuffle, rearrange, id. 
        destruct get_parent; try reflexivity.
        unfold extract1, inj_fin_add, bij_rew_forward, surj_fin_add, id, rearrange,sequence.
        destruct (eq_rect r3 fin f s2 (eq_sym eqxy)).
        destruct (PeanoNat.Nat.ltb_spec0 x 0).
        lia.
        unfold rearrange.
        erewrite <- (parent_proof_irrelevant b2 (x - 0) (x - 0) ((ZifyClasses.rew_iff_rev (x - 0 < s2) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (BinInt.Z.of_nat s2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (x - 0) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n0 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl) s2 (BinInt.Z.of_nat s2) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat 0)) (BinInt.Z.of_nat s2) VarMap.Empty) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (VarMap.Elt (BinInt.Z.of_nat x)))) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0))) (ZifyClasses.rew_iff (x < 0 + s2) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl (0 + s2) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s2)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl s2 (BinInt.Z.of_nat s2) eq_refl)) l) (ZifyClasses.rew_iff (~ x < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) (ZifyClasses.not_morph (x < 0) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat 0)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl)) n))))).
        destruct get_parent; try reflexivity.
        unfold extract1. destruct f0.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ (0 + x0) _).
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r2 s1 _ (0 + x0) _).
        destruct (PeanoNat.Nat.ltb_spec0 (0 + x0) 0).
        f_equal.
        apply subset_eq_compat.
        lia.
        erewrite <- (parent_proof_irrelevant b1 (0 + x0 - 0) (0 + x0 - 0) ((ZifyClasses.rew_iff_rev (0 + x0 - 0 < s1) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (BinInt.Z.of_nat s1)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0 - 0) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat (fun n1 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n1 m)) Znat.Nat2Z.inj_sub_max (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl) s1 (BinInt.Z.of_nat s1) eq_refl) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.OR (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)))) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) |} tt)) (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) BinNums.Z0)) (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpEq; RingMicromega.Frhs := EnvRing.PEc BinNums.Z0 |} tt))) None (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH)) |} tt) None (Tauto.IMPL (Tauto.NOT (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)) |} tt)) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH) |} tt)))) [ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof; ZMicromega.RatProof (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3) (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat 0)) (BinInt.Z.of_nat s1) VarMap.Empty) (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (VarMap.Elt (BinInt.Z.of_nat (0 + x0))))) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0))) (ZifyClasses.rew_iff (0 + x0 < 0 + s1) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl (0 + s1) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat s1)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl s1 (BinInt.Z.of_nat s1) eq_refl)) (eq_rect r2 (fun a : nat => 0 + x0 < a) (ZifyClasses.rew_iff_rev (0 + x0 < 0 + r2) (BinInt.Z.lt (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x0)) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2))) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat x0)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl x0 (BinInt.Z.of_nat x0) eq_refl) (0 + r2) (BinInt.Z.add (BinInt.Z.of_nat 0) (BinInt.Z.of_nat r2)) (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add Znat.Nat2Z.inj_add 0 (BinInt.Z.of_nat 0) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl)) (ZMicromega.ZTautoChecker_sound (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX (BinNums.xO BinNums.xH); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEX (BinNums.xI BinNums.xH) |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xO BinNums.xH)); RingMicromega.Fop := RingMicromega.OpLt; RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX BinNums.xH) (EnvRing.PEX (BinNums.xI BinNums.xH)) |} tt)) [] eq_refl (VarMap.find BinNums.Z0 (VarMap.Branch (VarMap.Elt (BinInt.Z.of_nat x0)) (BinInt.Z.of_nat 0) (VarMap.Elt (BinInt.Z.of_nat r2)))) (ZifyClasses.rew_iff (x0 < r2) (BinInt.Z.lt (BinInt.Z.of_nat x0) (BinInt.Z.of_nat r2)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x0 (BinInt.Z.of_nat x0) eq_refl r2 (BinInt.Z.of_nat r2) eq_refl) l0))) s1 (eq_sym eqxy))) (ZifyClasses.rew_iff (~ 0 + x0 < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) (ZifyClasses.not_morph (0 + x0 < 0) (BinInt.Z.lt (BinInt.Z.of_nat (0 + x0)) (BinInt.Z.of_nat 0)) (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (0 + x0) (BinInt.Z.of_nat (0 + x0)) eq_refl 0 (BinInt.Z.of_nat 0) eq_refl)) n0))))).
        destruct get_parent; try reflexivity.
        f_equal.
        destruct f0.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) r1 r1 _ (0 + (0 + x1)) _).
        apply subset_eq_compat.
        lia.
        lia.
        lia.
    + apply functional_extensionality.
      destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
      - unfold parallel, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id, rearrange, switch_link. simpl. 
        unfold in_app_or_m_nod_dup, extract1.
        rewrite <- (innername_proof_irrelevant b3 i123 i0). 
        destruct get_link; try reflexivity.
        unfold permut_list_forward. destruct s0.
        f_equal. apply subset_eq_compat. reflexivity.
      - unfold parallel, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id, rearrange, switch_link. simpl.
        unfold rearrange, switch_link, bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id, extract1. 
        unfold bij_join_port_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward.
        destruct p123. simpl.  
        destruct x as [[v|a']|[[v|b']|c']]; try destruct v.
        * unfold bij_rew_forward, funcomp, id, join, void_univ_embedding. destruct f.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. f_equal. destruct s0. apply subset_eq_compat. reflexivity.
          reflexivity.
        * unfold bij_rew_forward, funcomp, id, join, void_univ_embedding, permut_list_forward. destruct f.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
          reflexivity.
        * unfold bij_rew_forward, funcomp, id, join, void_univ_embedding, permut_list_forward. destruct f.
          rewrite <- eq_rect_eq.
          unfold eq_rect_r.
          simpl.
          rewrite <- eq_rect_eq.
          destruct get_link. destruct s0. f_equal. apply subset_eq_compat. reflexivity.
          reflexivity.
  Qed.


Lemma arity_nest_right_neutral {n Y} (G : bigraph 1 EmptyNDL n Y) :
  forall n, 
  Arity (get_control (G <.> bigraph_identity) n) =
  Arity (get_control G (bij_void_sum_neutral n)).
  Proof.
  intros s i r o i' i'' p p' b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed. *)



 
(* Theorem nest_neutral_elt {n Y} (G : bigraph 1 EmptyNDL n Y) : 
  bigraph_equality (G <.> bigraph_identity) G.
  Proof.
    unfold nest. simpl. 
  apply 
    (BigEq _ _ _ _ _ _ _ _ (G <.> bigraph_identity) G
      eq_refl
      (fun (name : Name) => transitivity (P_NP (permutation_id Y)) (P_NP (permutation_id Y)))
      eq_refl
      (fun (name : Name) => reflexivity (In name Y))
      bij_void_sum_neutral_r
      bij_void_sum_neutral_r 
      (fun n => bij_rew (P := fin) (arity_comp_right_neutral b n)) 
    ).
  +  *)




Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph 0 i2 s1 i1. Admitted.

(* Theorem atom_is_empty_ion : 
  bigraph_equality.
  (discrete_ion <o> ∅)
  discrete_atom. *)

End NestingBig.