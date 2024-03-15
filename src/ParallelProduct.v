Require Import ConcreteBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import TensorProduct.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.


(** * Juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Module ParallelProduct (s : Signature) (n : Names) (b: Bigraphs s n).
Module tp := TensorProduct s n b.
Include tp.

Definition union_possible {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :=
  forall (i : NameSub (i1 ∩ i2)),
  match (get_link b1 (inl (to_left i))) with
  | inr e => False
  | inl o1' => 
    match get_link b2 (inl (to_right i)) with
    | inr e => False
    | inl o2' => proj1_sig o1' = proj1_sig o2' 
    end
  end.

Definition link_juxt {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : union_possible b1 b2} (*i don't use it in this definition though*)
  (ip :NameSub (app_merge_NoDupList i1 i2) + Port (join (get_control b1) (get_control b2))) :
  NameSub (app_merge_NoDupList o1 o2) + type (findec_sum (get_edge b1) (get_edge b2)). 
  Proof.
  destruct ip as [[n npf] | p].
  + (*inner*)  
    apply in_app_or_m_nod_dup in npf; try (apply (nd i2); try (apply (nd i1))).
    destruct npf.
    * (*inner1*)
    destruct (get_link b1 (inl (exist (fun name : Name => In name i1) n i0))).
    ** (*l1 (i1) = o1 *)
    left. destruct s0. exists x. apply in_left_list. apply i3.
    ** (*l1 (i1) = e1 *)
    right. simpl. left. exact t.
    * (*inner2*) 
    destruct (get_link b2 (inl (exist (fun name : Name => In name i2) n i0))).
    ** (*l2 (i2) = o2 *)
    left. destruct s0. exists x. apply in_right_list. apply i3.
    ** (*l2 (i2) = e2 *)
    right. simpl. right. exact t.
    * apply (nd i1).
  + (*Port*)
    destruct p as [np nppf]. destruct np as [np1|np2].
    * (*Port1*)
    destruct (get_link b1 (inr (existT _ np1 nppf))).
    ** (*l1 (p1)=o1*)
    left. destruct s0. exists x. apply in_left_list. apply i0.
    ** (*l1 (p1) = e1 *)
    right. simpl. left. exact t.
    * (*Port2*) 
    destruct (get_link b2 (inr (existT _ np2 nppf))).
    ** (*l2 (p2) = o2 *)
    left. destruct s0. exists x. apply in_right_list. apply i0.
    ** (*l2 (p2) = e2 *)
    right. simpl. right. exact t.
  Defined.

Definition bigraph_parallel_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {up : union_possible b1 b2}
    : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2).
  Proof.
  refine (Big 
    (s1 + s2)
    (app_merge_NoDupList i1 i2)
    (r1 + r2)
    (app_merge_NoDupList o1 o2)
    (findec_sum (get_node b1) (get_node b2))
    (findec_sum (get_edge b1) (get_edge b2))
    (join (get_control b1) (get_control b2))
    ((bij_id <+> bijection_inv bij_fin_sum) <o>
      (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle)) <o> 
      (bij_id <+> bij_fin_sum))
    (link_juxt b1 b2 (up := up)) _
    ). 
  - rewrite <- tensor_alt.
  apply finite_parent_inout.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined. 

Global Notation "b1 || b2" := (bigraph_parallel_product b1 b2) (at level 50, left associativity).

Theorem disjoint_innernames_implies_union_possible {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2} :
  i1 # i2 -> union_possible b1 b2.
  Proof.
  intros.
  unfold union_possible.
  intros.
  destruct i0. exfalso.
  unfold intersectionNDL in i0.
  simpl in i0.
  rewrite (intersection_disjoint_empty_NDL H) in i0.
  apply i0.
  Qed. 

Theorem tp_eq_pp {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {dis_i : i1 # i2} {dis_o : o1 # o2} :
  bigraph_equality 
    (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) 
    (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible dis_i) b1 b2).
  Proof.
  refine (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b2) (b1 || b2)
    eq_refl
    (permutation_id (app_merge' i1 i2))
    eq_refl
    (permutation_id (app_merge' o1 o2))
    bij_id
    bij_id
    _  _ _ _
    ).
  - simpl. apply id_left_neutral.
  - rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  - rewrite bij_sigT_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    simpl.
    apply functional_extensionality.
    intros [inner|port].
    + unfold parallel, funcomp, sum_shuffle, bij_list_backward', link_juxt, id.
      simpl.
      destruct inner.
      destruct (in_dec EqDecN x i1).
      * destruct (in_app_or_m_nod_dup i1 i2 x (nd i1) (nd i2) i0) eqn:E.
      ** symmetry. rewrite <- (innername_proof_irrelevant b1 x i3). 
      destruct get_link; try reflexivity.
      ** exfalso. specialize (dis_i x). apply dis_i; assumption.
      * destruct (in_app_or_m_nod_dup i1 i2 x (nd i1) (nd i2) i0).
      ** exfalso. apply n. apply i3.
      ** rewrite <- (innername_proof_irrelevant b2 x i3). 
      destruct get_link; try reflexivity.
    + unfold parallel, funcomp, sum_shuffle, bij_join_port_backward, bij_list_backward', bij_list_forward, link_juxt, id.
      simpl.
      destruct port as [[p1|p2] [pf]].
      * assert (exist (fun p : nat => p < Arity (get_control b1 p1)) pf l =
      exist (fun p : nat => p < Arity (join (get_control b1) (get_control b2) (inl p1))) pf l). 
      {apply subset_eq_compat. reflexivity. }
      rewrite <- H.
      destruct get_link; try reflexivity.
      * assert (exist (fun p : nat => p < Arity (get_control b2 p2)) pf l =
      exist (fun p : nat => p < Arity (join (get_control b1) (get_control b2) (inr p2))) pf l).
      {apply subset_eq_compat. reflexivity. }
      rewrite <- H.
      destruct get_link; try reflexivity.
  Qed.


Lemma arity_pp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_parallel_product 
    (up := disjoint_innernames_implies_union_possible (void_disjoint_all_list_left i)) 
    ∅ b) n) = Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_parallel_product 
    (up := disjoint_innernames_implies_union_possible (void_disjoint_all_list_left i)) ∅ b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ || b) b
    eq_refl
    (left_empty i)
    eq_refl
    (left_empty o)
    bij_void_sum_neutral
    bij_void_sum_neutral
    (fun n => bij_rew (P := fin) (arity_tp_left_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      destruct get_parent; try reflexivity.
      destruct f. f_equal. apply subset_eq_compat. reflexivity.  
    - unfold funcomp, parallel, sum_shuffle.
      simpl. 
      destruct s1; unfold inj_fin_add; simpl.
      destruct PeanoNat.Nat.ltb_spec0.
      * exfalso. apply PeanoNat.Nat.nlt_0_r in l0. apply l0.
      * 
      assert (exist (fun p : nat => p < s) (x - 0)
        (ZifyClasses.rew_iff_rev (x - 0 < s) (BinInt.Z.lt (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0)) (BinInt.Z.of_nat s))
        (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt (x - 0)
        (BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0))
        (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat
        (fun n0 m : BinNums.Z => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m)) Znat.Nat2Z.inj_sub_max x (BinInt.Z.of_nat x) eq_refl 0 BinNums.Z0
        eq_refl) s (BinInt.Z.of_nat s) eq_refl)
        (ZMicromega.ZTautoChecker_sound
        (Tauto.IMPL
        (Tauto.OR
        (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.lt BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0)))
        (Tauto.A Tauto.isProp
        {|
        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
        RingMicromega.Fop := RingMicromega.OpEq;
        RingMicromega.Frhs := EnvRing.PEsub (EnvRing.PEX (BinNums.xI BinNums.xH)) (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH)))
        |} tt))
        (Tauto.AND (Tauto.X Tauto.isProp (BinInt.Z.le (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0) BinNums.Z0))
        (Tauto.A Tauto.isProp
        {|
        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
        RingMicromega.Fop := RingMicromega.OpEq;
        RingMicromega.Frhs := EnvRing.PEc BinNums.Z0
        |} tt))) None
        (Tauto.IMPL
        (Tauto.A Tauto.isProp
        {|
        RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH);
        RingMicromega.Fop := RingMicromega.OpLt;
        RingMicromega.Frhs := EnvRing.PEadd (EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))) (EnvRing.PEX (BinNums.xO BinNums.xH))
        |} tt) None
        (Tauto.IMPL
        (Tauto.NOT
        (Tauto.A Tauto.isProp
        {|
        RingMicromega.Flhs := EnvRing.PEX (BinNums.xI BinNums.xH);
        RingMicromega.Fop := RingMicromega.OpLt;
        RingMicromega.Frhs := EnvRing.PEX (BinNums.xO (BinNums.xO BinNums.xH))
        |} tt)) None
        (Tauto.A Tauto.isProp
        {|
        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
        RingMicromega.Fop := RingMicromega.OpLt;
        RingMicromega.Frhs := EnvRing.PEX (BinNums.xO BinNums.xH)
        |} tt))))
        [ZMicromega.RatProof
        (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3)
        (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2)
        (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 1) (RingMicromega.PsatzIn BinNums.Z 0)))) ZMicromega.DoneProof;
        ZMicromega.RatProof
        (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 3)
        (RingMicromega.PsatzAdd (RingMicromega.PsatzIn BinNums.Z 2) (RingMicromega.PsatzIn BinNums.Z 0))) ZMicromega.DoneProof] eq_refl
        (fun p : BinNums.positive =>
        match p with
        | BinNums.xI _ => BinInt.Z.of_nat x
        | BinNums.xO p0 => match p0 with
        | BinNums.xH => BinInt.Z.of_nat s
        | _ => BinNums.Z0
        end
        | BinNums.xH => BinInt.Z.max BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0)
        end) (BinInt.Z.max_spec BinNums.Z0 (BinInt.Z.sub (BinInt.Z.of_nat x) BinNums.Z0))
        (ZifyClasses.rew_iff (x < s) (BinInt.Z.lt (BinInt.Z.of_nat x) (BinInt.Z.of_nat s))
        (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl s 
        (BinInt.Z.of_nat s)
        (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.of_nat
        BinInt.Z.add Znat.Nat2Z.inj_add 0 BinNums.Z0 eq_refl s (BinInt.Z.of_nat s) eq_refl)) l)
        (ZifyClasses.rew_iff (~ x < 0) (~ BinInt.Z.lt (BinInt.Z.of_nat x) BinNums.Z0)
        (ZifyClasses.not_morph (x < 0) (BinInt.Z.lt (BinInt.Z.of_nat x) BinNums.Z0)
        (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat BinInt.Z.lt Znat.Nat2Z.inj_lt x (BinInt.Z.of_nat x) eq_refl 0 BinNums.Z0 eq_refl)) n)))
                  = exist (fun p : nat => p < s) x l).
      apply subset_eq_compat. lia.
      rewrite <- H. destruct get_parent.
      ** auto. ** f_equal. unfold surj_fin_add. destruct f. apply subset_eq_compat. reflexivity. 
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward, id.
      destruct i1.
      simpl.
      unfold id. 
      destruct in_app_or_m_nod_dup.
      * exfalso. apply in_nil in i1. apply i1.
      * rewrite <- (innername_proof_irrelevant b x i0 i1).
      destruct get_link; try reflexivity.
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id, link_juxt.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward, bij_subset_backward, bij_subset_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

Lemma arity_pp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (void_disjoint_all_list_right i)) b ∅) n) = Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_pp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_parallel_product (up := disjoint_innernames_implies_union_possible (void_disjoint_all_list_right i)) b ∅) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b || ∅) b
    (PeanoNat.Nat.add_0_r s)
    (right_empty i)
    (PeanoNat.Nat.add_0_r r)
    (right_empty o)
    bij_void_sum_neutral_r
    bij_void_sum_neutral_r
    (fun n => bij_rew (P := fin) (arity_tp_right_neutral b n)) 
  ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp, parallel.
      simpl. 
      destruct get_parent; try reflexivity.
      destruct f. f_equal. 
      unfold bij_rew_forward.
      unfold surj_fin_add.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + O) r _ x _).
      apply subset_eq_compat. 
      reflexivity.  
    - unfold funcomp, parallel, sum_shuffle.
      destruct s1. unfold eq_sym.
      unfold bij_rew_forward.
      unfold inj_fin_add.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) s (s + O) _ x _).
      destruct PeanoNat.Nat.ltb_spec0.
      * rewrite (proof_irrelevance _ _ l).
      destruct get_parent; try reflexivity.
      f_equal.  
      destruct f.
      unfold surj_fin_add.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + O) r _ x0 _).
      apply subset_eq_compat. 
      reflexivity.  
      * exfalso. apply n. apply l. 
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, parallel, link_juxt.
      simpl.
      unfold bij_subset_backward, bij_subset_forward, id.
      destruct i1.
      simpl.
      unfold id. 
      rewrite <- (innername_proof_irrelevant b x i0).
      destruct get_link; try reflexivity.
      destruct s0. f_equal. apply subset_eq_compat. reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id, link_juxt.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward, bij_subset_backward, bij_subset_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

(* Lemma arity_pp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) n12,
  Arity (get_control (b1 || b2) n12) = Arity (get_control (b2 || b1) (bij_sum_comm n12)).
  Proof.
  intros until n12.
  destruct n12.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_pp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  bigraph_equality (b1 ||b2) (b2 || b1).
  Proof.
  intros.
  refine (BigEq _ _ _ _ _ _ _ _ (b1 || b2) (b2 || b1)
    (@eq_sym _ _ _ _)
    in_app_merge'_comu
    (@eq_sym _ _ _ _)
    in_app_merge'_comu
    bij_sum_comm
    bij_sum_comm
    (fun n12 => bij_rew (P := fin) (arity_tp_comm b1 b2 n12))
    _ _ _
  ).
  + apply functional_extensionality.
    destruct x as [k2 | k1]; reflexivity.
  + apply functional_extensionality.
    (* destruct x as [[n2 | n1] | s21']; simpl; unfold funcomp; simpl. destruct get_parent . ; reflexivity.
  + apply functional_extensionality.
    destruct x as [i21 | (v1, (k1, Hvk1))]; simpl; unfold funcomp; simpl.
    - (*TODO destruct i*) Admitted.  *)
    (* destruct get_link; reflexivity.
    - destruct get_link; reflexivity.
    - destruct p12 as ([v2 | v1], (i21, Hvi21)); simpl.
      * unfold bij_rew_forward.
        unfold eq_rect_r.
        (*
          erewrite eq_rect_pi.
          erewrite (eq_rect_pi (x := inl v2)).
        *)
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
      * unfold bij_rew_forward.
        unfold eq_rect_r.
        (*
          erewrite eq_rect_pi.
          erewrite (eq_rect_pi (x := inl v2)).
        *)
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
  Qed. *)
Abort. We no longer have commutativity *)

Lemma union_possible_commutes {s1 i1 r1 o1 s2 i2 r2 o2}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  (up12 : union_possible b1 b2):
  union_possible b2 b1.
  Proof.
    unfold union_possible in *.
    unfold NameSub in *.
    intros i.
    specialize (up12 (to_commute i)).
    unfold to_commute in up12.
    destruct i as [i H21].
    unfold to_left,to_right in *.
    destruct get_link eqn:E.
    - rewrite <- (innername_proof_irrelevant b2 i (from_intersection_left H21)) in up12. 
    destruct (get_link b2 (inl (exist (fun name : Name => In name i2) i (from_intersection_left H21)))). 
    + rewrite <- (innername_proof_irrelevant b1 i (from_intersection_left (intersection_commutes H21))).
    rewrite E.
    destruct s0. destruct s3.
    simpl in *. symmetry. apply up12.
    + apply up12.
    - destruct (get_link b2
    (inl
      (exist (fun name : Name => In name i2) i
          (from_intersection_left H21)))) eqn:E'.
    + rewrite <- (innername_proof_irrelevant b1 i (from_intersection_left (intersection_commutes H21))).
    rewrite E. apply up12.
    + apply up12.
  Qed.

Lemma union_possible_assoc {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  {b3 : bigraph s3 i3 r3 o3}
  (up12 : union_possible b1 b2) 
  (up23 : union_possible b2 b3) 
  (up13 : union_possible b1 b3) :
  union_possible 
    (bigraph_parallel_product (up := up12) b1 b2)
    b3.
  Proof.
   unfold union_possible.
   intros [inter12_3 Hinter12_3].
   unfold intersectionNDL in *.
   simpl in *.
   pose Hinter12_3 as Htmp.
   rewrite intersection_eq in Htmp.
   destruct Htmp.
   unfold in_app_or_m_nod_dup.
   apply in_app_or_m in H.
   destruct H.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right in up23.
   rewrite <- (innername_proof_irrelevant b2 inter12_3 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** apply up23.
   * apply up23.
   + specialize (up13 (to_intersection inter12_3 H H0)).
   unfold to_intersection,to_left,to_right in up13.
   rewrite <- (innername_proof_irrelevant b1 inter12_3 (not_in_left (from_intersection_left Hinter12_3) n)) in up13.
   destruct get_link. 
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up13.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up13. apply up13.
   ** apply up13.
   * apply up13.
   - unfold union_possible in *.
   destruct (in_dec EqDecN inter12_3 i2).
   + specialize (up23 (to_intersection inter12_3 i0 H0)).
   unfold to_intersection,to_left,to_right in up23.
   rewrite <- (innername_proof_irrelevant b2 inter12_3 i0) in up23.
   destruct get_link.
   * set (Hi3 := from_intersection_right Hinter12_3).
   rewrite <- (innername_proof_irrelevant b3 inter12_3 Hi3) in up23.
   destruct get_link.
   ** destruct s0. destruct s4. simpl. simpl in up23. apply up23.
   ** apply up23.
   * apply up23.
   + exfalso. apply n. apply H.
  Qed.
   
Lemma arity_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : union_possible b1 b2} {up23 : union_possible b2 b3} {up13 : union_possible b1 b3} n12_3,
  Arity (get_control (
    bigraph_parallel_product 
      (up := (union_possible_assoc up12 up23 up13)) 
      (bigraph_parallel_product 
        (up := up12) 
        b1 
        b2) 
      b3) 
    n12_3) 
  = 
  Arity (get_control (
    bigraph_parallel_product 
      (up := union_possible_commutes (union_possible_assoc up23 (union_possible_commutes up13) (union_possible_commutes up12))) 
      b1 
      (bigraph_parallel_product 
        (up := up23) 
        b2 
        b3)) 
    (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
  {up12 : union_possible b1 b2} {up23 : union_possible b2 b3} {up13 : union_possible b1 b3},
  bigraph_equality 
    (bigraph_parallel_product 
      (up := (union_possible_assoc up12 up23 up13)) 
      (bigraph_parallel_product (up := up12) b1 b2) 
      b3)
    (bigraph_parallel_product 
      (up := union_possible_commutes (union_possible_assoc up23 (union_possible_commutes up13) (union_possible_commutes up12))) 
      b1 
      (bigraph_parallel_product (up := up23) b2 b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 || b2) || b3) (b1 || (b2 || b3))
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    tr_permutation
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    tr_permutation
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (P := fin) (arity_pp_assoc b1 b2 b3 n12_3))
  ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | s1_23']; simpl; unfold funcomp; simpl.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ x _).
      apply subset_eq_compat.
      reflexivity.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + x) _).
      apply subset_eq_compat.
      reflexivity.
    - destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + r2 + x) _).
      apply subset_eq_compat.
      rewrite PeanoNat.Nat.add_assoc.
      reflexivity.
    - destruct s1_23'; simpl.
      unfold parallel, id, sum_shuffle, inj_fin_add.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s1 + (s2 + s3)) (s1 + s2 + s3) _ x _).
      destruct (PeanoNat.Nat.ltb_spec0 x (s1 + s2)); simpl.
      * destruct (PeanoNat.Nat.ltb_spec0 x s1); simpl.
      ++ destruct get_parent; try reflexivity.
      f_equal.
      destruct f; simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ x0 _).
      apply subset_eq_compat.
      reflexivity.
      ++ destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2); simpl.
      -- rewrite (proof_irrelevance _ _ l1).
      destruct (get_parent b2); try reflexivity.
      f_equal.
      destruct f; simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + x0) _).
      apply subset_eq_compat.
      reflexivity.
      -- simpl. exfalso. apply n0. lia. 
      * destruct (PeanoNat.Nat.ltb_spec0 x s1).
      ++ lia.
      ++ destruct (PeanoNat.Nat.ltb_spec0 (x - s1) s2).
      -- lia.
      -- assert (forall H H', exist (fun p => p < s3) (x - (s1 + s2)) H =
      exist (fun p => p < s3) (x - s1 - s2) H').
      ** intros H H'.
      apply subset_eq_compat.
      lia.
      ** assert (x - s1 - s2 < s3) as H'; [ lia | unfold lt in H' ].
      rewrite (H _ H').
      symmetry.
      rewrite (proof_irrelevance _ _ H').
      destruct get_parent; simpl; try reflexivity.
      destruct f; simpl.
      f_equal.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r2 + r3) (r1 + (r2 + r3)) _ (r1 + r2 + x0) _).
      apply subset_eq_compat.
      rewrite PeanoNat.Nat.add_assoc.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[i123] | p123]; simpl; unfold funcomp; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. simpl. 
      unfold in_app_or_m_nod_dup.
      destruct (in_dec EqDecN i123 (app_merge' i2 i3)).
      * destruct (in_dec EqDecN i123 i3).
      ** destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).      
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 i123 i5). 
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_or_m in i4. destruct i4.
      -- apply n0. apply H.
      -- apply n. apply H.
      * destruct (in_dec EqDecN i123 i3).
      ** exfalso. apply n. apply in_right_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_left_list. apply i4.
      *** rewrite <- (innername_proof_irrelevant b1 i123 (not_in_left i0 n)). 
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        simpl. 
        unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
        simpl.
        unfold id. simpl. 
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.

Definition arity_pp_congruence_forward (*TODO: can't we deduce up24 from up13?*)
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : union_possible b1 b3} {up24 : union_possible b2 b4}
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 || b3))) :
    (fin (Arity (get_control (bigraph_parallel_product (up := up13) b1 b3) n13))) -> 
      (fin (Arity (get_control (bigraph_parallel_product (up := up24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_pp_congruence_backward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : union_possible b1 b3} {up24 : union_possible b2 b4}
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 || b3))) :
  (fin (Arity (get_control (bigraph_parallel_product (up := up24) b2 b4) ((bij_n12 <+> bij_n34) n13)))) 
  -> (fin (Arity (get_control (bigraph_parallel_product (up := up13) b1 b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_pp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : union_possible b1 b3} {up24 : union_possible b2 b4}
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 || b3))),
  bijection 
    (fin (Arity (get_control (bigraph_parallel_product (up := up13) b1 b3) n13))) 
    (fin (Arity (get_control (bigraph_parallel_product (up := up24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ 
    (arity_pp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) 
    (arity_pp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
  + destruct n13 as [n1 | n3]; simpl.
    - rewrite <- (fob_id _ _ (bij_p12 n1)).
      reflexivity.
    - rewrite <- (fob_id _ _ (bij_p34 n3)).
      reflexivity.
  + destruct n13 as [n1 | n3]; simpl.
    - rewrite <- (bof_id _ _ (bij_p12 n1)).
      reflexivity.
    - rewrite <- (bof_id _ _ (bij_p34 n3)).
      reflexivity.
  Defined.

Theorem bigraph_pp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  {up13 : union_possible b1 b3} {up24 : union_possible b2 b4},
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> 
    bigraph_equality (bigraph_parallel_product (up := up13) b1 b3) (bigraph_parallel_product (up := up24) b2 b4).
  Proof.
  intros until b4.
  intros up13 up24 Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 || b3) (b2 || b4)
    (f_equal2_plus _ _ _ _ bij_s12 bij_s34)
    (app_merge'_cong bij_i12 bij_i34)
    (f_equal2_plus _ _ _ _ bij_r12 bij_r34)
    (app_merge'_cong bij_o12 bij_o34)
    (bij_n12 <+> bij_n34)
    (bij_e12 <+> bij_e34)
    (arity_pp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
  ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2' | n4'] | s24']; simpl; unfold funcomp; simpl.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r3) (r2 + r4) _ x _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) r1 r2 _ x _).
      apply subset_eq_compat.
      reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r1 + r3) (r2 + r4) _ (r1 + x) _).
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) r3 r4 _ x _).
      apply subset_eq_compat.
      congruence.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel, id, bij_rew_forward, inj_fin_add.
      destruct s24'.
      simpl.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (s2 + s4) (s1 + s3) _ x _).
      subst.
      destruct (PeanoNat.Nat.ltb_spec0 x s2).
      * rewrite (@eq_rect_exist nat nat (fun n x => x < n) s2 s2 _ x).
        rewrite <- eq_rect_eq.
        destruct get_parent; try reflexivity.
        rewrite <- eq_rect_eq.
        destruct f; simpl.
        f_equal.
        rewrite <- eq_rect_eq.
        apply subset_eq_compat.
        reflexivity.
      * rewrite <- big_parent_eq34.
        rewrite <- eq_rect_eq.
        simpl.
        unfold parallel, funcomp, bij_rew_forward.
        rewrite <- eq_rect_eq.
        destruct get_parent; simpl; try reflexivity.
        f_equal.
        destruct f.
        rewrite <- eq_rect_eq.
        apply subset_eq_compat.
        reflexivity.
  + apply functional_extensionality. 
    destruct x as [[i24] | ([n2' | n4'], (i', Hi'))]; simpl.
    - rewrite <- big_link_eq34.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, in_app_or_m_nod_dup, link_juxt, in_app_or_m_nod_dup, id.
      simpl.
      unfold bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward, parallel, funcomp.
      simpl.
      unfold id.
      destruct (in_dec EqDecN i24 i3).
      * destruct (in_dec EqDecN i24 i4).
      ** symmetry. rewrite <- (innername_proof_irrelevant b3 i24 i5).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. apply bij_i34. apply i5.
      * destruct (in_dec EqDecN i24 i4).
      ** exfalso. apply n. apply bij_i34. apply i5.
      ** rewrite <- big_link_eq12.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, in_app_or_m_nod_dup, link_juxt, in_app_or_m_nod_dup, id.
      simpl.
      unfold bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward, parallel, funcomp.
      simpl.
      unfold id.
      set (Hn := match bij_i12 i24 with | conj _ H => H  end
        (eq_ind_r (fun b : Name => In b i2) (not_in_left i0 n0) eq_refl)).  
      rewrite <- (innername_proof_irrelevant b1 i24 Hn).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    - rewrite <- big_link_eq12.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold eq_rect_r.
      unfold parallel, funcomp.     
      simpl.
      erewrite <- (eq_rect_map (f := inl) (a := n2')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b1)) (type (get_node b2)) bij_n12) n2')).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) n2'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity. 
    - rewrite <- big_link_eq34.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold eq_rect_r.
      unfold parallel, funcomp.
      simpl.
      erewrite <- (eq_rect_map (f := inr) (a := n4')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b3)) (type (get_node b4)) bij_n34) n4')).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) n4'))).
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0.
      apply subset_eq_compat. reflexivity.
  Qed.

Fail Definition bigraph_packed_pp (b1 b2 : bigraph_packed) := 
  packing ((big b1) || (big b2)).

Fail Add Parametric Morphism :
  bigraph_packed_pp with
  signature bigraph_packed_equality ==> 
  bigraph_packed_equality ==> 
  bigraph_packed_equality as juxtaposition_morphism.
    (* Proof.
    unfold bigraph_packed_equality, bigraph_packed_pp.
    destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
    apply bigraph_pp_congruence.
    assumption.
    Qed. *)

(* Theorem bigraph_packed_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_pp ∅ b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_pp_left_neutral.
  Qed.

Theorem bigraph_packed_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_packed_equality (bigraph_packed_pp (bigraph_packed_pp b1 b2) b3) (bigraph_packed_pp b1 (bigraph_packed_pp b2 b3)).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_pp_assoc.
  Qed.

Lemma bigraph_packed_pp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_pp b ∅) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_pp_right_neutral.
  Qed. *)

(* Bifunctorial property *)

Theorem union_possible_dist {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {b1 : bigraph s1 i1o3 r1 o1} 
  {b2 : bigraph s2 i2o4 r2 o2} 
  {b3 : bigraph s3 i3 s1 o3i1} 
  {b4 : bigraph s4 i4 s2 o4i2}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (up12 : union_possible b1 b2) (up34 : union_possible b3 b4) :
  union_possible 
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4).
  Proof.
    unfold union_possible, NameSub in *.
    unfold bigraph_composition.
    simpl. 
    intros.
    unfold funcomp, parallel, id, sequence, switch_link, permut_list_forward, bij_join_port_backward.
    unfold rearrange, extract1.
    simpl.
    specialize (up34 i0).
    destruct get_link eqn:E.
    - destruct s0 as [o' Ho'].
      destruct (in_dec EqDecN o' i2o4).
      + pose Ho' as Ho''.
        apply (p13 o') in Ho''.
        specialize (up12 (to_intersection o' Ho'' i1)).
        unfold to_left, to_right, to_intersection in *.
        rewrite <- (innername_proof_irrelevant b1 o' (from_intersection_left (in_both_in_intersection Ho'' i1))).
        destruct get_link eqn:E'.
        ++ destruct i0.
          destruct (get_link b4 (inl (exist (fun name : Name => In name i4) x (from_intersection_right i0)))) eqn:E''.
          * destruct s5.
            simpl in up34. destruct up34.
            rewrite <- (innername_proof_irrelevant b2 o' (from_intersection_right
            (in_both_in_intersection Ho'' i1))).
            destruct (get_link b2 (inl (exist (fun inner : Name => In inner i2o4) o' (from_intersection_right (in_both_in_intersection Ho'' i1))))) eqn:E'''.
            ** apply up12.
            ** apply up12.
          * apply up34.
        ++ apply up12.
      + destruct i0.
      unfold to_left, to_right in *.
      destruct get_link; destruct get_link.
      * destruct s0. destruct s5. simpl in *. destruct up34.
      exfalso. apply n. apply (p24 o'). apply i2.
      * exfalso. apply up34.
      * destruct s0. simpl in *. destruct up34.
      exfalso. apply n. apply (p24 o'). apply i1.
      * exfalso. apply up34.
    - apply up34.
  Qed.


Theorem arity_comp_pp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {up12 : union_possible b1 b2} {up34 : union_possible b3 b4}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (n12_34:type (get_node (b1 || b2 <<o>> (b3 || b4)))),
  Arity (get_control
    (bigraph_composition (p := permutation_distributive p13 p24)
      (bigraph_parallel_product (up := up12) b1 b2) 
      (bigraph_parallel_product (up := up34) b3 b4)) n12_34) =
  Arity (get_control 
    ((bigraph_parallel_product (up := union_possible_dist up12 up34)
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4))) 
    (sum_shuffle n12_34)).
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.

Theorem bigraph_comp_pp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {up12 : union_possible b1 b2} {up34 : union_possible b3 b4}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)},
  bigraph_equality 
    (bigraph_composition (p := permutation_distributive p13 p24)
      (bigraph_parallel_product (up := up12) b1 b2) 
      (bigraph_parallel_product (up := up34) b3 b4))
    ((bigraph_parallel_product (up := union_possible_dist up12 up34)
      (bigraph_composition (p:=p13) b1 b3) 
      (bigraph_composition (p:=p24) b2 b4))) .
  Proof.
  intros.
  apply (BigEq
    _ _ _ _
    _ _ _ _ 
    ((b1 || b2) <<o>> (b3 || b4)) 
    ((b1 <<o>> b3) || (b2 <<o>> b4))
    (reflexivity (s3 + s4)) (*s3 + s4*)
    reflnames (*i3 + i4*)
    (reflexivity (r1 + r2)) (*r1 + r2*)
    reflnames (*o1 + o2*)
    bij_sum_shuffle(* n1 + n2 + n3 + n4*)
    bij_sum_shuffle (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (P := fin) (arity_comp_pp_dist b1 b2 b3 b4 n12_34)) (* Port *)
  ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|(s34, Hs34)]; simpl; unfold funcomp; simpl; unfold sequence, extract1, inject, sum_shuffle, parallel, id.
    - destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. destruct get_parent; try reflexivity.
      destruct f as (s1', Hs1').
      simpl.
      destruct PeanoNat.Nat.ltb_spec0.
      * rewrite (proof_irrelevance _ l Hs1').
        destruct get_parent; try reflexivity.
      * contradiction.
    - destruct get_parent; try reflexivity.
    - destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2'). unfold rearrange, extract1.
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    * exfalso. assert (forall a b, ~ a + b < a).
      {intros. lia. } 
      apply (H s1 s2'). apply l.
    * assert 
    (exist (fun p : nat => p < s2) (s1 + s2' - s1)
      (ZifyClasses.rew_iff_rev (s1 + s2' - s1 < s2)
        (BinInt.Z.lt
            (BinInt.Z.max BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1))) (BinInt.Z.of_nat s2))
        (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
            BinInt.Z.lt Znat.Nat2Z.inj_lt 
            (s1 + s2' - s1)
            (BinInt.Z.max BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1)))
            (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
              BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat
              BinInt.Z.of_nat BinInt.Z.of_nat
              (fun n0 m : BinNums.Z =>
                BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n0 m))
              Znat.Nat2Z.inj_sub_max (s1 + s2')
              (BinInt.Z.of_nat (s1 + s2')) eq_refl s1
              (BinInt.Z.of_nat s1) eq_refl) s2 
            (BinInt.Z.of_nat s2) eq_refl)
        (ZMicromega.ZTautoChecker_sound
            (Tauto.IMPL
              (Tauto.OR
                  (Tauto.AND
                    (Tauto.X Tauto.isProp
                        (BinInt.Z.lt BinNums.Z0
                          (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                              (BinInt.Z.of_nat s1))))
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpEq;
                          RingMicromega.Frhs :=
                            EnvRing.PEsub
                              (EnvRing.PEX (BinNums.xI BinNums.xH))
                              (EnvRing.PEX
                                (BinNums.xO (BinNums.xO BinNums.xH)))
                        |} tt))
                  (Tauto.AND
                    (Tauto.X Tauto.isProp
                        (BinInt.Z.le
                          (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                              (BinInt.Z.of_nat s1)) BinNums.Z0))
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpEq;
                          RingMicromega.Frhs := EnvRing.PEc BinNums.Z0
                        |} tt))) None
              (Tauto.IMPL
                  (Tauto.A Tauto.isProp
                    {|
                      RingMicromega.Flhs :=
                        EnvRing.PEX (BinNums.xI BinNums.xH);
                      RingMicromega.Fop := RingMicromega.OpLt;
                      RingMicromega.Frhs :=
                        EnvRing.PEadd
                          (EnvRing.PEX
                              (BinNums.xO (BinNums.xO BinNums.xH)))
                          (EnvRing.PEX (BinNums.xO BinNums.xH))
                    |} tt) None
                  (Tauto.IMPL
                    (Tauto.NOT
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEX (BinNums.xI BinNums.xH);
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEX
                                (BinNums.xO (BinNums.xO BinNums.xH))
                          |} tt)) None
                    (Tauto.A Tauto.isProp
                        {|
                          RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                          RingMicromega.Fop := RingMicromega.OpLt;
                          RingMicromega.Frhs :=
                            EnvRing.PEX (BinNums.xO BinNums.xH)
                        |} tt))))
            [ZMicromega.RatProof
              (RingMicromega.PsatzAdd
                  (RingMicromega.PsatzIn BinNums.Z 3)
                  (RingMicromega.PsatzAdd
                    (RingMicromega.PsatzIn BinNums.Z 2)
                    (RingMicromega.PsatzAdd
                        (RingMicromega.PsatzIn BinNums.Z 1)
                        (RingMicromega.PsatzIn BinNums.Z 0))))
              ZMicromega.DoneProof;
            ZMicromega.RatProof
              (RingMicromega.PsatzAdd
                  (RingMicromega.PsatzIn BinNums.Z 3)
                  (RingMicromega.PsatzAdd
                    (RingMicromega.PsatzIn BinNums.Z 2)
                    (RingMicromega.PsatzIn BinNums.Z 0)))
              ZMicromega.DoneProof] eq_refl
            (fun p : BinNums.positive =>
            match p with
            | BinNums.xI _ => BinInt.Z.of_nat (s1 + s2')
            | BinNums.xO p0 =>
                match p0 with
                | BinNums.xI _ => BinNums.Z0
                | BinNums.xO _ => BinInt.Z.of_nat s1
                | BinNums.xH => BinInt.Z.of_nat s2
                end
            | BinNums.xH =>
                BinInt.Z.max BinNums.Z0
                  (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                      (BinInt.Z.of_nat s1))
            end)
            (BinInt.Z.max_spec BinNums.Z0
              (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1)))
            (ZifyClasses.rew_iff (s1 + s2' < s1 + s2)
              (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.add (BinInt.Z.of_nat s1)
                    (BinInt.Z.of_nat s2)))
              (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                  BinInt.Z.lt Znat.Nat2Z.inj_lt 
                  (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                  (s1 + s2)
                  (BinInt.Z.add (BinInt.Z.of_nat s1)
                    (BinInt.Z.of_nat s2))
                  (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
                    BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat
                    BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add
                    Znat.Nat2Z.inj_add s1 
                    (BinInt.Z.of_nat s1) eq_refl s2
                    (BinInt.Z.of_nat s2) eq_refl))
              (ZifyClasses.rew_iff_rev (s1 + s2' < s1 + s2)
                  (BinInt.Z.lt
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2'))
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2)))
                  (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                    BinInt.Z.lt Znat.Nat2Z.inj_lt 
                    (s1 + s2')
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2'))
                    (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                        BinNums.Z BinNums.Z PeanoNat.Nat.add
                        BinInt.Z.of_nat BinInt.Z.of_nat
                        BinInt.Z.of_nat BinInt.Z.add
                        Znat.Nat2Z.inj_add s1 
                        (BinInt.Z.of_nat s1) eq_refl s2'
                        (BinInt.Z.of_nat s2') eq_refl) 
                    (s1 + s2)
                    (BinInt.Z.add (BinInt.Z.of_nat s1)
                        (BinInt.Z.of_nat s2))
                    (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                        BinNums.Z BinNums.Z PeanoNat.Nat.add
                        BinInt.Z.of_nat BinInt.Z.of_nat
                        BinInt.Z.of_nat BinInt.Z.add
                        Znat.Nat2Z.inj_add s1 
                        (BinInt.Z.of_nat s1) eq_refl s2
                        (BinInt.Z.of_nat s2) eq_refl))
                  (ZMicromega.ZTautoChecker_sound
                    (Tauto.IMPL
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEX (BinNums.xO BinNums.xH);
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEX (BinNums.xI BinNums.xH)
                          |} tt) None
                        (Tauto.A Tauto.isProp
                          {|
                            RingMicromega.Flhs :=
                              EnvRing.PEadd 
                                (EnvRing.PEX BinNums.xH)
                                (EnvRing.PEX (BinNums.xO BinNums.xH));
                            RingMicromega.Fop := RingMicromega.OpLt;
                            RingMicromega.Frhs :=
                              EnvRing.PEadd 
                                (EnvRing.PEX BinNums.xH)
                                (EnvRing.PEX (BinNums.xI BinNums.xH))
                          |} tt)) [] eq_refl
                    (fun p : BinNums.positive =>
                      match p with
                      | BinNums.xI _ => BinInt.Z.of_nat s2
                      | BinNums.xO _ => BinInt.Z.of_nat s2'
                      | BinNums.xH => BinInt.Z.of_nat s1
                      end)
                    (ZifyClasses.rew_iff 
                        (s2' < s2)
                        (BinInt.Z.lt (BinInt.Z.of_nat s2')
                          (BinInt.Z.of_nat s2))
                        (ZifyClasses.mkrel nat BinNums.Z lt
                          BinInt.Z.of_nat BinInt.Z.lt
                          Znat.Nat2Z.inj_lt s2' 
                          (BinInt.Z.of_nat s2') eq_refl s2
                          (BinInt.Z.of_nat s2) eq_refl) Hs2'))))
            (ZifyClasses.rew_iff (~ s1 + s2' < s1)
              (~
                BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                  (BinInt.Z.of_nat s1))
              (ZifyClasses.not_morph (s1 + s2' < s1)
                  (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                    (BinInt.Z.of_nat s1))
                  (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                    BinInt.Z.lt Znat.Nat2Z.inj_lt 
                    (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                    s1 (BinInt.Z.of_nat s1) eq_refl)) n)))
          = exist (fun p : nat => p < s2) s2' Hs2').
    apply subset_eq_compat. lia.
    rewrite <- H.
    destruct get_parent; try reflexivity.
    - unfold rearrange, extract1. 
    destruct PeanoNat.Nat.ltb_spec0.
    * destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2').
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    ** rewrite (proof_irrelevance _ l0 Hs2').
      destruct get_parent; try reflexivity.
    ** contradiction.
    * destruct get_parent; try reflexivity.
    destruct f as (s2', Hs2').
    simpl.
    destruct PeanoNat.Nat.ltb_spec0.
    ** exfalso. assert (forall a b, ~ a + b < a).
      {intros. lia. } 
      apply (H s1 s2'). apply l.
    ** 
    assert (exist (fun p : nat => p < s2) (s1 + s2' - s1)
      (ZifyClasses.rew_iff_rev (s1 + s2' - s1 < s2)
       (BinInt.Z.lt
          (BinInt.Z.max BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1))) (BinInt.Z.of_nat s2))
       (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
          BinInt.Z.lt Znat.Nat2Z.inj_lt 
          (s1 + s2' - s1)
          (BinInt.Z.max BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1)))
          (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
             BinNums.Z PeanoNat.Nat.sub BinInt.Z.of_nat
             BinInt.Z.of_nat BinInt.Z.of_nat
             (fun n1 m : BinNums.Z =>
              BinInt.Z.max BinNums.Z0 (BinInt.Z.sub n1 m))
             Znat.Nat2Z.inj_sub_max (s1 + s2')
             (BinInt.Z.of_nat (s1 + s2')) eq_refl s1
             (BinInt.Z.of_nat s1) eq_refl) s2 
          (BinInt.Z.of_nat s2) eq_refl)
       (ZMicromega.ZTautoChecker_sound
          (Tauto.IMPL
             (Tauto.OR
                (Tauto.AND
                   (Tauto.X Tauto.isProp
                      (BinInt.Z.lt BinNums.Z0
                         (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                            (BinInt.Z.of_nat s1))))
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpEq;
                        RingMicromega.Frhs :=
                          EnvRing.PEsub
                            (EnvRing.PEX (BinNums.xI BinNums.xH))
                            (EnvRing.PEX
                               (BinNums.xO (BinNums.xO BinNums.xH)))
                      |} tt))
                (Tauto.AND
                   (Tauto.X Tauto.isProp
                      (BinInt.Z.le
                         (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                            (BinInt.Z.of_nat s1)) BinNums.Z0))
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpEq;
                        RingMicromega.Frhs := EnvRing.PEc BinNums.Z0
                      |} tt))) None
             (Tauto.IMPL
                (Tauto.A Tauto.isProp
                   {|
                     RingMicromega.Flhs :=
                       EnvRing.PEX (BinNums.xI BinNums.xH);
                     RingMicromega.Fop := RingMicromega.OpLt;
                     RingMicromega.Frhs :=
                       EnvRing.PEadd
                         (EnvRing.PEX
                            (BinNums.xO (BinNums.xO BinNums.xH)))
                         (EnvRing.PEX (BinNums.xO BinNums.xH))
                   |} tt) None
                (Tauto.IMPL
                   (Tauto.NOT
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEX (BinNums.xI BinNums.xH);
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEX
                               (BinNums.xO (BinNums.xO BinNums.xH))
                         |} tt)) None
                   (Tauto.A Tauto.isProp
                      {|
                        RingMicromega.Flhs := EnvRing.PEX BinNums.xH;
                        RingMicromega.Fop := RingMicromega.OpLt;
                        RingMicromega.Frhs :=
                          EnvRing.PEX (BinNums.xO BinNums.xH)
                      |} tt))))
          [ZMicromega.RatProof
             (RingMicromega.PsatzAdd
                (RingMicromega.PsatzIn BinNums.Z 3)
                (RingMicromega.PsatzAdd
                   (RingMicromega.PsatzIn BinNums.Z 2)
                   (RingMicromega.PsatzAdd
                      (RingMicromega.PsatzIn BinNums.Z 1)
                      (RingMicromega.PsatzIn BinNums.Z 0))))
             ZMicromega.DoneProof;
           ZMicromega.RatProof
             (RingMicromega.PsatzAdd
                (RingMicromega.PsatzIn BinNums.Z 3)
                (RingMicromega.PsatzAdd
                   (RingMicromega.PsatzIn BinNums.Z 2)
                   (RingMicromega.PsatzIn BinNums.Z 0)))
             ZMicromega.DoneProof] eq_refl
          (fun p : BinNums.positive =>
           match p with
           | BinNums.xI _ => BinInt.Z.of_nat (s1 + s2')
           | BinNums.xO p0 =>
               match p0 with
               | BinNums.xI _ => BinNums.Z0
               | BinNums.xO _ => BinInt.Z.of_nat s1
               | BinNums.xH => BinInt.Z.of_nat s2
               end
           | BinNums.xH =>
               BinInt.Z.max BinNums.Z0
                 (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                    (BinInt.Z.of_nat s1))
           end)
          (BinInt.Z.max_spec BinNums.Z0
             (BinInt.Z.sub (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1)))
          (ZifyClasses.rew_iff (s1 + s2' < s1 + s2)
             (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.add (BinInt.Z.of_nat s1)
                   (BinInt.Z.of_nat s2)))
             (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                BinInt.Z.lt Znat.Nat2Z.inj_lt 
                (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                (s1 + s2)
                (BinInt.Z.add (BinInt.Z.of_nat s1)
                   (BinInt.Z.of_nat s2))
                (ZifyClasses.mkapp2 nat nat nat BinNums.Z BinNums.Z
                   BinNums.Z PeanoNat.Nat.add BinInt.Z.of_nat
                   BinInt.Z.of_nat BinInt.Z.of_nat BinInt.Z.add
                   Znat.Nat2Z.inj_add s1 
                   (BinInt.Z.of_nat s1) eq_refl s2
                   (BinInt.Z.of_nat s2) eq_refl))
             (ZifyClasses.rew_iff_rev (s1 + s2' < s1 + s2)
                (BinInt.Z.lt
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2'))
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2)))
                (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                   BinInt.Z.lt Znat.Nat2Z.inj_lt 
                   (s1 + s2')
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2'))
                   (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                      BinNums.Z BinNums.Z PeanoNat.Nat.add
                      BinInt.Z.of_nat BinInt.Z.of_nat
                      BinInt.Z.of_nat BinInt.Z.add
                      Znat.Nat2Z.inj_add s1 
                      (BinInt.Z.of_nat s1) eq_refl s2'
                      (BinInt.Z.of_nat s2') eq_refl) 
                   (s1 + s2)
                   (BinInt.Z.add (BinInt.Z.of_nat s1)
                      (BinInt.Z.of_nat s2))
                   (ZifyClasses.mkapp2 nat nat nat BinNums.Z
                      BinNums.Z BinNums.Z PeanoNat.Nat.add
                      BinInt.Z.of_nat BinInt.Z.of_nat
                      BinInt.Z.of_nat BinInt.Z.add
                      Znat.Nat2Z.inj_add s1 
                      (BinInt.Z.of_nat s1) eq_refl s2
                      (BinInt.Z.of_nat s2) eq_refl))
                (ZMicromega.ZTautoChecker_sound
                   (Tauto.IMPL
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEX (BinNums.xO BinNums.xH);
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEX (BinNums.xI BinNums.xH)
                         |} tt) None
                      (Tauto.A Tauto.isProp
                         {|
                           RingMicromega.Flhs :=
                             EnvRing.PEadd 
                               (EnvRing.PEX BinNums.xH)
                               (EnvRing.PEX (BinNums.xO BinNums.xH));
                           RingMicromega.Fop := RingMicromega.OpLt;
                           RingMicromega.Frhs :=
                             EnvRing.PEadd 
                               (EnvRing.PEX BinNums.xH)
                               (EnvRing.PEX (BinNums.xI BinNums.xH))
                         |} tt)) [] eq_refl
                   (fun p : BinNums.positive =>
                    match p with
                    | BinNums.xI _ => BinInt.Z.of_nat s2
                    | BinNums.xO _ => BinInt.Z.of_nat s2'
                    | BinNums.xH => BinInt.Z.of_nat s1
                    end)
                   (ZifyClasses.rew_iff 
                      (s2' < s2)
                      (BinInt.Z.lt (BinInt.Z.of_nat s2')
                         (BinInt.Z.of_nat s2))
                      (ZifyClasses.mkrel nat BinNums.Z lt
                         BinInt.Z.of_nat BinInt.Z.lt
                         Znat.Nat2Z.inj_lt s2' 
                         (BinInt.Z.of_nat s2') eq_refl s2
                         (BinInt.Z.of_nat s2) eq_refl) Hs2'))))
          (ZifyClasses.rew_iff (~ s1 + s2' < s1)
             (~
              BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                (BinInt.Z.of_nat s1))
             (ZifyClasses.not_morph (s1 + s2' < s1)
                (BinInt.Z.lt (BinInt.Z.of_nat (s1 + s2'))
                   (BinInt.Z.of_nat s1))
                (ZifyClasses.mkrel nat BinNums.Z lt BinInt.Z.of_nat
                   BinInt.Z.lt Znat.Nat2Z.inj_lt 
                   (s1 + s2') (BinInt.Z.of_nat (s1 + s2')) eq_refl
                   s1 (BinInt.Z.of_nat s1) eq_refl)) n0))) = 
        exist (fun p : nat => p < s2) s2' Hs2'). 
    apply subset_eq_compat. lia.
    rewrite <- H.
    destruct get_parent; try reflexivity.
  + apply functional_extensionality.
    destruct x as [[i' ipf]|p].
    - (*bijs l1234(i34) =l1324(i34)*)
      rewrite bij_subset_compose_id.
      rewrite bij_subset_compose_id.
      simpl.
      unfold bij_list_forward, sequence, switch_link, rearrange, parallel, extract1, funcomp, id.
      unfold bij_subset_forward.
      unfold permut_list_forward. 
      unfold link_juxt, bij_subset_backward.
      unfold id.
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      unfold union_possible in *.
      destruct (in_dec EqDecN i' i4).
      * (*bijs l1234(i4) =l1324(i4)*) 
      destruct get_link; try reflexivity.
      destruct s0 as [o' opf]. 
      destruct (in_dec EqDecN o' i2o4).
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 o' i1). 
      destruct get_link; try reflexivity.
      *** exfalso. apply n. apply (p24 o'). assumption.
      * (*bijs l1234(i3) =l1324(i3)*)
      destruct get_link eqn:E; try reflexivity. 
      destruct s0 as [o' opf']. 
      destruct (in_dec EqDecN o' i2o4).
      *** 
      (* exfalso.  *)
      (* unfold Disjoint in dis_i12. *)
      (* apply (dis_i12 o'). *)
      pose opf' as opf''.
      unfold permutation in *.
      apply (p13 o') in opf''.
      specialize (up12 (to_intersection o' opf'' i0)).
      unfold to_left, to_right, to_intersection in up12.
      rewrite <- (innername_proof_irrelevant b1 o' (from_intersection_left
      (in_both_in_intersection opf'' i0))).
      destruct get_link eqn:E'.
      **** rewrite <- (innername_proof_irrelevant b2 o' i0) in up12.      
      destruct (get_link b2
      (inl (exist (fun name : Name => In name i2o4) o' i0))).
      ++ f_equal. destruct s0. destruct s5. apply subset_eq_compat.
      simpl in up12. symmetry. apply up12.
      ++ exfalso. apply up12. 
      **** exfalso. apply up12.
      *** rewrite <- (innername_proof_irrelevant b1 o' (match p13 o' with
      | conj H _ => H
      end opf')).
      destruct (get_link b1 (inl (exist (fun name : Name => In name i1o3) o' (match p13 o' with | conj H _ => H end opf')))).
      **** f_equal.
      **** reflexivity.
    - (*bijs l1234(p34) =l1324(p34)*)
    unfold union_possible in *.
    destruct p as ([[v1 | v2] | [v3 | v4]], (i1234, Hvi1234)); unfold bij_join_port_backward; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward.
      unfold bij_rew_forward, funcomp.
      rewrite <- eq_rect_eq. simpl. unfold equal_f. unfold f_equal, id, eq_rect_r. 
      rewrite <- eq_rect_eq. simpl.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0.
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      destruct (in_dec EqDecN x i2o4).
      ** unfold permutation in *.
      pose i0 as i0'.
      apply (p13 x) in i0'.
      clear Hvi1234.
      specialize (up12 (to_intersection x i0' i1)).
      unfold to_left, to_right, to_intersection in up12.
      rewrite <- (innername_proof_irrelevant b1 x (match p13 x with | conj H _ => H end i0)) in up12.
      destruct get_link eqn:E'.
      *** rewrite <- (innername_proof_irrelevant b2 x i1) in up12.      
      destruct (get_link b2
      (inl (exist (fun name : Name => In name i2o4) x i1))).
      ++ f_equal. destruct s0. destruct s5. apply subset_eq_compat.
      simpl in up12. symmetry. apply up12.
      ++ exfalso. apply up12. 
      *** exfalso. apply up12.
      ** rewrite <- (innername_proof_irrelevant b1 x (match p13 x with | conj H _ => H end i0)).
      destruct (get_link b1
      (inl
         (exist (fun inner : Name => In inner i1o3) x
            (match p13 x with
             | conj H _ => H
             end i0)))).
      **** f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
      **** reflexivity.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    *  unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      unfold permutation_distributive, permut_list_forward.
      destruct get_link; unfold rearrange; unfold extract1; simpl; try reflexivity.
      ** destruct s0.
      unfold in_app_or_m_nod_dup.
      unfold in_app_or_m, sum_shuffle.
      destruct (in_dec EqDecN x i2o4).
      *** symmetry. rewrite <- (innername_proof_irrelevant b2 x i1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply n. apply (p24 x). assumption.
  Qed. 


Lemma union_possible_id {X Y: NoDupList} :
  union_possible (@bigraph_id 0 X) (@bigraph_id 0 Y).
  unfold union_possible.
  intros [iXY Hi].
  simpl. reflexivity.
  Qed.

Lemma id_union : forall X Y:NoDupList, 
  bigraph_equality
  (@bigraph_id 0 (app_merge_NoDupList X Y))
  (bigraph_parallel_product (up := union_possible_id) (@bigraph_id 0 X) (@bigraph_id 0 Y)).
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
    (BigEq 0 0 (0+0) _ _ _ _ _ (bigraph_id) (bigraph_id || bigraph_id)
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
    Unshelve. apply union_possible_id.
  Qed.
End ParallelProduct.