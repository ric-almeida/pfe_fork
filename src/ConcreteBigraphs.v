Require Import Coq.Logic.Decidable.
Require Import Coq.Setoids.Setoid.
Require Import ToolsForBigraphs.
Require Import FinFun.
Require Import MyBasics.
Require Import Basics.
Require Import Morphisms.
Require Import FinDecTypes.
Require Import Bijections.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.

Set Printing All.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs.

Variable Kappa:Type.
Variable Arity:Kappa-> nat.

(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.
Definition Port {node : Type} (control : node -> Kappa): Type :=
  { n : node & fin (Arity (control n)) }.

Definition join {A B C : Type} (p : A -> C) (q : B -> C) (ac : A+B) : C :=
  match ac with
  | inl a => (p a)
  | inr b => (q b)
  end.

Definition bij_join_port_forward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa) :
  Port c1 + Port c2 -> 
  Port (join c1 c2).
  Proof.
  refine (fun p => match p with
              | inl (existT _ vi1 Hvi1) => _
              | inr (existT _ vi2 Hvi2) => _
              end).
  + exists (inl vi1).
    destruct Hvi1 as (i1, Hi1).
    exists i1.
    exact Hi1.
  + exists (inr vi2).
    destruct Hvi2 as (i2, Hi2).
    exists i2.
    exact Hi2.
  Defined.

Definition bij_join_port_backward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  Port (join c1 c2) -> Port c1 + Port c2.
  Proof.
    destruct 1 as ([v1 | v2], (i, Hvi)).
    + left.
      exists v1.
      exists i.
      apply Hvi.
    + right.
      exists v2.
      exists i.
      apply Hvi.
    Defined.

Definition bij_join_port { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  bijection (Port c1 + Port c2) (Port (join c1 c2)).
  Proof.
  apply 
    (mkBijection _ _ 
    (bij_join_port_forward c1 c2) 
    (bij_join_port_backward c1 c2)).
  + apply functional_extensionality.
    destruct x as ([v1|v2], (i, Hvi)).
    - reflexivity.
    - reflexivity.
  + apply functional_extensionality.
    destruct x as [(v1, (i1, Hvi1)) | (v2, (i2, Hvi2))].
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
  Defined.

Definition bij_port_void (c : void -> Kappa) : bijection (Port c) void.
  Proof.
  apply (mkBijection _ _ (fun vi => match vi with existT _ v _ => void_univ_embedding v end) (void_univ_embedding)).
  + apply functional_extensionality.
    destruct x.
  + apply functional_extensionality.
    destruct x as (v, (i, H)).
    destruct v.
  Defined.

Lemma tensor_alt : forall {N1 I1 O1 N2 I2 O2} (f1 : N1 + I1 -> N1 + O1) (f2 : N2 + I2 -> N2 + O2), 
  f1 ** f2 = (bij_sum_shuffle <o> (parallel f1 f2) <o> (bijection_inv bij_sum_shuffle)).
  Proof.
  intros.
  apply functional_extensionality.
  destruct x as [[n1|n2]|[i1|i2]]; reflexivity.
  Qed.

Record bigraph  (site: FinDecType) 
                (innername: FinDecType) 
                (root: FinDecType) 
                (outername: FinDecType) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    control : (type node) -> (Kappa) ;
    parent : (type node) + (type site) -> (type node) + (type root) ; 
    link : (type innername) + Port control -> (type outername) + (type edge); 
    ap : FiniteParent parent ;
  }.
End IntroBigraphs.

(** * Getters
This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s i r o : FinDecType} (bg : bigraph s i r o) : FinDecType := 
  node s i r o bg.
Definition get_edge {s i r o : FinDecType} (bg : bigraph s i r o) : FinDecType := 
  edge s i r o bg.
Definition get_control {s i r o : FinDecType} (bg : bigraph s i r o) : type (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s i r o : FinDecType} (bg : bigraph s i r o) : (type (get_node bg)) + (type s) -> (type (get_node bg)) + (type r) :=
  @parent s i r o bg.
Definition get_link {s i r o : FinDecType} (bg : bigraph s i r o) : (type i) + Port (get_control bg) -> (type o) + type (get_edge bg) :=
  @link s i r o bg.
End GettersBigraphs.

(** * Equivalence between two bigraphs
  This section defines the equivalence relation between bigraphs. 
  We say there's an equivalence between two types if we give a bijection 
  (cf support_for_bigraphs) between the two types. To define the equivalence 
  between bigraphs, we want an equivalence between each Type and between 
  each function.
  To do that, we make definitions of equivalence between each function. 
  We coerce the Record bigraph_equality into a Prop, which means that we can
  access the bjections, but also that their existence means the Prop is True.
  Note that our equivalence is heterogeneous. 
  We prove that our relation bigraph_equality is reflexive, 
  symmetric and transitive. This is going to be useful to be able to rewrite 
  bigraphs at will. *)
Section EquivalenceBigraphs.
(** ** On the heterogeneous type *)
Record bigraph_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigEq
  {
    bij_s : bijection (type s1) (type s2) ;
    bij_i : bijection (type i1) (type i2) ;
    bij_r : bijection (type r1) (type r2) ;
    bij_o : bijection (type o1) (type o2) ;
    bij_n : bijection (type (get_node b1)) (type (get_node b2));
    bij_e : bijection (type (get_edge b1)) (type (get_edge b2));
    bij_p : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n n1))));
    big_control_eq : (bij_n -->> (@bijection_id Kappa)) (get_control b1) = get_control b2;
    big_parent_eq  : ((bij_n <+> bij_s) -->> (bij_n <+> bij_r)) (get_parent b1) = get_parent b2;
    big_link_eq    : ((bij_i <+> <{ bij_n & bij_p }>) -->> (bij_o <+> bij_e)) (get_link b1) = get_link b2
  }.

Lemma bigraph_equality_refl {s i r o : FinDecType} (b : bigraph s i r o) :
  bigraph_equality b b.
  Proof.
  eapply (BigEq _ _ _ _ _ _ _ _ _ _ bijection_id bijection_id bijection_id bijection_id bijection_id bijection_id (fun _ => bijection_id)).
  + rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_sigT_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  Qed.

Lemma bigraph_equality_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  bigraph_equality b1 b2
      -> bigraph_equality b2 b1.
  Proof.
  intro Heqb1b2.
  destruct Heqb1b2.
  apply (BigEq _ _ _ _ _ _ _ _ b2 b1
          (bijection_inv bij_s)
          (bijection_inv bij_i)
          (bijection_inv bij_r)
          (bijection_inv bij_o)
          (bijection_inv bij_n)
          (bijection_inv bij_e)
          (adjunction_bij bij_n bij_p)).
  + simpl. 
    rewrite <- big_control_eq.
    simpl.
    rewrite comp_assoc.
    rewrite id_left_neutral.
    rewrite comp_assoc.
    rewrite id_left_neutral.
    rewrite bij_n.(bof_id _ _).
    rewrite id_right_neutral.
    reflexivity.
  + rewrite <- big_parent_eq.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    simpl.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite parallel_compose.
    rewrite bij_n.(bof_id _ _).
    rewrite bij_s.(bof_id _ _).
    rewrite parallel_id.
    rewrite id_right_neutral.
    rewrite <- comp_assoc.
    rewrite parallel_compose.
    rewrite bij_n.(bof_id _ _).
    rewrite bij_r.(bof_id _ _).
    rewrite parallel_id.
    reflexivity.
  + rewrite <- bij_inv_sum.
    rewrite <- bij_inv_sigT.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    rewrite <- big_link_eq.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_inv_left_simpl.
    reflexivity.
  Qed.

Lemma bigraph_equality_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
    bigraph_equality b1 b2
      -> bigraph_equality b2 b3  
        -> bigraph_equality b1 b3.
  Proof.
  intros Heqb1b2 Heqb2b3.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb2b3 as (bij_s23, bij_i23, bij_r23, bij_o23, bij_n23, bij_e23, bij_p23, big_control_eq23, big_parent_eq23, big_link_eq23).
  apply (BigEq _ _ _ _ _ _ _ _ b1 b3
          (bij_s23 <O> bij_s12)
          (bij_i23 <O> bij_i12)
          (bij_r23 <O> bij_r12)
          (bij_o23 <O> bij_o12)
          (bij_n23 <O> bij_n12)
          (bij_e23 <O> bij_e12)
          (fun n1 => (bij_p23 (bij_n12 n1)) <O> (bij_p12 n1))).
  + rewrite <- big_control_eq23.
    rewrite <- big_control_eq12.
    reflexivity.
  + rewrite <- big_parent_eq23.
    rewrite <- big_parent_eq12.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_fun_compose_compose.
    simpl.
    reflexivity.
  + rewrite <- big_link_eq23.
    rewrite <- big_link_eq12.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_fun_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sigT_compose_compose.
    reflexivity.
  Qed.

(** ** On the packed type 
  The issue with the previous relation is that a parametric relation asks for two 
  objects of the exact same Type and our equality is heterogeneous. The solution we 
  will implement is to create a "packed bigraph" Type that will hold the interfaces 
  inside of it. This is a WIP. *)
Record bigraph_packed : Type :=
  mkPacked
  {
  s: FinDecType;
  i: FinDecType;
  r: FinDecType;
  o: FinDecType;
  big : bigraph s i r o
  }.
Coercion packing {s i r o} (b : bigraph s i r o) := 
  (mkPacked s i r o b).
Definition bigraph_packed_equality (bp1 bp2 : bigraph_packed) := 
  bigraph_equality (big bp1) (big bp2).

Lemma bigraph_packed_equality_refl (bp : bigraph_packed) : bigraph_packed_equality bp bp.
  Proof.
  apply bigraph_equality_refl.
  Qed.

Lemma bigraph_packed_equality_sym (bp1 bp2 : bigraph_packed) : bigraph_packed_equality bp1 bp2 -> bigraph_packed_equality bp2 bp1.
  Proof.
  apply bigraph_equality_sym.
  Qed.

Lemma bigraph_packed_equality_trans (bp1 bp2 bp3 : bigraph_packed) : bigraph_packed_equality bp1 bp2 -> bigraph_packed_equality bp2 bp3 -> bigraph_packed_equality bp1 bp3.
  Proof.
  apply bigraph_equality_trans.
  Qed.
  
End EquivalenceBigraphs.

Add Parametric Relation: (bigraph_packed) (bigraph_packed_equality)
  reflexivity proved by (bigraph_packed_equality_refl)
  symmetry proved by (bigraph_packed_equality_sym)
  transitivity proved by (bigraph_packed_equality_trans)
    as bigraph_packed_equality_rel.


Definition bigraph_juxtaposition {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    : bigraph (findec_sum s1 s2) (findec_sum i1 i2) (findec_sum r1 r2) (findec_sum o1 o2).
  Proof.
  apply (Big (findec_sum s1 s2)
             (findec_sum i1 i2)
             (findec_sum r1 r2)
             (findec_sum o1 o2)
             (findec_sum (get_node b1) (get_node b2))
             (findec_sum (get_edge b1) (get_edge b2))
             (join (get_control b1) (get_control b2))
             (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle))
             (bij_sum_shuffle <o> (parallel (get_link b1)   (get_link b2))   <o> (bijection_inv bij_sum_shuffle) <o> 
               (bijection_inv (@bijection_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))
        ).
  rewrite <- tensor_alt.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined.

Notation "b1 || b2" := (bigraph_juxtaposition b1 b2) (at level 50, left associativity).

(** * Disjoint juxtaposition
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Section DisjointJuxtaposition.
Definition bigraph_empty : bigraph findec_void findec_void findec_void findec_void.
  Proof.
  apply (Big findec_void findec_void findec_void findec_void
            findec_void findec_void
            (@void_univ_embedding _)
            (choice void_univ_embedding void_univ_embedding)
            (choice void_univ_embedding (void_univ_embedding <o> (bij_port_void (@void_univ_embedding _))))).
  intro n.
  destruct n.
  Defined.

Notation "∅" := bigraph_empty.
Lemma arity_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
        Arity (get_control (∅ || b) n) = Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_empty || b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (bigraph_empty || b) b
          bij_void_sum_neutral
          bij_void_sum_neutral
          bij_void_sum_neutral
          bij_void_sum_neutral
          bij_void_sum_neutral
          bij_void_sum_neutral
          (fun n => bij_rew (P := fin) (arity_juxt_left_neutral b n)) 
        ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_link; reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; reflexivity.
  Qed.

Lemma arity_juxt_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) n12,
  Arity (get_control (b1 || b2) n12) = Arity (get_control (b2 || b1) (bij_sum_comm n12)).
  Proof.
  intros until n12.
  destruct n12.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_juxt_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  bigraph_equality (b1 ||b2) (b2 || b1).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ (b1 || b2) (b2 || b1)
          bij_sum_comm
          bij_sum_comm
          bij_sum_comm
          bij_sum_comm
          bij_sum_comm
          bij_sum_comm
          (fun n12 => bij_rew (P := fin) (arity_juxt_comm b1 b2 n12))
        ).
  + apply functional_extensionality.
    destruct x as [k2 | k1]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2 | n1] | [s2' | s1']]; simpl; unfold funcomp; simpl; destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i2' | i1'] | p12]; simpl; unfold funcomp; simpl.
    - destruct get_link; reflexivity.
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
  Qed.

Lemma arity_juxt_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) n12_3,
  Arity (get_control ((b1 || b2) || b3) n12_3) = Arity (get_control (b1 || (b2 || b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_juxt_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_equality ((b1 || b2) || b3) (b1 || (b2 || b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 || b2) || b3) (b1 || (b2 || b3))
          bij_sum_assoc
          bij_sum_assoc
          bij_sum_assoc
          bij_sum_assoc
          bij_sum_assoc
          bij_sum_assoc
          (fun n12_3 => bij_rew (P := fin) (arity_juxt_assoc b1 b2 b3 n12_3))
        ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | [s1' | [s2' | s3']]]; simpl; unfold funcomp; simpl; destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i1' | [i2' | i3']] | p123]; simpl; unfold funcomp; simpl.
    - destruct get_link; reflexivity.
    - destruct get_link; reflexivity.
    - destruct get_link; reflexivity.
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
  Qed.

Definition arity_juxt_congruence_forward {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
                                    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
                                    (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
                                    (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
                                    (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
                                    (n13 : type (get_node (b1 || b3))) :
 (fin (Arity (get_control (b1 || b3) n13))) -> (fin (Arity (get_control (b2 || b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_juxt_congruence_backward {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
                                    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
                                    (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
                                    (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
                                    (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
                                    (n13 : type (get_node (b1 || b3))) :
 (fin (Arity (get_control (b2 || b4) ((bij_n12 <+> bij_n34) n13)))) -> (fin (Arity (get_control (b1 || b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_juxt_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
                                    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
                                    (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
                                    (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
                                    (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
                                    (n13 : type (get_node (b1 || b3))),
 bijection (fin (Arity (get_control (b1 || b3) n13))) (fin (Arity (get_control (b2 || b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ (arity_juxt_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) (arity_juxt_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
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

Theorem bigraph_juxt_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4),
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> bigraph_equality (b1 || b3) (b2 || b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 || b3) (b2 || b4)
          (bij_s12 <+> bij_s34)
          (bij_i12 <+> bij_i34)
          (bij_r12 <+> bij_r34)
          (bij_o12 <+> bij_o34)
          (bij_n12 <+> bij_n34)
          (bij_e12 <+> bij_e34)
          (arity_juxt_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
        ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2' | n4'] | [s2' | s4']]; simpl; unfold funcomp; simpl.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i2' | i4'] | ([n2' | n4'], (i', Hi'))]; simpl.
    - rewrite <- big_link_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_link; reflexivity.
    - rewrite <- big_link_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_link; reflexivity.
    - rewrite <- big_link_eq12.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold eq_rect_r.
      unfold parallel, funcomp.
      simpl.
      erewrite <- (eq_rect_map (f := inl) (a := n2')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b1)) (type (get_node b2)) bij_n12) n2')).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) n2'))).
      destruct get_link; reflexivity.
    - rewrite <- big_link_eq34.
      simpl.
      unfold sum_shuffle, parallel, choice, funcomp, id.
      simpl.
      unfold eq_rect_r.
      unfold parallel, funcomp.
      simpl.
      erewrite <- (eq_rect_map (f := inr) (a := n4')).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b3)) (type (get_node b4)) bij_n34) n4')).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) n4'))).
      destruct get_link; reflexivity.
  Qed.

Definition bigraph_packed_juxtaposition (b1 b2 : bigraph_packed) := 
  packing ((big b1) || (big b2)).
End DisjointJuxtaposition.

Add Parametric Morphism : bigraph_packed_juxtaposition with
 signature bigraph_packed_equality ==> bigraph_packed_equality ==> bigraph_packed_equality as juxtaposition_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
  apply bigraph_juxt_congruence.
  assumption.
  Qed.

Theorem bigraph_packed_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_juxtaposition bigraph_empty b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  intros.
  apply bigraph_juxt_left_neutral.
  Qed.

Theorem bigraph_packed_juxt_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  bigraph_packed_equality (bigraph_packed_juxtaposition b1 b2) (bigraph_packed_juxtaposition b2 b1).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  intros.
  apply bigraph_juxt_comm.
  Qed.

Theorem bigraph_packed_juxt_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_packed_equality (bigraph_packed_juxtaposition (bigraph_packed_juxtaposition b1 b2) b3) (bigraph_packed_juxtaposition b1 (bigraph_packed_juxtaposition b2 b3)).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  intros.
  apply bigraph_juxt_assoc.
  Qed.

Lemma bigraph_juxt_right_neutral : forall {s i r o} (b : bigraph s i r o), bigraph_packed_equality (bigraph_packed_juxtaposition b bigraph_empty) b.
  Proof.
  intros.
  rewrite bigraph_packed_juxt_comm.
  rewrite bigraph_packed_juxt_left_neutral.
  reflexivity.
  Qed.



(* Definition seq_link {s1 i1 r1 o1 s2 i2 : FinDecType} 
  {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 s1 i1} :=
  switch_link (switch_link (get_link b2) >> switch_link (get_link b1)) <o>
  (backward (@bijection_id _ <+> (bij_join_port (get_control b1) (get_control b2)))).

  Check seq_link. *)

Definition bigraph_composition {s1 i1 r1 o1 s2 i2 : FinDecType} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) 
    : bigraph s2 i2 r1 o1.
  Proof. 
  (* l :  i2 + (p1 + p2) -> o1 + (e1 + e2) *)
  (* l1 : i1 + p1 -> o1 + e1 *)
  (* l2 : i2 + p2 -> i1 + e2, o2 <=> i1 *)
  apply (Big s2 i2 r1 o1
        (findec_sum (get_node b1) (get_node b2))
        (findec_sum (get_edge b1) (get_edge b2))
        (join (get_control b1) (get_control b2))
        ((get_parent b2) >> (get_parent b1))
        (switch_link (switch_link (get_link b2) >> switch_link (get_link b1)) <o>
        (backward (@bijection_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))).
  apply (finite_parent_sequence).
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined.

Notation "b1 '<<o>>' b2" := (bigraph_composition b1 b2) (at level 50, left associativity).
(** * Composition
  This section deals with the operation of composition. This is the act
  of putting a bigraph inside another one. To do b1 o b2, the outerface 
  of b2 needs to be the innerface of b1. WIP: or just a bijection? *)
Section CompositionBigraphs.
Definition bigraph_identity {s i}: bigraph s i s i.
  Proof.
  apply (Big s i s i
          findec_void 
          findec_void
          (@void_univ_embedding _)
          id).
  - intros [inner | p].
    + left. exact inner.
    + destruct p. destruct x.
  - intro n.
    destruct n.
  Defined.

Lemma arity_comp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control ((bigraph_identity) <<o>> b) n) =
  Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
    + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_comp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_identity <<o>> b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (bigraph_identity <<o>> b) b
          bijection_id
          bijection_id
          bijection_id
          bijection_id
          bij_void_sum_neutral
          bij_void_sum_neutral
          (fun n => bij_rew (P := fin) (arity_comp_left_neutral b n)) 
        ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_link; reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; reflexivity.
  Qed.

Lemma arity_comp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (b <<o>> bigraph_identity) n) =
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_comp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (b <<o>> (bigraph_identity)) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b <<o>> bigraph_identity) b
          bijection_id
          bijection_id
          bijection_id
          bijection_id
          bij_void_sum_neutral_r
          bij_void_sum_neutral_r
          (fun n => bij_rew (P := fin) (arity_comp_right_neutral b n)) 
        ).
  + apply functional_extensionality.
    intro x.
    reflexivity. 
  + apply functional_extensionality.
    destruct x as [n1 | s1]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl.
      destruct get_link; reflexivity.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; reflexivity.
  Qed.


Lemma arity_comp_assoc : forall {s1 i1 r1 o1 s2 i2 s3 i3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) (b3 : bigraph s3 i3 s2 i2) n12_3,
  Arity (get_control ((b1 <<o>> b2) <<o>> b3) n12_3) = Arity (get_control (b1 <<o>> (b2 <<o>> b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_comp_assoc : forall {s1 i1 r1 o1 s2 i2 s3 i3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) (b3 : bigraph s3 i3 s2 i2),
  bigraph_equality ((b1 <<o>> b2) <<o>> b3) (b1 <<o>> (b2 <<o>> b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 <<o>> b2) <<o>> b3) (b1 <<o>> (b2 <<o>> b3))
          bijection_id
          bijection_id
          bijection_id
          bijection_id
          bij_sum_assoc
          bij_sum_assoc
          (fun n12_3 => bij_rew (P := fin) (arity_juxt_assoc b1 b2 b3 n12_3))
        ).
  + apply functional_extensionality.
    destruct x as [n1 | [n2 | n3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1' | [n2' | n3']] | s123]; simpl; unfold funcomp; simpl.
    - destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. unfold rearrange. destruct get_parent. reflexivity. unfold extract1. destruct get_parent; reflexivity.
    - unfold rearrange; unfold extract1; simpl. destruct get_parent. reflexivity. unfold rearrange. destruct get_parent. reflexivity. unfold extract1. destruct get_parent; reflexivity. 
  + apply functional_extensionality.
    destruct x as [i3' | p123]; simpl; unfold funcomp; simpl. 
    - unfold parallel. unfold switch_link. simpl. unfold rearrange.
     unfold extract1. simpl. destruct get_link.
     * destruct get_link.
     ** destruct get_link; reflexivity.
     ** reflexivity.
     * reflexivity.
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link. 
        destruct get_link. 
        reflexivity.
        reflexivity.
        reflexivity.
      * unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link.
        unfold id.
        unfold sequence.
        unfold rearrange.
        unfold extract1. 
        destruct get_link. 
        destruct get_link. 
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
  Qed.

Definition arity_comp_congruence_forward {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 s1 i1) (b4 : bigraph s4 i4 s2 i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (b1 <<o>> b3) n13))) -> (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_comp_congruence_backward {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 s1 i1) (b4 : bigraph s4 i4 s2 i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))) -> (fin (Arity (get_control (b1 <<o>> b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_comp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 s1 i1) (b4 : bigraph s4 i4 s2 i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))),
  bijection (fin (Arity (get_control (b1 <<o>> b3) n13))) (fin (Arity (get_control (b2 <<o>> b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ (arity_comp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) (arity_comp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
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

Theorem bigraph_comp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2) 
  (b3 : bigraph s3 i3 s1 i1) 
  (b4 : bigraph s4 i4 s2 i2),
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> bigraph_equality (b1 <<o>> b3) (b2 <<o>> b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq 
          s3 i3 r1 o1
          s4 i4 r2 o2
          (b1 <<o>> b3)
          (b2 <<o>> b4)
          (bij_s34)
          (bij_i34)
          (bij_r12)
          (bij_o12)
          (bij_n12 <+> bij_n34)
          (bij_e12 <+> bij_e34)
          (arity_juxt_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
        ).
  + apply functional_extensionality.
    destruct x as [n2' | n4']; simpl.
    - rewrite <- big_control_eq12.
      reflexivity.
    - rewrite <- big_control_eq34.
      reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2' | n4'] | s4']; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold parallel; simpl; auto.
    - rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      simpl.
      unfold funcomp.
      simpl.
      destruct get_parent.
      * reflexivity.
      * simpl.
        rewrite <- big_parent_eq12.
        simpl.
        unfold funcomp.
        simpl.
        unfold parallel.
        simpl.
        destruct (get_parent b1 (inr t)) eqn:Et.
      ** destruct (get_parent b1
      (inr ((bij_s12 ⁻¹) (bij_r34 t)))) eqn:Et0. Admitted. (*WEIRD*)

End CompositionBigraphs.


Theorem arity_comp_juxt_dist : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2) 
  (b3 : bigraph s3 i3 s1 i1) 
  (b4 : bigraph s4 i4 s2 i2) (n12_34:type (get_node (b1 || b2 <<o>> (b3 || b4)))),
  Arity (get_control
    ((b1 || b2) <<o>> (b3 || b4)) n12_34) =
  Arity (get_control 
    ((b1 <<o>> b3) || (b2 <<o>> b4)) (bij_sum_rearrange n12_34)) .
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.

Theorem bigraph_comp_juxt_dist : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2) 
  (b3 : bigraph s3 i3 s1 i1) 
  (b4 : bigraph s4 i4 s2 i2),
  bigraph_equality 
    ((b1 || b2) <<o>> (b3 || b4)) 
    ((b1 <<o>> b3) || (b2 <<o>> b4)).
  Proof.
  intros.
  apply (BigEq
    _ _ _ _
    _ _ _ _ 
    ((b1 || b2) <<o>> (b3 || b4)) 
    ((b1 <<o>> b3) || (b2 <<o>> b4))
    bijection_id (*s3 + s4*)
    bijection_id (*i3 + i4*)
    bijection_id (*r1 + r2*)
    bijection_id (*o1 + o2*)
    bij_sum_rearrange(* n1 + n2 + n3 + n4*)
    bij_sum_rearrange (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (P := fin) (arity_comp_juxt_dist b1 b2 b3 b4 n12_34)) (* Port *)
  ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|[s3'|s4']]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold rearrange_sum; unfold sum_shuffle; unfold parallel.
    - destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i3'|i4']|p]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold rearrange_sum; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    - destruct get_link. simpl. destruct get_link; reflexivity. reflexivity.
    - destruct get_link. simpl. destruct get_link; reflexivity. reflexivity.
    - destruct p as ([[v1 | v2] | [v3 | v4]], (i1234, Hvi1234)); unfold bij_join_port_backward; simpl.
    * unfold bij_rew_forward, eq_rect_r.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; reflexivity.
    * unfold bij_rew_forward, eq_rect_r.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link. simpl. destruct get_link; reflexivity. reflexivity.
    * unfold bij_rew_forward, eq_rect_r.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link. simpl. reflexivity. unfold extract1. reflexivity.
    * unfold bij_rew_forward, eq_rect_r.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; unfold rearrange; unfold extract1; simpl. 
      destruct get_link; reflexivity. reflexivity.
  Qed.
    
End Bigraphs.