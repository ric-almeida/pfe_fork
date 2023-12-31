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
Require Import SignatureBig.
Require Import Names.
Require Import Coq.Lists.List.

Set Printing All.


Import ListNotations.

Locate Port.
(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs (s : Signature) (n : Names).
Include s.
Include n.
(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.
Record bigraph  (site: FinDecType) 
                (innername: NoDupList) 
                (root: FinDecType) 
                (outername: NoDupList) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    control : (type node) -> Kappa ;
    parent : (type node) + (type site) -> (type node) + (type root) ; 
    link : (NameSub innername) + Port control -> (NameSub outername) + (type edge); 
    ap : FiniteParent parent ;
  }.
End IntroBigraphs.

(** * Getters
  This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s r : FinDecType} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  node s i r o bg.
Definition get_edge {s r : FinDecType} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  edge s i r o bg.
Definition get_control {s r : FinDecType} {i o : NoDupList} (bg : bigraph s i r o) : type (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s r : FinDecType} {i o : NoDupList} (bg : bigraph s i r o) : (type (get_node bg)) + (type s) -> (type (get_node bg)) + (type r) :=
  @parent s i r o bg.
Definition get_link {s r : FinDecType} {i o : NoDupList} (bg : bigraph s i r o) : {inner:Name | In inner i} + Port (get_control bg) -> {outer:Name | In outer o} + type (get_edge bg) :=
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
Record bigraph_equality {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigEq
  {
    bij_s : bijection (type s1) (type s2) ;
    bij_i : forall name, In name i1 <-> In name i2 ; (*Permutation i1 i2*)
    bij_r : bijection (type r1) (type r2) ;
    bij_o : forall name, In name o1 <-> In name o2 ;
    bij_n : bijection (type (get_node b1)) (type (get_node b2)) ;
    bij_e : bijection (type (get_edge b1)) (type (get_edge b2)) ;
    bij_p : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n n1)))) ;
    big_control_eq : (bij_n -->> (@bij_id Kappa)) (get_control b1) = get_control b2 ;
    big_parent_eq  : ((bij_n <+> bij_s) -->> (bij_n <+> bij_r)) (get_parent b1) = get_parent b2 ;
    big_link_eq    : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link b1) = get_link b2
  }.

Lemma bigraph_equality_refl {s r : FinDecType} {i o : NoDupList} (b : bigraph s i r o) :
  bigraph_equality b b.
  Proof.
  eapply (BigEq _ _ _ _ _ _ _ _ _ _ bij_id _ bij_id _ bij_id bij_id (fun _ => bij_id)).
  + rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_sigT_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  Unshelve.
  - intros. tauto.
  - intros. tauto.
  Qed.

Lemma bigraph_equality_sym {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  bigraph_equality b1 b2
      -> bigraph_equality b2 b1.
  Proof.
  intro Heqb1b2.
  destruct Heqb1b2 as (bij_s, bij_i, bij_r, bij_o, bij_n, bij_e, bij_p, big_control_eq, big_parent_eq, big_link_eq).
  apply (BigEq _ _ _ _ _ _ _ _ b2 b1
          (bijection_inv bij_s)
          (adjunction_equiv bij_id bij_i)
          (bijection_inv bij_r)
          (adjunction_equiv (bij_id) bij_o)
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
  + 
    rewrite <- bij_inv_sigT.
    change (
      (<{ (bijection_inv bij_id) | adjunction_equiv bij_id bij_i }> <+>
      bijection_inv <{ bij_n & bij_p }> -->>
      <{ (bijection_inv bij_id) | adjunction_equiv bij_id bij_o }> <+> bijection_inv bij_e)
        (get_link b2) = get_link b1
    ). (* just rewriting bij_id as bij_inv bij_id, TODO : look for more elegant way?*)
    rewrite <- bij_inv_subset.
    rewrite <- bij_inv_subset.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    rewrite <- big_link_eq.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_inv_left_simpl.
    reflexivity.
  Qed.

(*TODO*) Lemma bigraph_equality_trans 
  {s1 r1 s2 r2 s3 r3 : FinDecType} {i1 o1 i2 o2 i3 o3: NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
    bigraph_equality b1 b2
      -> bigraph_equality b2 b3  
        -> bigraph_equality b1 b3.
  Proof.
  intros Heqb1b2 Heqb2b3.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb2b3 as (bij_s23, bij_i23, bij_r23, bij_o23, bij_n23, bij_e23, bij_p23, big_control_eq23, big_parent_eq23, big_link_eq23).
  eapply (BigEq _ _ _ _ _ _ _ _ b1 b3
          (bij_s23 <O> bij_s12)
          ((fun a => iff_trans (bij_i12 a) (bij_i23 (bij_id a))))
          (bij_r23 <O> bij_r12)
          (fun a => iff_trans (bij_o12 a) (bij_o23 (bij_id a)))
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
  + Fail change ((
    (<{ bij_id <O> bij_id | fun a : Name => iff_trans (bij_i12 a) (bij_i23 (bij_id a)) }> <+> 
    <{ bij_n23 <O> bij_n12 & fun n1 : type (get_node b1) => bij_p23 (bij_n12 n1) <O> bij_p12 n1 }>) -->>
    <{ bij_id <O> bij_id  | fun a : Name => iff_trans (bij_o12 a) (bij_o23 (bij_id a)) }> <+>
    bij_e23 <O> bij_e12
    ) (get_link b1) = get_link b3
    ). (* idk why I can't do that change, bij_id <O> bij_id = bij_id! cf bij_eq_comp_id in Bijections file*)
    change ((
    (<{ bij_id | fun a : Name => iff_trans (bij_i12 a) (bij_i23 (bij_id a)) }> <+> 
    <{ bij_n23 <O> bij_n12 & fun n1 : type (get_node b1) => bij_p23 (bij_n12 n1) <O> bij_p12 n1 }>) -->>
    <{ bij_id <O> bij_id  | fun a : Name => iff_trans (bij_o12 a) (bij_o23 (bij_id a)) }> <+>
    bij_e23 <O> bij_e12
    ) (get_link b1) = get_link b3
    ). (*but I can do the change on the second bij_id (the second innername basically) *)
    Fail rewrite <- (bij_subset_compose_compose bij_id bij_id bij_o12 bij_o23).
    Fail rewrite <- (bij_subset_compose_compose_id bij_i12 bij_i23).
    rewrite <- big_link_eq23.
    rewrite <- big_link_eq12.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_fun_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sigT_compose_compose.
    Fail rewrite <- (bij_subset_compose_compose bij_id bij_id bij_o12 bij_o23).
    Fail rewrite <- (bij_subset_compose_compose_id bij_i12 bij_i23).
    (* reflexivity. *)
  Abort.

Lemma bigraph_equality_dec {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  {bigraph_equality b1 b2} + {~ bigraph_equality b1 b2}.
  Proof. (* Need to have access to a more transparent definition of bigraph_equality *)
  Abort.

(** ** On the packed type 
  The issue with the previous relation is that a parametric relation asks for two 
  objects of the exact same Type and our equality is heterogeneous. The solution we 
  will implement is to create a "packed bigraph" Type that will hold the interfaces 
  inside of it. This is a WIP. *)
Record bigraph_packed : Type :=
  mkPacked
  {
  s: FinDecType;
  i: NoDupList;
  r: FinDecType;
  o: NoDupList;
  big : bigraph s i r o
  }.
Coercion packing {s i r o} (b : bigraph s i r o) := 
  (mkPacked s i r o b).
(* Coercion unpacking (b : bigraph_packed) : (bigraph (s b) (i b) (r b) (o b)) := 
  (big b). *)
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

(* TODO when bigraph_equality_trans done *) Lemma bigraph_packed_equality_trans (bp1 bp2 bp3 : bigraph_packed) : bigraph_packed_equality bp1 bp2 -> bigraph_packed_equality bp2 bp3 -> bigraph_packed_equality bp1 bp3.
  Proof.
  Fail apply bigraph_equality_trans. 
  Abort.

Record support_equivalent {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  SupEq
  {
    s_bij_s : bijection (type s1) (type s2) ;
    s_bij_i : forall name, In name i1 <-> In name i2 ; (* Permutation i1 i2 *)
    s_bij_r : bijection (type r1) (type r2) ;
    s_bij_o : forall name, In name o1 <-> In name o2 ;
  }.
(* TODO on support translation : Would need to prove 
i) ρ preserves controls, i.e. ctrl G ◦ ρV = ctrl F . 
It follows that ρ induces a bijection ρP : PF → PG on ports, defined by ρP ((v, i)) def =(ρV (v),i).
ii) ρ commutes with the structural maps as follows: prnt G ◦ (Idm U ρV )= I (dn U ρV ) ◦ prnt F link G ◦ (IdX U ρP )= I (dY U ρE) ◦ link F*)
End EquivalenceBigraphs.


Instance big_Equivalence: Equivalence bigraph_packed_equality.
constructor. exact @bigraph_packed_equality_refl. exact @bigraph_packed_equality_sym. Abort. 
(* exact @bigraph_packed_equality_trans. Defined. *)

(* TODO when bigraph_equality_trans done *)
(* Add Parametric Relation: (bigraph_packed) (bigraph_packed_equality)
  reflexivity proved by (bigraph_packed_equality_refl)
  symmetry proved by (bigraph_packed_equality_sym)
  transitivity proved by (bigraph_packed_equality_trans)
    as bigraph_packed_equality_rel. *)

Lemma bigraph_packed_equality_dec  
  (b1 : bigraph_packed) (b2 : bigraph_packed) :
  {bigraph_packed_equality b1 b2} + {~ bigraph_packed_equality b1 b2}.
  Proof. (* same problem, bigraph_packed_equality not transparent enough *)
  Fail decide equality. Abort.

(* Juxtaposition is a tensor product when the sets of names are disjoint 
  On this we can prove associativity, neutral elt, and distribution to composition (M1 M2 M3 in Milner's book p21) 
  But bascially i'ts just juxtaposition with added hypothesis*)
Definition bigraph_tensor_product {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList} 
  {dis_i : Disjoint i1 i2}
  {dis_o : Disjoint o1 o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    : bigraph (findec_sum s1 s2) (app_NoDupList i1 i2) (findec_sum r1 r2) (app_NoDupList o1 o2).
  Proof.
  apply (Big 
    (findec_sum s1 s2)
    (app_NoDupList i1 i2)
    (findec_sum r1 r2)
    (app_NoDupList o1 o2)
    (findec_sum (get_node b1) (get_node b2))
    (findec_sum (get_edge b1) (get_edge b2))
    (join (get_control b1) (get_control b2))
    (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle))
    ( ((bij_list_names o1 o2) <+> bij_id) <o>
      bij_sum_shuffle <o> (parallel (get_link b1) (get_link b2)) <o> (bijection_inv bij_sum_shuffle) <o> 
      (bijection_inv ((bij_list_names i1 i2) <+> (bij_join_port (get_control b1) (get_control b2)))))
    ).
  rewrite <- tensor_alt.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined. 

Notation "b1 ⊗ b2" := (bigraph_tensor_product b1 b2) (at level 50, left associativity).

(*juxtaposition, also called parallel product
  in the book, parallel product is defined from tensor product p33 with the sentence "is defined just as tensor product, except that its link map allows name-sharing"
  but I think we should probably do it the other way around *)
Definition bigraph_juxtaposition {s1 r1 s2 r2 : FinDecType} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    : bigraph (findec_sum s1 s2) (app_NoDupList i1 i2) (findec_sum r1 r2) (app_NoDupList o1 o2).
  Proof.
  apply (Big 
    (findec_sum s1 s2)
    (app_NoDupList i1 i2)
    (findec_sum r1 r2)
    (app_NoDupList o1 o2)
    (findec_sum (get_node b1) (get_node b2))
    (findec_sum (get_edge b1) (get_edge b2))
    (join (get_control b1) (get_control b2))
    (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle))
    ( ((bij_list_names o1 o2) <+> bij_id) <o>
      bij_sum_shuffle <o> (parallel (get_link b1) (get_link b2)) <o> (bijection_inv bij_sum_shuffle) <o> 
      (bijection_inv ((bij_list_names i1 i2) <+> (bij_join_port (get_control b1) (get_control b2)))))
    ).
  rewrite <- tensor_alt.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined.

Notation "b1 || b2" := (bigraph_juxtaposition b1 b2) (at level 50, left associativity).

Definition void_link (ip : NameSub EmptyNDL + Port void_univ_embedding) :
  NameSub EmptyNDL + type voidfd. 
  Proof.
  destruct ip as [i|p].
  - left. apply i.
  - right. apply (bij_port_void void_univ_embedding p).
  Qed. (*Qed not defined bc very unsure about the definition *)


Definition bigraph_empty : bigraph voidfd EmptyNDL voidfd EmptyNDL.
  Proof.
  refine (Big voidfd EmptyNDL voidfd EmptyNDL
            voidfd voidfd
            (@void_univ_embedding _)
            (choice void_univ_embedding void_univ_embedding)
            void_link _ 
            ).
  - intro n.
  destruct n.
  Defined.

Notation "∅" := bigraph_empty.

(** * Disjoint juxtaposition/ Tensor Product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
(* Section DisjointJuxtaposition.
Lemma arity_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
        Arity (get_control (∅ ⊗ b) n) = Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.
  
Theorem bigraph_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (∅ || b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ || b) b
          bij_void_sum_neutral
          (left_empty i)
          bij_void_sum_neutral
          (left_empty o)
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
      simpl. (* TODO INTERESTING PART when bij done *)
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
End DisjointJuxtaposition. *)

(** * Disjoint juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Section Juxtaposition.
Lemma arity_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
        Arity (get_control (∅ || b) n) = Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (∅ || b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ || b) b
          bij_void_sum_neutral
          (left_empty i)
          bij_void_sum_neutral
          (left_empty o)
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
      simpl. (* TODO INTERESTING PART when bij done *) Admitted.
      (* destruct get_link; reflexivity.
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
  Qed. *)

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
          in_app_merge'_comu
          bij_sum_comm
          in_app_merge'_comu
          bij_sum_comm
          bij_sum_comm
          (fun n12 => bij_rew (P := fin) (arity_juxt_comm b1 b2 n12))
        ).
  + apply functional_extensionality.
    destruct x as [k2 | k1]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2 | n1] | [s2' | s1']]; simpl; unfold funcomp; simpl; destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [i21 | (v1, (k1, Hvk1))]; simpl; unfold funcomp; simpl.
    - (*TODO destruct i*) Admitted. 
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
          in_app_merge'_transi
          bij_sum_assoc
          in_app_merge'_transi
          bij_sum_assoc
          bij_sum_assoc
          (fun n12_3 => bij_rew (P := fin) (arity_juxt_assoc b1 b2 b3 n12_3))
        ).
  + apply functional_extensionality.
    destruct x as [k1 | [k2 | k3]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n1 | [n2 | n3]] | [s1' | [s2' | s3']]]; simpl; unfold funcomp; simpl; destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i] | p123]; simpl; unfold funcomp; simpl.
    - (* TODO destruct i *) Admitted.
     (* destruct get_link; reflexivity.
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
  Qed. *)

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
   Fail apply (BigEq _ _ _ _ _ _ _ _ (b1 || b3) (b2 || b4)
          (bij_s12 <+> bij_s34)
          (* expected to have type
 "forall name : Name,
  In name (app_NoDupList i1 i3) <->
  In name (app_NoDupList i2 i4)" *)
          (bij_r12 <+> bij_r34)
          (bij_o12 <+> bij_o34)
          (bij_n12 <+> bij_n34)
          (bij_e12 <+> bij_e34)
          (arity_juxt_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
        ). Admitted.
  (* + apply functional_extensionality.
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
  Qed. *)

Definition bigraph_packed_juxtaposition (b1 b2 : bigraph_packed) := 
  packing ((big b1) || (big b2)).
End Juxtaposition.

Add Parametric Morphism : bigraph_packed_juxtaposition with
 signature bigraph_packed_equality ==> 
 bigraph_packed_equality ==> 
 bigraph_packed_equality as juxtaposition_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
  apply bigraph_juxt_congruence.
  assumption.
  Qed.

Theorem bigraph_packed_juxt_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_juxtaposition ∅ b) b.
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

Lemma bigraph_juxt_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_juxtaposition b ∅) b.
  Proof.
  intros. Admitted.
  (* rewrite bigraph_packed_juxt_comm.
  rewrite bigraph_packed_juxt_left_neutral.
  reflexivity.
  Qed. *)

Definition bigraph_composition {s1 r1 s2 : FinDecType} {i1 o1 i2 : NoDupList}
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
          (backward (@bij_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))).
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
          voidfd 
          voidfd
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

Definition reflnames {r} : forall name : Name,
In name r <-> In name r.
reflexivity. Defined.
Print reflnames.

Theorem bigraph_comp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_identity <<o>> b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (bigraph_identity <<o>> b) b
          bij_id (*s*)
          (fun (name : Name) => reflexivity (In name i)) (*i*)
          bij_id (*r*)
          (fun (name : Name) => reflexivity (In name o)) (*o*)
          bij_void_sum_neutral (*n*)
          bij_void_sum_neutral (*e*)
          (fun n => bij_rew (P := fin) (arity_comp_left_neutral b n)) (*p*)
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
    destruct x as [name | (v1, (k1, Hvk1))]; simpl.
    - unfold reflexivity. unfold iff_Reflexive.  unfold id. simpl. 
    unfold bij_subset_forward, bij_subset_backward. simpl. unfold id. simpl. 
    unfold funcomp. simpl. unfold rearrange, switch_link, parallel.
      simpl. 
      destruct name as [name pf].
      destruct (iff_refl (In name i)). simpl.
      destruct get_link eqn:E.
      * destruct s0 as [outer pf2]. 
      simpl. 
      destruct iff_refl. destruct conj. simpl. admit. * admit. 
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link.
      * admit.
      * reflexivity.
  Admitted.

Lemma arity_comp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (b <<o>> bigraph_identity) n) =
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Lemma example_goal {l1} {B} (v1 : NameSub l1) (v2 : NameSub l1) :
  @inl (NameSub l1) B v1 = inl v2 -> v1 = v2.
  Proof.
    intros H.
    inversion H.
    reflexivity.
  Qed.

Theorem bigraph_comp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (b <<o>> (bigraph_identity)) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b <<o>> bigraph_identity) b
          bij_id
          (fun (name : Name) => reflexivity (In name i))
          bij_id
          (fun (name : Name) => reflexivity (In name o))
          bij_void_sum_neutral_r
          bij_void_sum_neutral_r(*probably not that anymore*)
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
    destruct x as [(name,pf) | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      destruct get_link. * destruct s0. admit. * admit.
    - unfold parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
    (*
        erewrite eq_rect_pi.
        erewrite (eq_rect_pi (x := v1)).
    *)
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link. * destruct s0. unfold id.
      Admitted.


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
  Fail apply (BigEq _ _ _ _ _ _ _ _ ((b1 <<o>> b2) <<o>> b3) (b1 <<o>> (b2 <<o>> b3))
          bij_id
          (fun (name : Name) => reflexivity (In name i3))
          bij_id
          (fun (name : Name) => reflexivity (In name i3))
          bij_sum_assoc
          bij_sum_assoc
          (fun n12_3 => bij_rew (P := fin) (arity_juxt_assoc b1 b2 b3 n12_3))
        ). (*TODO why does it not work?*) Admitted.
  (* + apply functional_extensionality.
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
  Qed. *)

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

Definition bij_or_eq (s1:Type) (s2:Type) (H: s1 = s2): bijection s1 s2.
  rewrite H.
  exact bij_id. Defined.

Theorem bigraph_comp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2) 
  (b3 : bigraph s3 i3 s1 i1) 
  (b4 : bigraph s4 i4 s2 i2)
  (be12 : bigraph_equality b1 b2)
  (be34 : bigraph_equality b3 b4), 
  bigraph_equality (b1 <<o>> b3) (b2 <<o>> b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34_s12, bij_o34_i12, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq 
          s3 r1 
          s4 r2 
          i3 o1 i4 o2
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
      unfold parallel.
      destruct (get_parent b3 (inl ((bij_n34 ⁻¹) n4'))) eqn:RE.
      * reflexivity.
      * rewrite <- big_parent_eq12.
        simpl.
        unfold funcomp.
        simpl.
        unfold parallel. Abort. (*TODO*) 
        (*Missing a hypothesis that says bij_s12 = bij_r34_s12 in the equalities *)

Definition bigraph_packed_composition {s1 i1 r1 o1 s2 i2} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) : bigraph_packed :=
  packing ((b1) <<o>> (b2)).

Definition bigraph_packed_composition' (*{s1 i1 r1 o1 s2 i2 : FinDecType} *)
  (b1 : bigraph_packed) (b2 : bigraph_packed) : bigraph_packed. Abort.

Theorem bigraph_packed_comp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_composition bigraph_identity b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_left_neutral.
  Qed. 

(* Theorem bigraph_packed_comp_assoc : forall {s1 i1 r1 o1 s2 i2 s3 i3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) (b3 : bigraph s3 i3 s2 i2),
  bigraph_packed_equality 
    (bigraph_packed_composition (bigraph_packed_composition b1 b2) b3) 
    (bigraph_packed_composition b1 (bigraph_packed_composition b2 b3)).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_juxtaposition.
  intros.
  apply bigraph_comp_assoc.
  Qed.  *)

Lemma bigraph_packed_comp_right_neutral : forall {s i r o} (b : bigraph s i r o), bigraph_packed_equality (bigraph_packed_composition b bigraph_identity) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_right_neutral.
  Qed. 

End CompositionBigraphs.
(* Add Parametric Morphism : bigraph_packed_composition with
 signature bigraph_packed_equality ==> 
 bigraph_packed_equality ==> 
 bigraph_packed_equality as composition_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
  apply bigraph_comp_congruence.
  assumption.
  Qed.  *)

Theorem arity_comp_juxt_dist : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 s4 i4} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2) 
  (b3 : bigraph s3 i3 s1 i1) 
  (b4 : bigraph s4 i4 s2 i2) (n12_34:type (get_node (b1 || b2 <<o>> (b3 || b4)))),
  Arity (get_control
    ((b1 || b2) <<o>> (b3 || b4)) n12_34) =
  Arity (get_control 
    ((b1 <<o>> b3) || (b2 <<o>> b4)) (sum_shuffle n12_34)) .
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
    bij_id (*s3 + s4*)
    reflnames (*i3 + i4*)
    bij_id (*r1 + r2*)
    reflnames (*o1 + o2*)
    bij_sum_shuffle(* n1 + n2 + n3 + n4*)
    bij_sum_shuffle (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (P := fin) (arity_comp_juxt_dist b1 b2 b3 b4 n12_34)) (* Port *)
  ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|[s3'|s4']]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel.
    - destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
    - destruct get_parent. reflexivity. destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [i'|p]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    - (*TODO destruct i*) Admitted.
    (* destruct get_link. simpl. destruct get_link; reflexivity. reflexivity.
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
  Qed. *)
    
Section NestingBig.

Definition rm_void_parent {s1 r1 node0: FinDecType} 
  (p : type node0 + type (findec_sum voidfd s1) ->
    type node0 + type (findec_sum voidfd r1)) : 
    type node0 + type s1 -> type node0 + type r1.
  Proof. intros [n|s].
    - destruct (p (inl n)) eqn:Epn.
    + left. exact t.
    + right. destruct t. destruct t. exact t.
    - destruct (p (inr (inr s))) eqn:Epn.
    + left. exact t.
    + right. destruct t. destruct t. exact t. Defined.

Definition rm_void_sumtype {r1 : FinDecType} (x:type (findec_sum voidfd r1)) : type r1 := 
  match x with
    | inl t =>
        match t return (type r1) with
        end
    | inr t => t end.
  (* destruct x. destruct t. exact t. Defined. *)

Definition rm_void_sumtype' {r1 : FinDecType} (x:type (findec_sum voidfd r1)) : type r1.
  Proof.
  destruct x. destruct t. exact t. Defined.

Definition rm_void_pair {node root : FinDecType} (pns : type node + type (findec_sum voidfd root)):
  type node + type root :=
  match pns with 
  | inl n => inl n
  | inr (v_r) => inr (rm_void_sumtype' v_r) 
  end.


Definition rm_void_parent' {s1 r1 node0: FinDecType} 
  (p : type node0 + type (findec_sum voidfd s1) ->
    type node0 + type (findec_sum voidfd r1)) : 
    type node0 + type s1 ->
      type node0 + type r1 :=
  (fun ns => match ns with 
    | inl n => rm_void_pair (p (inl n))
    | inr s => rm_void_pair (p (inr (inr s)))
    end).   

Definition rm_void_link {i1 o1 node0 edge0: FinDecType} {control0 : (type node0) -> Kappa} 
  (l : type (findec_sum i1 voidfd) + Port control0 ->
    type (findec_sum i1 o1) + type edge0) : 
      type i1 + Port control0 ->
        type (findec_sum i1 o1) + type edge0 :=
  (fun ip => match ip with 
  | inl i => match l (inl (inl i)) with 
    | inl i1o1 => inl i1o1
    | inr e => inr e 
    end 
  | inr p => match l (inr p) with
    | inl i1o1 => inl i1o1
    | inr e => inr e 
  end end).   

Lemma acyclic_rm_void_parent {node s r: FinDecType} {n:type node}
  {p: type node + type (findec_sum voidfd s) ->
  type node + type (findec_sum voidfd r)} :
  Acc (fun n' n : type node => p (inl n) = inl n') n
  -> Acc
  (fun n' n0 : type node => rm_void_parent' p (inl n0) = inl n') n.
  Proof. 
    intros H.
    unfold rm_void_parent'.
    unfold rm_void_pair.
    unfold rm_void_sumtype'. simpl.

    eapply Acc_inv in H.
    destruct H as [H_acc _].
    - admit.
    - admit.
  Admitted.

Definition rm_void_finDecSum {s1 i1 o1 r1} 
  (b : bigraph (findec_sum voidfd s1) (app_NoDupList i1 EmptyNDL) (findec_sum voidfd r1) (app_NoDupList i1 o1)) : 
  bigraph s1 i1 r1 (app_NoDupList i1 o1).
  Proof. 
  destruct b. Admitted.
  (* apply 
    (Big
      s1 i1 r1 (app_NoDupList i1 o1)
      node0
      edge0
      control0
      (rm_void_parent' parent0)
      (rm_void_link link0)
    ).
    unfold FiniteParent in *.
    intros n.
    specialize (ap0 n).
    apply acyclic_rm_void_parent.
    apply ap0.
    Qed. *)


Definition nest {s1 i1 r1 o1 i2} (* TODO check definition*)
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph voidfd i2 s1 i1) :=
  (rm_void_finDecSum ((@bigraph_identity voidfd i1) || b1)) <<o>> b2.

Definition nest' {I m X n Y} (* TODO check definition*)
  (F : bigraph voidfd I m X) (G : bigraph m EmptyNDL n Y) 
  : bigraph voidfd I n (app_NoDupList X Y) :=
  (rm_void_finDecSum ((@bigraph_identity voidfd X) || G)) <<o>> F.

Example I : NoDupList. Admitted.
Example m : FinDecType. Admitted.
Example X : NoDupList. Admitted.
Example n : FinDecType. Admitted.
Example Y : NoDupList. Admitted.
Example F : bigraph voidfd I m X. Admitted.
Example G : bigraph m EmptyNDL n Y. Admitted.

Check (@bigraph_identity voidfd X) || G.
Check rm_void_finDecSum ((@bigraph_identity voidfd X) || G).
Check (rm_void_finDecSum ((@bigraph_identity voidfd X) || G)) <<o>> F.
Check nest' F G.

Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph voidfd i2 s1 i1. Admitted.

Check nest b1 b2.

End NestingBig.



Definition symmetry_arrow (I J:Type) : bijection (I + J) (J + I).
  Proof. 
  apply (bij_sum_comm). 
  Defined.

Lemma symmetry_S1 {I}: 
  forall i:I, symmetry_arrow I void (inl i) = inr i.
  Proof.
  intros i.
  auto.
  Qed.
  
Lemma symmetry_S2 {I J}: 
  forall ij, 
    ((symmetry_arrow J I) <o> (symmetry_arrow I J)) ij = ij.
  Proof.
  intros [i|j];
  unfold funcomp; auto.
  Qed.

Lemma symmetry_S3 {I0 J0 I1 J1}
  {f : bijection I0 I1}
  {g : bijection J0 J1}: 
  symmetry_arrow I1 J1 <o> (f <+> g) = 
    (g <+> f) <o> symmetry_arrow I0 J0.
  Proof.
  simpl. unfold funcomp.
  apply functional_extensionality.
  intros [xi0 | xj0]; unfold parallel; reflexivity.
  Qed. 
  
Lemma symmetry_S4 {I J K} :
  forall x,
  (symmetry_arrow (I+J) K) x =
    ((bij_sum_assoc) <O> 
    ((symmetry_arrow I K) <+> (@bij_id J)) <O> 
    ((bijection_inv bij_sum_assoc) <O> 
    ((@bij_id I) <+> (symmetry_arrow J K)) 
    <O> bij_sum_assoc)) x. 
  Proof.
  intros [[i | j] | k];
  simpl; unfold parallel, funcomp; reflexivity.
  Qed.


End Bigraphs.

