
Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".


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
Require Import Lia.


Import ListNotations.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs (s : Signature) (n : Names).
Include s.
Include n.
(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.
Record bigraph  (site: nat) 
                (innername: NoDupList) 
                (root: nat) 
                (outername: NoDupList) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    control : (type node) -> Kappa ;
    parent : (type node) + (fin site) -> (type node) + (fin root) ; 
    link : (NameSub innername) + (Port control) -> (NameSub outername) + (type edge); 
    ap : FiniteParent parent ;
  }.
End IntroBigraphs.

(** * Getters
  This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  node s i r o bg.
Definition get_edge {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  edge s i r o bg.
Definition get_control {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : type (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : (type (get_node bg)) + (fin s) -> (type (get_node bg)) + (fin r) :=
  @parent s i r o bg.
Definition get_link {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : {inner:Name | In inner i} + Port (get_control bg) -> {outer:Name | In outer o} + type (get_edge bg) :=
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
Record bigraph_equality {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigEq
  {
    bij_s : s1 = s2 ;
    bij_i : permutation i1 i2 ; (*Permutation i1 i2*)
    bij_r : r1 = r2 ;
    bij_o : permutation o1 o2 ;
    bij_n : bijection (type (get_node b1)) (type (get_node b2)) ;
    bij_e : bijection (type (get_edge b1)) (type (get_edge b2)) ;
    bij_p : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n n1)))) ;
    (* TODO Could simply be Arity (get_control b1 n1) = Arity (get_control b2 (bij_n n1))*)
    big_control_eq : (bij_n -->> (@bij_id Kappa)) (get_control b1) = get_control b2 ;
    big_parent_eq  : ((bij_n <+> (bij_rew (P := fin) bij_s)) -->> (bij_n <+> ((bij_rew (P := fin) bij_r)))) (get_parent b1) = get_parent b2 ;
    big_link_eq    : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link b1) = get_link b2
  }.

Lemma bigraph_equality_refl {s r : nat} {i o : NoDupList} (b : bigraph s i r o) :
  bigraph_equality b b.
  Proof.
  eapply (BigEq _ _ _ _ _ _ _ _ _ _ eq_refl _ eq_refl _ bij_id bij_id (fun _ => bij_id)).
  + rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_rew_id.
    rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
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
  - unfold permutation. intros. reflexivity.
  - unfold permutation. intros. reflexivity.
  Qed.

Lemma bigraph_equality_sym {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  bigraph_equality b1 b2
      -> bigraph_equality b2 b1.
  Proof.
  intro Heqb1b2.
  destruct Heqb1b2 as (bij_s, bij_i, bij_r, bij_o, bij_n, bij_e, bij_p, big_control_eq, big_parent_eq, big_link_eq).
  apply (BigEq _ _ _ _ _ _ _ _ b2 b1
          (eq_sym bij_s)
          (adjunction_equiv bij_id bij_i)
          (eq_sym bij_r)
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
    rewrite <- bij_inv_rew.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_rew.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_inv_left_simpl.
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

Lemma bigraph_equality_trans 
  {s1 r1 s2 r2 s3 r3 : nat} {i1 o1 i2 o2 i3 o3: NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
    bigraph_equality b1 b2
      -> bigraph_equality b2 b3  
        -> bigraph_equality b1 b3.
  Proof.
  intros Heqb1b2 Heqb2b3.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb2b3 as (bij_s23, bij_i23, bij_r23, bij_o23, bij_n23, bij_e23, bij_p23, big_control_eq23, big_parent_eq23, big_link_eq23).
  apply (BigEq _ _ _ _ _ _ _ _ b1 b3
          (eq_trans bij_s12 bij_s23)
          (fun name : Name => @iff_trans 
            (@In Name name (ndlist i1)) 
            (@In Name name (ndlist i2))
            (@In Name (@forward Name Name (@bij_id Name) name) (ndlist i3))
            (bij_i12 name) (bij_i23 (@forward Name Name (@bij_id Name) name))
          )
          (eq_trans bij_r12 bij_r23)
          (fun a => iff_trans (bij_o12 a) (bij_o23 (bij_id a)))
          (bij_n23 <O> bij_n12)
          (bij_e23 <O> bij_e12)
          (fun n1 => (bij_p23 (bij_n12 n1)) <O> (bij_p12 n1))).
  + rewrite <- big_control_eq23.
    rewrite <- big_control_eq12.
    reflexivity.
  + rewrite <- big_parent_eq23.
    rewrite <- big_parent_eq12.
    rewrite <- bij_rew_compose.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_rew_compose.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_fun_compose_compose.
    reflexivity.
  + rewrite <- (@bij_subset_compose_compose_id Name (fun name => In name i1) (fun name => In name i2) (fun name => In name i3) bij_i12 bij_i23). 
    rewrite <- (@bij_subset_compose_compose_id Name (fun name => In name o1) (fun name => In name o2) (fun name => In name o3) bij_o12 bij_o23). 
    rewrite <- big_link_eq23.
    rewrite <- big_link_eq12.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_fun_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sigT_compose_compose.
    reflexivity.
  Qed.

(* Lemma bigraph_equality_refl_permutation {s1 r1: nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1):
  permutation i1 i2 -> permutation o1 o2 -> bigraph_equality b1 b2. *)

Lemma bigraph_equality_dec {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  {bigraph_equality b1 b2} + {~ bigraph_equality b1 b2}.
  Proof. 
    (* Need to have access to a more transparent definition of bigraph_equality *)
  Abort.

(** ** On the packed type 
  The issue with the previous relation is that a parametric relation asks for two 
  objects of the exact same Type and our equality is heterogeneous. The solution we 
  will implement is to create a "packed bigraph" Type that will hold the interfaces 
  inside of it. This is a WIP. *)
Record bigraph_packed : Type :=
  mkPacked
  {
  s: nat;
  i: NoDupList;
  r: nat;
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

Lemma bigraph_packed_equality_trans (bp1 bp2 bp3 : bigraph_packed) : bigraph_packed_equality bp1 bp2 -> bigraph_packed_equality bp2 bp3 -> bigraph_packed_equality bp1 bp3.
  Proof.
  apply bigraph_equality_trans.
  Qed. 

(* Record support_equivalent {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  SupEq
  {
    s_bij_s : bijection (type s1) (type s2) ;
    s_bij_i : forall name, In name i1 <-> In name i2 ; (* Permutation i1 i2 *)
    s_bij_r : bijection (type r1) (type r2) ;
    s_bij_o : forall name, In name o1 <-> In name o2 ;
  }. *)
(* TODO on support translation : Would need to prove 
i) ρ preserves controls, i.e. ctrl G ◦ ρV = ctrl F . 
It follows that ρ induces a bijection ρP : PF → PG on ports, defined by ρP ((v, i)) def =(ρV (v),i).
ii) ρ commutes with the structural maps as follows: prnt G ◦ (Idm U ρV )= I (dn U ρV ) ◦ prnt F link G ◦ (IdX U ρP )= I (dY U ρE) ◦ link F*)
End EquivalenceBigraphs.


#[export] Instance big_Equivalence: Equivalence bigraph_packed_equality.
constructor. exact @bigraph_packed_equality_refl. exact @bigraph_packed_equality_sym. exact @bigraph_packed_equality_trans. Defined. 
(* exact @bigraph_packed_equality_trans. Defined. *)

Add Parametric Relation: (bigraph_packed) (bigraph_packed_equality)
  reflexivity proved by (bigraph_packed_equality_refl)
  symmetry proved by (bigraph_packed_equality_sym)
  transitivity proved by (bigraph_packed_equality_trans)
    as bigraph_packed_equality_rel.

Lemma bigraph_packed_equality_dec  
  (b1 : bigraph_packed) (b2 : bigraph_packed) :
  {bigraph_packed_equality b1 b2} + {~ bigraph_packed_equality b1 b2}.
  Proof. (* same problem, bigraph_packed_equality not transparent enough *)
  Fail decide equality. Abort.

Notation "l1 # l2" := (Disjoint l1 l2) (at level 50, left associativity).
(* Juxtaposition is a tensor product when the sets of nodes, edges, innernames, outernames are disjoint 
  nodes & edges are automatically disjoint bc + is a disjoint sum
  On this we can prove associativity, neutral elt, and distribution to composition (M1 M2 M3 in Milner's book p21) 
  But bascially i'ts just juxtaposition with added hypothesis*)
Definition bigraph_tensor_product {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {dis_i : i1 # i2}
  {dis_o : o1 # o2}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    : bigraph (s1 + s2) (app_merge_NoDupList i1 i2) (r1 + r2) (app_merge_NoDupList o1 o2).
  Proof. 
  apply (Big 
    (s1 + s2)
    (app_merge_NoDupList i1 i2) (*app_merge'_id says it's eq to i1 ++ i2*)
    (r1 + r2)
    (app_merge_NoDupList o1 o2)
    (findec_sum (get_node b1) (get_node b2))
    (findec_sum (get_edge b1) (get_edge b2))
    (join (get_control b1) (get_control b2))
    ((bij_id <+> bijection_inv bij_fin_sum) <o>
      (bij_sum_shuffle <o> (parallel (get_parent b1) (get_parent b2)) <o> (bijection_inv bij_sum_shuffle)) <o> 
      (bij_id <+> bij_fin_sum))
    ( ((@bij_list_names o1 o2 dis_o) <+> bij_id) <o>
      bij_sum_shuffle <o> (parallel (get_link b1) (get_link b2)) <o> (bijection_inv bij_sum_shuffle) <o> 
      (bijection_inv ((@bij_list_names i1 i2 dis_i) <+> (bij_join_port (get_control b1) (get_control b2)))))
    ).
  rewrite <- tensor_alt.
  apply finite_parent_inout.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined. 

Notation "b1 ⊗ b2" := (bigraph_tensor_product b1 b2) (at level 50, left associativity).

Remark void_disjoint_all_list_left : forall l:NoDupList, EmptyNDL # l.
  Proof.
    intros. unfold Disjoint. intros. unfold EmptyNDL. auto. 
  Qed. 

Remark void_disjoint_all_list_right : forall l:NoDupList, l # EmptyNDL.
  Proof.
    intros. unfold Disjoint. intros. unfold EmptyNDL. auto. 
  Qed. 

(*juxtaposition, also called parallel product
  in the book, parallel product is defined from tensor product p33 with the sentence "is defined just as tensor product, except that its link map allows name-sharing"
  but I think we should probably do it the other way around *)
Definition link_juxt {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
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

Definition bigraph_juxtaposition {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
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
    (link_juxt b1 b2) _
    ). 
  - rewrite <- tensor_alt.
  apply finite_parent_inout.
  apply finite_parent_tensor.
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined. 

Notation "b1 || b2" := (bigraph_juxtaposition b1 b2) (at level 50, left associativity).

Theorem innername_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n:Name, forall Hn: In n i, forall Hn':In n i,
  get_link b (inl (exist _ n Hn)) = get_link b (inl (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.
  
Theorem tp_eq_pp {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
  {dis_i : i1 # i2} {dis_o : o1 # o2}:
  bigraph_equality 
    (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) 
    (b1 || b2).
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

Definition bigraph_empty : bigraph 0 EmptyNDL 0 EmptyNDL.
  Proof.
  eapply (Big 0 EmptyNDL 0 EmptyNDL
            voidfd voidfd
            (@void_univ_embedding _)
            (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero))
            _ 
            ).
  - intro n.
  destruct n.
  Unshelve.
  intros. destruct X.
  + left. apply n.
  + destruct p. right. apply x.
  Defined. (*TODO unsure of the definition of link def 2.7*)

Notation "∅" := bigraph_empty.


(** * Disjoint juxtaposition/ Tensor Product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove existence of a unit, commutativity, associativity and congruence. *)
Section DisjointJuxtaposition.
Lemma arity_tp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_tensor_product (dis_i := void_disjoint_all_list_left i) (dis_o := void_disjoint_all_list_left o) ∅ b) n) = 
  Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_tp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_tensor_product (dis_i := void_disjoint_all_list_left i) (dis_o := void_disjoint_all_list_left o) ∅ b) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (∅ ⊗ b) b
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
    - unfold funcomp.
      simpl.
      destruct get_parent; try reflexivity.
      destruct f; simpl.
      f_equal.
      apply subset_eq_compat; reflexivity.
    - unfold funcomp, parallel.
      simpl.
      destruct s1; simpl.
      destruct PeanoNat.Nat.ltb_spec0; simpl.
      * elim (PeanoNat.Nat.nlt_0_r _ l0).
      * erewrite (subset_eq_compat _ _ (x - 0) x _ _ (PeanoNat.Nat.sub_0_r x)).
        instantiate (1 := l).
        destruct get_parent; try reflexivity.
        destruct f; simpl.
        f_equal.
        apply subset_eq_compat.
        reflexivity.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. 
      destruct i1 as [iname1 Hiname1].
      rewrite <- (innername_proof_irrelevant b iname1 Hiname1).
      simpl. destruct get_link; try reflexivity.
      f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp, id.
      simpl.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Qed.

Lemma arity_tp_right_neutral : forall {s i r o} (b : bigraph s i r o) n, 
  Arity (get_control (bigraph_tensor_product (dis_i := void_disjoint_all_list_right i) (dis_o := void_disjoint_all_list_right o) b ∅) n) = 
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o b n.
  destruct n as [ n | v].
  + reflexivity.
  + destruct v.
  Qed.
  
Theorem bigraph_tp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (bigraph_tensor_product (dis_i := void_disjoint_all_list_right i) (dis_o := void_disjoint_all_list_right o) b ∅) b.
  Proof.
  intros s i r o b.
  apply (BigEq _ _ _ _ _ _ _ _ (b ⊗ ∅) b
    (PeanoNat.Nat.add_0_r _)
    (right_empty i)
    (PeanoNat.Nat.add_0_r _)
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
      destruct f; simpl.
      f_equal.
      unfold bij_rew_forward.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + 0) r _ x _).
      apply subset_eq_compat; reflexivity.
    - unfold funcomp, parallel.
      simpl.
      destruct s1; simpl.
      unfold bij_rew_forward, inj_fin_add.
      rewrite (@eq_rect_exist nat nat (fun n x => x < n) s (s + 0) _ x _).
      destruct PeanoNat.Nat.ltb_spec0; simpl.
      * rewrite (proof_irrelevance _ l0 l).
        destruct get_parent; simpl; try reflexivity.
        destruct f; simpl.
        f_equal.
        rewrite (@eq_rect_exist nat nat (fun n x => x < n) (r + 0) r _ x0 _).
        apply subset_eq_compat.
        reflexivity.
      * contradiction.
  + apply functional_extensionality.
    destruct x as [i1 | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
      simpl. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. 
      destruct i1 as [iname1 Hiname1].
      destruct (in_dec EqDecN iname1 i).
      * rewrite <- (innername_proof_irrelevant b iname1 Hiname1).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * exfalso. apply n. apply Hiname1.
    - unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold bij_rew_forward, eq_rect_r, funcomp, id.
      simpl.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      destruct get_link; try reflexivity. 
      apply f_equal. destruct s0. apply subset_eq_compat.
      reflexivity.
  Qed.

Lemma arity_tp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} 
 {dis_i : i1 # i2} {dis_o : o1 # o2} 
 (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) n12,
  Arity (get_control (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) n12) = Arity (get_control (bigraph_tensor_product (dis_i:= rev_disjoint dis_i) (dis_o := rev_disjoint dis_o) b2 b1) (bij_sum_comm n12)).
  Proof.
  intros until n12.
  destruct n12.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_tp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} 
  {dis_i : i1 # i2} {dis_o : o1 # o2}   
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  bigraph_equality 
    (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) b1 b2) 
    (bigraph_tensor_product (dis_i:= rev_disjoint dis_i) (dis_o := rev_disjoint dis_o) b2 b1).
  Proof.
  intros.
Abort. (*We no longer have commutativity?*)
  (* apply (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b2) (b2 ⊗ b1)
          (@eq_sym _ _ _ _)
          in_app_merge'_comu
          (@eq_sym _ _ _ _)
          in_app_merge'_comu
          bij_sum_comm
          bij_sum_comm
          (fun n12 => bij_rew (P := fin) (arity_tp_comm b1 b2 n12))
        ).
  + apply functional_extensionality.
    destruct x as [k2 | k1]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[n2 | n1] | [s2' | s1']]; simpl; unfold funcomp; simpl; destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [inner1 | p12]; simpl; unfold funcomp; simpl.
    - unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id. 
      destruct inner1 as [iname Hiname].
      destruct (in_dec EqDecN iname i1).
      * destruct (in_dec EqDecN iname i2).
      ** exfalso. apply (not_in_both i1 i2 iname); assumption.
      ** 
      set (Hn' := 
        match
          in_app_or_m_nod_dup i2 i1 iname
            (match
              i2 as n0
              return
                ((In iname n0 ->
                  ~ In iname i1) ->
                  In iname
                    (app_merge' n0 i1) ->
                  ~ In iname n0 -> NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : In iname ndlist0 ->
                        ~ In iname i1)
                  (_ : In iname
                          (app_merge'
                          ndlist0 i1))
                  (_ : ~ In iname ndlist0)
                => nd0
            end (rev_disjoint dis_i iname)
              Hiname n)
            (match
              i1 as n0
              return
                ((In iname i2 ->
                  ~ In iname n0) ->
                  In iname
                    (app_merge' i2 n0) ->
                  NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : In iname i2 ->
                        ~ In iname ndlist0)
                  (_ : In iname
                          (app_merge' i2
                          ndlist0)) => nd0
            end (rev_disjoint dis_i iname)
              Hiname) Hiname
        with
        | inl i3 =>
            False_ind (In iname i1) (n i3)
        | inr i3 => i3
        end).
      rewrite (innername_proof_irrelevant b1 iname i0 Hn').
      destruct get_link; try reflexivity. 
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** reflexivity.
      * destruct (in_dec EqDecN iname i2).
      **
      set (Hn' := 
        match
        in_app_or_m_nod_dup i1 i2 iname
          (match
            i1 as n0
            return
              ((In iname n0 -> ~ In iname i2) ->
                In iname (app_merge' n0 i2) ->
                ~ In iname n0 -> NoDup n0)
          with
          | {| ndlist := ndlist0; nd := nd0 |} =>
              fun
                (_ : In iname ndlist0 ->
                      ~ In iname i2)
                (_ : In iname
                        (app_merge' ndlist0 i2))
                (_ : ~ In iname ndlist0) => nd0
          end (dis_i iname)
            (match in_app_merge'_comu iname with
              | conj _ H0 => H0
              end
                (eq_ind_r
                  (fun b : Name =>
                    In b (app_merge' i2 i1)) Hiname
                  eq_refl)) n)
          (match
            i2 as n0
            return
              ((In iname i1 -> ~ In iname n0) ->
                In iname (app_merge' i1 n0) ->
                NoDup n0)
          with
          | {| ndlist := ndlist0; nd := nd0 |} =>
              fun
                (_ : In iname i1 ->
                      ~ In iname ndlist0)
                (_ : In iname
                        (app_merge' i1 ndlist0)) =>
              nd0
          end (dis_i iname)
            (match in_app_merge'_comu iname with
              | conj _ H0 => H0
              end
                (eq_ind_r
                  (fun b : Name =>
                    In b (app_merge' i2 i1)) Hiname
                  eq_refl)))
          (match in_app_merge'_comu iname with
          | conj _ H0 => H0
          end
            (eq_ind_r
                (fun b : Name =>
                In b (app_merge' i2 i1)) Hiname
                eq_refl))
        with
        | inl i3 => False_ind (In iname i2) (n i3)
        | inr i3 => i3
        end).
      rewrite (innername_proof_irrelevant b2 iname i0 Hn').
      destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** reflexivity.
      ** exfalso. apply in_app_iff in Hiname. destruct Hiname. apply n0. apply H. apply n. apply H.
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
        unfold bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id. 
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. simpl. reflexivity.
        ** reflexivity.
      * unfold bij_rew_forward.
        unfold eq_rect_r.
        (*
          erewrite eq_rect_pi.
          erewrite (eq_rect_pi (x := inl v2)).
        *)
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        unfold bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id. 
        destruct get_link; try reflexivity.
        ** apply f_equal. destruct s0. apply subset_eq_compat. simpl. reflexivity.
        ** reflexivity.
  Qed. *)

Lemma arity_tp_assoc : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  {dis_i12 : i1 # i2} {dis_i23 : i2 # i3} {dis_i13 : i1 # i3}
  {dis_o12 : o1 # o2} {dis_o23 : o2 # o3} {dis_o13 : o1 # o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) n12_3,
  Arity (get_control (bigraph_tensor_product (dis_i := dis_trans dis_i23 dis_i13) (dis_o := dis_trans dis_o23 dis_o13) (bigraph_tensor_product (dis_i:= dis_i12) (dis_o := dis_o12) b1 b2) b3) n12_3) 
  = 
  Arity (get_control (bigraph_tensor_product (dis_i := dis_trans_r dis_i12 dis_i13) (dis_o := dis_trans_r dis_o12 dis_o13) b1 (bigraph_tensor_product (dis_i:= dis_i23) (dis_o := dis_o23) b2 b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_tp_assoc : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} 
  {dis_i12 : i1 # i2} {dis_i23 : i2 # i3} {dis_i13 : i1 # i3}
  {dis_o12 : o1 # o2} {dis_o23 : o2 # o3} {dis_o13 : o1 # o3}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_equality
    (bigraph_tensor_product (dis_i := dis_trans dis_i23 dis_i13) (dis_o := dis_trans dis_o23 dis_o13) (bigraph_tensor_product (dis_i:= dis_i12) (dis_o := dis_o12) b1 b2) b3) 
    (bigraph_tensor_product (dis_i := dis_trans_r dis_i12 dis_i13) (dis_o := dis_trans_r dis_o12 dis_o13) b1 (bigraph_tensor_product (dis_i:= dis_i23) (dis_o := dis_o23) b2 b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 ⊗ b2) ⊗ b3) (b1 ⊗ (b2 ⊗ b3))
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    in_app_merge'_transi
    (eq_sym (PeanoNat.Nat.add_assoc _ _ _))
    in_app_merge'_transi
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (P := fin) (arity_tp_assoc b1 b2 b3 n12_3))
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
      destruct (in_dec EqDecN i123 (app_merge' i1 i2)).
      * destruct (in_dec EqDecN i123 i1).
      destruct get_link; try reflexivity.
      ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** destruct (in_dec EqDecN i123 i2).
      ***
      set (Hn' := match
          in_app_or_m_nod_dup i1 i2 i123
            (match
              i1 as n0
              return
                ((In i123 n0 -> ~ In i123 i2) ->
                  In i123 (app_merge' n0 i2) ->
                  ~ In i123 n0 -> NoDup n0)
            with
            | {|
                ndlist := ndlist0; nd := nd0
              |} =>
                fun
                  (_ : In i123 ndlist0 ->
                        ~ In i123 i2)
                  (_ : In i123
                        (app_merge' ndlist0
                        i2))
                  (_ : ~ In i123 ndlist0) =>
                nd0
            end (dis_i12 i123) i4 n)
            (match
              i2 as n0
              return
                ((In i123 i1 -> ~ In i123 n0) ->
                  In i123 (app_merge' i1 n0) ->
                  NoDup n0)
            with
            | {|
                ndlist := ndlist0; nd := nd0
              |} =>
                fun
                  (_ : In i123 i1 ->
                        ~ In i123 ndlist0)
                  (_ : In i123
                        (app_merge' i1
                        ndlist0)) => nd0
            end (dis_i12 i123) i4) i4
        with
        | inl i6 =>
            False_ind (In i123 i2) (n i6)
        | inr i6 => i6
        end).
      rewrite (innername_proof_irrelevant b2 i123 i5 Hn').      
      destruct get_link; try reflexivity.
      **** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply in_app_iff in i4. destruct i4. apply n. apply H. apply n0. apply H.
      * destruct (in_dec EqDecN i123 i1).
      ** exfalso. apply n. apply in_left_list. apply i4.
      ** destruct (in_dec EqDecN i123 i2).
      *** exfalso. apply n. apply in_right_list. apply i4.
      *** 
      set (Hn' :=
        match
        in_app_or_m_nod_dup (app_merge' i1 i2) i3 i123
        (NoDup_app_merge i1 i2 (nd i1) (nd i2))
        (match
        i3 as n2
        return
        ((In i123 (app_merge' i1 i2) -> ~ In i123 n2) ->
        In i123 (app_merge' (app_merge' i1 i2) n2) ->
        NoDup n2)
        with
        | {| ndlist := ndlist0; nd := nd0 |} =>
        fun
        (_ : In i123 (app_merge' i1 i2) ->
        ~ In i123 ndlist0)
        (_ : In i123
        (app_merge' (app_merge' i1 i2) ndlist0))
        => nd0
        end (dis_trans dis_i23 dis_i13 i123)
        (in_app_merge'_trans i123
        (eq_ind_r
        (fun b : Name =>
        In b (app_merge' i1 (app_merge' i2 i3)))
        i0 eq_refl)))
        (in_app_merge'_trans i123
        (eq_ind_r
        (fun b : Name =>
        In b (app_merge' i1 (app_merge' i2 i3))) i0
        eq_refl))
        with
        | inl i4 => False_ind (In i123 i3) (n i4)
        | inr i4 => i4
        end).       
      symmetry. rewrite <- (innername_proof_irrelevant b3 i123 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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
        ** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. (*TODO best example of tactic use*)
  Qed.

Definition arity_tp_congruence_forward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))) :
  (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))) -> (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_tp_congruence_backward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))) :
  (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))) -> (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_tp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 ⊗ b3))),
  bijection (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) n13))) (fin (Arity (get_control (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  intros until n13.
  apply (mkBijection _ _ (arity_tp_congruence_forward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13) (arity_tp_congruence_backward b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34 n13)).
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

Theorem bigraph_tp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  {dis_i13 : i1 # i3} {dis_o13 : o1 # o3}
  {dis_i24 : i2 # i4} {dis_o24 : o2 # o4}
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4),
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> 
    bigraph_equality 
      (bigraph_tensor_product (dis_i := dis_i13) (dis_o := dis_o13) b1 b3) 
      (bigraph_tensor_product (dis_i := dis_i24) (dis_o := dis_o24) b2 b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb3b4 as (bij_s34, bij_i34, bij_r34, bij_o34, bij_n34, bij_e34, bij_p34, big_control_eq34, big_parent_eq34, big_link_eq34).
  apply (BigEq _ _ _ _ _ _ _ _ (b1 ⊗ b3) (b2 ⊗ b4)
    (f_equal2_plus _ _ _ _ bij_s12 bij_s34)
    (app_merge'_cong bij_i12 bij_i34)
    (f_equal2_plus _ _ _ _ bij_r12 bij_r34)
    (app_merge'_cong bij_o12 bij_o34)
    (bij_n12 <+> bij_n34)
    (bij_e12 <+> bij_e34)
    (arity_tp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
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
    - rewrite <- big_link_eq12.
      simpl.
      unfold funcomp.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      destruct (in_dec EqDecN i24 i1).
      * (*link i1 = link i2 *) 
      destruct (in_dec EqDecN i24 i2).
      ** 
      set (Hn' := 
        match bij_i12 i24 with
        | conj _ H => H
        end (eq_ind_r (fun b : Name => In b i2) i6 eq_refl)).
      rewrite (innername_proof_irrelevant b1 i24 i5 Hn').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. apply bij_i12. apply i5.
      * (*link i2 = link i1 *)  
      destruct (in_dec EqDecN i24 i2).
      ** exfalso. apply n. apply bij_i12. apply i5.
      **  
      set (Hn' := 
          match
          in_app_or_m_nod_dup i2 i4 i24
            (match
              i2 as n1
              return
                ((In i24 n1 -> ~ In i24 i4) ->
                  In i24 (app_merge' n1 i4) -> ~ In i24 n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 ndlist0 -> ~ In i24 i4)
                  (_ : In i24 (app_merge' ndlist0 i4)) (_ : ~ In i24 ndlist0) => nd0
            end (dis_i24 i24) i0 n0)
            (match
              i4 as n1
              return
                ((In i24 i2 -> ~ In i24 n1) -> In i24 (app_merge' i2 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 i2 -> ~ In i24 ndlist0)
                  (_ : In i24 (app_merge' i2 ndlist0)) => nd0
            end (dis_i24 i24) i0) i0
        with
        | inl i5 => False_ind (In i24 i4) (n0 i5)
        | inr i5 => i5
        end).
      set (Hn := 
          match
          in_app_or_m_nod_dup i1 i3 i24
            (match
              i1 as n1
              return
                ((In i24 n1 -> ~ In i24 i3) ->
                  In i24 (app_merge' n1 i3) -> ~ In i24 n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 ndlist0 -> ~ In i24 i3)
                  (_ : In i24 (app_merge' ndlist0 i3)) 
                  (_ : ~ In i24 ndlist0) => nd0
            end (dis_i13 i24)
              (match app_merge'_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl))
              n)
            (match
              i3 as n1
              return
                ((In i24 i1 -> ~ In i24 n1) ->
                  In i24 (app_merge' i1 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In i24 i1 -> ~ In i24 ndlist0)
                  (_ : In i24 (app_merge' i1 ndlist0)) => nd0
            end (dis_i13 i24)
              (match app_merge'_cong bij_i12 bij_i34 i24 with
                | conj _ H => H
                end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl)))
            (match app_merge'_cong bij_i12 bij_i34 i24 with
            | conj _ H => H
            end (eq_ind_r (fun b : Name => In b (app_merge' i2 i4)) i0 eq_refl))
        with
        | inl i5 => False_ind (In i24 i3) (n i5)
        | inr i5 => i5
        end).
      simpl. simpl.
      rewrite <- big_link_eq34.
      simpl.
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      set (Hn'' := 
        match bij_i34 i24 with
        | conj _ H => H
        end (eq_ind_r (fun b : Name => In b i4) Hn' eq_refl
        )).
      rewrite (innername_proof_irrelevant b3 i24 Hn Hn'').
      destruct get_link; try reflexivity.
      *** apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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

Definition bigraph_packed_tp (b1 b2 : bigraph_packed) 
 (dis_i : (i b1) # (i b2)) (dis_o : (o b1) # (o b2)) := 
  packing (bigraph_tensor_product (dis_i:= dis_i) (dis_o := dis_o) (big b1) (big b2)).
End DisjointJuxtaposition. 

(** * Disjoint juxtaposition / Parallel product
  This section deals with the operation of disjoint juxtaposition. This is the act
  of putting two bigraphs with disjoint interfaces "next" to one another. 
  After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Section Juxtaposition.
Lemma arity_pp_left_neutral : forall {s i r o} (b : bigraph s i r o) n, 
        Arity (get_control (∅ || b) n) = Arity (get_control b (bij_void_sum_neutral n)).
  Proof.
  intros s i r o b n.
  destruct n as [ v | n].
  + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_equality (∅ || b) b.
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

Lemma arity_pp_comm : forall {s1 i1 r1 o1 s2 i2 r2 o2} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) n12,
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
Abort.
Lemma arity_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) n12_3,
  Arity (get_control ((b1 || b2) || b3) n12_3) = Arity (get_control (b1 || (b2 || b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_pp_assoc : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
  bigraph_equality ((b1 || b2) || b3) (b1 || (b2 || b3)).
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

Definition arity_pp_congruence_forward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
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

Definition arity_pp_congruence_backward 
  {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
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

Lemma arity_pp_congruence : 
  forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 || b3))),
  bijection (fin (Arity (get_control (b1 || b3) n13))) (fin (Arity (get_control (b2 || b4) ((bij_n12 <+> bij_n34) n13)))).
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

Theorem bigraph_pp_congruence : forall {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 s4 i4 r4 o4} (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) (b4 : bigraph s4 i4 r4 o4),
  bigraph_equality b1 b2 -> bigraph_equality b3 b4 -> 
    bigraph_equality (b1 || b3) (b2 || b4).
  Proof.
  intros until b4.
  intros Heqb1b2 Heqb3b4.
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

Definition bigraph_packed_pp (b1 b2 : bigraph_packed) := 
  packing ((big b1) || (big b2)).
End Juxtaposition.

Add Parametric Morphism : (*TODO Check w supervisors about that*)
 bigraph_packed_pp with
 signature bigraph_packed_equality ==> 
 bigraph_packed_equality ==> 
 bigraph_packed_equality as juxtaposition_morphism.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
  apply bigraph_pp_congruence.
  assumption.
  Qed.

Theorem bigraph_packed_pp_left_neutral : forall {s i r o} (b : bigraph s i r o), 
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

Lemma bigraph_pp_right_neutral : forall {s i r o} (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_pp b ∅) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  Fail apply bigraph_pp_right_neutral.
  Admitted.

Definition permut_list_forward (l1 l2 : list Name) (p : permutation l1 l2)
  (nl1 : {name:Name|In name l1}) : {name:Name|In name l2}.
  Proof.
    destruct nl1.
    exists x.
    unfold permutation in p. apply p in i0. apply i0.
  Defined.

Definition bij_permut_list (l1 l2 : list Name) (p : permutation l1 l2) :
  bijection {name:Name|In name l1} {name:Name|In name l2}.
  Proof.
    refine (mkBijection
    {name:Name|In name l1} {name:Name|In name l2}
    (permut_list_forward l1 l2 p)
    (permut_list_forward l2 l1 (symmetry p)) _ _
    ).
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    - apply functional_extensionality. intros nl2. unfold funcomp, permut_list_forward, symmetry, id.
    destruct nl2. apply subset_eq_compat. reflexivity.
    Unshelve. apply symmetric_permutation.
  Defined.

Definition bigraph_composition {s1 r1 s2 : nat} {i1o2 o2i1 o1 i2 : NoDupList}
  {p: permutation o2i1 i1o2}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 s1 o2i1) 
    : bigraph s2 i2 r1 o1.
  Proof. 
  set (sl2:= (bij_id <+> bij_permut_list  o2i1 i1o2 p) <o> (switch_link (get_link b2))). 
  set (sl1:= switch_link (get_link b1)). 
  apply (Big s2 i2 r1 o1
        (findec_sum (get_node b1) (get_node b2))
        (findec_sum (get_edge b1) (get_edge b2))
        (join (get_control b1) (get_control b2))
        ((get_parent b2) >> (get_parent b1))
        (switch_link (sl2 >> sl1) <o>
          (backward (@bij_id _ <+> (bij_join_port (get_control b1) (get_control b2)))))).
  apply (finite_parent_sequence).
  + exact (ap _ _ _ _ b1).
  + exact (ap _ _ _ _ b2).
  Defined.
  (* l :  i2 + (p1 + p2) -> o1 + (e1 + e2) *)
  (* l1 : i1o2 + p1 -> o1 + e1 *)
  (* l2 : i2 + p2 -> o2i1 + e2, o2i1 <=> i1o2 *)
  
Notation "b1 '<<o>>' b2" := (bigraph_composition b1 b2) (at level 50, left associativity).
Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.
Class PermutationNames (l1 l2 : list Name) := { disj : permutation l1 l2 }.
#[export] Instance permutN_refl (l : list Name) : PermutationNames l l.
  Proof.
  constructor.
  unfold permutation.
  intros n.
  reflexivity.
  Qed.

Lemma permut_refl {l:list Name} : permutation l l.
  Proof.
  constructor; auto.
  Qed.

(** * Composition
  This section deals with the operation of composition. This is the act
  of putting a bigraph inside another one. To do b1 <<o>> b2, the outerface 
  of b2 needs to be the innerface of b1. TODO/note: or just a bijection? 
  We prove left and right neutral for identity bigraph and associativity *)
Section CompositionBigraphs.
Definition bigraph_identity {s i i'} {p:permutation (ndlist i) (ndlist i')}: bigraph s i s i'. (*actually s i s (permutation i) *)
  Proof.
  apply (Big s i s i'
          voidfd (*node : ∅*)
          voidfd (*edge : ∅*)
          (@void_univ_embedding _) (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  - intros [inner | port]. (*link_|{names} : id*)
    + left. destruct inner. exists x. unfold permutation in p. apply p in i0. apply i0.
    + destruct port. destruct x.
  - intro n. (*acyclic parent*)
    destruct n.
  Defined.

Lemma arity_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')}
  (b : bigraph s i r o) n,  
  let b_id := bigraph_identity (s := r) (i := o') (i' := o'') (p:=p') in
  Arity (get_control (bigraph_composition (p := p) (bigraph_identity (p:=p')) b) n) =
  Arity (get_control b (bij_void_sum_neutral n)).
  (* b : s i r o, -> b_id : r (p o) r (p (p o)) *)
  Proof.
  intros s i r o o' o'' p p' b n b_id.
  destruct n as [ v | n].
    + destruct v.
  + reflexivity.
  Qed.

Theorem bigraph_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')} (b : bigraph s i r o), 
  bigraph_equality (bigraph_composition (p := p) (bigraph_identity (p := p')) b) b.
  Proof.
  intros s i r o o' o'' p p' b.
  refine (
    BigEq s r s r i o'' i o (bigraph_identity <<o>> b) b
      eq_refl (*s*)
      (fun (name : Name) => reflexivity (In name i)) (*i*)
      eq_refl (*r*)
      (fun (name : Name) => transitivity (symmetry p' name) (symmetry p name)) (*o*)
      bij_void_sum_neutral (*n*)
      bij_void_sum_neutral (*e*)
      (fun n => bij_rew (P := fin) (@arity_comp_left_neutral s i r o o' o'' p p' b n)) (*p*)
      _ _ _
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
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp.
    simpl. 
    unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
    simpl.
    unfold rearrange, switch_link, id. simpl.
    rewrite <- (innername_proof_irrelevant b name i0).
    destruct get_link; try reflexivity.
    * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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
      destruct get_link; try reflexivity.
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Unshelve. apply symmetric_permutation. apply symmetric_permutation.
  Qed.

Lemma arity_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o) n,  
  let b_id := bigraph_identity (s := s) (i := i') (i' := i'') (p:=p') in 
  Arity (get_control (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) n) =
  Arity (get_control b (bij_void_sum_neutral_r n)).
  Proof.
  intros s i r o i' i'' p p' b n b_id.
  destruct n as [n | v].
  + reflexivity.
  + destruct v.
  Qed.

Theorem bigraph_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o), 
  bigraph_equality (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) b.
  Proof.
  intros s i r o i' i'' p p' b.
  apply 
    (BigEq _ _ _ _ _ _ _ _ (b <<o>> bigraph_identity) b
      eq_refl
      (fun (name : Name) => transitivity (p' name) (p name))
      eq_refl
      (fun (name : Name) => reflexivity (In name o))
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
    destruct x as [[name] | (v1, (k1, Hvk1))]; simpl.
    - unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      unfold funcomp, bij_subset_forward, extract1, switch_link, parallel, id.
      simpl.
      rewrite <- (innername_proof_irrelevant b name i0).
      destruct get_link; try reflexivity. 
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
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
      destruct get_link; try reflexivity. 
      * apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
  Qed.


Lemma arity_comp_assoc : 
  forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2) n12_3,
  Arity (get_control (bigraph_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) n12_3) = 
  Arity (get_control (bigraph_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)) (bij_sum_assoc n12_3)).
  Proof.
  intros until n12_3.
  destruct n12_3 as [[n1 | n2] | n3].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

Theorem bigraph_comp_assoc : forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2),
  bigraph_equality 
  (bigraph_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) 
  (bigraph_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)).
  Proof.
  intros.
  apply (BigEq _ _ _ _ _ _ _ _ ((b1 <<o>> b2) <<o>> b3) (b1 <<o>> (b2 <<o>> b3))
    eq_refl
    (fun (name : Name) => iff_refl (In name i3))
    eq_refl
    (fun (name : Name) => iff_refl (In name o1))
    bij_sum_assoc
    bij_sum_assoc
    (fun n12_3 => bij_rew (P := fin) (arity_comp_assoc b1 b2 b3 n12_3))
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
    destruct x as [[i3'] | p123]; simpl; unfold funcomp; simpl. 
    - unfold parallel. unfold switch_link. simpl. unfold rearrange.
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      rewrite <- (innername_proof_irrelevant b3 i3' i0).
      destruct get_link; try reflexivity.
      * destruct get_link; try reflexivity.
      ** destruct get_link; try reflexivity. apply f_equal. destruct s5. apply subset_eq_compat. reflexivity. 
    - destruct p123 as ([v1 | [v2 | v3]], (i123, Hvi123)); simpl.
      * unfold parallel. unfold switch_link. simpl. unfold rearrange.
        unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
        unfold id.
        unfold bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        destruct get_link; try reflexivity.
        apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, bij_subset_backward, bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        simpl.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link; try reflexivity. 
        destruct get_link; try reflexivity. 
        apply f_equal. destruct s4. apply subset_eq_compat. reflexivity.
      * unfold bij_subset_forward, bij_subset_backward, bij_rew_forward, eq_rect_r.
        rewrite <- eq_rect_eq.
        rewrite <- eq_rect_eq.
        unfold rearrange.
        unfold extract1.
        unfold parallel.
        unfold switch_link.
        destruct get_link; try reflexivity.
        unfold id.
        unfold sequence.
        unfold rearrange.
        unfold extract1. 
        destruct get_link; try reflexivity. 
        destruct get_link; try reflexivity. 
        apply f_equal. destruct s5. apply subset_eq_compat. reflexivity.
  Qed.

Definition arity_comp_congruence_forward 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))) -> 
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (bij_p12 n1).
  + exact (bij_p34 n3).
  Defined.

Definition arity_comp_congruence_backward
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))) :
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))) -> 
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))).
  Proof.
  destruct n13 as [n1 | n3].
  + exact (backward (bij_p12 n1)).
  + exact (backward (bij_p34 n3)).
  Defined.

Lemma arity_comp_congruence : forall 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (bij_n12 : bijection (type (get_node b1)) (type (get_node b2))) (bij_n34 : bijection (type (get_node b3)) (type (get_node b4)))
  (bij_p12 : forall (n1 : type (get_node b1)), bijection (fin (Arity (get_control b1 n1))) (fin (Arity (get_control b2 (bij_n12 n1)))))
  (bij_p34 : forall (n3 : type (get_node b3)), bijection (fin (Arity (get_control b3 n3))) (fin (Arity (get_control b4 (bij_n34 n3)))))
  (n13 : type (get_node (b1 <<o>> b3))),
  bijection 
  (fin (Arity (get_control (bigraph_composition (p:=p13) b1 b3) n13))) 
  (fin (Arity (get_control (bigraph_composition (p:=p24) b2 b4) ((bij_n12 <+> bij_n34) n13)))).
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

Theorem bigraph_comp_congruence : forall 
  {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  (be12 : bigraph_equality b1 b2)
  (be34 : bigraph_equality b3 b4), 
  bigraph_equality (bigraph_composition (p:=p13) b1 b3) (bigraph_composition (p:=p24) b2 b4).
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
    (arity_comp_congruence b1 b2 b3 b4 bij_n12 bij_n34 bij_p12 bij_p34) 
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
      rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel.
      simpl.
      destruct get_parent.
      * reflexivity.
      * unfold bij_rew_forward.
        erewrite eq_rect_compose.
        instantiate (1 := eq_refl). simpl. 
        destruct get_parent; reflexivity.
    - rewrite <- big_parent_eq34.
      rewrite <- big_parent_eq12.
      simpl.
      unfold funcomp, parallel.
      destruct get_parent.
      * reflexivity.
      * unfold bij_rew_forward.
        erewrite eq_rect_compose.
        instantiate (1 := eq_refl). simpl. 
        destruct get_parent; reflexivity.
  + apply functional_extensionality.
    destruct x as [[i4'] | p123]; simpl; unfold funcomp; simpl. 
    - rewrite <- big_link_eq34. simpl.
      unfold funcomp, parallel. unfold switch_link. simpl. unfold rearrange.
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      destruct get_link; try reflexivity.
      rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold rearrange, switch_link, id. 
      destruct s0. unfold permut_list_forward.
      set (Hn' := match bij_i12 x with
        | conj _ H => H
        end
          (eq_ind_r (fun b : Name => In b i2o4)
            (match p24 x with
              | conj H _ => H
              end (proj1 (bij_o34_i12 x) i1)) eq_refl)).
      set (Hn := match p13 x with
        | conj H _ => H
        end i1). 
      rewrite (innername_proof_irrelevant b1 x Hn Hn').
      destruct get_link; try reflexivity.
    - destruct p123 as ([v2 | v3], (i123, Hvi123)); simpl.
      * unfold bij_list_backward', bij_list_forward, bij_subset_forward, parallel, sum_shuffle, choice, funcomp, id.
      simpl.
      rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold extract1, rearrange, bij_rew_forward, eq_rect_r, funcomp, parallel, id.
      simpl. (*pourquoi j'ai un get_link b3?*)
      unfold extract1.
      erewrite <- (eq_rect_map (f := inl) (a := v2)).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b1)) (type (get_node b2)) bij_n12) v2)).
      destruct (backward (bij_p12 ((bij_n12 ⁻¹) v2))).
      destruct get_link; try reflexivity.
      * unfold extract1, rearrange, bij_rew_forward, eq_rect_r, funcomp, parallel, id.
      simpl.
      rewrite <- big_link_eq34. simpl.
      unfold funcomp, parallel. 
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      erewrite <- (eq_rect_map (f := inr) (a := v3)).
      instantiate (1 := eq_sym (equal_f (fob_id (type (get_node b3)) (type (get_node b4)) bij_n34) v3)).
      destruct (backward (bij_p34 ((bij_n34 ⁻¹) v3))).
      destruct get_link; try reflexivity.
      ** rewrite <- big_link_eq12. simpl.
      unfold funcomp, parallel. 
      unfold extract1, bij_subset_forward, bij_subset_backward, id. simpl.
      unfold id.
      destruct s0. unfold permut_list_forward.
      set (Hn := match p13 x0 with
        | conj H _ => H
        end i0).
      set (Hn' := match bij_i12 x0 with
        | conj _ H => H
        end
          (eq_ind_r (fun b : Name => In b i2o4)
            (match p24 x0 with
              | conj H _ => H
              end (proj1 (bij_o34_i12 x0) i0)) eq_refl)).
      rewrite (innername_proof_irrelevant b1 x0 Hn Hn').
      destruct get_link; try reflexivity. 
  Qed. 
  (*Missing a hypothesis that says bij_s12 = bij_r34_s12 in the equalities *)

Definition bigraph_packed_composition {s1 i1o2 r1 o1 s2 i2 o2i1} {p: permutation (ndlist o2i1) (ndlist i1o2)}
  (b1 : bigraph s1 i1o2 r1 o1) (b2 : bigraph s2 i2 s1 o2i1) : bigraph_packed :=
  packing (bigraph_composition (p := p) b1 b2).

Definition bigraph_packed_composition' (*{s1 i1 r1 o1 s2 i2 : FinDecType} *)
  (b1 : bigraph_packed) (b2 : bigraph_packed) : bigraph_packed. Admitted.

Theorem bigraph_packed_comp_left_neutral : forall {s i r o o' o''} 
  {p : permutation (ndlist o) (ndlist o')} 
  {p' : permutation (ndlist o') (ndlist o'')}
  (b : bigraph s i r o), 
  bigraph_packed_equality (bigraph_packed_composition (p:=p) (bigraph_identity (p := p')) b) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_left_neutral.
  Qed. 

Theorem bigraph_packed_comp_assoc : forall {s1 i1o2 r1 o1 s2 i2o3 o2i1 s3 i3 o3i2} 
  {pi1o2 : permutation (ndlist o2i1) (ndlist i1o2)}
  {pi2o3 : permutation (ndlist o3i2) (ndlist i2o3)}
  (b1 : bigraph s1 i1o2 r1 o1) 
  (b2 : bigraph s2 i2o3 s1 o2i1) 
  (b3 : bigraph s3 i3 s2 o3i2),
  bigraph_packed_equality 
    (bigraph_packed_composition (p:=pi2o3) (bigraph_composition (p:=pi1o2) b1 b2) b3) 
    (bigraph_packed_composition (p:=pi1o2) b1 (bigraph_composition (p:=pi2o3) b2 b3)).
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_pp.
  intros.
  apply bigraph_comp_assoc.
  Qed.

Lemma bigraph_packed_comp_right_neutral : forall {s i r o i' i''} 
  {p : permutation (ndlist i'') (ndlist i)} 
  {p' : permutation (ndlist i') (ndlist i'')}
  (b : bigraph s i r o), 
    bigraph_packed_equality (bigraph_composition (p := p) b (bigraph_identity (p:=p'))) b.
  Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  intros.
  apply bigraph_comp_right_neutral.
  Qed. 

End CompositionBigraphs.
Fail Add Parametric Morphism : bigraph_packed_composition with
 signature bigraph_packed_equality ==> 
 bigraph_packed_equality ==> 
 bigraph_packed_equality as composition_morphism.
  (* Proof.
  unfold bigraph_packed_equality, bigraph_packed_composition.
  destruct x; destruct y; simpl; destruct x0; destruct y0; simpl.
  apply bigraph_comp_congruence.
  assumption.
  Qed. *)

(* Bifunctorial property*)
Theorem arity_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)}
  (n12_34:type (get_node (b1 ⊗ b2 <<o>> (b3 ⊗ b4)))),
  Arity (get_control
    (bigraph_composition (p := permutation_distributive p13 p24)
      (bigraph_tensor_product (dis_i := dis_i12) (dis_o := dis_o12) b1 b2) 
      (bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o34) b3 b4)) n12_34) =
  Arity (get_control 
    ((bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o12) 
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4))) 
    (sum_shuffle n12_34)).
  Proof.
  intros.
  destruct n12_34 as [[n1|n2]|[n3|n4]]; reflexivity.
  Qed.

Definition reflnames {r} : forall name : Name,
  In name r <-> In name r.
  reflexivity. Defined.

Theorem bigraph_comp_tp_dist : forall {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 i3 o3i1 s4 i4 o4i2} 
  (b1 : bigraph s1 i1o3 r1 o1) 
  (b2 : bigraph s2 i2o4 r2 o2) 
  (b3 : bigraph s3 i3 s1 o3i1) 
  (b4 : bigraph s4 i4 s2 o4i2)
  {dis_i12 : i1o3 # i2o4} {dis_o12 : o1 # o2}
  {dis_i34 : i3 # i4} {dis_o34 : o3i1 # o4i2}
  {p13 : permutation (ndlist o3i1) (ndlist i1o3)}
  {p24 : permutation (ndlist o4i2) (ndlist i2o4)},
  bigraph_equality 
  (bigraph_composition (p := permutation_distributive p13 p24)
    (bigraph_tensor_product (dis_i := dis_i12) (dis_o := dis_o12) b1 b2) 
    (bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o34) b3 b4))
  ((bigraph_tensor_product (dis_i := dis_i34) (dis_o := dis_o12) 
    (bigraph_composition (p:=p13) b1 b3) 
    (bigraph_composition (p:=p24) b2 b4))) .
  Proof.
  intros.
  apply (BigEq
    _ _ _ _
    _ _ _ _ 
    ((b1 ⊗ b2) <<o>> (b3 ⊗ b4)) 
    ((b1 <<o>> b3) ⊗ (b2 <<o>> b4))
    (reflexivity (s3 + s4)) (*s3 + s4*)
    reflnames (*i3 + i4*)
    (reflexivity (r1 + r2)) (*r1 + r2*)
    reflnames (*o1 + o2*)
    bij_sum_shuffle(* n1 + n2 + n3 + n4*)
    bij_sum_shuffle (* e1 + e2 + e3 + e4 *)
    (fun n12_34 => bij_rew (P := fin) (arity_comp_tp_dist b1 b2 b3 b4 n12_34)) (* Port *)
  ).
  + apply functional_extensionality.
    destruct x as [[n1|n3]|[n2|n4]]; reflexivity.
  + apply functional_extensionality.
    destruct x as [[[n1|n3]|[n2|n4]]|(s34, Hs34)]; simpl; unfold funcomp; simpl; unfold sequence, extract, inject, sum_shuffle, parallel, id.
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
    destruct x as [[i']|p]; simpl; unfold funcomp; simpl; unfold rearrange; unfold extract1; unfold sum_shuffle; unfold parallel; unfold switch_link; simpl.
    - unfold bij_list_forward, bij_list_backward', bij_subset_forward, bij_subset_backward, parallel, sum_shuffle, choice, funcomp, id. 
      simpl.
      unfold id.
      unfold bij_join_port_backward, bij_dep_sum_2_forward, bijection_inv, bij_dep_sum_1_forward.
      simpl.
      unfold rearrange, switch_link, extract1, bij_subset_forward.
      simpl.
      destruct (in_dec EqDecN i' i3).
      * destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0 as [n npf]. 
      destruct (in_dec EqDecN n i1o3).
      ***
      set (npf' := match p13 n with
        | conj H _ => H
        end npf).
      rewrite <- (innername_proof_irrelevant b1 n i2 npf').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      *** exfalso. apply n0. unfold permutation in p13. destruct (p13 n). apply H. apply npf.
      * unfold permutation_distributive, permut_list_forward.
      set (Hn := match
          in_app_or_m_nod_dup i3 i4 i'
            (match
              i3 as n0
              return
                ((In i' n0 -> ~ In i' i4) ->
                  In i'
                    (app_merge' n0 i4) ->
                  ~ In i' n0 -> NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : 
                    In i' ndlist0 ->
                    ~ In i' i4)
                  (_ : 
                    In i'
                      (app_merge' ndlist0
                      i4))
                  (_ : ~ In i' ndlist0)
                => nd0
            end (dis_i34 i')
              (match reflnames i' with
                | conj _ H => H
                end
                  (eq_ind_r
                    (fun b : Name =>
                      In b
                      (app_merge' i3 i4))
                    i0 eq_refl)) n)
            (match
              i4 as n0
              return
                ((In i' i3 -> ~ In i' n0) ->
                  In i'
                    (app_merge' i3 n0) ->
                  NoDup n0)
            with
            | {|
                ndlist := ndlist0;
                nd := nd0
              |} =>
                fun
                  (_ : 
                    In i' i3 ->
                    ~ In i' ndlist0)
                  (_ : 
                    In i'
                      (app_merge' i3
                      ndlist0)) => nd0
            end (dis_i34 i')
              (match reflnames i' with
                | conj _ H => H
                end
                  (eq_ind_r
                    (fun b : Name =>
                      In b
                      (app_merge' i3 i4))
                    i0 eq_refl)))
            (match reflnames i' with
            | conj _ H => H
            end
              (eq_ind_r
                  (fun b : Name =>
                  In b
                    (app_merge' i3 i4))
                  i0 eq_refl))
        with
        | inl i5 =>
            False_ind (In i' i4) (n i5)
        | inr i5 => i5
        end). 
      set (Hn' := 
        match
          in_app_or_m_nod_dup i3 i4 i'
            (match
                i3 as n0
                return
                  ((In i' n0 -> ~ In i' i4) ->
                  In i' (app_merge' n0 i4) ->
                  ~ In i' n0 -> NoDup n0)
              with
              | {|
                  ndlist := ndlist0;
                  nd := nd0
                |} =>
                  fun
                    (_ : In i' ndlist0 ->
                        ~ In i' i4)
                    (_ : In i'
                        (app_merge' ndlist0
                        i4))
                    (_ : ~ In i' ndlist0) =>
                  nd0
              end (dis_i34 i') i0 n)
            (match
                i4 as n0
                return
                  ((In i' i3 -> ~ In i' n0) ->
                  In i' (app_merge' i3 n0) ->
                  NoDup n0)
              with
              | {|
                  ndlist := ndlist0;
                  nd := nd0
                |} =>
                  fun
                    (_ : In i' i3 ->
                        ~ In i' ndlist0)
                    (_ : In i'
                        (app_merge' i3
                        ndlist0)) => nd0
              end (dis_i34 i') i0) i0
        with
        | inl i5 =>
            False_ind (In i' i4) (n i5)
        | inr i5 => i5
        end).
      rewrite <- (innername_proof_irrelevant b4 i' Hn Hn').
      destruct get_link; try reflexivity. 
      destruct s0 as [n' npf']. 
      destruct (in_dec EqDecN n' i1o3).
      *** exfalso. unfold Disjoint in dis_i12. specialize (dis_i12 n'). apply dis_i12; try assumption.
      unfold permutation in p24. destruct (p24 n'). apply H; assumption.
      *** destruct in_app_or_m. {exfalso. apply n0. unfold permutation in p13. destruct (p13 n'). apply H; assumption. }
      set (Hn'' := match
        in_app_or_m_nod_dup i1o3 i2o4 n'
            (match
              i1o3 as n1
              return
                ((In n' n1 -> ~ In n' i2o4) ->
                  In n' (app_merge' n1 i2o4) ->
                  ~ In n' n1 -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In n' ndlist0 -> ~ In n' i2o4)
                  (_ : In n' (app_merge' ndlist0 i2o4))
                  (_ : ~ In n' ndlist0) => nd0
            end (dis_i12 n')
              match p13 n' with
              | conj _ _ =>
                  match p24 n' with
                  | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                  end
              end n0)
            (match
              i2o4 as n1
              return
                ((In n' i1o3 -> ~ In n' n1) ->
                  In n' (app_merge' i1o3 n1) -> NoDup n1)
            with
            | {| ndlist := ndlist0; nd := nd0 |} =>
                fun (_ : In n' i1o3 -> ~ In n' ndlist0)
                  (_ : In n' (app_merge' i1o3 ndlist0)) => nd0
            end (dis_i12 n')
              match p13 n' with
              | conj _ _ =>
                  match p24 n' with
                  | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                  end
              end)
            match p13 n' with
            | conj _ _ =>
                match p24 n' with
                | conj H _ => in_right_list n' i1o3 i2o4 (H i1)
                end
            end
        with
        | inl i2 => False_ind (In n' i2o4) (n0 i2)
        | inr i2 => i2
        end). fold Hn''.
      set (Hn'''' := match p24 n' with
        | conj H _ => H
        end npf').
      rewrite <- (innername_proof_irrelevant b2 n' Hn'' Hn'''').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
    - destruct p as ([[v1 | v2] | [v3 | v4]], (i1234, Hvi1234)); unfold bij_join_port_backward; simpl.
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity. apply f_equal. destruct s0. apply subset_eq_compat. reflexivity. 
    * unfold bij_rew_forward, eq_rect_r, extract1, bij_list_forward, bij_subset_forward, bij_list_backward', rearrange, extract1.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      simpl.
      destruct get_link; try reflexivity.
      unfold permutation_distributive, permut_list_forward.
      destruct s0.
      destruct (in_dec EqDecN x i1o3).
      **
      set (Hn := match p13 x with
        | conj H _ => H
        end i0). 
      rewrite <- (innername_proof_irrelevant b1 x i1 Hn).
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** exfalso. apply n. unfold permutation in p13. destruct (p13 x). apply H; assumption.
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
      destruct get_link; unfold rearrange; unfold extract1; simpl.
      ** destruct s0.
      destruct (in_dec EqDecN x i1o3).
      *** exfalso. unfold Disjoint in dis_i12. specialize (dis_i12 x).
      apply dis_i12; try assumption.
      unfold permutation in p24. destruct (p24 x). apply H; assumption. 
      *** 
      set (i0' := match p24 x with
        | conj H _ => H
        end i0).
      rewrite <- (innername_proof_irrelevant b2 x i0').
      destruct get_link; try reflexivity.
      apply f_equal. destruct s0. apply subset_eq_compat. reflexivity.
      ** reflexivity.
  Qed.
    
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

(* Lemma acyclic_rm_void_parent {node s r: FinDecType} {n:type node}
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
    destruct H as [H_acc].
    - admit.
    - admit.
  Admitted. *)

(* Definition rm_void_finDecSum {s1 i1 o1 r1} 
  (b : bigraph (findec_sum voidfd s1) (app_NoDupList i1 EmptyNDL) (findec_sum voidfd r1) (app_NoDupList i1 o1)) : 
  bigraph s1 i1 r1 (app_NoDupList i1 o1).
  Proof. 
  destruct b. Admitted. *)
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


(* Definition nest {s1 i1 r1 o1 i2} (* TODO check definition*)
  (b1 : bigraph s1 EmptyNDL r1 o1) (b2 : bigraph voidfd i2 s1 i1) :=
  (rm_void_finDecSum ((@bigraph_identity voidfd i1) || b1)) <<o>> b2.

Definition nest' {I m X n Y} (* TODO check definition*)
  (F : bigraph voidfd I m X) (G : bigraph m EmptyNDL n Y) 
  : bigraph voidfd I n (app_NoDupList X Y) :=
  (rm_void_finDecSum ((@bigraph_identity voidfd X) || G)) <<o>> F. *)

Example I : NoDupList. Admitted.
Example m : nat. Admitted.
Example X : NoDupList. Admitted.
Example n : nat. Admitted.
Example Y : NoDupList. Admitted.
Example F : bigraph 0 I m X. Admitted.
Example G : bigraph m EmptyNDL n Y. Admitted.


Example b1 {s1 r1 o1}: bigraph s1 EmptyNDL r1 o1. Admitted.
Example b2 {s1 i2 i1}: bigraph 0 i2 s1 i1. Admitted.


End NestingBig.

End Bigraphs.

