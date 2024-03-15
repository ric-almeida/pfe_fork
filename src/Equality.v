Require Import ConcreteBigraphs.
Require Import Bijections.
Require Import Names.
Require Import SignatureBig.
Require Import Fintypes.
Require Import FinDecTypes.
Require Import MyBasics.

Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.

Import ListNotations.

(** This module implements equivalence between two bigraphs
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
Module EquivalenceBigraphs (s : Signature) (n : Names) (b: Bigraphs s n).
Include b. 

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


Add Parametric Relation: (bigraph_packed) (bigraph_packed_equality)
  reflexivity proved by (bigraph_packed_equality_refl)
  symmetry proved by (bigraph_packed_equality_sym)
  transitivity proved by (bigraph_packed_equality_trans)
    as bigraph_packed_equality_rel.

Lemma bigraph_packed_equality_dec  
  (b1 : bigraph_packed) (b2 : bigraph_packed) :
  {bigraph_packed_equality b1 b2} + {~ bigraph_packed_equality b1 b2}.
  Proof. (* same problem, bigraph_packed_equality not transparent enough *)
    Fail decide equality. 
  Abort.

#[export] Instance big_Equivalence: Equivalence bigraph_packed_equality.
  constructor. 
  exact @bigraph_packed_equality_refl. 
  exact @bigraph_packed_equality_sym. 
  exact @bigraph_packed_equality_trans. Defined. 


(* Class DisjointNamesPacked (b1 b2 : bigraph_packed) :=
  { disj_inner :> (i b1) # (i b2);
    disj_outer :> (o b1) # (o b2)
  }.
  
#[export] Instance disj_packed (b1 b2 : bigraph_packed) (Disji12 : (i b1) # (i b2)) (Disjo12 : (o b1) # (o b2)) : 
  DisjointNamesPacked b1 b2.
  Proof.
  constructor.
  + exact Disji12.
  + exact Disjo12.
  Qed. *)
  
(* Record disjoint_bigraph_packed_disjoint_pair :=
  { 
    bp1 : bigraph_packed;
    bp2 : bigraph_packed;
    dis_i12 : (i bp1) # (i bp2);
    dis_o12 : (o bp1) # (o bp2);
  }.
Arguments Build_bigraph_packed_disjoint_pair _ _ {disj_pp}. (*What does this do?*)
  
Record bigraph_packed_disjoint_pair_equality (pp1 pp2 : bigraph_packed_disjoint_pair) : Prop :=
  { 
    fst_pp_equ : bigraph_packed_equality (fst_pp pp1) (fst_pp pp2);
    snd_pp_equ : bigraph_packed_equality (snd_pp pp1) (snd_pp pp2)
  }. (*Why 4 bigraphs?*)
  
Lemma bigraph_packed_disjoint_pair_equality_refl (pp : bigraph_packed_disjoint_pair) :
  bigraph_packed_disjoint_pair_equality pp pp.
  Proof.
  constructor.
  + apply bigraph_equality_refl.
  + apply bigraph_equality_refl.
  Qed.
  
Lemma bigraph_packed_disjoint_pair_equality_sym (pp1 pp2 : bigraph_packed_disjoint_pair):
  bigraph_packed_disjoint_pair_equality pp1 pp2 -> bigraph_packed_disjoint_pair_equality pp2 pp1.
  Proof.
  intros H12.
  constructor.
  + symmetry.
    apply (fst_pp_equ _ _ H12).
  + symmetry.
    apply (snd_pp_equ _ _ H12).
  Qed.
  
Lemma bigraph_packed_disjoint_pair_equality_trans (pp1 pp2 pp3 : bigraph_packed_disjoint_pair):
  bigraph_packed_disjoint_pair_equality pp1 pp2 -> bigraph_packed_disjoint_pair_equality pp2 pp3 ->
    bigraph_packed_disjoint_pair_equality pp1 pp3.
  Proof.
  intros H12 H23.
  constructor.
  + etransitivity.
    - apply (fst_pp_equ _ _ H12).
    - apply (fst_pp_equ _ _ H23).
  + etransitivity.
    - apply (snd_pp_equ _ _ H12).
    - apply (snd_pp_equ _ _ H23).
  Qed.
  
Add Parametric Relation : 
  bigraph_packed_disjoint_pair bigraph_packed_disjoint_pair_equality
  reflexivity proved by (bigraph_packed_disjoint_pair_equality_refl)
  symmetry proved by (bigraph_packed_disjoint_pair_equality_sym)
  transitivity proved by (bigraph_packed_disjoint_pair_equality_trans)
    as bigraph_packed_disjoint_pair_equality_rel. *)

End EquivalenceBigraphs.