Set Warnings "-notation-overridden, -parsing, -masking-absolute-name, -cannot-define-projection".

Require Import ConcreteBigraphs.
Require Import Bijections.
Require Import InfSets.
Require Import SignatureBig.
Require Import MyBasics.
Require Import MathCompAddings.
Require Import FunctionalExtensionality.


Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import ProofIrrelevance.


From mathcomp Require Import all_ssreflect.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div.


Import ListNotations.

(** This module implements equivalence between two bigraphs
  This section defines the equivalence relation between bigraphs. 
  We say there's an equivalence between two types if we give a bijection 
  (cf support_for_bigraphs) between the two types. To define the equivalence 
  between bigraphs, we want an equivalence between each Type and between 
  each function.
  To do that, we make definitions of equivalence between each function. 
  We coerce the Record support_equivalence into a Prop, which means that we can
  access the bjections, but also that their existence means the Prop is True.
  Note that our equivalence is heterogeneous. 
  We prove that our relation support_equivalence is reflexive, 
  symmetric and transitive. This is going to be useful to be able to rewrite 
  bigraphs at will. *)
Module SupportEquivalenceBigraphs (s : SignatureParameter)
  (np : InfiniteParameter)
  (vp : InfiniteParameter)
  (ep : InfiniteParameter).
Module b := Bigraphs s np vp ep.
Import b. 


(** ** On the heterogeneous type *)
Record support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : n.NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  SupEq
  {
    bij_s : s1 = s2 ;
    bij_i : n.permutation (n.ndlist i1) (n.ndlist i2) ; 
    bij_r : r1 = r2 ;
    bij_o : n.permutation (n.ndlist o1) (n.ndlist o2) ; 
    bij_n : v.permutation (v.ndlist (get_node b1)) (v.ndlist (get_node b2));
    bij_e : e.permutation (e.ndlist (get_edge b1)) (e.ndlist (get_edge b2));
    bij_p : forall (n1 : v.ListType (get_node b1)),
      bijection 
        ('I_(Arity (get_control (bg:=b1) n1))) 
        ('I_(Arity (get_control (bg:=b2) (<{bij_id | bij_n}> n1)))) ;
    big_control_eq : (<{bij_id | bij_n}> -->> (@bij_id Kappa)) (get_control (bg:=b1)) = get_control (bg:=b2) ;
    big_parent_eq : ((<{bij_id | bij_n}> <+> (bij_rew bij_s)) -->> (<{bij_id | bij_n}> <+> ((bij_rew bij_r)))) (get_parent (bg:=b1)) = get_parent (bg:=b2) ;
    big_link_eq : ((<{bij_id | bij_i}> <+> <{ <{bij_id | bij_n}> & bij_p }>) -->> (<{bij_id| bij_o}> <+> <{bij_id | bij_e}>)) (get_link (bg := b1)) = get_link (bg := b2)
  }.

Lemma bij_subset_v_permutation_id {s r} {i o} (b : bigraph s i r o) : 
  <{ bij_id | v.permutation_id (v.ndlist (get_node b)) }> = bij_id.
  Proof.
  apply Bijections.bij_eq;simpl; apply functional_extensionality; intros [node Hnode].
  unfold bij_subset_forward. apply subset_eq_compat. reflexivity.
  unfold bij_subset_backward. apply subset_eq_compat. reflexivity.
  Qed.

Lemma bij_subset_e_permutation_id {s r} {i o} (b : bigraph s i r o) : 
  <{ bij_id | e.permutation_id (e.ndlist (get_edge b)) }> = bij_id.
  Proof.
  apply Bijections.bij_eq;simpl; apply functional_extensionality; intros [node Hnode].
  unfold bij_subset_forward. apply subset_eq_compat. reflexivity.
  unfold bij_subset_backward. apply subset_eq_compat. reflexivity.
  Qed.

Lemma bij_subset_n_permutation_id {l} : 
  <{ bij_id | n.permutation_id l }> = bij_id.
  Proof.
  apply Bijections.bij_eq;simpl; apply functional_extensionality; intros [name Hname].
  unfold bij_subset_forward. apply subset_eq_compat. reflexivity.
  unfold bij_subset_backward. apply subset_eq_compat. reflexivity.
  Qed.

Lemma eq_rect_bij_id {s r} {i o} (b : bigraph s i r o)
  (n1 : v.ListType (get_node b)) : 
  forall p,
  nat_of_ord (eq_rect bij_id
    (fun y : bijection 
      {x : v.InfType | In x (v.ndlist (get_node b))} 
      {x : v.InfType | In x (v.ndlist (get_node b))} =>
        bijection 
          'I_(Arity (get_control (bg:=b) n1))
          'I_(Arity (get_control (bg:=b) (y n1)))) 
    bij_id
    <{ bij_id | v.permutation_id (v.ndlist (get_node b)) }>
    (Logic.eq_sym (bij_subset_v_permutation_id b)) p) = nat_of_ord p.
  intros. unfold eq_rect.
  destruct p. simpl.
  Admitted.


Lemma support_equivalence_refl {s r} {i o} (b : bigraph s i r o) :
  support_equivalence b b.
  Proof.
  eapply (SupEq _ _ _ _ _ _ _ _ _ _ 
    erefl 
    (n.permutation_id (n.ndlist i)) 
    erefl 
    (n.permutation_id (n.ndlist o)) 
    (v.permutation_id (v.ndlist (get_node b))) 
    (e.permutation_id (e.ndlist (get_edge b))) 
    (fun _ => _)).
  Unshelve. 4:{ rewrite bij_subset_v_permutation_id. exact bij_id. }
  + rewrite bij_subset_v_permutation_id. 
    rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_subset_v_permutation_id.
    rewrite bij_rew_id.
    rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_subset_n_permutation_id.
    rewrite bij_subset_n_permutation_id.
    rewrite bij_subset_e_permutation_id.
    rewrite bij_sum_compose_id.
    rewrite bij_subset_v_permutation_id.
    unfold eq_rect_r. 
    simpl. unfold funcomp,parallel,bij_dep_sum_2_forward, bijection_inv.
    simpl.
    apply functional_extensionality. 
    intros [inner|[[port]]].
    reflexivity. 
    simpl.
    apply port_proof_irrelevant_full.
    apply subset_eq_compat. reflexivity.
    simpl.
    rewrite eq_rect_bij_id.

    unfold eq_rect_r,eq_ind_r. simpl.
    unfold bij_subset_forward,bij_subset_backward.
    destruct o0.
    simpl.

    apply val_inj.
    unfold eq_rect. simpl.
    destruct (@Logic.eq_sym (@In v.InfType port (v.ndlist (@get_node s r i o
b)))
(@proj1
(forall _ : @In v.InfType port (v.ndlist (@get_node s r i
o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(forall _ : @In v.InfType port (v.ndlist (@get_node s r i
o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(@conj
(forall _ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(forall _ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(fun H : @In v.InfType port (v.ndlist (@get_node s r i
o b)) => H)
(fun H : @In v.InfType port (v.ndlist (@get_node s r i
o b)) => H))
i0) i0
(proof_irrelevance
(@In v.InfType port (v.ndlist (@get_node s r i o b)))
(@proj1
(forall _ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(forall _ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(@conj
(forall
_ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(forall
_ : @In v.InfType port
(v.ndlist (@get_node s r i o b)),
@In v.InfType port (v.ndlist (@get_node s r i o b)))
(fun x : @In v.InfType port
(v.ndlist (@get_node s r i o b)) => x)
(fun x : @In v.InfType port
(v.ndlist (@get_node s r i o b)) => x))
i0) i0) in (@eq _ _ a)).
    Set Printing All.

    erewrite (proof_irrelevance _).
    Search (eq_rect).
    rewrite rew_opp_r.
    unfold eq_rect_r,eq_ind_r.
    erewrite eq_rect_pi. 
    f_equal.
     simpl.
    
    unfold bij_subset_backward.

    erewrite port_proof_irrelevant.
  Unshelve.
  - unfold permutation. intros. reflexivity.
  - unfold permutation. intros. reflexivity.
  Qed.

Lemma support_equivalence_sym {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  support_equivalence b1 b2
      -> support_equivalence b2 b1.
  Proof.
  intro Heqb1b2.
  destruct Heqb1b2 as (bij_s, bij_i, bij_r, bij_o, bij_n, bij_e, bij_p, big_control_eq, big_parent_eq, big_link_eq).
  apply (SupEq _ _ _ _ _ _ _ _ b2 b1
          (esym bij_s)
          (adjunction_equiv bij_id bij_i)
          (esym bij_r)
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
        (get_link (bg:=b2)) = get_link (bg:=b1)
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

Lemma support_equivalence_trans 
  {s1 r1 s2 r2 s3 r3 : nat} {i1 o1 i2 o2 i3 o3: NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
    support_equivalence b1 b2
      -> support_equivalence b2 b3  
        -> support_equivalence b1 b3.
  Proof.
  intros Heqb1b2 Heqb2b3.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb2b3 as (bij_s23, bij_i23, bij_r23, bij_o23, bij_n23, bij_e23, bij_p23, big_control_eq23, big_parent_eq23, big_link_eq23).
  apply (SupEq _ _ _ _ _ _ _ _ b1 b3
          (eq_trans bij_s12 bij_s23)
          (fun name : InfType => @iff_trans 
            (@In InfType name (ndlist i1)) 
            (@In InfType name (ndlist i2))
            (@In InfType (@forward InfType InfType (@bij_id InfType) name) (ndlist i3))
            (bij_i12 name) (bij_i23 (@forward InfType InfType (@bij_id InfType) name))
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
  + rewrite <- (@bij_subset_compose_compose_id InfType (fun name => In name i1) (fun name => In name i2) (fun name => In name i3) bij_i12 bij_i23). 
    rewrite <- (@bij_subset_compose_compose_id InfType (fun name => In name o1) (fun name => In name o2) (fun name => In name o3) bij_o12 bij_o23). 
    rewrite <- big_link_eq23.
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
  s: nat;
  i: NoDupList;
  r: nat;
  o: NoDupList;
  big : bigraph s i r o
  }.

Coercion packing {s i r o} (b : bigraph s i r o) := 
  (mkPacked s i r o b).

Definition unpacking (b : bigraph_packed) : bigraph (s b) (i b) (r b) (o b) := 
  big b.

Definition bigraph_pkd_s_e (bp1 bp2 : bigraph_packed) := 
  support_equivalence (big bp1) (big bp2).

Theorem eq_packed_eq_eq {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
   support_equivalence b1 b2 <-> bigraph_pkd_s_e b1 b2.
   split. auto. auto. 
   Qed. 

Lemma bigraph_pkd_s_e_refl (bp : bigraph_packed) : bigraph_pkd_s_e bp bp.
  Proof.
  apply support_equivalence_refl.
  Qed.

Lemma bigraph_pkd_s_e_sym (bp1 bp2 : bigraph_packed) : bigraph_pkd_s_e bp1 bp2 -> bigraph_pkd_s_e bp2 bp1.
  Proof.
  apply support_equivalence_sym.
  Qed.

Lemma bigraph_pkd_s_e_trans (bp1 bp2 bp3 : bigraph_packed) : bigraph_pkd_s_e bp1 bp2 -> bigraph_pkd_s_e bp2 bp3 -> bigraph_pkd_s_e bp1 bp3.
  Proof.
  apply support_equivalence_trans.
  Qed. 

Add Parametric Relation: (bigraph_packed) (bigraph_pkd_s_e)
  reflexivity proved by (bigraph_pkd_s_e_refl)
  symmetry proved by (bigraph_pkd_s_e_sym)
  transitivity proved by (bigraph_pkd_s_e_trans)
    as bigraph_pkd_s_e_rel.

Lemma bigraph_pkd_s_e_dec  
  (b1 : bigraph_packed) (b2 : bigraph_packed) :
  {bigraph_pkd_s_e b1 b2} + {~ bigraph_pkd_s_e b1 b2}.
  Proof. (* same problem, bigraph_pkd_s_e not transparent enough *)
    Fail decide equality. 
  Abort.

#[export] Instance big_Equivalence: Equivalence bigraph_pkd_s_e.
  constructor. 
  exact @bigraph_pkd_s_e_refl. 
  exact @bigraph_pkd_s_e_sym. 
  exact @bigraph_pkd_s_e_trans. Defined. 



End SupportEquivalenceBigraphs.