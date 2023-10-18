From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.


Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Decidable.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Coq.Setoids.Setoid.


From MyProofs Require Import support_for_bigraphs.

(* Require Import support_for_bigraphs. *)
Set Warnings "-parsing".
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "parsing".

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope bool_scope.
Import ListNotations.  


(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraph.

(** * Definition of a bigraph
This section defines the Type bigraph *)
Section IntroBigraphs.
  Inductive void : Type := .

  Definition merge {A B : Type} (la : list A) (lb : list B) : list (A + B) :=
    (map inl la) ++ (map inr lb).

  Definition finite (A : Type) : Type := { l : list A | Listing l }.

  Record FinDecType : Type :=
    {
      type :> Type ;
      finite_type : finite type ;
      dec_type : EqDec type
    }.

  Definition acyclic (node site root : Type) (parent : node + site -> node + root) : Prop :=
    forall (n:node), Acc (fun n n' => parent (inl n) = (inl n')) n.

  Definition acyclic' (node site root : Type) (parent : node + site -> node + root) : Prop :=
    forall (n:node), Acc (fun n n' => parent (inl n') = (inl n)) n.

  Definition Port {kind : Type} (node : Type) (control : node -> kind) (arity : kind -> nat): Type :=
    { vi : node * nat | let (v, i) := vi in let k := control v in let a := arity k in i < a }.

Record bigraph  (site: FinDecType) 
                (innername: FinDecType) 
                (root: FinDecType) 
                (outername: FinDecType) : Type := 
  mkBig  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    kind : FinDecType ;
    arity : kind -> nat ;
    control : node -> kind ;
    parent : node + site -> node + root ; 
    link : innername + Port node control arity -> outername + edge; 
    ap : acyclic node site root parent ;
  }.
End IntroBigraphs.

(** * Getters
This section is just getters to lightenn some notations *)
Section GettersBigraphs.
  Definition get_node {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  node s i r o bg.
  Definition get_edge {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  edge s i r o bg.
  Definition get_kind {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  kind s i r o bg.
  Definition get_arity {s i r o : FinDecType} (bg : bigraph s i r o) : 
  (get_kind bg) -> nat := 
  arity s i r o bg.
  Definition get_control {s i r o : FinDecType} (bg : bigraph s i r o) 
  : get_node bg -> (get_kind bg) :=
  @control s i r o bg.
  Definition get_parent {s i r o : FinDecType} (bg : bigraph s i r o) : 
  (get_node bg) + s -> (get_node bg) + r :=
  @parent s i r o bg.
  Definition get_link {s i r o : FinDecType} (bg : bigraph s i r o) : 
  i + Port (get_node bg) (get_control bg) (get_arity bg) -> o + get_edge bg :=
  @link s i r o bg. 
  Definition get_nd {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (get_node bg) :=
  @dec_type (node s i r o bg).
  Definition get_nf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (get_node bg) :=
  @finite_type (node s i r o bg).
  Definition get_ed {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (get_edge bg) :=
  @dec_type (edge s i r o bg).
  Definition get_ef {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (get_edge bg) :=
  @finite_type (edge s i r o bg).
  Definition get_kd {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (get_kind bg) :=
  @dec_type (kind s i r o bg).
  Definition get_kf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (get_kind bg) :=
  @finite_type (kind s i r o bg).
  Definition get_sd {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec s :=
  @dec_type s.
  Definition get_sf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite s :=
  @finite_type s.
  Definition get_id {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec i :=
  @dec_type i.
  Definition get_if {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite i :=
  @finite_type i.
  Definition get_rd {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec r :=
  @dec_type r.
  Definition get_rf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite r :=
  @finite_type r.
  Definition get_od {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec o :=
  @dec_type o.
  Definition get_of {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite o :=
  @finite_type o.
  Definition get_ap {s i r o : FinDecType} (bg : bigraph s i r o) : 
  acyclic (get_node bg) s r (get_parent bg) :=
  @ap s i r o bg.
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
Note that our equivalence is heterogeneous. *)
Section EquivalenceBigraphs.
  Definition bigraph_arity_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_k : bijection (get_kind b1) (get_kind b2)): Prop :=
      forall k1:get_kind b1, let k2 := bij_k.(forward (get_kind b1) (get_kind b2)) k1 in 
      get_arity b1 k1 = get_arity b2 k2.

  Definition bigraph_control_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_n : bijection (get_node b1) (get_node b2))
    (bij_k : bijection (get_kind b1) (get_kind b2)) : Prop :=
      forall n1:get_node b1, 
      let kind1 := get_control b1 n1 in
      let n2 := forward (get_node b1) (get_node b2) bij_n n1 in 
      let kind2 := get_control b2 n2 in
      forward (get_kind b1) (get_kind b2) bij_k kind1 = kind2.

  Definition bigraph_parent_site_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_s : bijection s1 s2)
    (bij_r : bijection r1 r2)
    (bij_n : bijection (get_node b1) (get_node b2)) : Prop :=
      forall site1:s1, 
      let site2 := forward s1 s2 bij_s site1 in
      match (get_parent b1 (inr site1)),(get_parent b2 (inr site2)) with
      | inr root1, inr root2  => forward r1 r2 bij_r root1 = root2
      | inl node1, inl node2  => forward (get_node b1) (get_node b2) bij_n node1 = node2
      | _, _ => False
      end.

  Definition bigraph_parent_node_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_r : bijection r1 r2)
    (bij_n : bijection (get_node b1) (get_node b2)): Prop :=
      forall n1:get_node b1, 
      let n2 := bij_n.(forward (get_node b1) (get_node b2)) n1 in 
      match (get_parent b1 (inl n1)),(get_parent b2 (inl n2)) with
      | inr root1, inr root2  => forward r1 r2 bij_r root1 = root2
      | inl node1, inl node2  => forward (get_node b1) (get_node b2) bij_n node1 = node2
      | _, _ => False
      end.

  Definition bigraph_parent_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_s : bijection s1 s2)
    (bij_r : bijection r1 r2)
    (bij_n : bijection (get_node b1) (get_node b2)): Prop :=
    bigraph_parent_node_equality b1 b2 bij_r bij_n /\ bigraph_parent_site_equality b1 b2 bij_s bij_r bij_n.

  Definition bigraph_link_innername_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_i : bijection i1 i2)
    (bij_o : bijection o1 o2)
    (bij_e : bijection (get_edge b1) (get_edge b2)) : Prop :=
      forall inner1:i1,
      let inner2 := forward i1 i2 bij_i inner1 in
      match (get_link b1 (inl inner1)),(get_link b2 (inl inner2)) with
      | inr edge1, inr edge2  => forward (get_edge b1) (get_edge b2) bij_e edge1 = edge2
      | inl outer1, inl outer2  =>  forward o1 o2 bij_o outer1 = outer2
      | _, _ => False
      end.

  Definition bigraph_link_port_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_o : bijection o1 o2)
    (bij_e : bijection (get_edge b1) (get_edge b2))
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) : Prop :=
      forall p1:(Port (get_node b1) (get_control b1) (get_arity b1)), 
      let p2 := bij_p.(forward (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) p1 in
      match (get_link b1 (inr p1)),(get_link b2 (inr p2)) with
      | inr edge1, inr edge2  => forward (get_edge b1) (get_edge b2) bij_e edge1 = edge2
      | inl outer1, inl outer2  => forward o1 o2 bij_o outer1 = outer2
      | _, _ => False
      end.

  Definition bigraph_link_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (bij_i : bijection i1 i2)
    (bij_o : bijection o1 o2)
    (bij_e : bijection (get_edge b1) (get_edge b2))
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) : Prop :=
    bigraph_link_innername_equality b1 b2 bij_i bij_o bij_e /\ bigraph_link_port_equality b1 b2 bij_o bij_e bij_p.

Record bigraph_equality {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigEq'
  {
    bij_s : bijection s1 s2 ;
    bij_i : bijection i1 i2 ;
    bij_r : bijection r1 r2 ;
    bij_o : bijection o1 o2 ;
    bij_n : bijection (get_node b1) (get_node b2);
    bij_e : bijection (get_edge b1) (get_edge b2);
    bij_k : bijection (get_kind b1) (get_kind b2);
    bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)); 
    big_arity_eq : bigraph_arity_equality b1 b2 bij_k ; 
    big_control_eq : bigraph_control_equality b1 b2 bij_n bij_k ; 
    big_parent_eq : bigraph_parent_equality b1 b2 bij_s bij_r bij_n ;
    big_link_eq : bigraph_link_equality b1 b2 bij_i bij_o bij_e bij_p
  }.
End EquivalenceBigraphs.

(** * Proving our equivalence is a relation *)
(** ** On the heterogeneous type  
In this section, we prove that our relation bigraph_equality is reflexive, 
symmetric and transitive. This is going to be useful to be able to rewrite 
bigraphs at will. *)
Section EquivalenceIsRelation.
  Lemma arity_refl {s i r o : FinDecType} (b : bigraph s i r o) :
    let bij_k := bijection_id  in
    bigraph_arity_equality b b bij_k.
    Proof. unfold bigraph_arity_equality. (* auto. *) 
    intros. unfold bijection_id. simpl. unfold id. reflexivity. Qed.

  Lemma control_refl {s i r o : FinDecType} (b : bigraph s i r o) :
    let bij_n := bijection_id  in
    let bij_k := bijection_id  in
    bigraph_control_equality b b bij_n bij_k.
    Proof. unfold bigraph_control_equality. (* auto. *) 
    intros. unfold bijection_id. simpl. unfold id. reflexivity. Qed.

  Lemma parent_refl {s i r o : FinDecType} (b : bigraph s i r o) :
    let bij_s := bijection_id  in
    let bij_r := bijection_id  in
    let bij_n := bijection_id  in
    bigraph_parent_equality b b bij_s bij_r bij_n.
    Proof. unfold bigraph_parent_equality. split. 
      + (* bigraph_parent_node_equality *)
      unfold bigraph_parent_node_equality. intros. 
      unfold bijection_id. simpl. unfold id. 
      set (pn1 := get_parent b (inl n1)). 
      destruct pn1 as [pn1 | pr1]; reflexivity.
      + (*bigraph_parent_site_equality*) 
      unfold bigraph_parent_site_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (ps1 := get_parent b (inr site1)). 
      destruct ps1 as [pn1 | pr1]; reflexivity. Qed.

  Lemma link_refl {s i r o : FinDecType} (b : bigraph s i r o) :
    let bij_i := bijection_id  in
    let bij_o := bijection_id  in
    let bij_e := bijection_id  in
    let bij_p := bijection_id  in
    bigraph_link_equality b b bij_i bij_o bij_e bij_p.
    Proof. unfold bigraph_link_equality. split.
      + (* bigraph_link_innername_equality *) 
      unfold bigraph_link_innername_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (li1 := get_link b (inl inner1)). 
      destruct li1 as [lo1 | le1]; reflexivity.
      + (* bigraph_link_port_equality *) 
      unfold bigraph_link_port_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (lp1 := get_link b (inr p1)). 
      destruct lp1 as [lo1 | le1]; reflexivity. Qed.

  Theorem bigraph_equality_refl {s i r o : FinDecType} 
    (b : bigraph s i r o) :
    bigraph_equality b b.
    Proof.
    apply (BigEq' s i r o s i r o b b (bijection_id) (bijection_id) (bijection_id) (bijection_id) (bijection_id) (bijection_id) (bijection_id) (bijection_id)).   
    + apply arity_refl. 
    + apply control_refl.
    + apply parent_refl.
    + apply link_refl.
    Qed.

  Lemma arity_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    (bij_k : bijection (get_kind b1) (get_kind b2)) :
    bigraph_arity_equality b1 b2 (bij_k) -> bigraph_arity_equality b2 b1 (bijection_inv bij_k).
    Proof. 
      unfold bigraph_arity_equality. 
      intros H k2. simpl.
      set (k1 := bij_k.(backward (get_kind b1) (get_kind b2)) k2).
      specialize (H k1). 
      rewrite H. 
      unfold k1.
      rewrite <- (@fob_a_eq_a (get_kind b1) (get_kind b2) bij_k).
      reflexivity.
      Qed.

  Lemma control_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    (bij_n : bijection (get_node b1) (get_node b2))
    (bij_k : bijection (get_kind b1) (get_kind b2)) :
    bigraph_control_equality b1 b2 (bij_n) (bij_k) 
      -> bigraph_control_equality b2 b1 (bijection_inv bij_n) (bijection_inv bij_k).
    Proof.
    intros H.
    unfold bigraph_control_equality in *. intros n2. simpl.
    rewrite (bij_preserve_equality (bij_k)).
    rewrite H.
    rewrite <- (@fob_a_eq_a (get_kind b1) (get_kind b2) bij_k).
    rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
    reflexivity. Qed.

  Lemma parent_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    (bij_s : bijection s1 s2) 
    (bij_r : bijection r1 r2) 
    (bij_n : bijection (get_node b1) (get_node b2)) :
    bigraph_parent_equality b1 b2 bij_s bij_r bij_n -> 
      bigraph_parent_equality b2 b1 (bijection_inv bij_s) (bijection_inv bij_r)(bijection_inv bij_n).
    Proof.
    intros [Hn Hs].
    unfold bigraph_parent_equality in *.
    split.
    - (* bigraph_parent_node_equality *)
      unfold bigraph_parent_node_equality in *. simpl.
      intros n2. 
      set (p2n2 := get_parent b2 (inl n2)).
      destruct p2n2 as [pn2 | pr2] eqn:E;
      unfold p2n2 in E;
      set (n1 := backward (get_node b1) (get_node b2) bij_n n2);
      specialize (Hn n1);
      destruct (get_parent b1 (inl n1)) as [pn2' | pr2'] eqn:E';
      unfold n1 in Hn;
      rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n) in Hn;
      rewrite E in Hn.
      + (* p2 (n2) = n2' /\ p1 (bij n2) = n2' *)
        rewrite (bij_preserve_equality (bij_n)). 
        rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
        symmetry.
        apply Hn.
      + (* p2 (n2) = n2' /\ p1 (bij n2) = r2 : False *)
        apply Hn.
      + (* p2 (n2) = r2 /\ p1 (bij n2) = n2' : False *)
        apply Hn.
      + (* p2 (n2) = r2 /\ p1 (bij n2) = r2 *)
        rewrite (bij_preserve_equality (bij_r)). 
        rewrite <- (@fob_a_eq_a r1 r2 bij_r).
        symmetry. 
        apply Hn.
    - (* bigraph_parent_site_equality *)
      unfold bigraph_parent_site_equality in *. simpl.
      intros site2.
      set (p2s2 := get_parent b2 (inr site2)).
      destruct p2s2 as [p2s2_n | p2s2_r] eqn:E;
      unfold p2s2 in E;
      set (site1 := backward s1 s2 bij_s site2);
      specialize (Hs site1);
      destruct (get_parent b1 (inr site1)) as [psn | psr] eqn:E';
      unfold site1 in Hs;
      rewrite <- (@fob_a_eq_a s1 s2 bij_s) in Hs;
      rewrite E in Hs.
      + (* p2 (s2) = n2 /\ p1 (bij s2) = n2 *)
        rewrite (bij_preserve_equality (bij_n)). 
        rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
        symmetry. apply Hs.
      + (* p2 (s2) = n2 /\ p1 (bij s2) = r2 : False *)
        apply Hs.
      + (* p2 (s2) = r2 /\ p1 (bij s2) = n2 : False *)
        apply Hs.
      + (* p2 (s2) = r2 /\ p1 (bij s2) = r2 *)
        rewrite (bij_preserve_equality (bij_r)). 
        rewrite <- (@fob_a_eq_a r1 r2 bij_r).
        symmetry. 
        apply Hs.
    Qed.


  Lemma link_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    (bij_i : bijection i1 i2)
    (bij_o : bijection o1 o2)
    (bij_e : bijection (get_edge b1) (get_edge b2))
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) :
    bigraph_link_equality b1 b2 bij_i bij_o bij_e bij_p -> 
      bigraph_link_equality b2 b1 (bijection_inv bij_i) (bijection_inv bij_o) (bijection_inv bij_e) (bijection_inv bij_p).
    Proof.
    intros [Hi Hp].
    unfold bigraph_link_equality in *.
    split.
    - unfold bigraph_link_innername_equality in *. simpl.
      intros inner2.
      set (l2i2 := get_link b2 (inl inner2)).
      destruct l2i2 as [l2p_o | l2p_i] eqn:E;
      unfold l2i2 in E;
      set (inner1 := backward i1 i2 bij_i inner2);
      specialize (Hi inner1);
      destruct (get_link b1 (inl inner1)) as [l1i_o | l1i_e] eqn:E';
      unfold inner1 in Hi;
      rewrite <- (@fob_a_eq_a i1 i2 bij_i) in Hi;
      rewrite E in Hi.
      + (* l2 (i2) = o2 /\ l1 (bij i2) = o2 *)
        rewrite (bij_preserve_equality (bij_o)). 
        rewrite <- (@fob_a_eq_a o1 o2 bij_o).
        symmetry. apply Hi.
      + (* l2 (i2) = o2 /\ l1 (bij i2) = e2 : False *)
        apply Hi.
      + (* l2 (i2) = e2 /\ l1 (bij p2) = o2 : False *)
        apply Hi.
      + (* l2 (i2) = e2 /\ l1 (bij p2) = e2 *)
        rewrite (bij_preserve_equality (bij_e)). 
        rewrite <- (@fob_a_eq_a (get_edge b1) (get_edge b2) bij_e).
        symmetry. apply Hi.
    - unfold bigraph_link_port_equality in *. simpl.
      intros port. 
      set (l2p := get_link b2 (inr port)).
      destruct l2p as [l2p_o | l2p_i] eqn:E;
      unfold l2p in E;
      set (p1 := backward (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p port);
      specialize (Hp p1);
      destruct (get_link b1 (inr p1)) as [l1p_o | l1p_e] eqn:E';
      unfold p1 in Hp;
      rewrite <- (@fob_a_eq_a (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p) in Hp;
      rewrite E in Hp.
      + (* l2 (p2) = o2 /\ l1 (bij p2) = o2 *)
        rewrite (bij_preserve_equality (bij_o)). 
        rewrite <- (@fob_a_eq_a o1 o2 bij_o).
        symmetry. apply Hp.
      + (* l2 (p2) = o2 /\ l1 (bij p2) = p2 : False *)
        apply Hp.
      + (* l2 (p2) = o2 /\ l1 (bij p2) = p2 : False *)
        apply Hp.
      + (* l2 (p2) = o2 /\ l1 (bij p2) = o2 *)
        rewrite (bij_preserve_equality (bij_e)). 
        rewrite <- (@fob_a_eq_a (get_edge b1) (get_edge b2) bij_e).
        symmetry. apply Hp.
    Qed.
  
  Theorem bigraph_equality_sym {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    bigraph_equality b1 b2
        -> bigraph_equality b2 b1.
    Proof.
      intros H. inversion H.
      apply (BigEq' s2 i2 r2 o2 s1 i1 r1 o1 b2 b1 (bijection_inv bij_s) (bijection_inv bij_i) (bijection_inv bij_r) (bijection_inv bij_o) (bijection_inv bij_n) (bijection_inv bij_e) (bijection_inv bij_k) (bijection_inv bij_p)).
      + apply arity_sym. apply big_arity_eq.
      + apply control_sym. apply big_control_eq.
      + apply parent_sym. apply big_parent_eq.
      + apply link_sym. apply big_link_eq.
      Qed.

  Lemma arity_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) 
    (bij_k12 : bijection (get_kind b1) (get_kind b2)) 
    (bij_k23 : bijection (get_kind b2) (get_kind b3)):
    bigraph_arity_equality b1 b2 (bij_k12) -> 
      bigraph_arity_equality b2 b3 (bij_k23) ->
        bigraph_arity_equality b1 b3 (bij_k23 <O> bij_k12).
    Proof. unfold bigraph_arity_equality. intros H1 H2 k1.
    simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

  Lemma control_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
    (bij_n12 : bijection (get_node b1) (get_node b2)) 
    (bij_n23 : bijection (get_node b2) (get_node b3)) 
    (bij_k12 : bijection (get_kind b1) (get_kind b2)) 
    (bij_k23 : bijection (get_kind b2) (get_kind b3)):
    bigraph_control_equality b1 b2 (bij_n12) (bij_k12) -> 
      bigraph_control_equality b2 b3 (bij_n23) (bij_k23) ->
        bigraph_control_equality b1 b3 (bij_n23 <O> bij_n12) (bij_k23 <O> bij_k12).
    Proof. unfold bigraph_control_equality. intros H1 H2 n1.
    simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

  Lemma parent_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
    (bij_s12 : bijection s1 s2) 
    (bij_s23 : bijection s2 s3)
    (bij_r12 : bijection r1 r2) 
    (bij_r23 : bijection r2 r3)
    (bij_n12 : bijection (get_node b1) (get_node b2)) 
    (bij_n23 : bijection (get_node b2) (get_node b3)) :
    bigraph_parent_equality b1 b2 bij_s12 bij_r12 (bij_n12) -> 
      bigraph_parent_equality b2 b3 bij_s23 bij_r23 (bij_n23) ->
        bigraph_parent_equality b1 b3 (bij_s23 <O> bij_s12) (bij_r23 <O> bij_r12) (bij_n23 <O> bij_n12).
    Proof. 
      unfold bigraph_parent_equality.
      intros [H12n H12s] [H23n H23s].
      split.
      - unfold bigraph_parent_node_equality in *. 
        intros n1. simpl.
        specialize (H12n n1).
        unfold funcomp. 
        set (p1n1 := get_parent b1 (inl n1)).
        destruct p1n1 as [p1n1_n | p1n1_r] eqn:E;
        unfold p1n1 in E;
        rewrite E in H12n;
        set (n2 := forward (get_node b1) (get_node b2) bij_n12 n1);  
        fold n2 in H12n;
        specialize (H23n n2);
        set (p2n2 := get_parent b2 (inl n2));
        fold p2n2 in H12n;
        destruct p2n2 as [p2n2_n | p2n2_r] eqn:E' in H12n;
        unfold p2n2 in E';
        rewrite E' in H23n;
        destruct (get_parent b3 (inl (forward (get_node b2) (get_node b3) bij_n23 n2))) as [p3n3_n | p3n3_r]. 
        + rewrite H12n. rewrite H23n. reflexivity.
        + apply H23n.
        + exfalso. apply H23n. 
        + apply H12n.
        + apply H12n.
        + exfalso. apply H23n.
        + apply H23n.  
        + rewrite H12n. rewrite H23n. reflexivity.
      - unfold bigraph_parent_site_equality in *. 
        intros site1. simpl.
        specialize (H12s site1).
        unfold funcomp. 
        set (p1s := get_parent b1 (inr site1)).
        destruct p1s as [p1s_n | p1s_r] eqn:E;
        unfold p1s in E; 
        rewrite E in H12s; 
        set (site2 := forward s1 s2 bij_s12 site1);
        fold site2 in H12s;
        specialize (H23s site2);
        set (p2s2 := get_parent b2 (inr site2));
        fold p2s2 in H12s;
        destruct p2s2 as [p2s_n | p2s_r] eqn:E' in H12s;
        unfold p2s2 in E'; 
        rewrite E' in H23s;
        destruct (get_parent b3 (inr (forward s2 s3 bij_s23 site2))) as [p3s_n | p3s_r].
        + rewrite H12s. rewrite H23s. reflexivity.
        + apply H23s.
        + exfalso. apply H23s. 
        + apply H12s.
        + apply H12s.
        + exfalso. apply H23s.
        + apply H23s.  
        + rewrite H12s. rewrite H23s. reflexivity.
      Qed.

  Lemma link_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3)
    (bij_i12 : bijection i1 i2) 
    (bij_i23 : bijection i2 i3) 
    (bij_o12 : bijection o1 o2) 
    (bij_o23 : bijection o2 o3) 
    (bij_e12 : bijection (get_edge b1) (get_edge b2)) 
    (bij_e23 : bijection (get_edge b2) (get_edge b3)) 
    (bij_p12 : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) 
    (bij_p23 : bijection (Port (get_node b2) (get_control b2) (get_arity b2)) (Port (get_node b3) (get_control b3) (get_arity b3))):
    bigraph_link_equality b1 b2 bij_i12 bij_o12 (bij_e12) (bij_p12) -> 
    bigraph_link_equality b2 b3 bij_i23 bij_o23 (bij_e23) (bij_p23) ->
    bigraph_link_equality b1 b3 (bij_i23 <O> bij_i12) (bij_o23 <O> bij_o12) (bij_e23 <O> bij_e12) (bij_p23 <O> bij_p12).
    Proof. 
      unfold bigraph_link_equality. intros [H12i H12p] [H23i H23p].
      split.
      - unfold bigraph_link_innername_equality in *. 
        intros inner1. simpl.
        specialize (H12i inner1).
        unfold funcomp. 
        set (l1i := get_link b1 (inl inner1)).
        destruct l1i as [l1i_o | l1i_e] eqn:E;
        unfold l1i in E;
        rewrite E in H12i;
        set (inner2 := forward i1 i2 bij_i12 inner1);
        specialize (H23i inner2);
        set (inner3 := forward i2 i3 bij_i23 inner2);
        fold inner2 in H12i;
        fold inner3 in H23i;
        set (l2i := get_link b2 (inl inner2));
        fold l2i in H12i;
        destruct l2i as [l2i_o | l2i_e] eqn:E' in H12i;
        unfold l2i in E'; 
        rewrite E' in H23i;
        destruct (get_link b3 (inl inner3)) as [l3i_o | l3i_e].
        + rewrite H12i. rewrite H23i. reflexivity.
        + apply H23i.
        + exfalso. apply H23i. 
        + apply H12i.
        + apply H12i.
        + exfalso. apply H23i.
        + apply H23i.  
        + rewrite H12i. rewrite H23i. reflexivity.
      - unfold bigraph_link_port_equality in *. intros p1. simpl.  
        specialize (H12p p1).
        unfold funcomp. 
        set (l1p := get_link b1 (inr p1)).
        destruct l1p as [l1p_n | l1p_r] eqn:E;
        unfold l1p in E;
        rewrite E in H12p; 
        set (p2 := forward (Port (get_node b1) (get_control b1) (get_arity b1))
        (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p12 p1);
        specialize (H23p p2);
        set (p3 := forward (Port (get_node b2) (get_control b2) (get_arity b2))
        (Port (get_node b3) (get_control b3) (get_arity b3)) bij_p23 p2);
        fold p2 in H12p;
        fold p3 in H23p;
        set (l2p2 := get_link b2 (inr p2));
        fold l2p2 in H12p;
        destruct l2p2 as [l2p2_o | l2p2_e] eqn:E' in H12p;
        unfold l2p2 in E'; 
        rewrite E' in H23p;
        destruct (get_link b3 (inr p3)).
        + rewrite H12p. rewrite H23p. reflexivity.
        + apply H23p.
        + exfalso. apply H23p. 
        + apply H12p.
        + apply H12p.
        + exfalso. apply H23p.
        + apply H23p.  
        + rewrite H12p. rewrite H23p. reflexivity.
      Qed.


  Theorem bigraph_equality_trans {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}  
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
      bigraph_equality b1 b2
        -> bigraph_equality b2 b3  
          -> bigraph_equality b1 b3.
    Proof.
      intros H12 H23. inversion H12. inversion H23.
      apply (BigEq' s1 i1 r1 o1 s3 i3 r3 o3 b1 b3 (bij_s0 <O> bij_s) (bij_i0 <O> bij_i) (bij_r0 <O> bij_r) (bij_o0 <O> bij_o) (bij_n0 <O> bij_n) (bij_e0 <O> bij_e) (bij_k0 <O> bij_k) (bij_p0 <O> bij_p)).
      + apply arity_trans. apply big_arity_eq. apply big_arity_eq0.
      + apply control_trans. apply big_control_eq. apply big_control_eq0.
      + apply parent_trans. apply big_parent_eq. apply big_parent_eq0.
      + apply link_trans. apply big_link_eq. apply big_link_eq0.
      Qed.

(** ** On the packed type 
The issue with the previous relation is that a parametric relation asks for two 
objects of the exact same Type and our equality is heterogeneous. The solution we 
will implement is to create a "packed bigraph" Type that will hold the interfaces 
inside of it. This is a WIP. *)
Record bigraph_packed : Type :=
  {
  s: FinDecType;
  i: FinDecType;
  r: FinDecType;
  o: FinDecType;
  big : bigraph s i r o
  }. 
(* TODO *)
  (* Add Parametric Relation: (bigraph_packed) (bigraph_equality)
      reflexivity proved by (bigraph_equality_refl)
      symmetry proved by (bigraph_equality_sym)
      transitivity proved by (bigraph_equality_trans)
        as bigraph_equality_rel. *)
End EquivalenceIsRelation.

(** * Disjoint juxtaposition
This section deals with the operation of disjoint juxtaposition. This is the act
of putting two bigraphs with disjoint interfaces "next" to one another. 
After the definition, we prove associativity and commutativity of dis_juxtaposition *)
Section DisjointJuxtaposition.
  (* cannot generalise NoDup_map to injective functions bc one maps on la the other on lb *)
  Lemma NoDup_map_inl {A B : Type} (la : list A) (lb : list B) :
    NoDup la -> NoDup (map (@inl A B) la).
    Proof.
      intro Hla.
      induction la as [| a la' IH].
      - constructor.
      - apply Injective_map_NoDup. 
        + unfold Injective.
          intros. inversion H. reflexivity.
        + apply Hla.      
    Qed.

  Lemma NoDup_map_inr {A B : Type} (la : list A) (lb : list B) :
    NoDup lb -> NoDup (map (@inr A B) lb).
    Proof.
      intro Hlb.
      induction lb as [| b lb' IH].
      - constructor.
      - apply Injective_map_NoDup. 
        + unfold Injective.
          intros. inversion H. reflexivity.
        + apply Hlb.      
    Qed. 

  Theorem noDup_app {A: Type} : forall (l:list A) (l':list A),
    (forall x, In x l -> ~ In x l') -> NoDup l -> NoDup l' -> NoDup (l ++ l').
    Proof.
      intros l l' H ndl. induction ndl ; intros ndl'.
      - auto.
      - simpl. apply NoDup_cons_iff.
        split.  
        + intros H1. apply (H x) ; simpl ; auto.
          apply in_app_or in H1 ; destruct H1 ; auto. 
          contradiction.
        + apply IHndl ; auto.
          intros x' H1. apply H. simpl. auto.
      Qed.
    
  Theorem noDup_merge {A B: Type}: forall (la: list A) (lb: list B), 
    NoDup la -> NoDup lb -> NoDup (merge la lb).
    Proof.
        intros la lb Hla Hlb.
        unfold merge. 
        apply noDup_app.
        - intros [a | b] Ha Hb. 
          + apply in_map_iff in Hb.
            destruct Hb as [b [H1 H2]]. discriminate H1.
          + apply in_map_iff in Ha.
          destruct Ha as [a [H1 H2]]. discriminate H1.
        - apply NoDup_map_inl; assumption. 
        - apply NoDup_map_inr; assumption. 
    Qed. 

  Theorem full_merge {A B: Type}: forall (la: list A) (lb: list B), Full la -> Full lb -> Full (merge la lb).
    Proof. intros la lb fa fb. unfold Full. destruct a as [a | b].
      - unfold merge. apply in_or_app. left. apply in_map. unfold Full in fa. apply fa.
      - unfold merge. apply in_or_app. right. apply in_map. unfold Full in fb. apply fb. 
    Qed.

  Theorem listing_merge {A B : Type}: forall (la: list A) (lb: list B), Listing la -> Listing lb -> Listing (merge la lb).
    Proof.
    intros la lb [nda fa] [ndb fb]. split.
    -   apply noDup_merge ; auto. 
    -   apply full_merge ; auto. Qed. 

  Lemma finite_sum {A B : Type} (fa : finite A) (fb : finite B) : finite (A + B).
    Proof. 
      destruct fa as [la Ha]. 
      destruct fb as [lb Hb].
      unfold finite. exists (merge la lb). apply listing_merge; auto. 
    Qed.
  Lemma EqDec_sum {A B : Type} (ea : EqDec A) (eb : EqDec B) : EqDec (A + B).
    Proof. 
      unfold EqDec in *. intros. destruct x as [xa | xb]; destruct y as [ya | yb].
        - destruct (ea xa ya). 
          + left. rewrite e. reflexivity. 
          + right. intro contra. congruence.  
        - right. intros contra. congruence.
        - right. intros contra. congruence. 
        - destruct (eb xb yb).
          + left. rewrite e. reflexivity. 
          + right. intro contra. congruence. 
    Qed.

  Definition sum_FinDecType (A B : FinDecType) : FinDecType :=
    {|
      type := A + B ;
      dec_type := EqDec_sum (@dec_type A) (@dec_type B);
      finite_type := finite_sum (@finite_type A) (@finite_type B)
    |}.

  Notation "A '+++' B" := (sum_FinDecType A B) (at level 50, left associativity).


  Definition mk_dis_arity {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    ((get_kind b1) + (get_kind b2)) -> nat :=
    let k1 := get_kind b1 in
    let k2 := get_kind b2 in
    let a1 := get_arity b1 in
    let a2 := get_arity b2 in
    let new_arity (k : k1+k2) : nat :=
      match k with
      | inl k1' => a1 k1'
      | inr k2' => a2 k2'
      end
    in new_arity.

  Definition mk_dis_control {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    ((get_node b1) + (get_node b2)) -> ((get_kind b1)+(get_kind b2))%type :=
    let c1 := get_control b1 in
    let c2 := get_control b2 in
    let n1 := get_node b1 in
    let n2 := get_node b2 in
    let k1 := get_kind b1 in
    let k2 := get_kind b2 in
    let new_control (n : n1+n2) : (k1+k2) := 
      match n with
      | inl n1' => inl (c1 n1')
      | inr n2' => inr (c2 n2')
      end 
    in new_control.


  Definition mk_dis_parent {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    ((@node s1 i1 r1 o1 b1) +++ (@node s2 i2 r2 o2 b2)) + 
      (s1 +++ s2) 
        -> ((@node s1 i1 r1 o1 b1) +++ (@node s2 i2 r2 o2 b2)) + 
        (r1 +++ r2) :=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let n1pn2 := ((@node s1 i1 r1 o1 b1) +++ (@node s2 i2 r2 o2 b2)) in
    let s1ps2 := (s1 +++ s2) in 
    let r1pr2 := (r1 +++ r2) in 
    let new_parent (p : (n1pn2) + (s1ps2)) : (n1pn2) + (r1pr2) :=
      match p with
      | inl (inl n1) => match p1 (inl n1) with (* p1 : n1 + s1 -> n1 + r1 *)
                        | inl n1' => inl (inl n1')
                        | inr r1 => inr (inl r1)
                        end
      | inl (inr s2) => match p2 (inl s2) with
                        | inl n2' => inl (inr n2')
                        | inr r2 => inr (inr r2)
                        end
      | inr (inl s1) => match p1 (inr s1) with
                        | inl n1' => inl (inl n1')
                        | inr r1 => inr (inl r1)
                        end
      | inr (inr s2) => match p2 (inr s2) with
                        | inl n2' => inl (inr n2')
                        | inr r2 => inr (inr r2)
                        end
      end
    in new_parent.



  (* Makes two distincts sets of ports from a set of ports from 2 disjointed bigraphs *)
  Definition mk_dis_port {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
    (p:Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2)) :
      Port (get_node b1) (get_control b1) (get_arity b1) +
      Port (get_node b2) (get_control b2) (get_arity b2).
        Proof. 
          destruct p as [vi12 P12].
          destruct vi12 as [[n1 | n2] i12]. 
          - left. 
            unfold mk_dis_control in P12. 
            unfold mk_dis_arity in P12.   
            unfold Port. 
            exists (n1, i12). 
            apply P12.  
          - right. 
            unfold mk_dis_control in P12.   
            unfold mk_dis_arity in P12.   
            unfold Port. 
            exists (n2,i12). 
            apply P12. 
        Defined.

  Definition mk_new_link {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    (i1 +++ i2)  + 
    Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2) 
      -> (o1 +++ o2) + 
        ((@edge s1 i1 r1 o1 b1) +++ (@edge s2 i2 r2 o2 b2)) :=
      let n1 := get_node b1 in
      let n2 := get_node b2 in
      let c := mk_dis_control b1 b2 in
      let a := mk_dis_arity b1 b2 in
      let p := Port (n1 + n2) c a in
      let e1 := get_edge b1 in
      let e2 := get_edge b2 in
      let l1 := get_link b1 in
      let l2 := get_link b2 in
      let new_link (ip : (i1 + i2) + p) : (o1 + o2) + (e1 + e2) :=
        match ip with 
        | inl (inl i1) => match l1 (inl i1) with (* l1 : i1 + p1 -> o1 + e1 *)
                          | inl o1 => inl (inl o1)
                          | inr e1 => inr (inl e1)
                          end
        | inl (inr i2) => match l2 (inl i2) with
                          | inl o2 => inl (inr o2)
                          | inr e2 => inr (inr e2)
                          end
        | inr p =>  let p' := mk_dis_port b1 b2 p in
                    match p' with 
                    | inl p1 => match (l1 (inr p1)) with 
                                | inl o1 => inl (inl o1)
                                | inr e1 => inr (inl e1)
                                end
                    | inr p2 => match (l2 (inr p2)) with 
                                | inl o2 => inl (inr o2)
                                | inr e2 => inr (inr e2)
                                end
                    end
        end
      in new_link.

  Theorem acyclic_dis_parent_left : forall {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (n1: get_node b1),
      Acc (fun n n' => (get_parent b1) (inl n) = inl n') n1 
        -> Acc (fun n n' => (mk_dis_parent b1 b2) (inl n) = inl n') (inl n1).
    Proof.
      intros.
      induction H as (n1, _, Hindn1').
      apply Acc_intro.
      destruct y as [n1' | n2'].
      + intro Hn1'.
        apply Hindn1'.
        simpl in Hn1'.
        unfold get_parent in *. 
        set (p1 := parent s1 i1 r1 o1 b1 (inl n1')). (*TODO FIXME*)
        fold p1 in Hn1'.
        change (p1 = inl n1).
        unfold get_node in n1. 
        destruct p1. 
        ++  injection Hn1'. intros. rewrite H. reflexivity. 
        ++  congruence.
      + intro Hn2'.
        simpl in Hn2'.
        unfold get_parent in *. 
        set (p2 := parent s2 i2 r2 o2 b2 (inl n2')).
        fold p2 in Hn2'.
        destruct p2; inversion Hn2'.
    Qed.

  Theorem acyclic_dis_parent_right : forall {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (n2: get_node b2),
      Acc (fun n n' => (get_parent b2) (inl n) = inl n') n2 
        -> Acc (fun n n' => (mk_dis_parent b1 b2) (inl n) = inl n') (inr n2).
    Proof.
      intros.
      induction H as (n2, _, Hindn2').
      apply Acc_intro.
      destruct y as [n1' | n2'].
      + intro Hn1'.
        simpl in Hn1'.
        unfold get_parent in *. 
        set (p1 := parent s1 i1 r1 o1 b1 (inl n1')).
        fold p1 in Hn1'.
        destruct p1 ; congruence.
      + intro Hn2'.
        apply Hindn2'.
        simpl in Hn2'.
        unfold get_parent in *. 
        set (p2 := parent s2 i2 r2 o2 b2 (inl n2')).
        fold p2 in Hn2'.
        change (p2 = inl n2).
        destruct p2. 
          ++ injection Hn2'. intros. rewrite H. reflexivity.
          ++ congruence.
    Qed.

  Definition mk_dis_ap {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    acyclic ((get_node b1) + (get_node b2)) (s1 + s2) (r1 + r2) (mk_dis_parent b1 b2).
    Proof.
    unfold acyclic ; intros [n1 | n2].
    - apply acyclic_dis_parent_left.
      destruct b1 ; auto.
    - apply acyclic_dis_parent_right.
      destruct b2 ; auto.
    Qed.
  
  
Definition dis_juxtaposition {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  : bigraph (s1 +++ s2) (i1 +++ i2) (r1 +++ r2) (o1 +++ o2) :=
{|
  node := (@node s1 i1 r1 o1 b1) +++ (@node s2 i2 r2 o2 b2);
  edge := (@edge s1 i1 r1 o1 b1) +++ (@edge s2 i2 r2 o2 b2);
  kind := (@kind s1 i1 r1 o1 b1) +++ (@kind s2 i2 r2 o2 b2);
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_dis_parent b1 b2 ; 
  link := mk_new_link b1 b2 ;
  ap := mk_dis_ap b1 b2 ;
|}.

Notation "b1 '||' b2" := (dis_juxtaposition b1 b2) (at level 50, left associativity).

(* THEOREMS ON DIS_JUXTAPOSITION *)
  Definition bij_assoc (A B C : Type) : bijection (A + B + C) (A + (B + C)).
    Proof. 
    apply (mkBijection 
            ((A + B) + C)   
            (A + (B + C))
            (fun abc => match abc with
              | inl ab => 
                match ab with 
                |inl a => inl a 
                |inr b => ((@inr A (B + C)) (@inl B C b))
                end
              | inr c => inr (inr c)
              end 
            )
            (fun abc => match abc with
              | inl a => inl (inl a)
              | inr bc => 
                match bc with 
                |inl b => inl (inr b) 
                |inr c => inr c
                end
              end 
            )).
    - unfold funcomp. apply functional_extensionality.
    intro abc. unfold id. destruct abc as [ a | [b | c]] ; auto.
    - unfold funcomp. apply functional_extensionality.
    intro abc. unfold id. destruct abc as [ [a | b] | c] ; auto. 
    Defined.


  Definition mk_port_l_assoc {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) 
    (p : Port (get_node (b1 || b2 || b3)) (get_control (b1 || b2 || b3)) (get_arity (b1 || b2 || b3)))
      : (Port (get_node (b1 || (b2 || b3))) (get_control (b1 || (b2 || b3))) (get_arity (b1 || (b2 || b3)))). 
    Proof.
      destruct p as [[[[n1 | n2] | n3] i123] P123];
      simpl in P123;
      unfold Port. 
      - exists (inl n1, i123). apply P123.
      - exists (inr (inl n2), i123). apply P123.
      - exists (inr (inr n3), i123). apply P123.
    Defined. 

  Definition mk_port_r_assoc {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) 
    (p : Port (get_node (b1 || (b2 || b3))) (get_control (b1 || (b2 || b3))) (get_arity (b1 || (b2 || b3))))
      : (Port (get_node (b1 || b2 || b3)) (get_control (b1 || b2 || b3)) (get_arity (b1 || b2 || b3))). 
    Proof.
      destruct p as [[[n1 | [n2 | n3]] i123] P123];
      simpl in P123;
      unfold Port. 
      - exists (inl (inl n1), i123). apply P123.
      - exists (inl (inr n2), i123). apply P123.
      - exists (inr n3, i123). apply P123.
    Defined. 

  Definition bijection_port_assoc {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3) :  
    bijection
      (Port (get_node (b1 || b2 || b3))
        (get_control (b1 || b2 || b3))
        (get_arity (b1 || b2 || b3)))
      (Port (get_node (b1 || (b2 || b3)))
        (get_control (b1 || (b2 || b3)))
        (get_arity (b1 || (b2 || b3)))).
    Proof.
      apply ( mkBijection 
          (Port (get_node (b1 || b2 || b3)) (get_control (b1 || b2 || b3)) (get_arity (b1 || b2 || b3)))
          (Port (get_node (b1 || (b2 || b3))) (get_control (b1 || (b2 || b3))) (get_arity (b1 || (b2 || b3))))
          (fun p => mk_port_l_assoc b1 b2 b3 p)
          (fun p => mk_port_r_assoc b1 b2 b3 p)
      ).
      - (* f <o> b = id *)
        apply functional_extensionality. intros p. unfold id. unfold funcomp.
        unfold mk_port_r_assoc. simpl.
        unfold mk_port_l_assoc. simpl.
        destruct p as [vi123 P123].
        destruct vi123 as [[n1 | [n2 | n3]] i123] eqn:E;
        simpl in P123; reflexivity.
      - (* b <o> f = id *)
        apply functional_extensionality. intros p. unfold id. unfold funcomp.
        unfold mk_port_r_assoc. simpl.
        unfold mk_port_l_assoc. simpl.
        destruct p as [vi123 P123].
        destruct vi123 as [[[n1 | n2] | n3] i123] eqn:E;
        simpl in P123; reflexivity.
      Defined.

  Lemma rearrange_match_outer1 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (outer1 : o1) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2 => inl (inl outer2)
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl (inr outer3)
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl outer2 => inl outer1 = outer2
    | inr _ => False
    end
      <->
        match p123 with
        | inl p1 =>
            match get_link b1 (inr p1) with
            | inl outer1' => @inl o1 (o2+o3) outer1 = inl outer1'
            | inr e1 => False
            end
        | inr p23 =>
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2 => inl outer1 = inr (@inl o2 o3 outer2)
                | inr e1 => False
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl outer1 = inr (@inr o2 o3 outer3)
                | inr e2 => False
                end
            end
        end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.
  
  Lemma rearrange_match_outer2 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (outer2 : o2) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2' => inl (inl outer2')
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl (inr outer3)
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl outer2' => inr (inl outer2) = outer2'
    | inr _ => False
    end
      <->
        match p123 with
        | inl p1 =>
            match get_link b1 (inr p1) with
            | inl outer1' => inr (@inl o2 o3 outer2) = inl outer1'
            | inr e1 => False
            end
        | inr p23 =>
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2' => @inr o1 (o2 + o3) (inl outer2) = inr (@inl o2 o3 outer2')
                | inr e1 => False
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => @inr o1 (o2 + o3) (inl outer2) = inr (@inr o2 o3 outer3)
                | inr e2 => False
                end
            end
        end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.
    
  Lemma rearrange_match_outer3 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (outer3 : o3) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2' => inl (inl outer2')
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3' => inl (inr outer3')
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl outer2' => inr (inr outer3) = outer2'
    | inr _ => False
    end
      <->
        match p123 with
        | inl p1 =>
            match get_link b1 (inr p1) with
            | inl outer1' => inr (@inr o2 o3 outer3) = inl outer1'
            | inr e1 => False
            end
        | inr p23 =>
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2' => @inr o1 (o2 + o3) (inr outer3) = inr (@inl o2 o3 outer2')
                | inr e1 => False
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3' => @inr o1 (o2 + o3) (inr outer3) = inr (@inr o2 o3 outer3')
                | inr e2 => False
                end
            end
        end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.


  Lemma rearrange_match_edge1 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (edge1 : get_edge b1) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2 => inl (inl outer2)
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl (inr outer3)
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl _ => False
    | inr edge2 => inl edge1 = edge2
    end
      <->
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => False
          | inr e1 => @inl (get_edge b1) ((get_edge b2) + (get_edge b3)) edge1 = inl e1
          end
      | inr p23 =>
          match mk_dis_port b2 b3 p23 with
          | inl p2 =>
              match get_link b2 (inr p2) with
              | inl outer2 => False
              | inr e1 =>  inl edge1 = inr (@inl (get_edge b2) ((get_edge b3)) e1)
              end
          | inr p3 =>
              match get_link b3 (inr p3) with
              | inl outer3 => False
              | inr e2 => inl edge1 = inr (@inr (get_edge b2) (get_edge b3) e2)
              end
          end
      end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.

  Lemma rearrange_match_edge2 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (edge2 : get_edge b2) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2 => inl (inl outer2)
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl (inr outer3)
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl _ => False
    | inr edge2' => inr (inl edge2) = edge2'
    end
      <->
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => False
          | inr e1 => inr (@inl (get_edge b2) (get_edge b3) edge2) = inl e1
          end
      | inr p23 =>
          match mk_dis_port b2 b3 p23 with
          | inl p2 =>
              match get_link b2 (inr p2) with
              | inl outer2 => False
              | inr e1 =>  @inr (get_edge b1) ((get_edge b2) + (get_edge b3)) (inl edge2) = inr (@inl (get_edge b2) ((get_edge b3)) e1)
              end
          | inr p3 =>
              match get_link b3 (inr p3) with
              | inl outer3 => False
              | inr e2 => @inr (get_edge b1) ((get_edge b2) + (get_edge b3)) (inl edge2) = inr (@inr (get_edge b2) (get_edge b3) e2)
              end
          end
      end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.

  Lemma rearrange_match_edge3 {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port (get_node b1) (get_control b1) (get_arity b1) + Port (get_node (b2 || b3)) (get_control (b2 || b3)) (get_arity (b2 || b3)))
    (edge3 : get_edge b3) :
    match
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inl outer1')
          | inr e1 => inr (inl e1)
          end
      | inr p23 =>
          match
            match mk_dis_port b2 b3 p23 with
            | inl p2 =>
                match get_link b2 (inr p2) with
                | inl outer2 => inl (inl outer2)
                | inr e1 => inr (inl e1)
                end
            | inr p3 =>
                match get_link b3 (inr p3) with
                | inl outer3 => inl (inr outer3)
                | inr e2 => inr (inr e2)
                end
            end
          with
          | inl outer23 => inl (inr outer23)
          | inr e23 => inr (inr e23)
          end
      end
    with
    | inl _ => False
    | inr edge2' => inr (inr edge3) = edge2'
    end
      <->
      match p123 with
      | inl p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => False
          | inr e1 => inr (@inr (get_edge b2) (get_edge b3) edge3) = inl e1
          end
      | inr p23 =>
          match mk_dis_port b2 b3 p23 with
          | inl p2 =>
              match get_link b2 (inr p2) with
              | inl outer2 => False
              | inr e1 =>  @inr (get_edge b1) ((get_edge b2) + (get_edge b3)) (inr edge3) = inr (@inl (get_edge b2) ((get_edge b3)) e1)
              end
          | inr p3 =>
              match get_link b3 (inr p3) with
              | inl outer3 => False
              | inr e2 => @inr (get_edge b1) ((get_edge b2) + (get_edge b3)) (inr edge3) = inr (@inr (get_edge b2) (get_edge b3) e2)
              end
          end
      end.
    Proof. split.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    - intros H. destruct p123 as [p1 | p23]. 
      + destruct (get_link b1 (inr p1)); apply H.
      + destruct (mk_dis_port b2 b3 p23) as [p2 | p3].
        ++ destruct (get_link b2 (inr p2)); apply H.
        ++ destruct (get_link b3 (inr p3)); apply H.
    Qed.

  Lemma dis_port_assoc_prop {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2} 
    {b3 : bigraph s3 i3 r3 o3}
    (p123 : Port
    (get_node (b1 || b2 || b3))
    (get_control
      (b1 || b2 || b3))
    (get_arity (b1 || b2 || b3)))
    (prop1 : Port (get_node b1) (get_control b1) (get_arity b1) -> Prop)
    (prop2 : Port (get_node b2) (get_control b2) (get_arity b2) -> Prop)
    (prop3 : Port (get_node b3) (get_control b3) (get_arity b3) -> Prop):
    match mk_dis_port (b1 || b2) b3 p123 with
      | inl p12 => 
        match mk_dis_port b1 b2 p12 with 
        | inl p1 => prop1 p1
        | inr p2 => prop2 p2
        end
      | inr p3 => prop3 p3
      end
        ->  match mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p123) with
            | inl p1 => prop1 p1
            | inr p23 => 
              match mk_dis_port b2 b3 p23 with 
              | inl p2 => prop2 p2
              | inr p3 => prop3 p3
              end
            end.
      Proof. intros H.
      destruct p123 as [[[[n1 | n2] | n3] i123] P123];
      simpl in P123; 
      unfold mk_dis_port in H.
      - unfold mk_port_l_assoc. unfold mk_dis_port. apply H.
      - unfold mk_port_l_assoc. unfold mk_dis_port. apply H.
      - unfold mk_port_l_assoc. unfold mk_dis_port. apply H.
      Qed.

  Lemma dis_juxtaposition_port_associative {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
    bigraph_link_port_equality 
      ((b1 || b2) || b3)  
      (b1 || (b2 || b3)) 
      (bij_assoc o1 o2 o3)
      (bij_assoc (get_edge b1) (get_edge b2) (get_edge b3))
      (bijection_port_assoc b1 b2 b3).
    Proof. intros b1 b2 b3.
    unfold bigraph_link_port_equality.
    intros p.
    simpl.
    destruct (mk_dis_port (b1 || b2) b3 p) as [p12 | p3] eqn:E.
    - destruct (mk_dis_port b1 b2 p12) as [p1 | p2] eqn:E'.
      + destruct (get_link b1 (inr p1)) as [outer1 | edge1] eqn:Eim1.
        ++ set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
          rewrite (rearrange_match_outer1 p123 outer1).
          set (prop1 := 
            fun p1 =>  match get_link b1 (inr p1) with
            | inl outer1' => inl outer1 = inl outer1'
            | inr _ => False
            end).
          set (prop2 := 
            fun p2 => match get_link b2 (inr p2) with
            | inl outer2 => inl outer1 = inr (inl outer2)
            | inr _ => False
            end).
          set (prop3 := 
            fun p3 => match get_link b3 (inr p3) with
            | inl outer3 => inl outer1 = inr (inr outer3)
            | inr _ => False
            end).
          apply (dis_port_assoc_prop p prop1 prop2 prop3).
          destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
            +++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
              ++++ unfold prop1. 
                inversion E. 
                rewrite <- H0 in E'. 
                rewrite E' in E'''.
                inversion E'''.
                rewrite <- H1.
                destruct (get_link b1 (inr p1)) as [outer1'|edge1'].
                  +++++ inversion Eim1. reflexivity.
                  +++++ inversion Eim1.
              ++++ unfold prop2. 
                inversion E. 
                rewrite <- H0 in E'. 
                rewrite E' in E'''.
                inversion E'''.
            +++ unfold prop3. 
            inversion E. 
        ++ set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
          rewrite (rearrange_match_edge1 p123 edge1).
          set (prop1 := 
            fun p1 =>  match get_link b1 (inr p1) with
            | inl _ => False
            | inr e1 => inl edge1 = inl e1
            end).
          set (prop2 := 
            fun p2 =>  match get_link b2 (inr p2) with
            | inl _ => False
            | inr e1 => inl edge1 = inr (inl e1)
            end).
          set (prop3 := 
            fun p3 => match get_link b3 (inr p3) with
            | inl _ => False
            | inr e2 => inl edge1 = inr (inr e2)
            end).
          apply (dis_port_assoc_prop p prop1 prop2 prop3).
          destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
            +++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
                ++++ unfold prop1. 
                  inversion E. 
                  rewrite <- H0 in E'. 
                  rewrite E' in E'''.
                  inversion E'''.
                  rewrite <- H1.
                  destruct (get_link b1 (inr p1)) as [outer1'|edge1'].
                    +++++ inversion Eim1.
                    +++++ inversion Eim1.  reflexivity.
                ++++ unfold prop2. 
                  inversion E. 
                  rewrite <- H0 in E'. 
                  rewrite E' in E'''.
                  inversion E'''.
              +++ unfold prop3. 
                inversion E. 
      + destruct (get_link b2 (inr p2)) as [outer2 | edge2] eqn:Eim1.
        ++ set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
        rewrite (rearrange_match_outer2 p123 outer2).
        set (prop1 := 
          fun p1 =>  match get_link b1 (inr p1) with
          | inl outer1' =>
              inr (inl outer2) = inl outer1'
          | inr _ => False
          end).
        set (prop2 := 
          fun p2 => match get_link b2 (inr p2) with
          | inl outer2' => inr (inl outer2) = inr (inl outer2')
          | inr _ => False
          end).
        set (prop3 := 
          fun p3 => match get_link b3 (inr p3) with
          | inl outer3 => inr (inl outer2) = inr (inr outer3)
          | inr _ => False
          end).
        apply (dis_port_assoc_prop p prop1 prop2 prop3).
        destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
          +++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
            ++++ unfold prop1. 
              inversion E. 
              rewrite <- H0 in E'. 
              rewrite E' in E'''.
              inversion E'''.
            ++++ unfold prop2. 
              inversion E. 
              rewrite <- H0 in E'. 
              rewrite E' in E'''.
              inversion E'''.
              rewrite <- H1.
              destruct (get_link b2 (inr p2)) as [outer2'|edge2'].
                +++++ inversion Eim1. reflexivity.
                +++++ inversion Eim1.
          +++ unfold prop3. 
          inversion E.
        ++ set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
        rewrite (rearrange_match_edge2 p123 edge2).
        set (prop1 := 
          fun p1 => match get_link b1 (inr p1) with
          | inl _ => False
          | inr e1 => inr (inl edge2) = inl e1
          end).
        set (prop2 := 
          fun p2 => match get_link b2 (inr p2) with
          | inl _ => False
          | inr e1 => inr (inl edge2) = inr (inl e1)
          end).
        set (prop3 := 
          fun p3 => match get_link b3 (inr p3) with
          | inl _ => False
          | inr e2 => inr (inl edge2) = inr (inr e2)
          end).
        apply (dis_port_assoc_prop p prop1 prop2 prop3).
        destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
          +++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
            ++++ unfold prop1. 
              inversion E. 
              rewrite <- H0 in E'. 
              rewrite E' in E'''.
              inversion E'''.
            ++++ unfold prop2. 
              inversion E. 
              rewrite <- H0 in E'. 
              rewrite E' in E'''.
              inversion E'''.
              rewrite <- H1.
              destruct (get_link b2 (inr p2)) as [outer2'|edge2'].
                +++++ inversion Eim1. 
                +++++ inversion Eim1. reflexivity.
          +++ unfold prop3. 
          inversion E.
    - destruct (get_link b3 (inr p3)) as [outer3 | edge3] eqn:Eim1.
      + set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
      rewrite (rearrange_match_outer3 p123 outer3).
      set (prop1 := 
        fun p1 =>  match get_link b1 (inr p1) with
        | inl outer1' => inr (inr outer3) = inl outer1'
        | inr _ => False
        end).
      set (prop2 := 
        fun p2 => match get_link b2 (inr p2) with
        | inl outer2' => inr (inr outer3) = inr (inl outer2')
        | inr _ => False
        end).
      set (prop3 := 
        fun p3 => match get_link b3 (inr p3) with
        | inl outer3' => inr (inr outer3) = inr (inr outer3')
        | inr _ => False
        end).
      apply (dis_port_assoc_prop p prop1 prop2 prop3).
      destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
        ++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
          +++ unfold prop1. 
            inversion E. 
          +++ unfold prop2. 
            inversion E. 
        ++ unfold prop3. 
        inversion E.
        destruct (get_link b3 (inr p3)) as [outer3'|edge3'].
          +++ inversion Eim1. reflexivity.
          +++ inversion Eim1.
      + set (p123 := mk_dis_port b1 (b2 || b3) (mk_port_l_assoc b1 b2 b3 p)).
      rewrite (rearrange_match_edge3 p123 edge3).
      set (prop1 := 
        fun p1 => match get_link b1 (inr p1) with
        | inl _ => False
        | inr e1 => inr (inr edge3) = inl e1
        end).
      set (prop2 := 
        fun p2 => match get_link b2 (inr p2) with
        | inl _ => False
        | inr e1 => inr (inr edge3) = inr (inl e1)
        end).
      set (prop3 := 
        fun p3 => match get_link b3 (inr p3) with
        | inl _ => False
        | inr e2 => inr (inr edge3) = inr (inr e2)
        end).
      apply (dis_port_assoc_prop p prop1 prop2 prop3).
      destruct (mk_dis_port (b1 || b2) b3 p) as [p12' | p3'] eqn:E''.
        ++ destruct (mk_dis_port b1 b2 p12') as [p1' | p2'] eqn:E'''.
          +++ unfold prop1. 
            inversion E. 
          +++ unfold prop2. 
            inversion E. 
        ++ unfold prop3.
          inversion E.
          destruct (get_link b3 (inr p3)) as [outer3'|edge3'].
            +++ inversion Eim1. 
            +++ inversion Eim1. reflexivity. 
    Qed.

  Theorem dis_juxtaposition_associative {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 : FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3),
    bigraph_equality ((b1 || b2) || b3) (b1 || (b2 || b3)).
    Proof. intros.
      apply (BigEq' 
      (s1 +++ s2 +++ s3)
      (i1 +++ i2 +++ i3) 
      (r1 +++ r2 +++ r3)
      (o1 +++ o2 +++ o3) 
      (s1 +++ (s2 +++ s3))
      (i1 +++ (i2 +++ i3))
      (r1 +++ (r2 +++ r3))
      (o1 +++ (o2 +++ o3))
      ((b1 || b2) || b3) 
      (b1 || (b2 || b3))
      (bij_assoc s1 s2 s3)
      (bij_assoc i1 i2 i3)
      (bij_assoc r1 r2 r3)
      (bij_assoc o1 o2 o3)
      (bij_assoc (get_node b1) (get_node b2) (get_node b3))
      (bij_assoc (get_edge b1) (get_edge b2) (get_edge b3))
      (bij_assoc (get_kind b1) (get_kind b2) (get_kind b3))
      (bijection_port_assoc b1 b2 b3)).
      - unfold bij_assoc. unfold bigraph_arity_equality. intros [[k1 | k2] | k3];
        simpl; unfold mk_dis_arity; simpl; unfold mk_dis_arity; reflexivity.
      - unfold bij_assoc. unfold bigraph_control_equality. intros [[n1 | n2] | n3];
        simpl; unfold mk_dis_control; simpl; unfold mk_dis_control; reflexivity.
      - unfold bigraph_parent_equality. split.
        + unfold bij_assoc. unfold bigraph_parent_node_equality. intros [[n1 | n2] | n3];
          simpl.
          ++ destruct (get_parent b1 (inl n1)); reflexivity.
          ++ destruct (get_parent b2 (inl n2)); reflexivity.
          ++ destruct (get_parent b3 (inl n3)); reflexivity.
        + unfold bij_assoc. unfold bigraph_parent_site_equality. intros [[site1 | site2] | site3];
          simpl.
          ++ destruct (get_parent b1 (inr site1)); reflexivity.
          ++ destruct (get_parent b2 (inr site2)); reflexivity.
          ++ destruct (get_parent b3 (inr site3)); reflexivity.
      - unfold bigraph_link_equality. split.
        + unfold bij_assoc. unfold bigraph_link_innername_equality. intros i123.
          simpl. 
          destruct (i123) as [[inner1 | inner2] | inner3] eqn:E.
          ++ destruct (get_link b1 (inl inner1)); reflexivity.
          ++ destruct (get_link b2 (inl inner2)); reflexivity.
          ++ destruct (get_link b3 (inl inner3)); reflexivity.
        + apply dis_juxtaposition_port_associative. 
    Qed. 

  Definition mk_port_commu {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2)
    (p : Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2)))
      : (Port (get_node (b2 || b1)) (get_control (b2 || b1)) (get_arity (b2 || b1))). 
    Proof.
      destruct p as [[[n1 | n2] i12] P12];
      simpl in P12;
      unfold Port. 
      - exists (inr n1, i12). apply P12.
      - exists (inl n2, i12). apply P12.
    Defined. 

  Definition bijection_port_commu {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :  
    bijection
      (Port (get_node (b1 || b2))
        (get_control (b1 || b2))
        (get_arity (b1 || b2)))
      (Port (get_node (b2 || b1))
        (get_control (b2 || b1))
        (get_arity (b2 || b1))).
    Proof. 
      apply ( mkBijection 
        (Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2)))
        (Port (get_node (b2 || b1)) (get_control (b2 || b1)) (get_arity (b2 || b1)))
        (fun p => mk_port_commu b1 b2 p)
        (fun p => mk_port_commu b2 b1 p)
      ).
      - (* f <o> b = id *)
        apply functional_extensionality. intros p. unfold id. unfold funcomp.
        unfold mk_port_commu. simpl.
        destruct p as [vi12 P12].
        destruct vi12 as [[n1 | n2] i12] eqn:E;
        simpl in P12; reflexivity.
      - (* b <o> f = id *)
        apply functional_extensionality. intros p. unfold id. unfold funcomp.
        unfold mk_port_commu. simpl.
        destruct p as [vi12 P12].
        destruct vi12 as [[n1 | n2] i12] eqn:E;
        simpl in P12; reflexivity.
    Defined.


    

    
  Lemma dis_port_commu_prop {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    {b1 : bigraph s1 i1 r1 o1} 
    {b2 : bigraph s2 i2 r2 o2}
    (p12 : Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2))) 
    (prop1 : Port (get_node b1) (get_control b1) (get_arity b1)-> Prop)
    (prop2 : Port (get_node b2) (get_control b2) (get_arity b2)-> Prop):
    match mk_dis_port b1 b2 p12 with
    | inl p1 => prop1 p1
    | inr p2 => prop2 p2
    end
      ->  match mk_dis_port b2 b1 (mk_port_commu b1 b2 p12) with
          | inl p2 => prop2 p2
          | inr p1 => prop1 p1
          end.
    Proof. intros H.
    destruct p12 as [[[n1 | n2] i12] P12];
    simpl in P12;
    unfold mk_dis_port in H.
    - unfold mk_port_commu. unfold mk_dis_port. apply H.
    - unfold mk_port_commu. unfold mk_dis_port. apply H.
    Qed.

  Lemma rearrange_match_outer {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2}
    (p21:Port (get_node b2) (get_control b2) (get_arity b2) + Port (get_node b1) (get_control b1) (get_arity b1)) 
    (outer1:o1):
    match
      match p21 with
      | inl p2 =>
          match get_link b2 (inr p2) with
          | inl outer2 => inl (inl outer2)
          | inr edge2 => inr (inl edge2)
          end
      | inr p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inr outer1')
          | inr edge1 => inr (inr edge1)
          end
      end
    with
    | inl outer2 => inr outer1 = outer2
    | inr _ => False
    end
      <-> 
        match p21 with
        | inl p2 =>
            match get_link b2 (inr p2) with
            | inl outer2 => inr outer1 = inl outer2
            | inr edge2 => False
            end
        | inr p1 =>
            match get_link b1 (inr p1) with
            | inl outer1' => @inr o2 o1 outer1 = inr outer1'
            | inr edge1 => False
            end
        end.
    Proof. split.
        - intros H. destruct p21 as [p2 | p1]. 
          + destruct (get_link b2 (inr p2)); apply H.
          + destruct (get_link b1 (inr p1)); apply H.
        - intros H. destruct p21 as [p2 | p1]. 
          + destruct (get_link b2 (inr p2)); apply H.
          + destruct (get_link b1 (inr p1)); apply H.
    Qed.

  Lemma rearrange_match_outer2' {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2}
    (p21:Port (get_node b2) (get_control b2) (get_arity b2) + Port (get_node b1) (get_control b1) (get_arity b1)) 
    (outer2:o2):
    match
      match p21 with
      | inl p2 =>
          match get_link b2 (inr p2) with
          | inl outer2 => inl (inl outer2)
          | inr edge2 => inr (inl edge2)
          end
      | inr p1 =>
          match get_link b1 (inr p1) with
          | inl outer1' => inl (inr outer1')
          | inr edge1 => inr (inr edge1)
          end
      end
    with
    | inl outer2' => inl outer2 = outer2'
    | inr _ => False
    end
      <-> 
        match p21 with
        | inl p2 =>
            match get_link b2 (inr p2) with
            | inl outer2' => @inl o2 o1 outer2 = inl outer2'
            | inr edge2 => False
            end
        | inr p1 =>
            match get_link b1 (inr p1) with
            | inl outer1 => @inl o2 o1 outer2 = inr outer1
            | inr edge1 => False
            end
        end.
        Proof. split.
        - intros H. destruct p21 as [p2 | p1]. 
          + destruct (get_link b2 (inr p2)); apply H.
          + destruct (get_link b1 (inr p1)); apply H.
        - intros H. destruct p21 as [p2 | p1]. 
          + destruct (get_link b2 (inr p2)); apply H.
          + destruct (get_link b1 (inr p1)); apply H.
    Qed.

  Lemma rearrange_match_edge {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2}
    (p21:Port (get_node b2) (get_control b2) (get_arity b2) + Port (get_node b1) (get_control b1) (get_arity b1)) 
    (edge1:get_edge b1):
    match
      match p21 with
      | inl p2 =>
          match get_link b2 (inr p2) with
          | inl o2 => inl (inl o2)
          | inr e2 => inr (inl e2)
          end
      | inr p1 =>
          match get_link b1 (inr p1) with
          | inl o1 => inl (inr o1)
          | inr e1 => inr (inr e1)
          end
      end
    with
    | inl _ => False
    | inr edge2 => inr edge1 = edge2
    end
      <-> 
        match p21 with
        | inl p2 =>
            match get_link b2 (inr p2) with
            | inl outer2 => False
            | inr edge2 => inl edge1 = inr edge2
            end
        | inr p1 =>
            match get_link b1 (inr p1) with
            | inl outer1 => False
            | inr edge1' => @inr (get_edge b2) (get_edge b1) edge1' = inr edge1
            end
        end.
      Proof. split.
      - intros H. destruct p21 as [p2 | p1]. 
        + destruct (get_link b2 (inr p2)). ++ apply H. ++ inversion H.  
        + destruct (get_link b1 (inr p1)). ++ apply H. ++ symmetry. apply H.
      - intros H. destruct p21 as [p2 | p1]. 
        + destruct (get_link b2 (inr p2)). ++ apply H. ++ inversion H.
        + destruct (get_link b1 (inr p1)). ++ apply H. ++ symmetry. apply H.
    Qed.

  Lemma rearrange_match_edge2' {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType}
    {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2}
    (p21:Port (get_node b2) (get_control b2) (get_arity b2) + Port (get_node b1) (get_control b1) (get_arity b1)) 
    (edge2:get_edge b2):
    match
      match p21 with
      | inl p2 =>
          match get_link b2 (inr p2) with
          | inl o2 => inl (inl o2)
          | inr e2 => inr (inl e2)
          end
      | inr p1 =>
          match get_link b1 (inr p1) with
          | inl o1 => inl (inr o1)
          | inr e1 => inr (inr e1)
          end
      end
    with
    | inl _ => False
    | inr edge2' => inl edge2 = edge2'
    end
      <-> 
        match p21 with
        | inl p2 =>
            match get_link b2 (inr p2) with
            | inl outer2 => False
            | inr edge2' => @inl (get_edge b2) (get_edge b1) edge2 = inl edge2'
            end
        | inr p1 =>
            match get_link b1 (inr p1) with
            | inl outer1 => False
            | inr edge1' => @inr (get_edge b2) (get_edge b1) edge1' = inl edge2
            end
        end.
      Proof. split.
      - intros H. destruct p21 as [p2 | p1]. 
        + destruct (get_link b2 (inr p2)). ++ apply H. ++ inversion H. reflexivity.  
        + destruct (get_link b1 (inr p1)). ++ apply H. ++ symmetry. apply H.
      - intros H. destruct p21 as [p2 | p1]. 
        + destruct (get_link b2 (inr p2)). ++ apply H. ++ inversion H. reflexivity.
        + destruct (get_link b1 (inr p1)). ++ apply H. ++ symmetry. apply H.
    Qed.


  Lemma dis_juxtaposition_port_commutative {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
    bigraph_link_port_equality 
      (b1 || b2)  
      (b2 || b1) 
      (bij_sum_comm)
      (bij_sum_comm)
      (bijection_port_commu b1 b2).
    Proof. intros b1 b2. unfold bigraph_link_port_equality.
      set (P12 := Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2))).
      set (P21 := Port (get_node (b2 || b1)) (get_control (b2 || b1)) (get_arity (b2 || b1))).
      intros p12.
      simpl.
      destruct (mk_dis_port b1 b2 p12) as [p1 | p2] eqn:E.
      - (*p1*)
        set (p21:= mk_dis_port b2 b1 (mk_port_commu b1 b2 p12)).
        destruct (get_link b1 (inr p1)) as [outer1 |edge1] eqn:E'.
        + (*link p1 = outer1 *)
        apply (rearrange_match_outer p21 outer1).
        set (prop1 := 
          fun p1 =>  match get_link b1 (inr p1) with
          | inl outer1' => inr outer1 = inr outer1'
          | inr _ => False
          end).
        set (prop2 := 
          fun p2 => match get_link b2 (inr p2) with
          | inl outer2 => inr outer1 = inl outer2
          | inr _ => False
          end).
        apply (dis_port_commu_prop p12 prop1 prop2).
        destruct (mk_dis_port b1 b2 p12) as [p1' | p2'].
          ++ unfold prop1.
          inversion E. destruct (get_link b1 (inr p1)) as [outer1' |edge1].
            +++ inversion E'. reflexivity.
            +++ inversion E'.
          ++ unfold prop2. inversion E.
        + 
        apply (rearrange_match_edge p21 edge1).
        set (prop1 := 
          fun p1 =>  match get_link b1 (inr p1) with
          | inl _ => False
          | inr edge1' => inr edge1' = inr edge1
          end).
        set (prop2 := 
          fun p2 => match get_link b2 (inr p2) with
          | inl _ => False
          | inr edge2 => inl edge1 = inr edge2
          end).
        apply (dis_port_commu_prop p12 prop1 prop2).
        destruct (mk_dis_port b1 b2 p12) as [p1' | p2'].
          ++ unfold prop1.
          inversion E. destruct (get_link b1 (inr p1)) as [outer1 |edge1'].
            +++ inversion E'.
            +++ inversion E'. inversion H1. reflexivity.
          ++ unfold prop2. inversion E.
      - (*p2*)
      set (p21:= mk_dis_port b2 b1 (mk_port_commu b1 b2 p12)).
      destruct (get_link b2 (inr p2)) as [outer2 |edge2] eqn:E'.
        + (*link p2 = outer2 *)
          apply (rearrange_match_outer2' p21 outer2).
          set (prop1 := 
            fun p1 =>  match get_link b1 (inr p1) with
            | inl outer1 => inl outer2 = inr outer1
            | inr _ => False
            end).
          set (prop2 := 
            fun p2 => match get_link b2 (inr p2) with
            | inl outer2' => inl outer2 = inl outer2'
            | inr _ => False
            end).
          apply (dis_port_commu_prop p12 prop1 prop2).
          destruct (mk_dis_port b1 b2 p12) as [p1' | p2'].
            ++ unfold prop1. inversion E. 
            ++ unfold prop2. inversion E.
            destruct (get_link b2 (inr p2)) as [outer2' |edge2].
              +++ inversion E'. reflexivity.
              +++ inversion E'.
          + 
          apply (rearrange_match_edge2' p21 edge2).
          set (prop1 := 
            fun p1 =>  match get_link b1 (inr p1) with
            | inl _ => False
            | inr edge1' => inr edge1' = inl edge2
            end).
          set (prop2 := 
            fun p2 => match get_link b2 (inr p2) with
            | inl _ => False
            | inr edge2' => inl edge2 = inl edge2'
            end).
          apply (dis_port_commu_prop p12 prop1 prop2).
          destruct (mk_dis_port b1 b2 p12) as [p1' | p2'].
            ++ unfold prop1. inversion E. 
            ++ unfold prop2. inversion E.            
            destruct (get_link b2 (inr p2)) as [outer2 |edge2'].
              +++ inversion E'.
              +++ inversion E'. inversion H1. reflexivity.
        Qed.

  Theorem dis_juxtaposition_commutative {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
    bigraph_equality (b1 || b2) (b2 || b1).
    Proof. 
      intros.
      apply (
        BigEq'
          (s1 +++ s2)
          (i1 +++ i2)
          (r1 +++ r2)
          (o1 +++ o2)
          (s2 +++ s1)
          (i2 +++ i1)
          (r2 +++ r1)
          (o2 +++ o1)
          (b1 || b2) 
          (b2 || b1)
          (@bij_sum_comm s1 s2)
          (bij_sum_comm)
          (bij_sum_comm)
          (bij_sum_comm)
          (bij_sum_comm)
          (bij_sum_comm)
          (bij_sum_comm)
          (bijection_port_commu b1 b2)
      ).
      - (* bigraph_arity_equality *)
        unfold bigraph_arity_equality. intros [k1 | k2];
        unfold bij_sum_comm; simpl; reflexivity.
      - (* bigraph_control_equality *)
        unfold bigraph_control_equality. intros [n1 | n2];
        unfold bij_sum_comm; simpl; reflexivity.
      - (* bigraph_parent_equality *)
        unfold bigraph_parent_equality. split.
        + unfold bigraph_parent_node_equality. intros n12.
          destruct n12 as [n1 | n2];
          unfold bij_sum_comm; simpl.
          ++ destruct (get_parent b1 (inl n1)); auto.
          ++ destruct (get_parent b2 (inl n2)); auto.
        + unfold bigraph_parent_site_equality. intros s12.
          destruct s12 as [site1 | site2];
          unfold bij_sum_comm; simpl.
          ++ destruct (get_parent b1 (inr site1)); auto.
          ++ destruct (get_parent b2 (inr site2)); auto.
      - (* bigraph_link_equality *)
        unfold bigraph_link_equality. split.
        + unfold bigraph_link_innername_equality. intros i12.
          destruct i12 as [inner1 | inner2];
          unfold bij_sum_comm; simpl.
          ++ destruct (get_link b1 (inl inner1)); auto.
          ++ destruct (get_link b2 (inl inner2)); auto.
        + apply dis_juxtaposition_port_commutative.
    Qed. 

End DisjointJuxtaposition.

(** * Composition
This section deals with the operation of composition. This is the act
of putting a bigraph inside another one. To do b1 o b2, the outerface of 
b2 needs to be the innerface of b1. WIP: or just a bijection? *)
Section CompositionBigraphs.
  Definition mk_comp_parent {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2))
     + s2 
     -> (sum_FinDecType (@node s1 i1 r1 o1 b1)  (@node s2 i2 s1 i1 b2)) 
        + r1 :=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let n1pn2 := (sum_FinDecType (@node s1 i1 r1 o1 b1)  (@node s2 i2 s1 i1 b2)) in
    let new_parent (p : (n1pn2) + s2) : (n1pn2) + r1 :=
      match p with
      | inl (inl n1) => match p1 (inl n1) with (* p1 : n1 + s1 -> n1 + r1 *)
                        | inl n1' => inl (inl n1')
                        | inr r1 => inr r1
                        end
      | inl (inr n2) => match p2 (inl n2) with (* p2 : n2 + s2 -> n2 + s1, r2 <=> s1 *)
                        | inl n2' => inl (inr n2')
                        | inr r2s1 => match p1 (inr r2s1) with (* p2 n2 : r2 *)
                                      | inl n1 => inl (inl n1)
                                      | inr r1 => inr r1
                                      end
                        end
      | inr s2 => match p2 (inr s2) with
                  | inl n2 => inl (inr n2)
                  | inr r2s1 => match p1 (inr r2s1) with (* p2 s2 : r2 *)
                                | inl n1' => inl (inl n1')
                                | inr r1 => inr r1
                                end
                  end
      end
    in new_parent.

  Definition mk_comp_link {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    i2 + Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2)  
    -> o1 + ((get_edge b1) + (get_edge b2)) :=
      let n1 := get_node b1 in
      let n2 := get_node b2 in
      let c := mk_dis_control b1 b2 in
      let p := Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2)  in
      let e1 := get_edge b1 in
      let e2 := get_edge b2 in
      let l1 := get_link b1 in
      let l2 := get_link b2 in
      let new_link (ip : i2 + p) : o1 + (e1 + e2) :=
        match ip with 
        | inr p =>  let p' := mk_dis_port b1 b2 p in
                    match p' with 
                    | inl p1 => match (l1 (inr p1)) with (* l1 : i1 + p1 -> o1 + e1 *)
                                | inl o1 => inl o1
                                | inr e1 => inr (inl e1)
                                end
                    | inr p2 => match (l2 (inr p2)) with (* l2 : i2 + p2 -> i1 + e2, o2 <=> i1 *)
                                | inl o2i1 => match (l1 (inl o2i1)) with (* l2 p2 : o2 *)
                                              | inl o1 => inl o1
                                              | inr e1 => inr (inl e1)
                                              end
                                | inr e2 => inr (inr e2)
                                end
                    end
        | inl i =>  match l2 (inl i) with
                    | inr e2 => inr (inr e2)
                    | inl o2i1 => match (l1 (inl o2i1)) with (* l2 i2 : o2 *)
                                  | inl o1 => inl o1
                                  | inr e1 => inr (inl e1)
                                  end
                    end
        end
      in new_link.


  Theorem acyclic_comp_parent_right : forall {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1)
    (n2 : get_node b2),
      Acc (fun n n' => (get_parent b2) (inl n) = inl n') n2 ->
      Acc (fun n n' => (mk_comp_parent b1 b2) (inl n) = inl n') (inr n2).
    Proof.
      intros.
      induction H as (n2, _, Hindn2').
      apply Acc_intro.
      unfold get_node in n2. 
      destruct y as [n1' | n2'].
      + intro Hn1'.
        unfold mk_comp_parent in Hn1'.
        unfold get_parent in *.
        set (p1 := parent s1 i1 r1 o1 b1 (inl n1')).
        fold p1 in Hn1'.
        destruct (p1); congruence. 
      + intro Hn2'.
        apply Hindn2'.
        unfold mk_comp_parent in Hn2'.
        unfold get_parent in *.
        set (p2 := parent s2 i2 s1 i1 b2 (inl n2')).
        fold p2 in Hn2'.
        change (p2 = inl n2).
        destruct p2.
        ++  injection Hn2'. intros. rewrite H. reflexivity.
        ++  set (p2' := parent s1 i1 r1 o1 b1).
            fold p2' in Hn2'. destruct p2'; congruence.
    Qed.  

  Theorem acyclic_comp_parent_left : forall {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1)
    (n1: get_node b1),
      Acc (fun n n' => (get_parent b1) (inl n) = inl n') n1 -> 
      acyclic (get_node b2) s2 s1 (get_parent b2) ->
      Acc (fun n n' => (mk_comp_parent b1 b2) (inl n) = inl n') (inl n1).
    Proof.
      intros s1 i1 r1 o1 s2 i2 b1 b2 n1 H a.
      induction H as (n1, _, Hindn1').
      apply Acc_intro.
      destruct y as [n1' | n2'].
      + intro Hn1'.
        apply Hindn1'.
        unfold mk_comp_parent in Hn1'.
        unfold get_parent in *.
        set (p1 := parent s1 i1 r1 o1 b1 (inl n1')).
        fold p1 in Hn1'.
        change (p1 = inl n1).
        destruct (p1). 
        ++ injection Hn1'. intros. rewrite H. reflexivity.
        ++ congruence.
      + intro Hn2'.
        apply acyclic_comp_parent_right.
        apply a.
    Qed.

  Definition mk_comp_ap {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    acyclic ((get_node b1) + (get_node b2)) s2 r1 (mk_comp_parent b1 b2).
    Proof. 
    unfold acyclic ; intros [n1 | n2].
    - apply acyclic_comp_parent_left.
      + destruct b1 ; auto.
      + destruct b2 ; auto.
    - apply acyclic_comp_parent_right ; destruct b2 ; auto.
    Qed.


Definition composition {s1 i1 r1 o1 s2 i2 : FinDecType} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) 
  : bigraph s2 i2 r1 o1 :=
{|
  node := sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2); (* TODO voir pourquoi +++ fonctionne pas ici *)
  edge := sum_FinDecType (@edge s1 i1 r1 o1 b1) (@edge s2 i2 s1 i1 b2);
  kind := sum_FinDecType (@kind s1 i1 r1 o1 b1) (@kind s2 i2 s1 i1 b2);
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_comp_parent b1 b2 ; 
  link := mk_comp_link b1 b2 ;
  ap := mk_comp_ap b1 b2 ;
|}.

Notation "b1 'o' b2" := (composition b1 b2) (at level 40, left associativity).
End CompositionBigraphs.


(* begin hide *)
(** * This section is a WIP. Mainly used to test stuff. *)
Section PlaygroundBigraphs.
  Lemma voidFinite : finite void.
  Proof. unfold finite. exists []. constructor. + constructor. + unfold Full.
  intros. destruct a. Qed.
  
  Lemma voidDec : EqDec void.
  Proof. unfold EqDec. intros. destruct x. Qed. 

  Definition voidFinDecType : FinDecType :=
    {|
      type := void ;
      finite_type := voidFinite;
      dec_type := voidDec
    |}.

  Lemma unitFinite : finite unit.
  Proof. unfold finite. exists [tt]. constructor. + apply NoDup_cons.
  ++ intros contra. contradiction.
  ++ constructor.
  + unfold Full.
  intros. destruct a. unfold In. auto. Qed.
  
  Lemma unitDec : EqDec unit.
  Proof. unfold EqDec. intros. destruct x. destruct y. left. auto. Qed. 

  Definition unitFinDecType : FinDecType :=
    {|
      type := unit ;
      finite_type := unitFinite;
      dec_type := unitDec
    |}.

  Example acyclic_unit : 
    acyclic unitFinDecType voidFinDecType unitFinDecType (fun _ => inl tt).
    Proof. unfold acyclic. intros. Admitted.
  Example vft : voidFinDecType. Proof. unfold voidFinDecType. simpl. Admitted. 
  (* Example my_control (n:FinDecType) : FinDecType. *)
  Example myUnitBigraph : bigraph voidFinDecType voidFinDecType unitFinDecType voidFinDecType :=
    {|
    node := unitFinDecType ;
    edge := voidFinDecType ;
    kind := unitFinDecType ;
    arity := (fun _ => 1) ;
    control := (fun _ => tt) ;
    parent := (fun _ => inl tt) ; 
    link := (fun _ => inr vft ) ;
    ap := acyclic_unit ;
  |}.

  (* Theorem ensemblefinite (N:nat) : finite {n:nat | n<N}.
  Proof. intros. unfold finite.  
  induction N.
  - exists []. unfold Listing. split. 
    + constructor.
    + unfold Full. intros. destruct a. contradiction l.
    
    constructor. edestruct NoDup. auto.  
  exists ([exist (fun n : nat => n < N) N (N<N)]). Admitted.

  Theorem ensembledec (N:nat) : EqDec {n:nat | n<N}.
  Proof.  unfold EqDec. intros. destruct x. destruct y. Admitted.

  Example site : FinDecType := 
  {|
    type := {n:nat | n<1} ;
    finite_type := ensemblefinite 1;
    dec_type := ensembledec 1
  |}.


  Example myInnername : Type := {n:nat | n<=0}.
  Example myRoot : Type := {n:nat | n<=0}.
  Example root0 : myRoot.
  Proof. unfold myRoot. exists 0. auto. Defined.
  Example myOutername : Type := {n:nat | n<=0}.
  Example outername0 : myOutername.
  Proof. unfold myOutername. exists 0. auto. Defined.

  Example myNode : Type := {n:nat | n<=1}.
  Example myEdge : Type := {n:nat | n<=1}.
  Example edge0 : myEdge.
  Proof. unfold myEdge. exists 0. auto. Defined.
  Example edge1 : myEdge.
  Proof. unfold myEdge. exists 1. auto. Defined.
  Example myKind : Type := {n:nat | n<=0}.

  Example myArity (k:myKind) : nat.
  Proof. exact 2.  Defined.
  Example myControl (n:myNode) : myKind. 
  Proof. unfold myKind. exists 0. auto. Defined.
  Example node0 : myNode.
  Proof. unfold myNode. exists 0. auto. Defined.
  Example node1 : myNode.
  Proof. unfold myNode. exists 1. auto. Defined.

  Theorem trivialxle1 : forall x:nat, x <= 1 -> x = 0 \/ x = 1.
  Proof. intros. induction x. 
  - left. auto.
  - assert (forall n:nat, S n <= 1 -> n = 0).
    + intros. inversion H0. ++ auto. ++ inversion H2.
    + apply (H0 x) in H. right. auto.
  Qed.

  Example fromnode0or1 : forall n:myNode, proj1_sig n = 0 \/ proj1_sig n = 1.
  Proof. destruct n. intros. unfold proj1_sig. 
  apply trivialxle1 in l. apply l. Qed.

  Example fromnode0or1' : forall n:myNode, n = node0 \/  n = node1.
  Proof. intros. destruct n. destruct x.
  Admitted.

  Example myParent : myNode + mySite -> myNode + myRoot.
  Proof. intros ns. 
  destruct ns as [n | s].
  - Admitted.

  (* Example myParent (ns : myNode + mySite) : myNode + myRoot :=
    match ns with
    | inl (exist _ n' prf) => 
      match n' with
        | 0 => inl node1
        | 1 => inr root0
      end
    | inr s => inl node0
    end.  *)

  Example myLink (ip: myInnername +  (Port myNode myControl myArity)) :
    myOutername + myEdge :=
    match ip with 
    | inl i => inr edge0
    | inr (exist _ ((exist _ n' prf'), idp) prf) => 
      match n',idp with
        | 0,0 => inr edge0 
        | 0,1 => inr edge1
        | 1,0 => inr edge1
        | _,_ => inl outername0
      end
    end.

  Lemma nat_le_dec : forall (n m : nat), {n <= m} + {~(n <= m)}.
  Proof. apply le_dec. Qed.

  Definition eq_nat_le_dec : forall (x y : {n : nat | n <= 1}), {x = y} + {x <> y}.
  Proof. intros. Search ({_ = _} + {_ <> _}).
    destruct x as [x Hx].
    destruct y as [y Hy].
    destruct (nat_le_dec x y) as [Hxy | Hxy].
    - destruct (nat_le_dec y x) as [Hyx | Hyx].
      + left. inversion Hx.
        ++ inversion Hy. Admitted.
        
  Example myNd : EqDec myNode.
  Proof. unfold myNode. unfold EqDec. auto. Admitted.
  Example myNf : finite myNode.
  Proof. unfold finite. unfold myNode. Admitted.
  Example myEd : EqDec myEdge.
  Proof. Admitted.
  Example myEf : finite myEdge.
  Proof. Admitted.

  Example myParent' (ns : myNode + mySite) : myNode + myRoot := 
  match ns with 
  | inl (exist _ 0 _) => inl node1
  | inl (exist _ 1 _) => inr root0
  | inr (exist _ 0 _) => inl node0
  | _ => inr root0
  end.


  Example myAp' : acyclic myNode mySite myRoot myParent'.
  Proof. unfold acyclic. intros. 
  apply Acc_intro.
  destruct y. Admitted.

  Example myAp : acyclic myNode mySite myRoot myParent.
  Proof. unfold acyclic. intros. destruct myParent.
  - left. exact node0. 
  - apply Acc_intro. intros. Admitted.

    
  Example myBigraph : bigraph mySite myInnername myRoot myOutername :=
    {|
    node := myNode ;
    edge := myEdge ;
    kind := myKind ;
    arity := myArity ;
    control := myControl ;
    parent := myParent ; 
    link := myLink ;
    ap := myAp ;
  |}. *)



End PlaygroundBigraphs.
(* end hide *)
End Bigraph.