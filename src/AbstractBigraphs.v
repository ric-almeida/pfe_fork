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



Module Bigraph.


Inductive void : Type := .

Definition merge {A B : Type} (la : list A) (lb : list B) : list (A + B) :=
  (map inl la) ++ (map inr lb).

Definition finite (A : Type) : Type := { l : list A | Listing l }.

Record FinDecType : Type :=
  {
    type : Type ;
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
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    kind : FinDecType ;
    arity : @type kind -> nat ;
    control : @type node -> @type kind ;
    parent : @type node + @type site -> @type node + @type root ; 
    link : @type innername + Port (@type node) control arity -> @type outername + @type edge; 
    ap : acyclic (@type node) (@type site) (@type root) parent ;
  }.

(* GETTERS *)
  Definition get_node {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  @type (node s i r o bg).
  Definition get_edge {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  @type (edge s i r o bg).
  Definition get_kind {s i r o : FinDecType} (bg : bigraph s i r o) : Type := 
  @type (kind s i r o bg).
  Definition get_arity {s i r o : FinDecType} (bg : bigraph s i r o) : 
  (get_kind bg) -> nat := 
  arity s i r o bg.
  Definition get_control {s i r o : FinDecType} (bg : bigraph s i r o) 
  : get_node bg -> (get_kind bg) :=
  @control s i r o bg.
  Definition get_parent {s i r o : FinDecType} (bg : bigraph s i r o) : 
  (get_node bg) + (@type s) -> (get_node bg) + (@type r) :=
  @parent s i r o bg.
  Definition get_link {s i r o : FinDecType} (bg : bigraph s i r o) : 
  (@type i) + Port (get_node bg) (get_control bg) (get_arity bg) -> (@type o) + get_edge bg :=
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
  EqDec (@type s) :=
  @dec_type s.
  Definition get_sf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (@type s) :=
  @finite_type s.
  Definition get_id {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (@type i) :=
  @dec_type i.
  Definition get_if {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (@type i) :=
  @finite_type i.
  Definition get_rd {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (@type r) :=
  @dec_type r.
  Definition get_rf {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (@type r) :=
  @finite_type r.
  Definition get_od {s i r o : FinDecType} (bg : bigraph s i r o) : 
  EqDec (@type o) :=
  @dec_type o.
  Definition get_of {s i r o : FinDecType} (bg : bigraph s i r o) : 
  finite (@type o) :=
  @finite_type o.
  Definition get_ap {s i r o : FinDecType} (bg : bigraph s i r o) : 
  acyclic (get_node bg) (@type s) (@type r) (get_parent bg) :=
  @ap s i r o bg.

(* Working on equivalence *)
  Definition bigraph_arity_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_k : bijection (get_kind b1) (get_kind b2)): Prop :=
      forall k1:get_kind b1, let k2 := bij_k.(forward (get_kind b1) (get_kind b2)) k1 in 
      get_arity b1 k1 = get_arity b2 k2.

  Definition bigraph_control_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2))
    (bij_k : bijection (get_kind b1) (get_kind b2)) : Prop :=
      forall n1:get_node b1, 
      let kind1 := get_control b1 n1 in
      let n2 := bij_n.(forward (get_node b1) (get_node b2)) n1 in 
      let kind2 := get_control b2 n2 in
      bij_k.(forward (get_kind b1) (get_kind b2)) kind1 = kind2.

  Definition bigraph_parent_site_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2)) : Prop :=
      forall site:(@type s), 
      match (get_parent b1 (inr site)),(get_parent b2 (inr site)) with
      | inr root1, inr root2  => root1 = root2
      | inl node1, inl node2  => bij_n.(forward (get_node b1) (get_node b2)) node1 = node2
      | _, _ => False
      end.

  Definition bigraph_parent_node_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2)): Prop :=
      forall n1:get_node b1, 
      let n2 := bij_n.(forward (get_node b1) (get_node b2)) n1 in 
      match (get_parent b1 (inl n1)),(get_parent b2 (inl n2)) with
      | inr root1, inr root2  => root1 = root2
      | inl node1, inl node2  => bij_n.(forward (get_node b1) (get_node b2)) node1 = node2
      | _, _ => False
      end.

  Definition bigraph_parent_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2)): Prop :=
    bigraph_parent_node_equality b1 b2 bij_n /\ bigraph_parent_site_equality b1 b2 bij_n.

  Definition bigraph_link_innername_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_e : bijection (get_edge b1) (get_edge b2)) : Prop :=
      forall inner:(@type i), 
      match (get_link b1 (inl inner)),(get_link b2 (inl inner)) with
      | inr edge1, inr edge2  => bij_e.(forward (get_edge b1) (get_edge b2)) edge1 = edge2
      | inl outer1, inl outer2  => outer1 = outer2
      | _, _ => False
      end.

  Definition bigraph_link_port_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) 
    (bij_e : bijection (get_edge b1) (get_edge b2)): Prop :=
      forall p1:(Port (get_node b1) (get_control b1) (get_arity b1)), 
      let p2 := bij_p.(forward (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) p1 in
      match (get_link b1 (inr p1)),(get_link b2 (inr p2)) with
      | inr edge1, inr edge2  => bij_e.(forward (get_edge b1) (get_edge b2)) edge1 = edge2
      | inl outer1, inl outer2  => outer1 = outer2
      | _, _ => False
      end.

  Definition bigraph_link_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_e : bijection (get_edge b1) (get_edge b2))
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) : Prop :=
    bigraph_link_innername_equality b1 b2 bij_e /\ bigraph_link_port_equality b1 b2 bij_p bij_e.

  Record bigraph_equality {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) : Prop :=
      BigEq 
      {
        bij_n : bijection (get_node b1) (get_node b2);
        bij_e : bijection (get_edge b1) (get_edge b2);
        bij_k : bijection (get_kind b1) (get_kind b2);
        bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)); 
        big_arity_eq : bigraph_arity_equality b1 b2 bij_k ; 
        big_control_eq : bigraph_control_equality b1 b2 bij_n bij_k ; 
        big_parent_eq : bigraph_parent_equality b1 b2 bij_n ;
        big_link_eq : bigraph_link_equality b1 b2 bij_e bij_p
      }.

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
    let bij_n := bijection_id  in
    bigraph_parent_equality b b bij_n.
    Proof. unfold bigraph_parent_equality. split. (* auto. *) 
      + unfold bigraph_parent_node_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (pn1 := get_parent b (inl n1)). 
      destruct pn1 as [pn1 | pr1]; reflexivity.
      + unfold bigraph_parent_site_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (ps1 := get_parent b (inr site)). 
      destruct ps1 as [pn1 | pr1]; reflexivity. Qed.

  Lemma link_refl {s i r o : FinDecType} (b : bigraph s i r o) :
    let bij_e := bijection_id  in
    let bij_p := bijection_id  in
    bigraph_link_equality b b bij_e bij_p.
    Proof. unfold bigraph_link_equality. split.
      + unfold bigraph_link_innername_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (li1 := get_link b (inl inner)). 
      destruct li1 as [lo1 | le1]; reflexivity.
      + unfold bigraph_link_port_equality. intros.
      unfold bijection_id. simpl. unfold id. 
      set (lp1 := get_link b (inr p1)). 
      destruct lp1 as [lo1 | le1]; reflexivity. Qed.



  Lemma bigraph_equality_refl' {s i r o : FinDecType} 
    (b : bigraph s i r o) :
    bigraph_equality b b.
    Proof.
    apply (BigEq s i r o b b (bijection_id) (bijection_id) (bijection_id) (bijection_id)).   
    + apply arity_refl. 
    + apply control_refl.
    + apply parent_refl.
    + apply link_refl.
    Qed.

  Lemma arity_sym {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_k : bijection (get_kind b1) (get_kind b2)) :
    bigraph_arity_equality b1 b2 (bij_k) -> bigraph_arity_equality b2 b1 (bijection_inv bij_k).
    Proof. unfold bigraph_arity_equality. intros H k2. 
    rewrite bijection_forward_inv_equals_backward.
    set (k2' := bij_k.(backward (get_kind b1) (get_kind b2)) k2). (*TODO need help to use fx_eq_by*)
    assert (k2 = forward (get_kind b1) (get_kind b2) bij_k k2').
    - change (k2 = forward (get_kind b1) (get_kind b2) bij_k (backward (get_kind b1)
    (get_kind b2) bij_k k2)). apply fob_a_eq_a.
    - rewrite H0. symmetry. apply H with (k1 := k2'). Qed.

  Lemma control_sym {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2))
    (bij_k : bijection (get_kind b1) (get_kind b2)) :
    bigraph_control_equality b1 b2 (bij_n) (bij_k) -> bigraph_control_equality b2 b1 (bijection_inv bij_n) (bijection_inv bij_k).
    Proof.
    intros H.
    unfold bigraph_control_equality in *. intros n2. simpl.
    rewrite (bij_preserve_equality (bij_k)).
    rewrite H.
    rewrite <- (@fob_a_eq_a (get_kind b1) (get_kind b2) bij_k).
    rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
    reflexivity. Qed.

  Lemma parent_sym {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_n : bijection (get_node b1) (get_node b2)) :
    bigraph_parent_equality b1 b2 (bij_n) -> bigraph_parent_equality b2 b1 (bijection_inv bij_n).
    Proof.
    intros [Hn Hs].
    unfold bigraph_parent_equality in *.
    split.
    - unfold bigraph_parent_node_equality in *. simpl.
      intros n2. 
      set (p2n2 := get_parent b2 (inl n2)).
      destruct p2n2 as [pn2 | pr2] eqn:E.
      + set (n1 := (inl (backward (get_node b1) (get_node b2) bij_n n2))).  
        destruct (get_parent b1 n1) as [pn2' | pr2'] eqn:E'.
        ++ rewrite (bij_preserve_equality (bij_n)). 
        rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n). Admitted.

    
  Lemma link_sym {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) 
    (bij_e : bijection (get_edge b1) (get_edge b2))
    (bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) :
    bigraph_link_equality b1 b2 (bij_e) (bij_p) -> bigraph_link_equality b2 b1 (bijection_inv bij_e) (bijection_inv bij_p).
    Proof.
    intros H.
    unfold bigraph_control_equality in *. simpl. Admitted.
  
  Lemma bigraph_equality_sym {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) :
    bigraph_equality b1 b2
        -> bigraph_equality b2 b1.
    Proof.
      intros H. inversion H.
      apply (BigEq s i r o b2 b1 (bijection_inv bij_n) (bijection_inv bij_e) (bijection_inv bij_k) (bijection_inv bij_p)).
      + apply arity_sym. apply big_arity_eq.
      + apply control_sym. apply big_control_eq.
      + apply parent_sym. apply big_parent_eq.
      + apply link_sym. apply big_link_eq.
      Qed.

  Lemma arity_trans {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
    (bij_k12 : bijection (get_kind b1) (get_kind b2)) 
    (bij_k23 : bijection (get_kind b2) (get_kind b3)):
    bigraph_arity_equality b1 b2 (bij_k12) -> 
      bigraph_arity_equality b2 b3 (bij_k23) ->
        bigraph_arity_equality b1 b3 (bij_k23 <O> bij_k12).
    Proof. unfold bigraph_arity_equality. intros H1 H2 k1.
    simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

  Lemma control_trans {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
    (bij_n12 : bijection (get_node b1) (get_node b2)) 
    (bij_n23 : bijection (get_node b2) (get_node b3)) 
    (bij_k12 : bijection (get_kind b1) (get_kind b2)) 
    (bij_k23 : bijection (get_kind b2) (get_kind b3)):
    bigraph_control_equality b1 b2 (bij_n12) (bij_k12) -> 
      bigraph_control_equality b2 b3 (bij_n23) (bij_k23) ->
        bigraph_control_equality b1 b3 (bij_n23 <O> bij_n12) (bij_k23 <O> bij_k12).
    Proof. unfold bigraph_control_equality. intros H1 H2 n1.
    simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

  Lemma parent_trans {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
    (bij_n12 : bijection (get_node b1) (get_node b2)) 
    (bij_n23 : bijection (get_node b2) (get_node b3)) :
    bigraph_parent_equality b1 b2 (bij_n12) -> 
      bigraph_parent_equality b2 b3 (bij_n23) ->
        bigraph_parent_equality b1 b3 (bij_n23 <O> bij_n12).
    Proof. unfold bigraph_parent_equality. intros [H1n H1s] [H2n H2s].
      split.
      - unfold bigraph_parent_node_equality in *. intros n1. simpl.      
        unfold funcomp. 
        destruct (get_parent b1 (inl n1)).
        + Admitted. 

  Lemma link_trans {s i r o : FinDecType}  
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
    (bij_e12 : bijection (get_edge b1) (get_edge b2)) 
    (bij_e23 : bijection (get_edge b2) (get_edge b3)) 
    (bij_p12 : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) 
    (bij_p23 : bijection (Port (get_node b2) (get_control b2) (get_arity b2)) (Port (get_node b3) (get_control b3) (get_arity b3))):
    bigraph_link_equality b1 b2 (bij_e12) (bij_p12) -> 
    bigraph_link_equality b2 b3 (bij_e23) (bij_p23) ->
    bigraph_link_equality b1 b3 (bij_e23 <O> bij_e12) (bij_p23 <O> bij_p12).
    Proof. Admitted. 
    (* unfold bigraph_control_equality. intros H1 H2 n1. *)
    (* simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed.  *)

  Lemma bigraph_equality_trans {s i r o : FinDecType} 
    (b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o):
      bigraph_equality b1 b2
        -> bigraph_equality b2 b3  
          -> bigraph_equality b1 b3.
    Proof.
      intros H12 H23. inversion H12. inversion H23.
      apply (BigEq s i r o b1 b3 (bij_n0 <O> bij_n) (bij_e0 <O> bij_e) (bij_k0 <O> bij_k) (bij_p0 <O> bij_p)).
      + apply arity_trans. apply big_arity_eq. apply big_arity_eq0.
      + apply control_trans. apply big_control_eq. apply big_control_eq0.
      + apply parent_trans. apply big_parent_eq. apply big_parent_eq0.
      + apply link_trans. apply big_link_eq. apply big_link_eq0.
      Qed.

(* MAKERS FOR DISJOINT JUXTAPOSITION   *)
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
      type := (@type A) + (@type B) ;
      dec_type := EqDec_sum (@dec_type A) (@dec_type B);
      finite_type := finite_sum (@finite_type A) (@finite_type B)
    |}.

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
    @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 r2 o2 b2)) + 
      @type (sum_FinDecType s1 s2) 
        -> @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 r2 o2 b2)) + 
        @type (sum_FinDecType r1 r2) :=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let n1pn2 := @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 r2 o2 b2)) in
    let s1ps2 := @type (sum_FinDecType s1 s2) in 
    let r1pr2 := @type (sum_FinDecType r1 r2) in 
    let new_parent (p : (n1pn2) + (s1ps2)) : (n1pn2) + (r1pr2) :=
      match p with
      | inl (inl n1) => match p1 (inl n1) with (* p1 : n1 + s1 -> n1 + r1 *)
                        | inl n1' => inl (inl n1')
                        | inr r1 => inr (inl r1)
                        end
      | inl (inr n2) => match p2 (inl n2) with
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
    @type (sum_FinDecType i1 i2)  + 
    Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2) 
      -> @type (sum_FinDecType o1 o2) + 
        @type (sum_FinDecType (@edge s1 i1 r1 o1 b1) (@edge s2 i2 r2 o2 b2)) :=
      let n1 := get_node b1 in
      let n2 := get_node b2 in
      let c := mk_dis_control b1 b2 in
      let a := mk_dis_arity b1 b2 in
      let p := Port (n1 + n2) c a in
      let e1 := get_edge b1 in
      let e2 := get_edge b2 in
      let l1 := get_link b1 in
      let l2 := get_link b2 in
      let new_link (ip : ((@type i1) + (@type i2)) + p) : ((@type o1) + (@type o2)) + (e1 + e2) :=
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
    acyclic ((get_node b1) + (get_node b2)) ((@type s1) + (@type s2)) ((@type r1) + (@type r2)) (mk_dis_parent b1 b2).
    Proof.
    unfold acyclic ; intros [n1 | n2].
    - apply acyclic_dis_parent_left.
      destruct b1 ; auto.
    - apply acyclic_dis_parent_right.
      destruct b2 ; auto.
    Qed.
  



  
Definition dis_juxtaposition {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  : bigraph (sum_FinDecType s1 s2) (sum_FinDecType i1 i2) (sum_FinDecType r1 r2) (sum_FinDecType o1 o2) :=
{|
  node := sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 r2 o2 b2);
  edge := sum_FinDecType (@edge s1 i1 r1 o1 b1) (@edge s2 i2 r2 o2 b2);
  kind := sum_FinDecType (@kind s1 i1 r1 o1 b1) (@kind s2 i2 r2 o2 b2);
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_dis_parent b1 b2 ; 
  link := mk_new_link b1 b2 ;
  ap := mk_dis_ap b1 b2 ;
|}.

Notation "b1 '||' b2" := (dis_juxtaposition b1 b2) (at level 50, left associativity).


Lemma correct_node_type {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  get_node (b1 || b2) = ((get_node b1) + (get_node b2))%type.
  Proof. auto. Qed.

(* THEOREMS ONLY TRUE WHEN EQUALITY BETWEEN BIGRAPHS IS ACTUALLY AN ISOMORPHISM *)
  (* Theorem dis_juxtaposition_associative {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 k3: FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3 k3),
    (b1 || b2) || b3 = b1 || (b2 || b3).

  Theorem dis_juxtaposition_commutative {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
    b1 || b2 = b2 || b1. *)




(* MAKERS FOR COMPOSITION *)
  Definition mk_comp_parent {s1 i1 r1 o1 s2 i2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2))
     + (@type s2) 
     -> @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2)) 
        + (@type r1) :=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let n1pn2 := @type (sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2)) in
    let new_parent (p : (n1pn2) + (@type s2)) : (n1pn2) + (@type r1) :=
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
    (@type i2) + Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2)  
    -> (@type o1) + ((get_edge b1) + (get_edge b2)) :=
      let n1 := get_node b1 in
      let n2 := get_node b2 in
      let c := mk_dis_control b1 b2 in
      let p := Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2)  in
      let e1 := get_edge b1 in
      let e2 := get_edge b2 in
      let l1 := get_link b1 in
      let l2 := get_link b2 in
      let new_link (ip : (@type i2) + p) : (@type o1) + (e1 + e2) :=
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
      acyclic (get_node b2) (@type s2) (@type s1) (get_parent b2) ->
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
    acyclic ((get_node b1) + (get_node b2)) (@type s2) (@type r1) (mk_comp_parent b1 b2).
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
  node := sum_FinDecType (@node s1 i1 r1 o1 b1) (@node s2 i2 s1 i1 b2);
  edge := sum_FinDecType (@edge s1 i1 r1 o1 b1) (@edge s2 i2 s1 i1 b2);
  kind := sum_FinDecType (@kind s1 i1 r1 o1 b1) (@kind s2 i2 s1 i1 b2);
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_comp_parent b1 b2 ; 
  link := mk_comp_link b1 b2 ;
  ap := mk_comp_ap b1 b2 ;
|}.

Notation "b1 'o' b2" := (composition b1 b2) (at level 40, left associativity).

(* IMPLEMENTATION OF A BIGRAPH *)
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
    acyclic (@type unitFinDecType) (@type voidFinDecType) (@type unitFinDecType) (fun _ => inl tt).
    Proof. unfold acyclic. intros. Admitted.
  Example vft : (@type voidFinDecType). Proof. unfold voidFinDecType. simpl. Admitted. 
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



End Bigraph.


Module EJCP.


  Inductive myZ : Type :=
    | z : Z -> myZ
    | plusinf : myZ
    | moinsinf : myZ.

  Record intervalle : Type :=
    {
      inf : Z ;
      sup : Z 
    }.

  Definition plus_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    {|
      inf := @inf int1 + @inf int2 ;
      sup := @sup int1 + @sup int2 
    |}.

  Notation "i1 '+i' i2" := (plus_inter i1 i2) (at level 40, left associativity).

  Definition moins_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    {|
      inf := @inf int1 - @sup int2 ;
      sup := @sup int1 - @inf int2 
    |}.


  Notation "i1 '-i' i2" := (moins_inter i1 i2) (at level 40, left associativity).

  Search (_ < _).

  Definition my_min (a b : Z) : Z := 
    if Z.ltb a b then b else a.

  Definition my_max (a b : Z) : Z :=
    if Z.gtb a b then b else a.

  Definition fois_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    let ac := Z.mul (@inf int1) (@inf int2) in
    let ad := Z.mul (@inf int1) (@sup int2) in
    let bc := Z.mul (@sup int1) (@inf int2) in
    let bd := Z.mul (@sup int1) (@sup int2) in
    {|
      inf := my_min (my_min (ac) (ad)) (my_min (bc) (bd)) ;
      sup := my_max (my_max (ac) (ad)) (my_max (bc) (bd)) ;
    |}.

  Notation "i1 '*i' i2" := (fois_inter i1 i2) (at level 40, left associativity).


  Definition div_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    let ac := Z.div (@inf int1) (@inf int2) in
    let ad := Z.div (@inf int1) (@sup int2) in
    let bc := Z.div (@sup int1) (@inf int2) in
    let bd := Z.div (@sup int1) (@sup int2) in
    {|
      inf := my_min (my_min (ac) (ad)) (my_min (bc) (bd)) ;
      sup := my_max (my_max (ac) (ad)) (my_max (bc) (bd)) ;
    |}.


  Notation "i1 '/i' i2" := (div_inter i1 i2) (at level 40, left associativity).

  Definition inter_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    {|
      inf := my_max (@inf int1) (@inf int2);
      sup := my_min (@sup int1) (@sup int2)
    |}.


  Notation "i1 '/\i' i2" := (inter_inter i1 i2) (at level 40, left associativity).

  Definition union_inter (int1 : intervalle) (int2 : intervalle) : intervalle :=
    {|
      inf := my_min (@inf int1) (@inf int2);
      sup := my_max (@sup int1) (@sup int2)
    |}.

  Notation "i1 '\/i' i2" := (union_inter i1 i2) (at level 40, left associativity).
  Definition eqb_inter (int1 : intervalle) (int2 : intervalle) : bool :=
    Z.eqb (@inf int1) (@inf int2) &&
    Z.eqb (@sup int1) (@sup int2).
  Notation "i1 '=i?' i2" := (eqb_inter i1 i2) (at level 40, left associativity).


  Definition eq_inter (int1 : intervalle) (int2 : intervalle) : Prop :=
    Z.eq (@inf int1) (@inf int2) /\
    Z.eq (@sup int1) (@sup int2).
  Notation "i1 '=i' i2" := (eq_inter i1 i2) (at level 40, left associativity).

  Inductive nodeAST :=
  | zAST : Z -> nodeAST
  | interAST : intervalle -> nodeAST
  | plusAST : intervalle -> nodeAST
  | moinsAST : intervalle -> nodeAST
  | foisAST : intervalle -> nodeAST
  | divAST : intervalle -> nodeAST
  | infAST : intervalle -> nodeAST
  | supAST : intervalle -> nodeAST.

  Inductive AST :=
  | EmptyAST : AST
  | rootAST : nodeAST -> AST -> AST -> AST.

  (* Fixpoint top_down (inter:intervalle) (ast:AST) : intervalle :=
    match ast with 
    | EmptyAST => inter
    | rootAST n ast_left ast_right => 
      match n with 
      | zAST z => inter /\i {| inf := z ; sup := z|} 
      | interAST inter' => inter
      | plusAST inter' => top_down (u /\i (r -i v)) ast_left
      | moinsAST : nodeAST
      | foisAST : nodeAST
      | divAST : nodeAST
      | infAST : nodeAST
      | supAST : nodeAST
      end
    end. *)

  (*Lemma inverse : forall (u : intervalle) (v : intervalle) (r : intervalle),
    r =i(u +i v) -> u =i (u /\i (r -i v)) /\ v =i (v /\i (r -i u)).
  Proof.
    intros.
    unfold eq_inter in H.
    unfold Z.eq in H.
    unfold plus_inter in H.
    simpl in H.
    destruct H as [Hinf Hsup].
    split.
    - unfold eq_inter.
      split.
      + unfold Z.eq.     
        unfold inter_inter. 
        unfold moins_inter.
        simpl.
        unfold my_max.
        induction Z.gtb.
        ++  *)


 
End EJCP.