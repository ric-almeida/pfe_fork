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

Definition Port {kind : Type} (node : Type) (control : node -> kind) (arity : kind -> nat): Type :=
  { vi : node * nat | let (v, i) := vi in let k := control v in let a := arity k in i < a }.

Record bigraph  (site: Type) 
                (innername: Type) 
                (root: Type) 
                (outername: Type) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : Type ;
    kind : Type ;
    arity : kind -> nat ;
    control : @type node -> kind ;
    parent : @type node + site -> @type node + root ; 
    link : innername + Port (@type node) control arity -> outername + edge; 
    ed : EqDec edge ;
    ef : finite edge ;
    ap : acyclic (@type node) site root parent ;
  }.



(* GETTERS *)
  Definition get_node {s i r o : Type} (bg : bigraph s i r o) : Type := 
  @type (node s i r o bg).
  Definition get_edge {s i r o : Type} (bg : bigraph s i r o) : Type := 
  edge s i r o bg.
  Definition get_kind {s i r o : Type} (bg : bigraph s i r o) : Type := 
  kind s i r o bg.
  Definition get_arity {s i r o : Type} (bg : bigraph s i r o) : 
  (get_kind bg) -> nat := 
  arity s i r o bg.
  Definition get_control {s i r o : Type} (bg : bigraph s i r o) 
  : get_node bg -> (get_kind bg) :=
  @control s i r o bg.
  Definition get_parent {s i r o : Type} (bg : bigraph s i r o) : 
  get_node bg + s -> get_node bg + r :=
  @parent s i r o bg.
  Definition get_link {s i r o : Type} (bg : bigraph s i r o) : 
  i + Port (get_node bg) (get_control bg) (get_arity bg) -> o + get_edge bg :=
  @link s i r o bg. 
  Definition get_nd {s i r o : Type} (bg : bigraph s i r o) : 
  EqDec (get_node bg) :=
  @dec_type (node s i r o bg).
  Definition get_nf {s i r o : Type} (bg : bigraph s i r o) : 
  finite (get_node bg) :=
  @finite_type (node s i r o bg).
  Definition get_ed {s i r o : Type} (bg : bigraph s i r o) : 
  EqDec (get_edge bg) :=
  @ed s i r o bg.
  Definition get_ef {s i r o : Type} (bg : bigraph s i r o) : 
  finite (get_edge bg) :=
  @ef s i r o bg.
  Definition get_ap {s i r o : Type} (bg : bigraph s i r o) : 
  acyclic (get_node bg) s r (get_parent bg) :=
    @ap s i r o bg.


(* MAKERS FOR DISJOINT JUXTAPOSITION   *)
  Definition mk_dis_arity {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
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

  Definition mk_dis_control {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
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




  Definition mk_dis_parent {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    ((get_node b1) + (get_node b2)) + (s1 + s2) -> ((get_node b1) + (get_node b2)) + (r1 + r2):=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let n1 := get_node b1 in
    let n2 := get_node b2 in
    let new_parent (p : (n1 + n2) + (s1 + s2)) : (n1 + n2) + (r1 + r2) :=
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
  Definition mk_dis_port {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
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

  Definition mk_new_link {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    (i1 + i2) + Port ((get_node b1) + get_node b2) (mk_dis_control b1 b2) (mk_dis_arity b1 b2) 
    -> (o1 + o2) + ((get_edge b1) + (get_edge b2)) :=
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

  Lemma EqDec_sum {A B : Type} (ea : EqDec A) (eb : EqDec B) :
    EqDec (A + B).
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
      Defined.

  Definition mk_new_nd {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    EqDec ((get_node b1) + (get_node b2)).
      Proof. 
        apply EqDec_sum; destruct b1; destruct b2; destruct node0; destruct node1; assumption.  
      Defined.

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

  Definition mk_new_nf {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    finite ((get_node b1) + (get_node b2)). 
    Proof. 
      apply finite_sum; destruct b1; destruct b2; destruct node0; destruct node1; assumption. 
    Qed.  


  Definition mk_new_ed {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    EqDec ((get_edge b1) + (get_edge b2)). 
    Proof. 
      apply EqDec_sum; destruct b1; destruct b2; assumption.  
    Defined.

  Definition mk_new_ef {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  finite ((get_edge b1) + (get_edge b2)). 
  Proof. 
    apply finite_sum; destruct b1; destruct b2; assumption. 
  Qed.  


  Theorem acyclic_dis_parent_left : forall {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
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
        set (p1 := parent s1 i1 r1 o1 b1 (inl n1')).
        fold p1 in Hn1'.
        change (p1 = inl n1).
        destruct p1;  congruence.
      + intro Hn2'.
        simpl in Hn2'.
        unfold get_parent in *. 
        set (p2 := parent s2 i2 r2 o2 b2 (inl n2')).
        fold p2 in Hn2'.
        destruct p2; inversion Hn2'.
    Qed.

  Theorem acyclic_dis_parent_right : forall {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
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
        destruct p2 ; congruence.
    Qed.

  Definition mk_dis_ap {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
    acyclic ((get_node b1) + (get_node b2)) (s1 + s2) (r1 + r2) (mk_dis_parent b1 b2).
    Proof.
    unfold acyclic ; intros [n1 | n2].
    - apply acyclic_dis_parent_left.
      destruct b1 ; auto.
    - apply acyclic_dis_parent_right.
      destruct b2 ; auto.
    Qed.
  
  Definition mk_dis_node {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : FinDecType :=
    {|
      type := (get_node b1) + (get_node b2) ;
      dec_type := mk_new_nd b1 b2 ;
      finite_type := mk_new_nf b1 b2
    |}.


    Definition dis_juxtaposition {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  : bigraph (s1+s2)%type (i1+i2)%type (r1+r2)%type (o1+o2)%type :=
{|
  node := mk_dis_node b1 b2 ;
  edge := (get_edge b1) + (get_edge b2) ;
  kind := (get_kind b1) + (get_kind b2) ;
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_dis_parent b1 b2 ; 
  link := mk_new_link b1 b2 ;
  ed := mk_new_ed b1 b2 ;
  ef := mk_new_ef b1 b2 ;
  ap := mk_dis_ap b1 b2 ;
|}.

Notation "b1 '||' b2" := (dis_juxtaposition b1 b2) (at level 50, left associativity).

Lemma correct_node_type {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  get_node (b1 || b2) = ((get_node b1) + (get_node b2))%type.
  Proof. auto. Qed.

(* THEOREMS ONLY TRUE WHEN EQUALITY BETWEEN BIGRAPHS IS ACTUALLY AN ISOMORPHISM *)
  (* Theorem dis_juxtaposition_associative {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 k3: Type} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3 k3),
    (b1 || b2) || b3 = b1 || (b2 || b3).

  Theorem dis_juxtaposition_commutative {s1 i1 r1 o1 s2 i2 r2 o2 : Type} :
    forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
    b1 || b2 = b2 || b1. *)




(* MAKERS FOR COMPOSITION *)
  Definition mk_comp_parent {s1 i1 r1 o1 s2 i2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    ((get_node b1) + (get_node b2)) + s2 -> ((get_node b1) + (get_node b2)) + r1 :=
    let p1 := get_parent b1 in
    let p2 := get_parent b2 in
    let node1 := get_node b1 in 
    let node2 := get_node b2 in
    let new_parent (p : (node1 + node2) + s2) : (node1 + node2) + r1 :=
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

  Definition mk_comp_link {s1 i1 r1 o1 s2 i2 : Type} 
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

  Theorem acyclic_comp_parent_right : forall {s1 i1 r1 o1 s2 i2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1)
    (n2 : get_node b2),
      Acc (fun n n' => (get_parent b2) (inl n) = inl n') n2 ->
      Acc (fun n n' => (mk_comp_parent b1 b2) (inl n) = inl n') (inr n2).
    Proof.
      intros.
      induction H as (n2, _, Hindn2').
      apply Acc_intro.
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
      ++ congruence.
      ++ set (p2' := parent s1 i1 r1 o1 b1 (inr s)).
      fold p2' in Hn2'. destruct p2'; congruence. 
    Qed.

  Theorem acyclic_comp_parent_left : forall {s1 i1 r1 o1 s2 i2 : Type} 
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
        destruct (p1); congruence.
      + intro Hn2'.
        apply acyclic_comp_parent_right.
        apply a.
    Qed.

  Definition mk_comp_ap {s1 i1 r1 o1 s2 i2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
    acyclic ((get_node b1) + (get_node b2)) s2 r1 (mk_comp_parent b1 b2).
    Proof. 
    unfold acyclic ; intros [n1 | n2].
    - apply acyclic_comp_parent_left.
      + destruct b1 ; auto.
      + destruct b2 ; auto.
    - apply acyclic_comp_parent_right ; destruct b2 ; auto.
    Qed.
  Definition mk_comp_node {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
    (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : FinDecType :=
      {|
        type := (get_node b1) + (get_node b2) ;
        dec_type := mk_new_nd b1 b2 ;
        finite_type := mk_new_nf b1 b2
      |}.

    Definition composition {s1 i1 r1 o1 s2 i2 : Type} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) 
  : bigraph s2 i2 r1 o1 :=
{|
  node := mk_dis_node b1 b2;
  edge := (get_edge b1) + (get_edge b2) ;
  kind := (get_kind b1) + (get_kind b2) ;
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_comp_parent b1 b2 ; 
  link := mk_comp_link b1 b2 ;
  ed := mk_new_ed b1 b2 ;
  ef := mk_new_ef b1 b2 ;
  ap := mk_comp_ap b1 b2 ;
|}.

Notation "b1 'o' b2" := (composition b1 b2) (at level 40, left associativity).

(* IMPLEMENTATION OF A BIGRAPH *)
  Example mySite : Type := {n:nat | n<=0}.
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
    ed := myEd ;
    ef := myEf ;
    ap := myAp ;
  |}.



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

Fixpoint top_down (inter:intervalle) (ast:AST) : intervalle :=
  match ast with 
  | EmptyAST => inter
  | rootAST n ast_left ast_right => 
    match n with =>
    | zAST z => inter /\i {| inf := z ; sup := z|} 
    | interAST inter' => inter
    | plusAST inter' => top_down (u /\i (r -i v)) ast_left
    | moinsAST : nodeAST
    | foisAST : nodeAST
    | divAST : nodeAST
    | infAST : nodeAST
    | supAST : nodeAST.
    end
  end.

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