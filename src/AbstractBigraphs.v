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

Definition acyclic (node site root : Type) (parent : node + site -> node + root) : Prop :=
  forall (n:node), Acc (fun n n' => parent (inl n) = (inl n')) n.

Fixpoint exp_function {A : Type} (f : A -> A) (a : A) (i : nat) : A :=
  match i with 
  | 0 => a
  | S i' => exp_function f (f a) (i')
  end.

Fixpoint exp_function' {A B C: Type} (f : A + B -> A + C) (a : A) (i : nat) : A + C :=
  match i with 
  | 0 => inl a
  | S i' => match (f (inl a)) with 
            | inl a' => exp_function' f a' i'
            | inr c => inr c
            end
  end.

Definition acyclic' (node site root : Type) (parent : node + site -> node + root) : Prop :=
  forall (n:node), forall (i:nat), exp_function' parent n i = (inl n) -> i = 0.

  (* Fixpoint closure_acylcic {A B : Type} (f : A -> A + B) (a : A):  
  match f a with 
  | inl a' => a' :: (closure_acylcic f a')
  | inr b => []
  end. *)

(* Definition acyclic' (node site root : Type) (parent : node + site -> node + root) : Prop :=
  forall (n:node), exists (r:root),  In (inl n) closure (parent (inl n)).  *)

Definition Port' (node : Type) (kind : Type) (control : node -> kind * nat) : Type :=
  { vi : node * nat | let (v, i) := vi in let (_, a) := control v in i < a }.


Definition Port {kind : Type} (node : Type) (control : node -> kind) (arity : kind -> nat): Type :=
  { vi : node * nat | let (v, i) := vi in let k := control v in let a := arity k in i < a }.

(*BIgraph avec toutes les finite et eqdec *)
  (*
  Record bigraph  (site: Type) 
                (innername: Type) 
                (root: Type) 
                (outername: Type) 
                (kind: Type) 
                (sf: finite site) 
                (sd: EqDec site) 
                (_if: finite innername) 
                (_id: EqDec innername) 
                (rf: finite root) 
                (rd: EqDec root) 
                (of: finite outername) 
                (od: EqDec outername) : Type := 
  Big  
  { 
    node : Type ;
    edge : Type ;
    control : node -> kind * nat;
    parent : node + site -> node + root ; 
    link : innername + Port node kind control -> outername + edge; 
    nd : EqDec node ;
    nf : finite node ;
    ed : EqDec edge ;
    ef : finite edge ;
    ap : acyclic node site root parent
  }.



  Definition get_node {s i r o : Type} 
    (sf: finite s) 
    (sd: EqDec s)
    (_if: finite i) 
    (_id: EqDec i)
    (rf: finite r) 
    (rd: EqDec r)
    (of: finite o) 
    (od: EqDec o)
    (bg : bigraph s i r o sf sd _if _id rf rd of od) : Type := 
    node s i r o sf sd _if _id rf rd of od bg.
    *)
Record bigraph  (site: Type) 
                (innername: Type) 
                (root: Type) 
                (outername: Type) : Type := 
  Big  
  { 
    node : Type ;
    edge : Type ;
    kind : Type ;
    arity : kind -> nat ;
    control : node -> kind ;
    parent : node + site -> node + root ; 
    link : innername + Port node control arity -> outername + edge; 
    nd : EqDec node ;
    nf : finite node ;
    ed : EqDec edge ;
    ef : finite edge ;
    ap : acyclic node site root parent ;
  }.





Definition get_node {s i r o : Type} (bg : bigraph s i r o) : Type := 
  node s i r o bg.

Definition get_edge {s i r o : Type} (bg : bigraph s i r o) : Type := 
  edge s i r o bg.

Definition get_kind {s i r o : Type} (bg : bigraph s i r o) : Type := 
  kind s i r o bg.

Definition get_arity {s i r o : Type} (bg : bigraph s i r o) : 
  (get_kind bg) -> nat := 
  arity s i r o bg.
  
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


Definition get_control {s i r o : Type} (bg : bigraph s i r o) 
  : node s i r o bg -> (get_kind bg) :=
  @control s i r o bg.

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

Definition get_parent {s i r o : Type} (bg : bigraph s i r o) : 
  node s i r o bg + s -> node s i r o bg + r :=
  @parent s i r o bg.

Definition mk_dis_parent {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  ((get_node b1) + (get_node b2)) + (s1 + s2) -> ((get_node b1) + (get_node b2)) + (r1 + r2):=
  let p1 := get_parent b1 in
  let p2 := get_parent b2 in
  let n1 := get_node b1 in
  let n2 := get_node b2 in
  let new_parent (p : (n1 + n2) + (s1 + s2)) : (n1 + n2) + (r1 + r2) :=
    match p with
     | inl node =>  match node with 
                    |inl n1' => match p1 (inl n1') with
                              | inl n1'' => inl (inl n1'')
                              | inr r1 => inr (inl r1)
                              end
                    |inr n2 => match p2 (inl n2) with
                              | inl n2' => inl (inr n2')
                              | inr r2 => inr (inr r2)
                              end
                    end
    | inr site => match site with 
                  |inl s1 => match p1 (inr s1) with
                            | inl n1' => inl (inl n1')
                            | inr r1 => inr (inl r1)
                            end
                  |inr s2 => match p2 (inr s2) with
                            | inl n2' => inl (inr n2')
                            | inr r2 => inr (inr r2)
                            end
    end
  end
  in new_parent.

Definition get_link {s i r o : Type} (bg : bigraph s i r o) : 
  i + Port (node s i r o bg) (get_control bg) (get_arity bg) -> o + get_edge bg :=
  @link s i r o bg. 

Definition mk_dis_port {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  (p:Port ((get_node b1) + get_node b2)%type 
          (mk_dis_control b1 b2) 
          (mk_dis_arity b1 b2)) :
  Port (get_node b1) (get_control b1) (get_arity b1) +
  Port (get_node b2) (get_control b2) (get_arity b2).
  Proof. destruct p as [vi12 P12]. unfold get_node in vi12. destruct vi12 as [v12 i12]. 
  destruct v12 as [n1 | n2].
  - left. unfold mk_dis_control in P12. unfold mk_dis_arity in P12.   
    unfold Port. exists (n1,i12).  
    destruct (get_arity b1) eqn:Hget_control; apply P12.
  - right. unfold mk_dis_control in P12.   unfold mk_dis_arity in P12.   
  unfold Port. exists (n2,i12); apply P12. Defined.

Definition mk_new_link {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  (i1 + i2) + Port ((get_node b1) + get_node b2)%type 
                    (mk_dis_control b1 b2) 
                    (mk_dis_arity b1 b2) 
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
      | inl i =>  match i with 
                  |inl i1 =>  match l1 (inl i1) with
                              | inl o1 => inl (inl o1)
                              | inr e1 => inr (inl e1)
                              end
                  |inr i2 =>  match l2 (inl i2) with
                              | inl o2 => inl (inr o2)
                              | inr e2 => inr (inr e2)
                              end
                  end
      end
    in new_link.

Definition get_nd {s i r o : Type} (bg : bigraph s i r o) : 
  EqDec (get_node bg) :=
  @nd s i r o bg.

Definition mk_new_nd {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  EqDec ((get_node b1) + (get_node b2)).
  Proof.  
    unfold EqDec. intros. destruct x as [x1 | x2]; destruct y as [y1 | y2].
      - destruct (get_nd b1 x1 y1).
        + left. rewrite e. auto. 
        + right. intro contra. congruence.  
      - right. intros contra. congruence.
      - right. intros contra. congruence. 
      - destruct (get_nd b2 x2 y2).
      + left. rewrite e. auto. 
      + right. intro contra. congruence. 
    Defined.


Definition get_nf {s i r o : Type} (bg : bigraph s i r o) : 
  finite (get_node bg) :=
  @nf s i r o bg.

Lemma NoDup_map_left {A B : Type} (la : list A) (lb : list B) (f: A -> A + B) (i: Injective f):
  NoDup la -> NoDup (map f la).
  Proof.
    intro Hla.
    induction la as [| a la' IH].
    - constructor.
    - apply Injective_map_NoDup. 
      + apply i.
      + apply Hla. Qed.

Lemma NoDup_map_inl {A B : Type} (la : list A) (lb : list B) :
  NoDup la -> NoDup (map (@inl A B) la).
  Proof.
    intro Hla.
    induction la as [| a la' IH].
    - constructor.
    - apply Injective_map_NoDup. 
      +  unfold Injective.
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
      - apply NoDup_map_left. 
        + assumption. 
        + unfold Injective. intros x y H. injection H. auto.
        + assumption.
      - apply NoDup_map_inr; auto. 
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

Definition mk_new_nf {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  finite ((get_node b1) + (get_node b2)). 
  Proof. 
    destruct (get_nf b1) as [l1 H1]. 
    destruct (get_nf b2) as [l2 H2].
    unfold finite. exists (merge l1 l2). apply listing_merge; auto. Qed.  

Definition get_ed {s i r o : Type} (bg : bigraph s i r o) : 
  EqDec (get_edge bg) :=
  @ed s i r o bg.
Definition mk_new_ed {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  EqDec ((get_edge b1) + (get_edge b2)). 
  Proof.  
    unfold EqDec. intros. destruct x as [x1 | x2]; destruct y as [y1 | y2].
      - destruct (get_ed b1 x1 y1).
        + left. rewrite e. auto. 
        + right. intro contra. congruence.  
      - right. intros contra. congruence.
      - right. intros contra. congruence. 
      - destruct (get_ed b2 x2 y2).
      + left. rewrite e. auto. 
      + right. intro contra. congruence. 
    Defined.
Definition get_ef {s i r o : Type} (bg : bigraph s i r o) : 
  finite (get_edge bg) :=
  @ef s i r o bg.
Definition mk_new_ef {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  finite ((get_edge b1) + (get_edge b2)). 
  Proof. 
    destruct (get_ef b1) as [l1 H1]. 
    destruct (get_ef b2) as [l2 H2].
    unfold finite. exists (merge l1 l2). apply listing_merge; auto. Qed.

Definition get_ap {s i r o : Type} (bg : bigraph s i r o) : 
  acyclic (get_node bg) s r (get_parent bg) :=
    @ap s i r o bg.

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
  



Definition dis_juxtaposition {s1 i1 r1 o1 s2 i2 r2 o2 : Type} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  : bigraph (s1+s2)%type (i1+i2)%type (r1+r2)%type (o1+o2)%type :=
{|
  node := (get_node b1) + (get_node b2) ;
  edge := (get_edge b1) + (get_edge b2) ;
  kind := (get_kind b1) + (get_kind b2) ;
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_dis_parent b1 b2 ; 
  link := mk_new_link b1 b2 ;
  nd := mk_new_nd b1 b2 ;
  nf := mk_new_nf b1 b2 ;
  ed := mk_new_ed b1 b2 ;
  ef := mk_new_ef b1 b2 ;
  ap := mk_dis_ap b1 b2 ;
|}.


Notation "b1 '||' b2" := (dis_juxtaposition b1 b2) (at level 50, left associativity).




(* Theorem dis_juxtaposition_associative {s1 i1 r1 o1 s2 i2 r2 o2 s3 i3 r3 o3 k3: Type} :
  forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3 k3),
  (b1 || b2) || b3 = b1 || (b2 || b3).

Theorem dis_juxtaposition_commutative {s1 i1 r1 o1 s2 i2 r2 o2 : Type} :
  forall (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2),
  b1 || b2 = b2 || b1. *)



Definition mk_comp_parent {s1 i1 r1 o1 s2 i2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
  ((get_node b1) + (get_node b2)) + s2 -> ((get_node b1) + (get_node b2)) + r1 :=
  let p1 := get_parent b1 in
  let p2 := get_parent b2 in
  let node1 := get_node b1 in 
  let node2 := get_node b2 in
  let new_parent (p : (node1 + node2) + s2) : (node1 + node2) + r1 :=
    match p with
     | inl node =>  match node with 
                    |inl n1 => match p1 (inl n1) with
                              | inl n1'' => inl (inl n1'')
                              | inr r1 => inr r1
                              end
                    |inr n2 => match p2 (inl n2) with
                              | inl n2' => inl (inr n2')
                              | inr r2s1 => match p1 (inr r2s1) with
                                            | inl n1' => inl (inl n1')
                                            | inr r1 => inr r1
                                            end
                              end
                    end
    | inr s2 => match p2 (inr s2) with
                  | inl n2' => inl (inr n2')
                  | inr r2s1 => match p1 (inr r2s1) with
                                | inl n1' => inl (inl n1')
                                | inr r1 => inr r1
                                end
                  end
    
    end
  in new_parent.

Definition mk_comp_link {s1 i1 r1 o1 s2 i2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
  i2 + Port ((get_node b1) + get_node b2)%type 
            (mk_dis_control b1 b2) 
            (mk_dis_arity b1 b2)  
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
                  | inl p1 => match (l1 (inr p1)) with 
                              | inl o1 => inl o1
                              | inr e1 => inr (inl e1)
                              end
                  | inr p2 => match (l2 (inr p2)) with 
                              | inl o2i1 => match (l1 (inl o2i1)) with 
                                            | inl o1 => inl o1
                                            | inr e1 => inr (inl e1)
                                            end
                              | inr e2 => inr (inr e2)
                              end
                  end
      | inl i =>  match l2 (inl i) with
                  | inr e2 => inr (inr e2)
                  | inl o2i1 => match (l1 (inl o2i1)) with 
                                | inl o1 => inl o1
                                | inr e1 => inr (inl e1)
                                end
                  end
      end
    in new_link.

Theorem acyclic_comp_parent_left : forall {s1 i1 r1 o1 s2 i2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1)
  (n1: get_node b1),
    Acc (fun n n' => (get_parent b1) (inl n) = inl n') n1 -> Acc (fun n n' => (mk_comp_parent b1 b2) (inl n) = inl n') (inl n1).
  Proof.
  intros.
  induction H as (n1, _, Hindn1').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
    apply Hindn1'.
    unfold mk_comp_parent in Hn1'.
    simpl in Hn1'.
    unfold get_parent in *.
    set (p1 := parent s1 i1 r1 o1 b1 (inl n1')).
    fold p1 in Hn1'.
    change (p1 = inl n1).
    destruct (p1) as [n1'' | r1'']; congruence.
  + intro Hn2'.
    simpl in Hn2'.
    unfold get_parent in *. 
    set (p2 := parent s2 i2 s1 i1 b2 (inl n2')).
    fold p2 in Hn2'.
    destruct p2.
    ++ congruence.
    ++ set (p1 := parent s1 i1 r1 o1 b1 (inr s)).
        fold p1 in Hn2'. destruct p1.
        +++ inversion Hn2'. Admitted.

Theorem acyclic_comp_parent_right : forall {s1 i1 r1 o1 s2 i2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1)
  (n2: get_node b2),
  acyclic (get_node b1) s1 r1 (get_parent b1) -> 
    Acc (fun n n' => (get_parent b2) (inl n) = inl n') n2 -> 
    Acc (fun n n' => (mk_comp_parent b1 b2) (inl n) = inl n') (inr n2).
  Proof.
  intros.
  induction H0 as (n2, _, Hindn2').
  apply Acc_intro.
  destruct y as [n1' | n2'].
  + intro Hn1'.
  apply acyclic_comp_parent_left.
  apply H.
  + intro Hn2'.
  apply Hindn2'.
  unfold mk_comp_parent in Hn2'.
  unfold get_parent in *.
  set (p2 := parent s2 i2 s1 i1 b2 (inl n2')).
  fold p2 in Hn2'.
  simpl in Hn2'.
  change (p2 = inl n2).
  destruct p2.
    ++ congruence.
    ++  set (p1 := parent s1 i1 r1 o1 b1 (inr s)).
        fold p1 in Hn2'. destruct p1; congruence.
  Qed.

Definition mk_comp_ap {s1 i1 r1 o1 s2 i2 : Type} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) :
  acyclic ((get_node b1) + (get_node b2)) s2 r1 (mk_comp_parent b1 b2).
  Proof. 
  unfold acyclic ; intros [n1 | n2].
  - apply acyclic_comp_parent_left.
    destruct b1 ; auto.
  - apply acyclic_comp_parent_right.
    + destruct b1 ; auto.
    + destruct b2 ; auto.
  Qed.

Definition composition {s1 i1 r1 o1 s2 i2 : Type} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) 
  : bigraph s2 i2 r1 o1 :=
{|
  node := (get_node b1) + (get_node b2) ;
  edge := (get_edge b1) + (get_edge b2) ;
  kind := (get_kind b1) + (get_kind b2) ;
  arity := mk_dis_arity b1 b2 ;
  control := mk_dis_control b1 b2 ;
  parent := mk_comp_parent b1 b2 ; 
  link := mk_comp_link b1 b2 ;
  nd := mk_new_nd b1 b2 ;
  nf := mk_new_nf b1 b2 ;
  ed := mk_new_ed b1 b2 ;
  ef := mk_new_ef b1 b2 ;
  ap := mk_comp_ap b1 b2 ;
|}.

Notation "b1 'o' b2" := (composition b1 b2) (at level 40, left associativity).

Definition b1b2 {s1 i1 r1 o1 s2 i2 : Type} 
(b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 s1 i1) 
: bigraph s2 i2 r1 o1 := b1 o b2.

Check b1b2.

Definition mySite : Type := nat.
Definition myInnerName : Type := nat.
Definition myRoot : Type := nat.
Definition myOuterName : Type := nat.
Definition myKind : Type := nat.
Definition myNode : Type := {n:nat | n<3}.
Definition myEdge : Type := nat.

Definition myControl : myNode -> nat * nat := fun _ => (10, 20).
Definition myParent : myNode + mySite -> myNode + myRoot := fun _ => inr 2.
Definition myLink : myInnerName + {x : myNode * nat | snd x < snd (myControl (fst x))} -> 
  myOuterName + myEdge := fun _ => inr 1.


Definition Full (l:list myNode) :=
forall n:myNode, In n l.


Definition node0 : myNode.
Proof. unfold myNode. exists 0. auto. Qed.

Definition node1 : myNode.
Proof. unfold myNode. exists 1. auto. Qed.

Definition node2 : myNode.
Proof. unfold myNode. exists 2. auto. Qed.




  
Definition myBigraph : bigraph mySite myInnerName myRoot myOuterName.
  Proof. unfold mySite. unfold myInnerName. unfold myRoot. unfold myOuterName.
  unfold myKind. 
  Admitted.
  




  (* TODO *)
  (* mettre des Defined au lieu de Qed *)
  (* sortir preuves des interfaces *)


End Bigraph.