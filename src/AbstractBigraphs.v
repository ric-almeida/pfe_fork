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


Definition merge {A B : Type} (la : list A) (lb : list B) : list (A + B) :=
  (map inl la) ++ (map inr lb).


Definition finite (A : Type) : Type := { l : list A | Listing l }.

Definition acyclic (node site root : Type) (parent : node + site -> node + root) : Prop :=
  forall (n:node), Acc (fun n n' => parent (inl n) = (inl n')) n.

Definition Kappa (kind : Type) (arity : kind -> nat) : Type := 
  { ki : kind * nat | let (k, i) := ki in i = arity k }.

Definition Port (node : Type) (kind : Type) (control : node -> kind * nat) : Type :=
  { vi : node * nat | let (v, i) := vi in let (_, a) := control v in i < a }.

Record bigraph (site: Type) (innername: Type) (root: Type) (outername: Type) (kind: Type) : Type := 
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


Check parent.



Definition getNode {s i r o k : Type} (bg : bigraph s i r o k) : Type := 
  node s i r o k bg.

Definition getEdge {s i r o k : Type} (bg : bigraph s i r o k) : Type := 
  edge s i r o k bg.
  
Definition getControl {s i r o k : Type} (bg : bigraph s i r o k) 
  : node s i r o k bg -> k * nat :=
  @control s i r o k bg.

Definition mk_new_control {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  ((getNode b1) + (getNode b2)) -> (k1+k2) * nat :=
  let c1 := getControl b1 in
  let c2 := getControl b2 in
  let n1 := getNode b1 in
  let n2 := getNode b2 in
  let new_control (n : n1+n2) : (k1+k2) * nat := 
    match n with
    | inl n1' => (inl (fst (c1 n1')), snd (c1 n1'))
    | inr n2' => (inr (fst (c2 n2')), snd (c2 n2'))
    end 
  in new_control.

Definition getParent {s i r o k : Type} (bg : bigraph s i r o k) : 
  node s i r o k bg + s -> node s i r o k bg + r :=
  @parent s i r o k bg.

Definition mk_new_parent {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  ((getNode b1) + (getNode b2)) + (s1 + s2) -> ((getNode b1) + (getNode b2)) + (r1 + r2):=
  let p1 := getParent b1 in
  let p2 := getParent b2 in
  let n1 := getNode b1 in
  let n2 := getNode b2 in
  let new_parent (p : (n1 + n2) + (s1 + s2)) : (n1 + n2) + (r1 + r2) :=
    match p with
     | inl node =>  match node with 
                    |inl n1 => match p1 (inl n1) with
                              | inl n1' => inl (inl n1')
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


Definition getLink {s i r o k : Type} (bg : bigraph s i r o k) : 
  i + Port (node s i r o k bg) k (getControl bg) -> o + getEdge bg :=
  @link s i r o k bg. 

Definition mk_port {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) 
  (p:Port ((getNode b1) + getNode b2) (k1 + k2) (mk_new_control b1 b2)) :
  Port (node s1 i1 r1 o1 k1 b1) k1 (getControl b1) +
  Port (node s2 i2 r2 o2 k2 b2) k2 (getControl b2).
  Proof. destruct p as [vi12 P12]. unfold getNode in vi12. destruct vi12 as [v12 i12]. 
  destruct v12 as [n1 | n2].
  - left. unfold mk_new_control in P12.   
    unfold Port. exists (n1,i12). unfold snd in P12. 
    destruct (getControl b1 n1) eqn:HgetControl. apply P12.
  - right. unfold mk_new_control in P12.   
  unfold Port. exists (n2,i12). unfold snd in P12. 
  destruct (getControl b2 n2) eqn:HgetControl. apply P12. Defined.
Print mk_port.
Definition mk_new_link {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  (i1 + i2) + (Port ((getNode b1) + getNode b2) (k1 + k2) (mk_new_control b1 b2)) 
  -> (o1 + o2) + ((getEdge b1) + (getEdge b2)) :=
    let n1 := getNode b1 in
    let n2 := getNode b2 in
    let c := mk_new_control b1 b2 in
    let p := Port (n1 + n2) (k1 + k2) c in
    let e1 := getEdge b1 in
    let e2 := getEdge b2 in
    let l1 := getLink b1 in
    let l2 := getLink b2 in
    let new_link (ip : (i1 + i2) + p) : (o1 + o2) + (e1 + e2) :=
      match ip with 
      | inr p =>  let p' := mk_port b1 b2 p in
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




Definition getNd {s i r o k : Type} (bg : bigraph s i r o k) : 
  EqDec (getNode bg) :=
  @nd s i r o k bg.

Definition mk_new_nd {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  EqDec ((getNode b1) + (getNode b2)).
  Proof.  
    unfold EqDec. intros. destruct x as [x1 | x2]; destruct y as [y1 | y2].
      - destruct (getNd b1 x1 y1).
        + left. rewrite e. auto. 
        + right. intro contra. congruence.  
      - right. intros contra. congruence.
      - right. intros contra. congruence. 
      - destruct (getNd b2 x2 y2).
      + left. rewrite e. auto. 
      + right. intro contra. congruence. 
    Defined.


Definition getNf {s i r o k : Type} (bg : bigraph s i r o k) : 
  finite (getNode bg) :=
  @nf s i r o k bg.

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
  
Theorem nodupAB {A B: Type}: forall (la: list A) (lb: list B), NoDup la -> NoDup lb -> NoDup (merge la lb).
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


Theorem listingAB {A B : Type}: forall (la: list A) (lb: list B), Listing la -> Listing lb -> Listing (merge la lb).
  Proof.
  intros la lb [nda fa] [ndb fb]. split.
  -   apply nodupAB ; auto. 
  -   unfold merge. simpl. Admitted.

Definition mk_new_nf {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  finite ((getNode b1) + (getNode b2)). 
  Proof. 
    destruct (getNf b1) as [l1 H1]. 
    destruct (getNf b2) as [l2 H2].
    unfold finite. exists (merge l1 l2). apply listingAB; auto. Qed.  

Definition getEd {s i r o k : Type} (bg : bigraph s i r o k) : 
  EqDec (getEdge bg) :=
  @ed s i r o k bg.
Definition mk_new_ed {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  EqDec ((getEdge b1) + (getEdge b2)). 
  Proof.  
    unfold EqDec. intros. destruct x as [x1 | x2]; destruct y as [y1 | y2].
      - destruct (getEd b1 x1 y1).
        + left. rewrite e. auto. 
        + right. intro contra. congruence.  
      - right. intros contra. congruence.
      - right. intros contra. congruence. 
      - destruct (getEd b2 x2 y2).
      + left. rewrite e. auto. 
      + right. intro contra. congruence. 
    Defined.
Definition mk_new_ef {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  finite ((getEdge b1) + (getEdge b2)). Admitted.
Definition mk_new_ap {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  acyclic ((getNode b1) + (getNode b2)) (s1 + s2) (r1 + r2) (mk_new_parent b1 b2). 
  Admitted.

Definition juxtaposition {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
(b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) 
  : bigraph (s1+s2)%type (i1+i2)%type (r1+r2)%type (o1+o2)%type (k1+k2)%type :=
{|
  node := (getNode b1) + (getNode b2) ;
  edge := (getEdge b1) + (getEdge b2) ;
  control := mk_new_control b1 b2 ;
  parent := mk_new_parent b1 b2 ; 
  link := mk_new_link b1 b2 ;
  nd := mk_new_nd b1 b2 ;
  nf := mk_new_nf b1 b2 ;
  ed := mk_new_ed b1 b2 ;
  ef := mk_new_ef b1 b2 ;
  ap := mk_new_ap b1 b2 ;
|}.



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



(* 
  Lemma myFinite : forall n:myNode, exists (l:list myNode), Full l.
  Proof.
  intros n. 
  unfold Full. exists [node0;node1;node2]. intros. destruct n0 as [n0 Hn0 Hn1 Hn2].
  apply Hn0. exists. unfold node0. 
  
  
  
  right. right. right. contradiction.  

  Instance EqDec_nat : EqDec nat := {| eq_dec := PeanoNat.Nat.eq_dec |}. *)

  
Definition myBigraph : bigraph mySite myInnerName myRoot myOuterName myKind.
  Proof. unfold mySite. unfold myInnerName. unfold myRoot. unfold myOuterName.
  unfold myKind. 
  Admitted.
  






End Bigraph.