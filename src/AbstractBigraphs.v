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

(* Set Implicit Arguments. *)

(* From MyProofs Require Import Decidable.  *)



Module Bigraph.

Definition finite (A : Type) : Type := { l : list A | Listing l }.
Definition acyclic (node site root : Type) (parent : node + site -> node + root) : Prop :=
  forall (n:node), Acc (fun n n' => parent (inl n) = (inl n')) n.

Definition Kappa (kind : Type) (arity : kind -> nat) : Type := 
  { ki : kind * nat | let (k, i) := ki in i = arity k }.

Definition Port (node : Type) (kind : Type) (control : node -> kind * nat) : Type :=
  { vi : node * nat | let (v, i) := vi in let (_, a) := control v in i < a }.

Record bigraph (site: Type) (innername: Type) (root: Type) (outername: Type) (kind: Type): Type := 
  Big  
  { 
    node : Type ;
    port : node * nat ;
    edge : Type ;
    control : node -> kind * nat; 
    parent : node + site -> node + root ; 
    link : innername + port -> outername + edge; 
    (* sd : EqDec site ;
    sf : finite site ;
    id_ : EqDec innername ;
    if_ : finite innername ;
    rd : EqDec root ;
    rf : finite root ;
    od : EqDec outername ;
    of : finite outername ; *)
    pc : forall p:port, snd p < snd (control (fst p)) ;
    nd : EqDec node ;
    nf : finite node ;
    ed : EqDec edge ;
    ef : finite edge ;
    ap : acyclic node site root parent ;
  }.
  (* sortir les preuves des types interface?*)

Check parent.

Fixpoint merge_list {A B : Type} (la : list A) (lb : list B) (acc : list (A + B)) : list (A + B) :=
  match la with
  | [] => acc ++ (map inr lb)
  | ha :: ta => merge_list ta lb ((inl ha) :: acc)
  end.
  
Definition merge {A B : Type} (la : list A) (lb : list B) : list (A + B) :=
  merge_list la lb [].

(* Fixpoint merge_list {A B: Type} (la: list A) (lb : list B) : list (A + B) :=
  match la, lb with 
  | ta :: qa, _ => (inl ta) :: merge_list qa lb
  | [], tb :: qb => (inr tb) :: merge_list [] qb
  | [], [] => []
  end. *)


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

Definition mk_new_link {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  (i1 + i2) + (Port ((getNode b1) + getNode b2) (k1 + k2) (mk_new_control b1 b2)) 
  -> (o1 + o2) + ((getEdge b1) + (getEdge b2)). 
    (* :=
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
      | inr p =>  let (n,i) := proj1_sig p in 
                  match n with 
                  | inl n1' =>  match (l1 (inr (n1',i))) with 
                                | inl o1 => inl (inl o1)
                                | inr e1 => inr (inl e1)
                                end
                  | inr n2' =>  match (l2 (inr n2',i)) with 
                                | inl o2 => inl (inl o2)
                                | inr e2 => inr (inl e2)
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
    in new_link. *)
  Admitted.


Definition mk_new_link' {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  (i1 + i2) + ((Port (getNode b1) k1 (getControl b1)) + (Port (getNode b2) k2 (getControl b2))) 
  -> (o1 + o2) + ((getEdge b1) + (getEdge b2)).
  Admitted.

Definition getNd {s i r o k : Type} (bg : bigraph s i r o k) : 
  EqDec (getNode bg) :=
  @nd s i r o k bg.
Definition mk_new_nd {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  EqDec ((getNode b1) + (getNode b2)).
  Proof.  
    destruct (getNd b1). EqDec. as [l1 H1]. 
    destruct (getNd b2) as [l2 H2].Admitted.
Definition getNf {s i r o k : Type} (bg : bigraph s i r o k) : 
  finite (getNode bg) :=
  @nf s i r o k bg.
  
Definition mk_new_nf {s i r o k : Type} 
  (bg : bigraph s i r o k) (bg' : bigraph s i r o k) :
  finite ((getNode bg) + (getNode bg')). 
  Proof. 
    destruct (getNf bg) as [l1 H1]. 
    destruct (getNf bg') as [l2 H2].
    unfold finite. 
    exists (merge l1 l2). 
    unfold merge. unfold merge_list. Admitted.
Definition mk_new_nf' {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  finite ((getNode b1) + (getNode b2)). 
  Proof. 
    destruct (getNf b1) as [l1 H1]. 
    destruct (getNf b2) as [l2 H2].
    unfold finite. Admitted.  
Definition mk_new_ed {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  EqDec ((getEdge b1) + (getEdge b2)). Admitted.
Definition mk_new_ef {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  finite ((getEdge b1) + (getEdge b2)). Admitted.
Definition mk_new_ap {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) :
  acyclic ((getNode b1) + (getNode b2)) (s1 + s2) (r1 + r2) (mk_new_parent b1 b2). Admitted.

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

(*comments*)
  (* let new_node : Type := (node b1 + node b2)%type in
  (* let eqdec_newnode := fun a b =>
    match a, b with
    | inl a1, inl b1 => nd a1 b1
    | inr a2, inr b2 => nd a2 b2
    | _, _ => False
    end in *)
  let new_edge : Type := ((edge b1) + (edge b2))%type in
  let new_kind : Type := (k1 + k2)%type in
  (* let new_arity (k : new_kind) : nat := 
    match k with
    | inl k1 => arity b1 k1 
    | inr k2 => arity b2 k2
    end  
  in *)
  let new_control (n : new_node) : new_kind * nat := 
    match n with
    | inl n1 => (inl (fst (control n1)), snd (control n1))
    | inr n2 => (inr (fst (control n2)), snd (control n2))
    end 
  in
  let new_parent (p : new_node + (s1 + s2)) : new_node + (r1 + r2) :=
    match p with
     | inl node =>  match node with 
                    |inl n1 => match parent (inl n1) with
                              | inl n1' => inl (inl n1')
                              | inr r1 => inr (inl r1)
                              end
                    |inr n2 => match parent (inl n2) with
                              | inl n2' => inl (inr n2')
                              | inr r2 => inr (inr r2)
                              end
                    end
    | inr site => match site with 
                  |inl s1 => match parent (inr s1) with
                            | inl n1' => inl (inl n1')
                            | inr r1 => inr (inl r1)
                            end
                  |inr s2 => match parent (inr s2) with
                            | inl n2' => inl (inr n2')
                            | inr r2 => inr (inr r2)
                            end
    end
  end
  in
  (*let new_port : Type := 
    ({x : node b1 * nat | snd x < snd (control (fst x))} + 
    {x : node b2 * nat | snd x < snd (control (fst x))})%type
  in*)
  let new_link (i : (i1 + i2) + (Port new_control)): (o1 + o2) + new_edge := 
    mk_new_link i
  in
  (* let new_link (i : (i1 + i2) + (Port new_control)): (o1 + o2) + new_edge := 
    match i with
    | inl innername => match innername with 
                      |inl i1 =>  match link (inl i1) with
                                  | inl o1 => inl (inl o1)
                                  | inr e1 => inr (inl e1)
                                  end
                      |inr i2 =>  match link (inl i2) with
                                  | inl o2 => inl (inr o2)
                                  | inr e2 => inr (inr e2)
                                  end
                      end
    | inr port => match fst (proj1_sig port) with
                  | inl n1 => let port1 := Port 
                  
                              match @link s1 i1 r1 o1 k1 b1 (inr port) with
                              | inl ot1 => inl (inl ot1)
                              | inr ed1 => inr (inl ed1)
                              end
                  | inr n2 => match link (inr port) with 
                              | inl o2 => inl (inr o2)
                              | inr e2 => inr (inr e2)
                              end
                  end
    end 
  in *)
  (* let new_ap : acyclic new_parent := ap in *)
  {|
    node := new_node ;
    edge := new_edge ;
    control := new_control ;
    parent := new_parent ;
    link := new_link ;
    (* sd := EqDec site ;
    sf := Finite site ;
    id_ := EqDec innername ;
    if_ := Finite innername ;
    rd := EqDec root ;
    rf : Finite root ;
    od : EqDec outername ;
    of : Finite outername ;
    nd : EqDec node ;
    nf : Finite node ;
    ed : EqDec edge ;
    ef : Finite edge ; *)
    (* ap := new_ap *)
  |}. *)
  (* Big new_parent new_link (s1+s2)%type (i1+i2) (r1+r2) (o1+o2) new_node new_edge new_control. 

  { node := new_node ;
    edge := new_edge ;
    control := new_control ;
    parent := new_parent ;
    link := new_link }.

  Big (node := new_node) (edge := new_edge) (control := new_control)
      (parent := new_parent) (link := new_link) (sd := sum_dec (sd b1) (sd b2))
      (sf := sum_finite (sf b1) (sf b2)) (id_ := sum_dec (id_ b1) (id_ b2))
      (if_ := sum_finite (if_ b1) (if_ b2)) (rd := sum_dec (rd b1) (rd b2))
      (rf := sum_finite (rf b1) (rf b2)) (od := sum_dec (od b1) (od b2))
      (of := sum_finite (of b1) (of b2)) (nd := sum_dec (nd b1) (nd b2))
      (nf := sum_finite (nf b1) (nf b2)) (ed := sum_dec (ed b1) (ed b2))
      (ef := sum_finite (ef b1) (ef b2)). *)

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
Admitted.







End Bigraph.