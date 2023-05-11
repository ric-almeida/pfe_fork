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

Set Implicit Arguments.

(* From MyProofs Require Import Decidable.  *)



Module Bigraph.

(* Definition node : Type := Type.
Definition root : Type := Type.
Definition site : Type.
Definition edge : Type.
Definition innername : Type.
Definition outername : Type.
Definition port : Type.

Definition place : Type := root + node + site.
Definition link : Type := edge + outername.
Definition point : Type := port + innername.

Definition kappa : Type := ADec.A * nat.
Definition control : Type := node -> kappa.

Definition parent : Type := node + site -> node + root. *)

(* Function decidability_A (A : Type) : Prop := forall (x y : A), {x = y} + {~x = y}.

Definition decidability_nat : forall (x y : nat), {x = y} + {~x = y} := (decidability_A nat). *)

(* Class EqDec (T: Type) :=
  { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }. *)

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
    edge : Type ;
    control : node -> kind * nat; (* k * nat *)
    parent : node + site -> node + root ; 
    link : innername + Port control -> outername + edge; 
    (* sd : EqDec site ;
    sf : finite site ;
    id_ : EqDec innername ;
    if_ : finite innername ;
    rd : EqDec root ;
    rf : finite root ;
    od : EqDec outername ;
    of : finite outername ; *)
    (* nd : EqDec node ;
    nf : finite node ;
    ed : EqDec edge ;
    ef : finite edge ;*)
    ap : acyclic parent
  }.
  (* sortir les preuves des types interface?*)

  Check ap.

Definition getNode {s i r o k : Type} (bg : bigraph s i r o k) : Type := node bg.
(* Definition getParent {s i r o : Type} (bg : bigraph s i r o) : 
  node bg + s -> node bg + r := 
    parent bg. *)
  
Definition getControl {s i r o k : Type} (bg : bigraph s i r o k) : node bg -> k * nat :=
@control s i r o k bg.

(*Check getControl.
Locate "+".

Print EqDec. *)
(* 
Definition foo (P:Prop) : Prop. *)

Definition mk_new_link {i1 i2 o1 o2 new_edge new_node new_kind: Type} (new_control: new_node -> new_kind * nat)
  (i : (i1 + i2) + (Port new_control)) : (o1 + o2) + new_edge.
  Admitted.

(*close_scope nat_scope*)
Definition juxtaposition {s1 i1 r1 o1 k1 s2 i2 r2 o2 k2 : Type} 
  (b1 : bigraph s1 i1 r1 o1 k1) (b2 : bigraph s2 i2 r2 o2 k2) 
    : bigraph (s1+s2)%type (i1+i2)%type (r1+r2)%type (o1+o2)%type (k1+k2)%type:=
  let new_node : Type := (node b1 + node b2)%type in
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
  let new_ap : acyclic new_parent := @ap (s1+s2) (i1+i2) (r1+r2) (o1+o2) (k1+k2)
  (* match n with 
  |inl n1 => ap
  |inr n2 => ap
  end *)
  in
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
    ap := new_ap
  |}.
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