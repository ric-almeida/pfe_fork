From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.



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


Require Import FMapInterface.



Module Type IdDec.

Parameter A : Type.
Parameter eq_decA : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

End IdDec.



Module MyBigraph.
  Variable A : Type.

  Inductive option {type:Type} : Type :=
    | Some : type -> option
    | None : option.

  Variant id (A:Type) : Type := 
    Id : A -> id A. 

  Variant root : Type := 
    Root : id A -> root.  

  Variant node (A:Type) : Type := 
    Node :  id A -> node A.

  Module NodeProperties (IDDD : IdDec).

    Definition A := IDDD.A.
    Definition eq_decA := IDDD.eq_decA.
  
    Definition getIdNode (n : node A) : A :=
      match n with Node (Id idn) => idn 
      end.
  
    Definition eq_nodes (n1 n2 : node A) : Prop :=
        getIdNode n1 = getIdNode n2.
    
    Definition eq_nodes_dec: forall (n1 n2 : node A),
      { getIdNode n1 = getIdNode n2 } + { ~ getIdNode n1 = getIdNode n2 }.
      intros. destruct n1 as [a1], n2 as [a2].
      destruct (eq_decA (getIdNode (Node a1)) (getIdNode (Node a2))); [left | right].
      - apply e.
      - apply n.
    Defined.
  
    Definition eq_nodes_b (n1:node A) (n2:node A) : bool.
      destruct (eq_decA (getIdNode n1) (getIdNode n2)).
      - exact true.
      - exact false.
      Defined.
  
    Theorem eqb_eq_dec_reflects : forall (n1 n2 : node A),
      reflect (eq_nodes n1 n2) (eq_nodes_b n1 n2).
    Proof.
      intros. unfold eq_nodes_b.
      destruct (eq_nodes_dec n1 n2) as [H1 | H2].
      - destruct eq_decA as [h1 | h2].
        + constructor. apply h1.
        + constructor. apply h2.
      - destruct eq_decA as [h1 | h2].
        + constructor. apply h1.
        + constructor. apply h2.
    Qed.
  
    Lemma eq_nodes_refl : forall n : node A, 
      eq_nodes n n.
    Proof. intros. unfold eq_nodes. unfold getIdNode. reflexivity. Qed.   
  
    Lemma eq_nodes_sym : forall (n1 n2 : node A), 
      eq_nodes n1 n2 -> eq_nodes n2 n1.
    Proof. intros. unfold eq_nodes.
    unfold eq_nodes in H. symmetry in H. apply H. Qed.   
  
    Lemma eq_nodes_trans : forall (n1 n2 n3: node A), 
      ((eq_nodes n1 n2) /\ (eq_nodes n2 n3)) -> (eq_nodes n1 n3).
    Proof. intros. unfold eq_nodes. 
    unfold eq_nodes in H. destruct H as [H1 H2].
    rewrite H1. rewrite H2. reflexivity. Qed.   
  
  
    (* Fixpoint getk {A:Type} (n:node A) (c:control A) : option :=
      match c with 
        | [] => None
        | (n', idk, k) :: q => if (eq_nodes_b n n') then Some k else getk n q
      end. 
  
  
    Example k_v0: getk v0 mybig = Some 2.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
    Example k_v1: getk v1 mybig = Some 2.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
    Example k_v2: getk v2 mybig = Some 4.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
  
    Fixpoint count_links_to_node {A: Type} (n:node A) (b:bigraph A) :=
      0. *)
  
  End NodeProperties.




  Variant site  : Type := 
    Site :  id A -> site. 

  Variant place  : Type := 
    | PRoot (r : root)
    | PNode (n : node A)
    | PSite (s : site).
  
  Variant nors  : Type := 
    | Ssite : site -> nors
    | Snode : node A -> nors.

  Variant norr  : Type := 
    | Rroot : root -> norr
    | Rnode : node A -> norr.

  Variant outername  : Type := 
    Outername :  id A -> outername. 

  Variant innername  : Type := 
    Innername :  id A -> innername.

  Variant edge  : Type := 
    Edge :  id A -> edge. 

  Variant port  : Type := 
    Port : node A -> nat -> port.

  Variant link  : Type := 
    | Ledge: edge -> link
    | Loutername : outername -> link.

  Variant point  : Type := 
    | Pport : port -> point
    | Pinnername : innername -> point.

  (****** SECTION ON MAPS ******)
    Definition key : Type := node A.
    Definition elt : Type := id A * nat.
    Definition t (e:Type) : Type := list (node A * e).
  (****** END SECTION ON MAPS ******)

  Definition control : Type := t elt.
  Definition parent  : Type := list (nors *  norr).
  Definition link_m  : Type := list (point * link).
  Definition empty_control : control := [].

  Variant linkgraph  : Type :=
    Linkgraph 
      (v : list (node A))  
      (e : list edge) 
      (ctrl : control) 
      (lnk : link_m)
      (x : list innername) 
      (y : list outername).

  Variant placegraph {A:Type}: Type :=
    Placegraph 
      (v : list (node A))  
      (ctrl : control) 
      (prnt : parent) 
      (m : list site) 
      (n : list root).

  Inductive bigraph: Type :=
    Bigraph 
      (v : list (node A) )  
      (e : list edge) 
      (ctrl : control) 
      (prnt : parent) 
      (lnk : link_m)
      (m : list site) 
      (n : list root)
      (x : list innername) 
      (y : list outername).

  Definition getv (b:bigraph) : list (node A) :=
    match b with
    | Bigraph v _ _ _ _ _ _ _ _ => v
    end.

  Definition gete (b:bigraph) : list edge :=
    match b with
    | Bigraph _ e _ _ _ _ _ _ _ => e
    end.

  Definition getctrl (b:bigraph) : control :=
    match b with
    | Bigraph _ _ ctrl _ _ _ _ _ _ => ctrl
    end.

  Definition getprnt (b:bigraph) : parent :=
    match b with
    | Bigraph _ _ _ prnt _ _ _ _ _ => prnt
    end.

  Definition getlnk (b:bigraph) : link_m :=
    match b with
    | Bigraph _ _ _ _ lnk _ _ _ _ => lnk
    end.

  Definition getm (b:bigraph) : list site :=
    match b with
    | Bigraph _ _ _ _ _ m _ _ _ => m
    end.

  Definition getn (b:bigraph) : list root :=
    match b with
    | Bigraph _ _ _ _ _ _ n _ _ => n
    end.

  Definition getx (b:bigraph) : list innername :=
    match b with
    | Bigraph _ _ _ _ _ _ _ x _ => x
    end.

  Definition gety (b:bigraph) : list outername :=
    match b with
    | Bigraph _ _ _ _ _ _ _ _ y => y
    end.

  End MyBigraph.

  (* Example
Section testBigraph.

  Example v0 := Node (Id "v0").
  Example v1 := Node (Id "v1").
  Example v2 := Node (Id "v2").

  Example x0 := Innername (Id "x0").
  Example x1 := Innername (Id "x1").

  Example y0 := Outername (Id "y0").
  Example y1 := Outername (Id "y1").
  Example y2 := Outername (Id "y2").

  Example e0 := Edge  (Id "e0").
  Example e1 := Edge  (Id "e1").
  Example e2 := Edge  (Id "e2").
  Example e3 := Edge  (Id "e3").
  Example e4 := Edge  (Id "e4").

  Example ctrltest : control string := 
    empty_control string.
  (* match v with 
    | Node (Id "v0") => (Id "K", 2) 
    | Node (Id "v1") => (Id "K", 2) 
    | Node (Id "v2") => (Id "M", 4)
    | _ => (Id "_", 0) (*weird case*)
    end. *)

  (* Check ctrltest : control string. *)

  Example site0 := Site (Id "s0").
  Example site1 := Site (Id "s1").
    
  Example root0 := Root (Id "r0").
  Example root1 := Root (Id "r1").

  Example prnttest :=
    [ (Snode v0, Rroot root0); 
      (Snode v1, Rnode v0); 
      (Snode v2, Rroot root1);
      (Ssite site0, Rnode v0);
      (Ssite site1, Rnode v2)].

  Example lnktest :=
    [ (Pport (Port v0 1) ,  Loutername y0);
      (Pport (Port v0 2) ,  Ledge e0);
      (Pport (Port v1 1) ,  Loutername y0);
      (Pport (Port v1 2) ,  Ledge e1);
      (Pport (Port v2 1) ,  Loutername y1);
      (Pport (Port v2 2) ,  Loutername y2);
      (Pport (Port v2 3) ,  Ledge e0);
      (Pport (Port v2 4) ,  Ledge e1);
      (Pinnername x0, Ledge e0);
      (Pinnername x1, Loutername y2)].

  Example mybig :=  
    Bigraph
      [ v0 ;  v1 ; v2 ]
      [ e0 ; e1 ; e2; e3 ; e4]
      ctrltest
      prnttest 
      lnktest
      [ site0 ; site1 ]
      [ root0 ; root1 ]
      [ x0 ; x1 ]
      [ y0 ; y1 ; yVariant id (a:A) : Type := 
    Id : a -> id A. 

  Variant root : Type := 
    Root : id A -> root.  

  Variant node  : Type := 
    Node :  id A -> node.

  Module NodeProperties (IDD : IdDec).
    Import IDD.
    Definition A := IDD.A.
  
    Definition getIdNode (n : node A) : A :=
      match n with Node (Id idn) => idn 
      end.
  
    Definition eq_nodes (n1 n2:node A) : Prop :=
        getIdNode n1 = getIdNode n2.
    
    Definition eq_nodes_dec: forall (n1 n2 : node A),
      { getIdNode n1 = getIdNode n2 } + { ~ getIdNode n1 = getIdNode n2 }.
      intros. destruct n1 as [a1], n2 as [a2].
      destruct (eq_decA (getIdNode (Node a1)) (getIdNode (Node a2))); [left | right].
      - apply e.
      - apply n.
    Defined.
  
    Definition eq_nodes_b (n1:node A) (n2:node A) : bool.
      destruct (eq_decA (getIdNode n1) (getIdNode n2)).
      - exact true.
      - exact false.
      Defined.
  
    Theorem eqb_eq_dec_reflects : forall (n1 n2 : node A),
      reflect (eq_nodes n1 n2) (eq_nodes_b n1 n2).
    Proof.
      intros. unfold eq_nodes_b.
      destruct (eq_nodes_dec n1 n2) as [H1 | H2].
      - destruct eq_decA as [h1 | h2].
        + constructor. apply h1.
        + constructor. apply h2.
      - destruct eq_decA as [h1 | h2].
        + constructor. apply h1.
        + constructor. apply h2.
    Qed.
  
    Lemma eq_nodes_refl : forall n : node A, 
      eq_nodes n n.
    Proof. intros. unfold eq_nodes. unfold getIdNode. reflexivity. Qed.   
  
    Lemma eq_nodes_sym : forall (n1 n2 : node A), 
      eq_nodes n1 n2 -> eq_nodes n2 n1.
    Proof. intros. unfold eq_nodes.
    unfold eq_nodes in H. symmetry in H. apply H. Qed.   
  
    Lemma eq_nodes_trans : forall (n1 n2 n3: node A), 
      ((eq_nodes n1 n2) /\ (eq_nodes n2 n3)) -> (eq_nodes n1 n3).
    Proof. intros. unfold eq_nodes. 
    unfold eq_nodes in H. destruct H as [H1 H2].
    rewrite H1. rewrite H2. reflexivity. Qed.   
  
  
    (* Fixpoint getk {A:Type} (n:node A) (c:control A) : option :=
      match c with 
        | [] => None
        | (n', idk, k) :: q => if (eq_nodes_b n n') then Some k else getk n q
      end. 
  
  
    Example k_v0: getk v0 mybig = Some 2.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
    Example k_v1: getk v1 mybig = Some 2.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
    Example k_v2: getk v2 mybig = Some 4.
    Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
  
    Fixpoint count_links_to_node {A: Type} (n:node A) (b:bigraph A) :=
      0. *)
  
  End Properties.




  Variant site  : Type := 
    Site :  id A -> site. 

  Variant place  : Type := 
    | PRoot (r : root)
    | PNode (n : node)
    | PSite (s : site).
  
  Variant nors  : Type := 
    | Ssite : site -> nors
    | Snode : node -> nors.

  Variant norr  : Type := 
    | Rroot : root -> norr
    | Rnode : node -> norr.

  Variant outername  : Type := 
    Outername :  id A -> outername. 

  Variant innername  : Type := 
    Innername :  id A -> innername.

  Variant edge  : Type := 
    Edge :  id A -> edge. 

  Variant port  : Type := 
    Port : node -> nat -> port.

  Variant link  : Type := 
    | Ledge: edge -> link
    | Loutername : outername -> link.

  Variant point  : Type := 
    | Pport : port -> point
    | Pinnername : innername -> point.

  (****** SECTION ON MAPS ******)
    Definition key : Type := node.
    Definition elt : Type := id A * nat.
    Definition t (e:Type) : Type := list (node * e).
  (****** END SECTION ON MAPS ******)

  Definition control : Type := t elt.
  Definition parent  : Type := list (nors *  norr).
  Definition link_m  : Type := list (point * link).
  Definition empty_control : control := [].

  Variant linkgraph  : Type :=
    Linkgraph 
      (v : list node)  
      (e : list edge) 
      (ctrl : control) 
      (lnk : link_m)
      (x : list innername) 
      (y : list outername).

  Variant placegraph {A:Type}: Type :=
    Placegraph 
      (v : list node)  
      (ctrl : control) 
      (prnt : parent) 
      (m : list site) 
      (n : list root).

  Inductive bigraph: Type :=
    Bigraph 
      (v : list node )  
      (e : list edge) 
      (ctrl : control) 
      (prnt : parent) 
      (lnk : link_m)
      (m : list site) 
      (n : list root)
      (x : list innername) 
      (y : list outername).

  Definition getv (b:bigraph) : list node :=
    match b with
    | Bigraph v _ _ _ _ _ _ _ _ => v
    end.

  Definition gete (b:bigraph) : list edge :=
    match b with
    | Bigraph _ e _ _ _ _ _ _ _ => e
    end.

  Definition getctrl (b:bigraph) : control :=
    match b with
    | Bigraph _ _ ctrl _ _ _ _ _ _ => ctrl
    end.

  Definition getprnt (b:bigraph) : parent :=
    match b with
    | Bigraph _ _ _ prnt _ _ _ _ _ => prnt
    end.

  Definition getlnk (b:bigraph) : link_m :=
    match b with
    | Bigraph _ _ _ _ lnk _ _ _ _ => lnk
    end.

  Definition getm (b:bigraph) : list site :=
    match b with
    | Bigraph _ _ _ _ _ m _ _ _ => m
    end.

  Definition getn (b:bigraph) : list root :=
    match b with
    | Bigraph _ _ _ _ _ _ n _ _ => n
    end.

  Definition getx (b:bigraph) : list innername :=
    match b with
    | Bigraph _ _ _ _ _ _ _ x _ => x
    end.

  Definition gety (b:bigraph) : list outername :=
    match b with
    | Bigraph _ _ _ _ _ _ _ _ y => y
    end.

  End Bigraphs.

  (* Example
Section testBigraph.

  Example v0 := Node (Id "v0").
  Example v1 := Node (Id "v1").
  Example v2 := Node (Id "v2").

  Example x0 := Innername (Id "x0").
  Example x1 := Innername (Id "x1").

  Example y0 := Outername (Id "y0").
  Example y1 := Outername (Id "y1").
  Example y2 := Outername (Id "y2").

  Example e0 := Edge  (Id "e0").
  Example e1 := Edge  (Id "e1").
  Example e2 := Edge  (Id "e2").
  Example e3 := Edge  (Id "e3").
  Example e4 := Edge  (Id "e4").

  Example ctrltest : control string := 
    empty_control string.
  (* match v with 
    | Node (Id "v0") => (Id "K", 2) 
    | Node (Id "v1") => (Id "K", 2) 
    | Node (Id "v2") => (Id "M", 4)
    | _ => (Id "_", 0) (*weird case*)
    end. *)

  (* Check ctrltest : control string. *)

  Example site0 := Site (Id "s0").
  Example site1 := Site (Id "s1").
    
  Example root0 := Root (Id "r0").
  Example root1 := Root (Id "r1").

  Example prnttest :=
    [ (Snode v0, Rroot root0); 
      (Snode v1, Rnode v0); 
      (Snode v2, Rroot root1);
      (Ssite site0, Rnode v0);
      (Ssite site1, Rnode v2)].

  Example lnktest :=
    [ (Pport (Port v0 1) ,  Loutername y0);
      (Pport (Port v0 2) ,  Ledge e0);
      (Pport (Port v1 1) ,  Loutername y0);
      (Pport (Port v1 2) ,  Ledge e1);
      (Pport (Port v2 1) ,  Loutername y1);
      (Pport (Port v2 2) ,  Loutername y2);
      (Pport (Port v2 3) ,  Ledge e0);
      (Pport (Port v2 4) ,  Ledge e1);
      (Pinnername x0, Ledge e0);
      (Pinnername x1, Loutername y2)].

  Example mybig :=  
    Bigraph
      [ v0 ;  v1 ; v2 ]
      [ e0 ; e1 ; e2; e3 ; e4]
      ctrltest
      prnttest 
      lnktest
      [ site0 ; site1 ]
      [ root0 ; root1 ]
      [ x0 ; x1 ]
      [ y0 ; y1 ; y2 ].

  (* Check mybig : bigraph string. *)

End testBigraph. *)
End MyBigraph.
2 ].

  (* Check mybig : bigraph string. *)

End testBigraph. *)


