From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Set Warnings "-parsing".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "parsing".

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope bool_scope.
Import ListNotations.




(*** Bigraph p13 *)

Module MyBigraph.

Variant id : Type := 
  Id : string -> id. 

Variant k : Type := 
  K : id -> k. 

Variant root : Type := 
  Root : id -> root.  

Variant node : Type := 
  Node : id -> k -> node. 

Variant site : Type := 
  Site : id -> site. 

Variant place : Type := 
  | PRoot (r : root)
  | PNode (n : node)
  | PSite (s : site).
(* Variant place : Type := 
  | Root (id : id)
  | Node (id : id)
  | Site (id : id). *)

Variant outername : Type := 
  Outername : id -> outername. 

Variant innername : Type := 
  Innername : id -> innername.
  
(*Pas décrit par Milner mais obligé pour avoir des edges*)
Variant attachables : Type := 
  | AttachableNode (n : node)
  | AttachableOutername (o : outername)
  | AttachableInnername (i : innername).

Variant edge : Type := 
Edge : id -> list attachables -> edge. 

(*Pas trouvé d'utilité encore*)
(*Variant link : Type := 
  | LinkEdge (e : edge)
  | LinkOutername (o : outername).*)

Variant port : Type := 
  Port : id -> node -> port.


(*Pas trouvé d'utilité encore*)
(*Variant point : Type := 
  | PointPort (p : port)
  | PointInnername (i : innername).*)



Variant placegraph : Type :=
  Placegraph (v : list node) 
        (ctrl : k -> nat) 
        (prnt : place -> place) 
        (m : list site) 
        (n : list root).


Variant linkgraph : Type :=
  Linkgraph  (v : list node)  
        (e : list edge) 
        (ctrl : k -> nat) 
        (link : port -> edge) 
        (x : list innername) 
        (y : list outername).


Inductive bigraph : Type :=
  Bigraph (v : list node) 
        (e : list edge) 
        (ctrl : k -> nat) 
        (prnt : place -> place) 
        (lnk : port -> edge) 
        (k : list root) 
        (m : list site) 
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

Definition getctrl (b:bigraph) : k -> nat :=
  match b with
  | Bigraph _ _ ctrl _ _ _ _ _ _ => ctrl
  end.

Definition getprnt (b:bigraph) : place -> place :=
  match b with
  | Bigraph _ _ _ prnt _ _ _ _ _ => prnt
  end.

Definition getlnk (b:bigraph) : port -> edge :=
  match b with
  | Bigraph _ _ _ _ lnk _ _ _ _ => lnk
  end.

Definition getk (b:bigraph) : list root :=
  match b with
  | Bigraph _ _ _ _ _ k _ _ _ => k
  end.

Definition getm (b:bigraph) : list site :=
  match b with
  | Bigraph _ _ _ _ _ _ m _ _ => m
  end.

Definition getx (b:bigraph) : list innername :=
  match b with
  | Bigraph _ _ _ _ _ _ _ x _ => x
  end.

Definition gety (b:bigraph) : list outername :=
  match b with
  | Bigraph _ _ _ _ _ _ _ _ y => y
  end.



(* Example *)
Module testBigraph.

Example v0 := Node (Id "v0") (K (Id "k")).
Example v1 := Node (Id "v0") (K (Id "k")).
Example v2 := Node (Id "v0") (K (Id "m")).

Example x0 := Innername (Id "x0").
Example x1 := Innername (Id "x0").

Example y0 := Outername (Id "y0").
Example y1 := Outername (Id "y1").
Example y2 := Outername (Id "y2").

Example e0 := 
  Edge  (Id "e0") 
    [AttachableNode v0; AttachableNode v2; AttachableInnername x0].

Example e1 := 
  Edge  (Id "e1") 
    [AttachableNode v1; AttachableNode v2].

Example e2 := 
  Edge  (Id "e2") 
    [AttachableNode v2; AttachableOutername y2; AttachableInnername x1].

Example e3 := 
  Edge  (Id "e3") 
    [AttachableNode v2; AttachableOutername y1].

Example e4 := 
  Edge  (Id "e4") 
    [AttachableNode v0; AttachableNode v1;AttachableOutername y0].

Example ctrltest (k:k) :=
  match k with 
  | K (Id "K") => 2
  | K (Id "M") => 4
  | _ => 0 (* ou None *)
  end.

Example root0 := Root (Id "r0").
Example root1 := Root (Id "r1").
 
Example site0 := Site (Id "s0").
Example site1 := Site (Id "s1").

Example prnttest (p:place) :=
  match p with
  | PNode (Node (Id id) _) => 
    match id with
    | "v0" => PRoot root0
    | "v1" => PNode v0
    | "v2" => PRoot root1
    | _ => PRoot (Root (Id "_")) (* Weird case *)
    end 
  | PSite (Site (Id id)) => 
    match id with
    | "s0" => PNode v0
    | "s1" => PNode v2
    | _ => PRoot (Root (Id "_")) (* Weird case *)
    end
  | _ => PRoot (Root (Id "_")) (* Weird case *)
  end.


Example p0_0 := Port (Id "p0_0") v0.
Example p0_1 := Port (Id "p0_1") v0.
Example p1_0 := Port (Id "p1_0") v1.
Example p1_1 := Port (Id "p1_1") v1.
Example p2_0 := Port (Id "p2_0") v2.
Example p2_1 := Port (Id "p2_1") v2.
Example p2_2 := Port (Id "p2_2") v2.
Example p2_3 := Port (Id "p2_3") v2.


Example linktest (p:port) :=
  match p with
  | Port (Id id) _ => 
    match id with
    | "p0_0" => e4
    | "p0_1" => e0
    | "p1_0" => e4
    | "p1_1" => e1
    | "p2_0" => e0
    | "p2_1" => e1
    | "p2_2" => e2
    | "p2_3" => e3
    | _ => Edge  (Id "_") [] (* Weird case *)
    end 
  end.

Example mybig :=  
  Bigraph
    [ v0 ;  v1 ; v2 ]
    [ e0 ; e1 ; e2; e3 ; e4]
    ctrltest
    prnttest 
    linktest
    [ root0 ; root1 ]
    [ site0 ; site1 ]
    [ x0 ; x1 ]
    [ y0 ; y1 ; y2 ].
     

Check mybig
  : bigraph.

End testBigraph.

Definition equalsnodes (n1:node) (n2:node) :=
  match n1 with Node (Id id1) _ =>
    match n2 with Node (Id id2) _ => eqb id1 id2
    end
  end.

Fixpoint count_ports_on_node_from_edges (atts:list attachables) (n:node) :=
  match atts with 
    | [] => 0
    | a :: q => 
      match a with
        | AttachableNode an =>
          if (equalsnodes an n)
            then 1 + (count_ports_on_node_from_edges q n)
            else (count_ports_on_node_from_edges q n)           
        | _ => (count_ports_on_node_from_edges q n)
      end
  end.
  
  (*obligée d'utiliser le comme arg decreasing*)
Fixpoint count_ports_on_node_from_bigraph (b:bigraph) (n:node) (le: list edge) {struct le}:=
  match le with
  | [] => 0
  | (Edge _ atts) :: es => 
    (count_ports_on_node_from_edges atts n) +
      (count_ports_on_node_from_bigraph (
        Bigraph (getv b) es (getctrl b) (getprnt b) (getlnk b) (getk b) (getm b) (getx b) (gety b)) 
        n
        es
      )
  end.


Fixpoint map (l:list node) (f: bigraph -> (k -> nat) -> node -> Prop) (b:bigraph) (ctrl: k -> nat) : Prop :=
  match l with
    | [] => True 
    | a :: t => (f b ctrl a) /\ (map t f b ctrl)
  end. 

Fixpoint ctrl_for_one_node (b:bigraph) (ctrl: k -> nat) (n:node) : Prop :=
  match n with
    | Node id k => count_ports_on_node_from_bigraph b n (gete b) = ctrl k
  end.

Theorem control_respected : forall b:bigraph, match b with
  | Bigraph v e ctrl prnt lnk k m x y => map v ctrl_for_one_node b ctrl 
  end.
Proof. intros. induction b.
  - induction v.
    + unfold map. reflexivity.
    + unfold map. unfold ctrl_for_one_node. unfold map. Admitted.





End MyBigraph.






(*  
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
*)













(*

(* Version bigraphe = place graphe + link graphe *)

Module DeuxGraphs. 

Definition leaf : Type := string. 

Inductive leaves : Type := 
  | Leaves : leaf -> leaves 
  | EmptyLeaves. 

Definition arcs : Type := leaves * leaves. 

Inductive tree : Set := leaves * arcs.

  | Leaf : string -> tree 
  | EmptyTree.

Inductive forest : Type := 
  | Tree : tree -> forest
  | EmptyForest.

Inductive hypergraph : Type := 
  | Node : string -> hypergraph
  | EmptyHypergraph.

Definition bigraph : Type := forest * hypergraph.

End DeuxGraphs.

(* version bigraphe = bigraphe *)

Module UnGraphe.

Definition leaf : Type := string * port. 

End UnGraphe. *)