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



Module MyBigraph.

Section Bigraphs.

  Variable A : Type.

  Variant id : Type := 
    Id : A -> id. 

  Variant root : Type := 
    Root : id -> root.  

  Variant node : Type := 
    Node : id -> node.

  Variant site : Type := 
    Site : id -> site. 

  Variant place : Type := 
    | PRoot (r : root)
    | PNode (n : node)
    | PSite (s : site).
  
  Variant nors : Type := 
    | Ssite : site -> nors
    | Snode : node -> nors.

  Variant norr : Type := 
    | Rroot : root -> norr
    | Rnode : node -> norr.

  Variant outername : Type := 
    Outername : id -> outername. 

  Variant innername : Type := 
    Innername : id -> innername.

  Variant edge : Type := 
    Edge : id -> edge. 

  Variant port : Type := 
    Port : node -> nat -> port.

  Variant link : Type := 
    | Ledge: edge -> link
    | Loutername : outername -> link.

  Variant point : Type := 
    | Pport : port -> point
    | Pinnername : innername -> point.

  Variant linkgraph : Type :=
    Linkgraph 
      (v : list node)  
      (e : list edge) 
      (ctrl : node -> id -> nat) 
      (lnk : point -> link) 
      (* lnk : port + innername -> edge + outername *)
      (x : list innername) 
      (y : list outername).

  Variant placegraph : Type :=
  Placegraph 
    (v : list node) 
    (ctrl : node -> id -> nat) 
    (prnt : nors -> norr) 
    (m : list site) 
    (n : list root).

  Inductive bigraph : Type :=
    Bigraph 
      (v : list node) 
      (e : list edge) 
      (ctrl : node -> id -> nat) 
      (prnt : nors -> norr) 
      (lnk : point -> link) 
      (m : list site) 
      (n : list root) 
      (x : list innername) 
      (y : list outername).

  Inductive bigraph_bis 
    (v : list node) 
    (e : list edge) 
    (ctrl : node -> id -> nat) 
    (prnt : node + site -> node + root)
    (lnk : point -> link)  
      : Type :=
        Bigraph_bis    
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

  Definition getctrl (b:bigraph) : node -> id -> nat :=
    match b with
    | Bigraph _ _ ctrl _ _ _ _ _ _ => ctrl
    end.

  Definition getprnt (b:bigraph) : nors -> norr :=
    match b with
    | Bigraph _ _ _ prnt _ _ _ _ _ => prnt
    end.

  Definition getlnk (b:bigraph) : point -> link :=
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

  (* Example *)
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

  Example kappa (i:id string) :=
    match i with 
    | Id "K" => 2
    | Id "M" => 4
    | _ => 0 (* ou None *)
    end.
  
  Example ctrltest (n:node string) :=
    match n with 
    | Node i => kappa 
    end.

  Example site0 := Site (Id "s0").
  Example site1 := Site (Id "s1").
    
  Example root0 := Root (Id "r0").
  Example root1 := Root (Id "r1").

  Example prnttest (p:nors string) :=
    match p with
    | Snode (Node (Id "v0")) => Rroot root0
    | Snode (Node (Id "v1")) => Rnode v0
    | Snode (Node (Id "v2")) => Rroot root1
    | Ssite (Site (Id "s0")) => Rnode v0
    | Ssite (Site (Id "s1")) => Rnode v2 
    | _ => Rroot (Root (Id "_")) (* Weird case *)
    end.

  Example lnktest (p:point string) :=
    match p with
    | Pport (Port (Node (Id "v0")) 1) => Loutername y0
    | Pport (Port (Node (Id "v0")) 2) => Ledge e0
    | Pport (Port (Node (Id "v1")) 1) => Loutername y0
    | Pport (Port (Node (Id "v1")) 2) => Ledge e1
    | Pport (Port (Node (Id "v2")) 1) => Loutername y1
    | Pport (Port (Node (Id "v2")) 2) => Loutername y2
    | Pport (Port (Node (Id "v2")) 3) => Ledge e0
    | Pport (Port (Node (Id "v2")) 4) => Ledge e1
    | Pinnername (Innername (Id "x0")) => Ledge e0
    | Pinnername (Innername (Id "x1")) => Loutername y2
    | _ => Loutername (Outername (Id "_"))
    end.

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

End testBigraph.

(*
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
  
  (*obligée d'utiliser le comme arg decreasing 
    (*TODO*) foldleft <- existe déja *)
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
    + unfold map. Admitted. 

*)



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