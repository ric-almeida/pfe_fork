(* From Coq Require Import Arith ZArith Psatz Bool
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

(* Inductive list (A : Type) : Type :=
| empty (* (n:list A) *) : list A
| elts : A -> list A -> list A.

Notation "[ ]" := empty (format "[ ]") : list_scope.
Notation "[ x ]" := (elts x empty) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (elts x (elts y .. (elts z empty) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope. *)



Module MyBigraph.

Inductive id : Type := 
  Id : string -> id. 

Inductive root : Type := 
  Root : id -> root. 

Inductive k : Type := 
  K : id -> k. 

Inductive node : Type := 
  Node : id -> k -> node. 

Inductive site : Type := 
  Site : id -> site.

Inductive place : Type := 
  | PlaceRoot (r : root)
  | PlaceNode (n : node)
  | PlaceSite (s : site).

(*Milner definition*)
Inductive edgeMilner : Type := 
  EdgeMilner : id -> list node -> edgeMilner. 

Inductive outernameMilner : Type := 
  OuternameMilner : id -> list node -> outernameMilner. 

Inductive link : Type := 
  | LinkEdgeMilner (e : edgeMilner)
  | LinkOuternameMilner (o : outernameMilner).

Inductive port : Type := 
  Port : id -> node -> port.

Inductive innernameMilner : Type := 
  InnernameMilner : id -> list node -> innernameMilner.

Inductive point : Type := 
  | PointPortMilner (p : port)
  | PointInnernameMilner (i : innernameMilner).

(*My definition*)
Inductive outername : Type := 
  Outername : id -> outername. 

Inductive innername : Type := 
  Innername : id -> innername. 

Inductive attachables : Type := 
  | AttachableNode (n : node)
  | AttachableOutername (o : outername)
  | AttachableInnername (i : innername).

Inductive edge : Type := 
  Edge : id -> list attachables -> edge. 

Definition control := k -> nat.

Definition parent := place -> place.

Inductive placegraph : Type :=
  | pg  (v : list node) 
        (ctrl : k -> nat) 
        (prnt : place -> place) 
        (m : list site) 
        (n : list root).

(* Check pg [] control parent (nil site) (nil root) : placegraph. *)


(*Inductive placegraph : Type := 
  | Vp (ns : list node)
  | ctrlp (c : k -> nat)
  | prntp (p : place -> place)
  | mp (ss : list site)
  | np (rs : list root).

Check (ctrlp control)
  : placegraph.

Check (prntp parent)
  : placegraph.*)

(* Definition lnk (p:port) : edge.
Proof. Admitted. *)

Inductive linkgraph : Type :=
  | lg  (v : list node)  
        (e : list edge) 
        (ctrl : k -> nat) 
        (link : port -> edge) 
        (x : list innername) 
        (y : list outername).

(* Check lg (empty node) (empty edge) control lnk (empty innername) (empty outername) : linkgraph. *)

(*Inductive linkgraph : Type := 
  | Vl (ns : list node)
  | El (es : list edge)
  | ctrll (c : k -> nat)
  | linkl (l : port -> edge)
  | Xl (ss : list innername)
  | Yl (rs : list outername).*)

Inductive bigraph : Type :=
  | big (v : list node) 
        (e : list edge) 
        (ctrl : k -> nat) 
        (prnt : place -> place) 
        (lnk : port -> edge) 
        (k : list root) 
        (m : list site) 
        (x : list innername) 
        (y : list outername)
  | pglg (pg : placegraph) (lg : linkgraph).

(* Check big (empty node) (empty edge) control parent lnk (empty root) (empty site) (empty innername) (empty outername) : bigraph.

Check pglg (pg (empty node) control parent (empty site) (empty root)) (lg (empty node) (empty edge) control lnk (empty innername) (empty outername)) : bigraph. *)
(*Inductive bigraph : Type :=
  | V (ns : list node)
  | E (es : list edge)
  | Ctrl (c : k -> nat)
  | Prnt (p : place -> place)
  | Lnk (l : port -> edge)
  | K (rs : list root)
  | M (ss : list site)
  | X (ss : list innername)
  | Y (rs : list outername).*)

Definition getnodes (b:bigraph) : list node :=
  match b with
  | big v _ _ _ _ _ _ _ _ => v
  | pglg (pg v _ _ _ _) _ => v (* je peux pas vérifier que c'est le même ensemble de nodes dans pg et lg*)
  end.

Definition getedges (b:bigraph) : list edge :=
  match b with
  | big _ e _ _ _ _ _ _ _ => e
  | pglg _ (lg _ e _ _ _ _) => e
  end.

Definition getctrl (b:bigraph) : k -> nat :=
  match b with
  | big _ _ ctrl _ _ _ _ _ _ => ctrl
  | pglg (pg _ ctrl _ _ _) _ => ctrl
  end.

Definition getprnt (b:bigraph) : place -> place :=
  match b with
  | big _ _ _ prnt _ _ _ _ _ => prnt
  | pglg (pg _ _ prnt _ _) _ => prnt
  end.

Definition getlnk (b:bigraph) : port -> edge :=
  match b with
  | big _ _ _ _ lnk _ _ _ _ => lnk
  | pglg _ (lg _ _ _ lnk _ _) => lnk
  end.

Definition getk (b:bigraph) : list root :=
  match b with
  | big _ _ _ _ _ k _ _ _ => k
  | pglg (pg _ _ _ _ n) _ => n
  end.

Definition getm (b:bigraph) : list site :=
  match b with
  | big _ _ _ _ _ _ m _ _ => m
  | pglg (pg _ _ _ m _) _ => m
  end.

Definition getx (b:bigraph) : list innername :=
  match b with
  | big _ _ _ _ _ _ _ x _ => x
  | pglg _ (lg _ _ _ _ x _) => x
  end.

Definition gety (b:bigraph) : list outername :=
  match b with
  | big _ _ _ _ _ _ _ _ y => y
  | pglg _ (lg _ _ _ _ _ y) => y
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
  | PlaceNode (Node (Id id) _) => 
    match id with
    | "v0" => PlaceRoot root0
    | "v1" => PlaceNode v0
    | "v2" => PlaceRoot root1
    | _ => PlaceRoot (Root (Id "_")) (* Weird case *)
    end 
  | PlaceSite (Site (Id id)) => 
    match id with
    | "s0" => PlaceNode v0
    | "s1" => PlaceNode v2
    | _ => PlaceRoot (Root (Id "_")) (* Weird case *)
    end
  | _ => PlaceRoot (Root (Id "_")) (* Weird case *)
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
  big
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


(* Smth that checks that number of ports = control(node) *)
Fixpoint count_ports (b:bigraph) (n:node) :=
  match b with
  (*| big (v : list node) 
        (e : list edge) 
        (ctrl : k -> nat) 
        (prnt : place -> place) 
        (lnk : port -> edge) 
        (k : list root) 
        (m : list site) 
        (x : list innername) 
        (y : list outername)
  | pglg pg lg => 0 (*TODO*)*)
  | _ => 0
  end.

Fixpoint map (l:list node) (f: bigraph -> (k -> nat) -> node -> Prop) (b:bigraph) (ctrl: k -> nat) : Prop :=
    match l with
      | [] => True 
      | a :: t => (f b ctrl a) /\ (map t f b ctrl)
    end. 

Fixpoint ctrl_for_one_node (b:bigraph) (ctrl: k -> nat) (n:node) : Prop :=
    match n with
      | Node id k => count_ports b n = ctrl k
    end.

Theorem control_respected : forall b:bigraph, match b with
  | big v e ctrl prnt lnk k m x y => map v ctrl_for_one_node b ctrl 
(*  | big v e ctrl prnt lnk k m x y => map v (fun n =>  count_ports b n = ctrl (K (Id "test")))*)
    (*match v with
      | empty _ => True
      | elts _ (Node id k) q => count_ports b (Node id k) = ctrl k /\ 
    end*)
  | pglg _ _ => True
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

End UnGraphe. *) *)