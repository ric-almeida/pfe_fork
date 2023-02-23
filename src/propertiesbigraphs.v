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


Require Export Bool DecidableType OrderedType.
Set Implicit Arguments.

From MyProofs Require Import AlgebraBigraphs. 

(*Definition Cmp (elt:Type)(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.


Module Type WSfun (E : DecidableType).



Section properties.
Variable A : Type.

Definition getIdNode {A : Type} (n : node A) : A :=
  match n with Node (Id idn) => idn 
  end.

Definition eq_nodes {A : Type} (n1:node A) (n2:node A) : Prop :=
    getIdNode n1 = getIdNode n2.

Example v2b := Node (Id "v2").
Example sameids : eq_nodes v0 v0.
Proof. unfold eq_nodes. unfold getIdNode. simpl. reflexivity. Qed. 
Example difIds : not (eq_nodes v0 v1).
Proof. unfold eq_nodes. unfold getIdNode. simpl. discriminate. Qed. 

Lemma eq_nodes_refl : forall A : Type, forall n : node A, eq_nodes n n.
Proof. intros. unfold eq_nodes. unfold getIdNode. reflexivity. Qed.   

Fixpoint getk (A:DecidableType) (n:node A) (c:control A) : option :=
  match c with 
    | [] => None
    | (n', idk, k) :: q => if (eq_nodes n n') then Some k else getk n q
  end. 

End properties.

Example k_v0: getk v0 mybig = Some 2.
Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
Example k_v1: getk v1 mybig = Some 2.
Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.
Example k_v2: getk v2 mybig = Some 4.
Proof. unfold getk. unfold getctrl. simpl. reflexivity. Qed.

Fixpoint count_links_to_node {A: Type} (n:node A) (b:bigraph A) :=
  0.

*)
  (** From the time with attachables*)
(*Fixpoint count_ports_on_node_from_edges (atts:list attachables) (n:node) :=
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
