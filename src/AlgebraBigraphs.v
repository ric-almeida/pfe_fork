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



Module IdDec.

Parameter A : Type.
Parameter eq_decA : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

End IdDec.



Module MyBigraph1.
  Variable A : Type.

  Inductive option {type:Type} : Type :=
    | Some : type -> option
    | None : option.

  Variant id (A:Type) : Type := 
    Id : A -> id A. 

  Variant node (A:Type) : Type := 
    Node :  id A -> node A.

(* End MyBigraph1. *)
  (***** NODE PROPERTIES *****)

  Module NodeProperties.

    Definition AD := IdDec.A.
    Definition eq_decA := IdDec.eq_decA.

    Definition getIdNode (n : node AD) : AD :=
      match n with Node (Id idn) => idn 
      end.
  
    Definition eq_nodes (n1 n2 : node AD) : Prop :=
        getIdNode n1 = getIdNode n2.
    
    Definition eq_nodes_dec: forall (n1 n2 : node AD),
      { getIdNode n1 = getIdNode n2 } + { ~ getIdNode n1 = getIdNode n2 }.
      intros. destruct n1 as [a1], n2 as [a2].
      destruct (eq_decA (getIdNode (Node a1)) (getIdNode (Node a2))); [left | right].
      - apply e.
      - apply n.
    Defined.
  
    Definition eq_nodes_b (n1:node AD) (n2:node AD) : bool.
      destruct (eq_decA (getIdNode n1) (getIdNode n2)).
      - exact true.
      - exact false.
      Defined.
  
    Theorem eqb_eq_dec_reflects : forall (n1 n2 : node AD),
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
  
    Lemma eq_nodes_refl : forall n : node AD, 
      eq_nodes n n.
    Proof. intros. unfold eq_nodes. unfold getIdNode. reflexivity. Qed.   
  
    Lemma eq_nodes_sym : forall (n1 n2 : node AD), 
      eq_nodes n1 n2 -> eq_nodes n2 n1.
    Proof. intros. unfold eq_nodes.
    unfold eq_nodes in H. symmetry in H. apply H. Qed.   
  
    Lemma eq_nodes_trans : forall (n1 n2 n3: node AD), 
      ((eq_nodes n1 n2) /\ (eq_nodes n2 n3)) -> (eq_nodes n1 n3).
    Proof. intros. unfold eq_nodes. 
    unfold eq_nodes in H. destruct H as [H1 H2].
    rewrite H1. rewrite H2. reflexivity. Qed.   
  
  End NodeProperties.
  (****** END NODE PROPERTIES ******)

  Import NodeProperties.

  Variant root (A:Type) : Type := 
    Root : id A -> root A.  

  Variant site (A:Type) : Type := 
    Site :  id A -> site A. 

  Variant place (A:Type) : Type := 
    | PRoot (r : root A)
    | PNode (n : node A)
    | PSite (s : site A).
  
  Variant nors (A:Type) : Type := 
    | Ssite : site A -> nors A
    | Snode : node A -> nors A.

  Variant norr (A:Type) : Type := 
    | Rroot : root A -> norr A
    | Rnode : node A -> norr A.

  Variant outername (A:Type) : Type := 
    Outername :  id A -> outername A. 

  Variant innername (A:Type) : Type := 
    Innername :  id A -> innername A.

  Variant edge (A:Type) : Type := 
    Edge :  id A -> edge A. 

  Variant port (A:Type) : Type := 
    Port : node AD -> nat -> port A.

  Variant link (A:Type) : Type := 
    | Ledge: edge A -> link A
    | Loutername : outername A -> link A.

  Variant point (A:Type) : Type := 
    | Pport : port A -> point A
    | Pinnername : innername A -> point A.

  (****** SECTION ON CONTROL ******)
    Definition control (A:Type) : Type.
     - exact (list (node A * (id A * nat))). Defined.
    Definition elements_control (A:Type) (elts:control A) : list (node A * (id A * nat)).
     - exact elts. Defined.
  (****** END SECTION ON CONTROL ******)

  (****** SECTION ON PARENT ******)
    Definition parent (A:Type) : Type.
    - exact (list (nors A *  norr A)). Defined.
    Definition elements_parent (A:Type) (elts:parent A) : list (nors A * norr A).
    - exact elts. Defined.
  (****** END SECTION ON PARENT ******)

  (****** SECTION ON LINK ******)
  Definition link_m (A:Type) : Type.
  - exact (list (point A * link A)). Defined.
  Definition elements_link_m (A:Type) (elts:link_m A) : list (point A * link A).
  - exact elts. Defined.
  (****** END SECTION ON LINK ******)
  
  (* Type is AD bc it needs to be decidable *)
  Variant linkgraph : Type :=
    Linkgraph 
      (v : list (node AD))  
      (e : list (edge AD)) 
      (ctrl : control AD) 
      (lnk : link_m AD)
      (x : list (innername AD)) 
      (y : list (outername AD)).      
      
  (* Type is AD bc it needs to be decidable *)
  Variant placegraph : Type :=
    Placegraph 
      (v : list (node AD))  
      (ctrl : control AD) 
      (prnt : parent AD) 
      (m : list (site AD)) 
      (n : list (root AD)).

  (* Type is AD bc it needs to be decidable *)
  Variant bigraph: Type :=
    Bigraph 
      (v : list (node AD) )  
      (e : list (edge AD)) 
      (ctrl : control AD) 
      (prnt : parent AD) 
      (lnk : link_m AD)
      (m : list (site AD)) 
      (n : list (root AD))
      (x : list (innername AD)) 
      (y : list (outername AD)).

  Definition getv (b:bigraph) : list (node AD) :=
    match b with
    | Bigraph v _ _ _ _ _ _ _ _ => v
    end.

  Definition setv (b:bigraph) (v': list (node AD)): bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v' e ctrl prnt lnk m n x y
    end.

  Definition gete (b:bigraph) : list (edge AD) :=
    match b with
    | Bigraph _ e _ _ _ _ _ _ _ => e
    end.

  Definition sete (b:bigraph) (e': list (edge AD)): bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e' ctrl prnt lnk m n x y
    end.

  Definition getctrl (b:bigraph) : control AD :=
    match b with
    | Bigraph _ _ ctrl _ _ _ _ _ _ => ctrl
    end.

  Definition setctrl (b:bigraph) (ctrl': control AD): bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl' prnt lnk m n x y
    end.

  Definition getprnt (b:bigraph) : parent AD :=
    match b with
    | Bigraph _ _ _ prnt _ _ _ _ _ => prnt
    end.

  Definition setprnt (b:bigraph) (prnt': parent AD): bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt' lnk m n x y
    end.

  Definition getlnk (b:bigraph) : link_m AD :=
    match b with
    | Bigraph _ _ _ _ lnk _ _ _ _ => lnk
    end.

  Definition setlnk (b:bigraph) (lnk': link_m AD): bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt lnk' m n x y
    end.

  Definition getm (b:bigraph) : list (site AD) :=
    match b with
    | Bigraph _ _ _ _ _ m _ _ _ => m
    end.

  Definition setm (b:bigraph) (m': list (site AD)) : bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt lnk m' n x y
    end.

  Definition getn (b:bigraph) : list (root AD) :=
    match b with
    | Bigraph _ _ _ _ _ _ n _ _ => n
    end.

  Definition setn (b:bigraph) (n': list (root AD)) : bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt lnk m n' x y
    end.

  Definition getx (b:bigraph) : list (innername AD) :=
    match b with
    | Bigraph _ _ _ _ _ _ _ x _ => x
    end.

  Definition setx (b:bigraph) (x': list (innername AD)) : bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt lnk m n x' y
    end.

  Definition gety (b:bigraph) : list (outername AD) :=
    match b with
    | Bigraph _ _ _ _ _ _ _ _ y => y
    end.

  Definition sety (b:bigraph) (y': list (outername AD)) : bigraph :=
    match b with
    | Bigraph v e ctrl prnt lnk m n x y => Bigraph v e ctrl prnt lnk m n x y'
    end.


  (** Try to prove that control is respected **)
  Fixpoint getk (n:node AD) (c:control AD) : option :=
    match (elements_control c) with 
      | [] => None
      | (n',(idA, k)) :: q => if (eq_nodes_b n n') then Some k else getk n q
    end.
  
  Fixpoint count_links_to_node (n:node AD) (l:link_m AD) : nat :=
    match (elements_link_m l) with 
      | [] => 0
      | (Pinnername _ , _) :: q => count_links_to_node n q
      | (Pport (Port _ n' _ ) , _) :: q => (* /!\ pas vérifié le type de Port décidable :Port AD n' i *)
        if (eq_nodes_b n n') then 1 + count_links_to_node n q else count_links_to_node n q
    end. 

  Definition control_for_one_node (b:bigraph) (n:node AD) :=
    match (getk n (getctrl b)) with 
      | None => False
      | Some k => k = count_links_to_node n (getlnk b)
    end.

  (* /!\ Problème avec l'élément décroissant *)
  Fixpoint map_control_for_one_node (b:bigraph) (v:list (node AD)) {struct v}:= 
    match v with
      | [] => True 
      | n :: q => control_for_one_node b n /\ map_control_for_one_node (setv b q) q
    end.

  (** Je pense qu'on peut pas le prouver, juste il fau supposer que c'est vrai **)
  Axiom control_respected : 
    forall (b:bigraph), map_control_for_one_node b (getv b).
  (*Proof. intros. destruct (getv b).
  - unfold map_control_for_one_node. auto.
  - unfold map_control_for_one_node. split; unfold control_for_one_node.
    + destruct (getk n (getctrl b)) as [n0 | H].
      ++ destruct count_links_to_node as [n2 | n3]. 
        +++ auto. Admitted.   *)

End MyBigraph1.





  
 
