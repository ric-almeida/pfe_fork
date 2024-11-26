Set Warnings "-notation-overridden, -parsing, -masking-absolute-name".


Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import ParallelProduct.
Require Import MergeProduct.
Require Import Nesting.
Require Import MathCompAddings.


Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Coq.Lists.List.



From mathcomp Require Import all_ssreflect.

Import ListNotations.

Module SortingBig (s : SignatureParameter) (n : NamesParameter).

Module MB := MergeBig s n.
Include MB. 



Section SortBigraphs.
Parameter sort:Type.
Parameter EqDecS : forall x y : sort, {x = y} + {x <> y}.
Parameter signatureK: Kappa -> sort.

(* Definition sort:Type:=nat.
Definition EqDecS : forall x y : sort, {x = y} + {x <> y}.
  intros.
  apply (decP eqnP).
  Defined.
Definition signatureK: Kappa -> sort := fun _ => 0. *)


(*different formations rules*)
Inductive formation_rule : Type :=
  | atomic (x:sort) (*node of sort x has no children*)
  | atomic_control (x:sort) (y:Kappa) (*node of sort x is atomic and has control y*) 
  | cardinality (x:sort) (z:sort) (n:nat) (*node of sort x has n children of sort z*)
  | child_relation (x:sort) (y:sort) (*node of sort x only has y type*)
  | other (p:Prop).

(*atomic node = has no children = is not an image through parent (neither through a site nor a node) *)
Definition not_is_atomic {s i r o} {b:bigraph s i r o} (n: get_node b) : bool := 
  Coq.Lists.List.existsb 
    (A := ordinal s)
    (fun s => match (get_parent (bg:=b)) (inr s) with 
      |inr _ => false 
      |inl n' => n == n'
      end) 
    (enum (ordinal s))
  || 
  Coq.Lists.List.existsb 
    (A := get_node b)
    (fun nod => match (get_parent (bg:=b)) (inl nod) with 
      |inr _ => false 
      |inl n' => n == n'
      end) 
    (enum ((get_node b))).


(*this supposes we give in l the list of nodes with the correct sort*)
Fixpoint check_atomic {s i r o} {b:bigraph s i r o} (l:list (get_node b)) :=
  match l with 
    | [] => true 
    | nh::nq => (negb (not_is_atomic (b:=b) nh)) && check_atomic nq
    end.

(*predicat on whether b verifies f*)
Definition check_formation_rule {s i r o}
    (b:bigraph s i r o) (f:formation_rule) : bool := 
  match f with 
  | atomic x => 
    (*checks all nodes with the correct sort are indeed atomic*)
    check_atomic (filter 
      (fun nh => EqDecS (signatureK (get_control (bg:=b) nh)) x) 
      (enum (get_node b)))
    (*need to add that no port/site/root/name has this sort?*)

  | atomic_control x y => 
    EqDecS x (signatureK y) &&
    (*checks all nodes with the correct control and sort are indeed atomic*)
    check_atomic (filter 
      (fun nh => EqDecK (get_control (bg:=b) nh) y && EqDecS (signatureK (get_control (bg:=b) nh)) x) 
      (enum (get_node b)))
    (*need to add that no port/site/root/name has this sort?*)

  | _ => true
  end.

End SortBigraphs.

End SortingBig.