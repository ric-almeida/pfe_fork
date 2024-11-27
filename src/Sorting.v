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


(*this supposes we give in l the list of nodes with the correct sort
it checks whether all elements of the list is atomic *)
Fixpoint check_atomic {s i r o} {b:bigraph s i r o} (l:list (get_node b)) :=
  match l with 
    | [] => true 
    | nh::nq => (negb (not_is_atomic (b:=b) nh)) && check_atomic nq
    end.


Definition get_children {s i r o} {b:bigraph s i r o} (n: get_node b) : list (get_node b) :=
  filter 
  (fun nh => 
    match (get_parent (bg:=b)) (inl nh) with 
    |inr _ => false
    |inl n' => n == n'
    end) 
  (enum (get_node b)).
    
Definition check_one_child {s i r o} {b:bigraph s i r o} (n: get_node b) : bool := 
  size (get_children n) == 1.

Parameter sort:Type.
Parameter DefautltSort:sort.
Parameter EqDecS : forall x y : sort, {x = y} + {x <> y}.
Parameter signatureK: Kappa -> sort.

Definition check_one_child_of_sort_s {s i r o} {b:bigraph s i r o} (s: sort) (n: get_node b): bool :=
  match get_children n with 
  | child :: [] => EqDecS (signatureK (get_control child)) s
  | _ => false
  end.

(*this supposes we give in l the list of nodes with the correct sort
it checks whether all elements of the list is atomic *)
Fixpoint check_check_one_child_of_sort_s {s i r o} {b:bigraph s i r o} 
  (s_child:sort) (l:list (get_node b)) :=
  match l with 
    | [] => true 
    | nh::nq => check_one_child_of_sort_s s_child nh && check_check_one_child_of_sort_s s_child nq
    end.

(* Definition sort:Type:=nat.
Definition EqDecS : forall x y : sort, {x = y} + {x <> y}.
  intros.
  apply (decP eqnP).
  Defined.
Definition signatureK: Kappa -> sort := fun _ => 0. *)

(*removed parenthesis case*)
Inductive pat : Type :=
  | and_pat (p:pat) (p':pat)
  | or_pat (p:pat) (p':pat)
  | star_pat (lp : list pat)
  | baseS_pat (s:sort).

(*missing the LinkGraph aspect*)
Inductive constructor : Type :=
  | ctrl_name (c:Kappa)
  | patterns (c: Kappa) (p:pat).

Inductive formation_rule : Type := 
  | sort_rule (s:sort) (constructors:list constructor).


Fixpoint check_list_constructor {s i r o}
  (b:bigraph s i r o) (s:sort) (clist:list constructor) : bool :=
  match clist with
    | [] => true
    | hclist :: qclist => 
      match hclist with
      | ctrl_name c =>
          EqDecS (signatureK c) s && 
          check_atomic (filter  (fun nh => EqDecK (get_control (bg:=b) nh) c) 
                                (enum (get_node b))) (*here, use a map*)
      | patterns c p => 
        match p with 
          | and_pat p p' => true
          | or_pat p p' => true
          | star_pat p => true
          | baseS_pat s_child => 
            check_check_one_child_of_sort_s s_child
            (filter  (fun nh => EqDecK (get_control (bg:=b) nh) c) 
                                (enum (get_node b))) 
        end
      end 
      && check_list_constructor b s qclist
    end.


Definition check_formation_rule {s i r o}
    (b:bigraph s i r o) (f:formation_rule) : bool := 
  match f with 
  | sort_rule s clist => check_list_constructor b s clist    
  end.





(*different formations rules*)
Inductive formation_rule : Type :=
  | atomic (x:sort) (*node of sort x has no children*)
  | atomic_control (x:sort) (y:Kappa) (*node of sort x is atomic and has control y*) 
  | cardinality (x:sort) (z:sort) (n:nat) (*node of sort x has n children of sort z*)
  | child_relation (x:sort) (y:sort) (*node of sort x only has y type*)
  | other (p:Prop).



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

  (* | atomic_control x y => 
    EqDecS x (signatureK y) &&
    (*checks all nodes with the correct control and sort are indeed atomic*)
    check_atomic (filter 
      (fun nh => EqDecK (get_control (bg:=b) nh) y && EqDecS (signatureK (get_control (bg:=b) nh)) x) 
      (enum (get_node b)))
    (* need to add that no port/site/root/name has this sort? *) *)

  | _ => true
  end.

End SortBigraphs.

End SortingBig.