From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.


Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FinFun.
Require Import Coq.Structures.Equalities.


Notation " f @@ x " := (apply f x)
  (at level 42, right associativity).


Set Warnings "-parsing".
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "parsing".

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope bool_scope.
Local Open Scope N. 
Import ListNotations.

Set Implicit Arguments.

From MyProofs Require Import Node Decidable Edge Innername Iterable Outername Port Root Site. 

Module Bigraph.
Import Nodes.
Import Roots.
Import Sites.
Import Edges.
Import Innernames.
Import Outernames.
Import Ports.

Check node : Type.
Check root : Type.
Check site : Type.
Check edge : Type.
Check innername : Type.
Check outername : Type.
Check port : Type.

Definition place : Type := root + node + site.
Definition link : Type := edge + outername.
Definition point : Type := port + innername.

Definition kappa : Type := ADec.A * nat.
Definition control : Type := node -> kappa.

Definition parent : Type := node + site -> node + root.

(* Function decidability_A (A : Type) : Prop := forall (x y : A), {x = y} + {~x = y}.

Definition decidability_nat : forall (x y : nat), {x = y} + {~x = y} := (decidability_A nat). *)

Record bigraph : Type := Big
  { v : Type ;
   p : parent ; 
    fv : Finite v}.


  
  (* 
      Finite 
      control respected
  *)

(* Add defs *)





End Bigraph.