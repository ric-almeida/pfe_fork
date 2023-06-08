From Coq Require Import Arith ZArith Psatz Bool
                        String List Program.Equality Program.Wf.
Require Import Relations.
Require Import Recdef.

Require Import OrderedType.


Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.


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

(*********************START OF DOC*********************)
Module Iterable.
Class Iter (T A : Type) : Type := {
    iter : forall {S E : Type},
      S -> (S -> A -> S + E) -> T -> S + E }.

Definition fold {T A : Type} `{Iter T A} {S : Type} (s : S)
(f : S -> A -> S) (l : T) : S :=
    match iter (E := Empty_set) s (fun s x => inl @@ f s x) l with
    | inl x => x
    | inr e => match e with end
    end.


Definition length {T A : Type} `{Iter T A} (l : T) : N :=
    fold 0 (fun n _ => N.succ n) l.
End Iterable.