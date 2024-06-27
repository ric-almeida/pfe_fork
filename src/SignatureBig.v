Require Import MyBasics.
Require Import Bijections.
Require Import FunctionalExtensionality.

(** * This module implements a signature
  It contains a Module Type with Kappa and Arity, and Ports built from the Signature *)
Module Type SignatureParameter.

Parameter Kappa:Type.
Parameter Arity:Kappa-> nat.

End SignatureParameter.

Module Signature (SP:SignatureParameter).
Include SP.
Definition Port {node : Type} (control : node -> Kappa): Type :=
  { n : node & fin (Arity (control n)) }.

Definition join {A B C : Type} (p : A -> C) (q : B -> C) (ac : A+B) : C :=
  match ac with
  | inl a => (p a)
  | inr b => (q b)
  end.

Definition bij_join_port_forward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa) :
  Port c1 + Port c2 -> 
  Port (join c1 c2).
  Proof.
  refine (fun p => match p with
              | inl (existT _ vi1 Hvi1) => _
              | inr (existT _ vi2 Hvi2) => _
              end).
  + exists (inl vi1).
    destruct Hvi1 as (i1, Hi1).
    exists i1.
    exact Hi1.
  + exists (inr vi2).
    destruct Hvi2 as (i2, Hi2).
    exists i2.
    exact Hi2.
  Defined.

Definition bij_join_port_backward { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  Port (join c1 c2) -> Port c1 + Port c2.
  Proof.
    destruct 1 as ([v1 | v2], (i, Hvi)).
    + left.
      exists v1.
      exists i.
      apply Hvi.
    + right.
      exists v2.
      exists i.
      apply Hvi.
    Defined.

Definition bij_join_port { n1 n2 } (c1 : n1 -> Kappa) (c2 : n2 -> Kappa)  :
  bijection (Port c1 + Port c2) (Port (join c1 c2)).
  Proof.
  apply 
    (mkBijection _ _ 
    (bij_join_port_forward c1 c2) 
    (bij_join_port_backward c1 c2)).
  + apply functional_extensionality.
    destruct x as ([v1|v2], (i, Hvi)).
    - reflexivity.
    - reflexivity.
  + apply functional_extensionality.
    destruct x as [(v1, (i1, Hvi1)) | (v2, (i2, Hvi2))].
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
    - unfold funcomp, id.
      simpl.
      apply f_equal.
      reflexivity.
  Defined.

Definition bij_port_void (c : void -> Kappa) : bijection (Port c) void.
  Proof.
  apply (mkBijection _ _ (fun vi => match vi with existT _ v _ => void_univ_embedding v end) (void_univ_embedding)).
  + apply functional_extensionality.
    destruct x.
  + apply functional_extensionality.
    destruct x as (v, (i, H)).
    destruct v.
  Defined.

End Signature.
