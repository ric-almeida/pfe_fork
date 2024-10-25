Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".


(* Require Import Coq.Logic.Decidable.
Require Import Coq.Setoids.Setoid. *)
(* Require Import ToolsForBigraphs. *)
(* Require Import FinFun. *)
Require Import MyBasics.
Require Import MyEqNat.
Require Import Basics.
Require Import Morphisms.
Require Import Bijections.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import SignatureBig.
Require Import InfSets.


Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Lia.

Require Import MathCompAddings.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Include MyEqNat. 

Import ListNotations.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs (sp : SignatureParameter) 
  (np : InfiniteParameter)
  (vp : InfiniteParameter)
  (ep : InfiniteParameter).
Module s := Signature sp.
Module n := FiniteSubset np.
Module v := FiniteSubset vp.
Module e := FiniteSubset ep.
Include s.
Import n.
Import v.
Import n.
(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.

Record bigraph  (site: nat) 
                (innername: n.NoDupList) 
                (root: nat) 
                (outername: n.NoDupList) : Type := 
  Big  
  { 
    node : v.NoDupList ;
    edge : e.NoDupList ;
    control : v.ListType node -> Kappa ;
    parent : v.ListType node + ordinal site -> v.ListType node + ordinal root ; 
    link : n.ListType innername + Port control -> 
                (ListType outername) + e.ListType edge; 
    ap : FiniteParent parent ;
  }.

End IntroBigraphs.

(** * Getters
  This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : v.NoDupList := 
  (@node s i r o bg).
Definition get_edge {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : e.NoDupList := 
  @edge s i r o bg.
Definition get_control {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : v.ListType (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : v.ListType (get_node bg) + (ordinal s) -> v.ListType (get_node bg) + (ordinal r) :=
  @parent s i r o bg.
Definition get_link {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : {inner:InfType | In inner i} + Port (@get_control s r i o bg) -> {outer:InfType | In outer o} + e.ListType (get_edge bg) :=
  @link s i r o bg.
Definition get_ap {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FiniteParent (get_parent (bg:=bg)) := 
  @ap s i r o bg.
Definition get_site {s i r o} (b:bigraph s i r o) : nat := s.
Definition get_root {s i r o} (b:bigraph s i r o) : nat := r.
Definition get_innername {s i r o} (b:bigraph s i r o) : NoDupList := i.
Definition get_outername {s i r o} (b:bigraph s i r o) : NoDupList := o.
End GettersBigraphs.

(** Tools for proof irrelevance *)

Theorem parent_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n n': 'I_s, n = n' ->
  get_parent (bg:=b) (inr n) = get_parent (inr n').
  Proof. 
  intros. f_equal. f_equal. apply H.
  Qed.

Theorem innername_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n:InfType, forall Hn: In n i, forall Hn':In n i,
  get_link (bg:=b) (inl (exist _ n Hn)) = get_link (bg:=b) (inl (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.
Theorem port_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n n':v.ListType (get_node b), forall port:nat, forall Hport Hport', n=n' ->
  get_link (bg:=b) (inr (existT 
    (fun n : v.ListType (get_node b) => 'I_(Arity (get_control (bg:=b) n))) 
    n
    (Ordinal (n:=Arity (get_control (bg:=b) n)) (m:=port) Hport))) =
  get_link (bg:=b) (inr (existT 
    (fun n : v.ListType (get_node b) => 'I_(Arity (get_control (bg:=b) n))) 
    n'
    (Ordinal (n:=Arity (get_control (bg:=b) n')) (m:=port) Hport'))).
  Proof. 
  intros. apply f_equal. apply f_equal. subst n. 
  rewrite (Ordinal_proof_irrelevance _ _ Hport). reflexivity.
  Qed.
Theorem port_proof_irrelevant_full {s i r o} (b:bigraph s i r o): 
  forall n n':v.ListType (get_node b), 
  forall port : 'I_(Arity (get_control n)),
  forall port': 'I_(Arity (get_control n')), 
  n=n' -> nat_of_ord port = nat_of_ord port' ->
  get_link (bg:=b) (inr (existT 
    _ 
    n port)) =
  get_link (bg:=b) (inr (existT 
    _ 
    n' port')).
  Proof. 
  intros. apply f_equal. apply f_equal. subst n.
  unfold nat_of_ord in H0.
  simpl in H0.
  destruct port as [m Hm]. 
  destruct port' as [m' Hm'].
  subst m.
  erewrite (Ordinal_proof_irrelevance _ _ Hm Hm').
  reflexivity.
  Qed.

(** Section defining some elementary bigraphs *)
Section ElementaryBigraphs. 
Definition bigraph_id (s: nat) (i : NoDupList) : bigraph s i s i. (*actually s i s (permutation i) *)
  Proof.
  eapply (@Big s i s i
          v.EmptyNDL (*node : ∅*)
          e.EmptyNDL (*edge : ∅*)
          _ (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  Unshelve.
  - intros [inner | port]. (*link_|{names} : id*)
    + left. apply inner. 
    + destruct port as [[port InPort] Hport]. destruct InPort.
  - intros [_ []]. (*acyclic parent*)
  - intros [_ []]. (*control*)
  Defined.

Definition bigraph_empty : bigraph 0 EmptyNDL 0 EmptyNDL := bigraph_id 0 EmptyNDL.


Definition discrete_atom 
  (node:vp.InfType) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 0 EmptyNDL 1 o.
  Proof.
  eapply (@Big
      0 EmptyNDL 1 o
      (v.OneelNDL node)
      (e.EmptyNDL)
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr (Ordinal (ltn0Sn 0))
        | inr s => _
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    3:{ intros [i|p].  
      - destruct i as [i H]. elim H. 
      - left. unfold ListType. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (Coq.Lists.List.nth p o DefaultInfType). 
      apply nth_In. destruct Hkappa as [Hkappa]. rewrite <- Hkappa.
      set (tmp := ltP (m:=p) (n:=Arity k)).
      apply Bool.reflect_iff in tmp.
      rewrite tmp.
      apply Hp. } (*link*)
    2:{ destruct s. exfalso. apply (nlt_0_it m). apply i. } (*parent*)
    unfold FiniteParent. simpl. (*acyclic*)
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    Defined. 

Definition discrete_ion (node:vp.InfType) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 1 EmptyNDL 1 o.
  Proof.
  eapply (@Big
      1 EmptyNDL 1 o
      (v.OneelNDL node)
      (e.EmptyNDL)
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr (Ordinal (ltn0Sn 0))
        | inr s => _
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    - unfold FiniteParent. simpl. (*Acyclic Parent*)
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    - left. unfold v.ListType. exists node. constructor. reflexivity. (*parent*)
    - intros [i|p].  (*link*)
      + destruct i as [i H]. elim H. 
      + left. unfold ListType. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (Coq.Lists.List.nth p o DefaultInfType). 
      apply nth_In. destruct Hkappa as [Hkappa].
      rewrite <- Hkappa.
      set (tmp := ltP (m:=p) (n:=Arity k)).
      apply Bool.reflect_iff in tmp.      
      rewrite tmp.
      apply Hp. 
    Defined. 

Definition permutationbig (n : nat) : bigraph n EmptyNDL n EmptyNDL. 
  Proof. 
  eapply (@Big n EmptyNDL n EmptyNDL
    v.EmptyNDL (*node : ∅*)
    e.EmptyNDL (*edge : ∅*)
    _ (*control : ∅_-> Kappa*)
    (fun sn => match sn with |inr s => inr s | inl n => _ end) (*parent : sites -> root*)
  ).
  Unshelve.
  - intros [[inner Hinner] | [[port Hp] Hport]]. (*link : ∅*)
    + destruct Hinner.
    + destruct Hp. 
  - intros [_ []]. (*acyclic parent*)
  - intros [_ []]. (*control*)
  - destruct n as [n []].
  Defined.

Definition merge {n:nat} : bigraph n EmptyNDL 1 EmptyNDL.
  Proof. 
  eapply (@Big n EmptyNDL 1 EmptyNDL
    v.EmptyNDL (*node : ∅*)
    e.EmptyNDL (*edge : ∅*)
    _ (*control : ∅ ->_Kappa*)
    (fun s => inr (Ordinal (ltn0Sn 0))) (*parent : sites -> root*)
  ).
  Unshelve.
  - intros [[inner Hinner] | [[port Hp] Hport]]. (*link : ∅*)
    + destruct Hinner.
    + destruct Hp. 
  - intros [_ []]. (*acyclic parent*)
  - intros [_ []]. (*control*)
  Defined.

Definition big_1 := @merge 0.

Definition symmetry_big (m:nat) (X:NoDupList) (n:nat) (Y:NoDupList) :
  bigraph (m+n) (X ∪ Y) (m+n) (X ∪ Y).
  Proof. 
  eapply (@Big (m+n) (X ∪ Y) (m+n) (X ∪ Y)
  v.EmptyNDL (*node : ∅*)
  e.EmptyNDL (*edge : ∅*)
  _ (*control : ∅ ->_Kappa*)
    _ _ _
  ).
  Unshelve.  
  - intros [_ []]. (*control*)
  - intros [[_ []]|s]. (*parent*)
    right. destruct s as [s Hs].
    destruct (ltnP s m).
    * exists (s+n). rewrite ltn_add2r. apply i.
    * exists (s-m). 
    set (tmp := leq_subr m s).
    apply (leq_ltn_trans tmp) in Hs.
    apply Hs.
  - intros [inner | [[_ []] []]]. (*link : ∅*)
    left. apply inner.
  - intros [_ []]. (*acyclic parent*)
  Defined.

Definition substitution (i:NoDupList) (name:InfType) : bigraph 0 i 0 (OneelNDL name).
  Proof. 
  eapply (@Big 0 i 0 (OneelNDL name)
    v.EmptyNDL (*node : ∅*)
    e.EmptyNDL (*edge : ∅*)
    _ (*control : ∅_Kappa*)
    _ (*parent : sites -> root*)
  ).
  Unshelve.
  - intros [inner | [[_ []] []]]. (*link : ∅*)
    left. exists name. simpl. left. reflexivity.
  - intros [_ []]. (*acyclic parent*)
  - intros [_ []]. (*control*)
  - intros [[_ []] | [site Hsite]]. (*parent*)
    discriminate Hsite.
  Defined.

Definition elementary_renaming (n n':InfType) := substitution (OneelNDL n) n'.

Definition closure (name:InfType) : bigraph 0 (OneelNDL name) 0 EmptyNDL.
  Proof. 
  eapply (@Big 0 (OneelNDL name) 0 EmptyNDL
    v.EmptyNDL (*node : ∅*)
    (e.OneelNDL (e.DefaultInfType)) (*edge : ∅*)
    _ (*control : ∅_Kappa*)
    _ (*parent : sites -> root*)
  ).
  Unshelve.
  - intros [inner | [[_ []] _]]. (*link : ∅*)
    right. unfold e.ListType. exists e.DefaultInfType. constructor. reflexivity.
  - intros [_ []]. (*acyclic parent*)
  - intros [_ []]. (*control*)
  - intros [[_ []] | [site Hsite]]. (*parent*)
    discriminate Hsite.
  Defined.

Definition join_big := @merge 2. 
End ElementaryBigraphs.

Global Notation "∅" := bigraph_empty.

End Bigraphs.

