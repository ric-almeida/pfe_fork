Set Warnings "-notation-overridden, -parsing".
Set Warnings "-notation-overridden, -notation-overriden".


Require Import Coq.Logic.Decidable.
Require Import Coq.Setoids.Setoid.
(* Require Import ToolsForBigraphs. *)
Require Import FinFun.
Require Import MyBasics.
Require Import Basics.
Require Import Morphisms.
Require Import FinDecTypes.
Require Import Bijections.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import PropExtensionality.
Require Import SignatureBig.
Require Import Names.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Lia.

Require Import mathcomp.ssreflect.fintype. 
Require Import ssrfun.


Import ListNotations.

(** This module implements bigraphs and basic operations on bigraphs *)
Module Bigraphs (sp : SignatureParameter) (np : Names.NamesParameter).
Module s := Signature sp.
Module n := Names np.
Include s.
Include n.
(** * Definition of a bigraph
  This section defines the Type bigraph *)
Section IntroBigraphs.

Record bigraph  (site: nat) 
                (innername: NoDupList) 
                (root: nat) 
                (outername: NoDupList) : Type := 
  Big  
  { 
    node : FinDecType ;
    edge : FinDecType ;
    control : type node -> Kappa ;
    parent : type node + fin site -> 
                (type node) + (fin root) ; 
    link : NameSub innername + Port control -> 
                (NameSub outername) + (type edge); 
    ap : FiniteParent parent ;
  }.
  
Record bigraph'  (site': nat) 
                (innername': NoDupList) 
                (root': nat) 
                (outername': NoDupList) : Type := 
  Big'  
  { 
    node' : finType ;
    edge' : finType ;
    control' : node' -> Kappa ;
    parent' : node' + fin site' -> 
                node' + (fin root') ; 
    link' : NameSub innername' + Port control' -> 
                (NameSub outername') + edge'; 
    ap' : FiniteParent parent' ;
  }.
End IntroBigraphs.

(** * Getters
  This section is just getters to lightenn some notations *)
Section GettersBigraphs.
Definition get_node {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  node s i r o bg.
Definition get_edge {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : FinDecType := 
  edge s i r o bg.
Definition get_control {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : type (get_node bg) -> Kappa :=
  @control s i r o bg.
Definition get_parent {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : (type (get_node bg)) + (fin s) -> (type (get_node bg)) + (fin r) :=
  @parent s i r o bg.
Definition get_link {s r : nat} {i o : NoDupList} (bg : bigraph s i r o) : {inner:Name | In inner i} + Port (get_control bg) -> {outer:Name | In outer o} + type (get_edge bg) :=
  @link s i r o bg.
End GettersBigraphs.

Class MyEqNat (x y : nat) := { eqxy : x = y }.
Definition howomg {a b} (m: MyEqNat a b) : a = b := eqxy. 
#[export] Instance MyEqNat_refl (x:nat) : MyEqNat x x.
  Proof. 
  constructor. reflexivity. 
  Qed.

#[export] Instance MyEqNat_add {s1 s2 r3 r4} (eqs2r4 : MyEqNat s2 r4) (eqs1r3 : MyEqNat s1 r3) : 
  MyEqNat (s1 + s2) (r3 + r4).
  Proof. 
  constructor. destruct eqs2r4 as [eqs2r4].
  destruct eqs1r3 as [eqs1r3].
  lia.
  Qed.

#[export] Instance MyEqNat_add_bis {s1 r3 s2 r4} (eqs2r4 : MyEqNat s2 r4) (eqs1r3 : MyEqNat s1 r3) : 
  MyEqNat (s1 + s2) (r3 + r4).
  Proof. 
  constructor. destruct eqs2r4 as [eqs2r4].
  destruct eqs1r3 as [eqs1r3].
  lia.
  Qed.


Theorem parent_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n n': nat, forall Hn Hn', n = n' ->
  get_parent b (inr (exist _ n Hn)) = get_parent b (inr (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Theorem innername_proof_irrelevant {s i r o} (b:bigraph s i r o): 
  forall n:Name, forall Hn: In n i, forall Hn':In n i,
  get_link b (inl (exist _ n Hn)) = get_link b (inl (exist _ n Hn')).
  Proof. 
  intros. apply f_equal. apply f_equal. apply subset_eq_compat. reflexivity.
  Qed.

Definition bigraph_empty : bigraph 0 EmptyNDL 0 EmptyNDL.
  Proof.
  eapply (Big 0 EmptyNDL 0 EmptyNDL
            voidfd voidfd
            (@void_univ_embedding _)
            (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero))
            _ 
            ).
  - intro n.
  destruct n.
  Unshelve.
  intros. destruct X.
  + left. apply n.
  + destruct p. right. apply x.
  Defined. (*TODO unsure of the definition of link def 2.7*)

Definition bigraph_empty' : bigraph' 0 EmptyNDL 0 EmptyNDL.
  Proof. 
  eapply (Big' 0 EmptyNDL 0 EmptyNDL
            void void 
            (of_void Kappa)
            (of_void _ ||| (void_univ_embedding <o> bij_fin_zero))
            _ 
            ).
  - intro n.
  destruct n.
  Unshelve.
  intros. destruct X.
  + left. apply n.
  + destruct p. right. apply x.
  Defined. (*TODO unsure of the definition of link def 2.7*)


Global Notation "∅" := bigraph_empty.

Definition bigraph_identity {s i i'} {p:PermutationNames (ndlist i) (ndlist i')}: bigraph s i s i'. (*actually s i s (permutation i) *)
  Proof.
  apply (Big s i s i'
          voidfd (*node : ∅*)
          voidfd (*edge : ∅*)
          (@void_univ_embedding _) (*control : ∅_Kappa*)
          id (*parent : id*)
        ).
  - intros [inner | port]. (*link_|{names} : id*)
    + left. destruct inner. exists x. destruct p as[p]. unfold permutation in p. apply p in i0. apply i0.
    + destruct port. destruct x.
  - intro n. (*acyclic parent*)
    destruct n.
  Defined.
  
Definition bigraph_id (s: nat) (i : NoDupList) := bigraph_identity (s := s) (i := i) (i' := i).

Example zero1 : type (findec_fin 1). exists 0. auto. Defined.

Definition discrete_atom {A} 
  (a:type A) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 0 EmptyNDL 1 o.
  eapply (Big
      0 EmptyNDL 1 o
      A
      voidfd
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr zero1
        | inr s => _
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    3:{ intros [i|p].  
      - destruct i as [i H]. elim H. 
      - left. unfold NameSub. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (nth p o DefaultName). 
      apply nth_In. destruct Hkappa as [Hkappa]. rewrite <- Hkappa. assumption. } (*link*)
    2:{ destruct s. apply Nat.nlt_0_r in l. elim l. } (*parent*)
    unfold FiniteParent. simpl. (*acyclic*)
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    Defined. 

Definition discrete_ion {A} 
  (a:type A) {k:Kappa} (o:NoDupList) 
  {Hkappa : MyEqNat (Arity k) (length (ndlist o))}: bigraph 1 EmptyNDL 1 o.
  eapply (Big
      1 EmptyNDL 1 o
      A
      voidfd
      (fun n => k) (*control*)
      (fun ns => match ns with 
        | inl n => inr zero1
        | inr s => inl a
      end) (*parent*)
      _ (*link*)
    ).
    Unshelve.
    2:{ intros [i|p].  
      - destruct i as [i H]. elim H. 
      - left. unfold NameSub. destruct o as [o Ho]. 
      destruct p as [i H]. destruct H as [p Hp]. 
      exists (nth p o DefaultName). 
      apply nth_In. destruct Hkappa as [Hkappa]. rewrite <- Hkappa. assumption. } (*link*)
    unfold FiniteParent. simpl.
    intros u.
    apply Acc_intro.
    intros u' H.
    exfalso. discriminate H.
    Defined. 


Definition placing (s : nat) (r : nat) := bigraph s EmptyNDL r EmptyNDL. (*manque la notion de node-free*)

Definition permutationbig' (n : nat) := placing n n. (*manque la notion de node-free*)
Definition permutationbig (n : nat) : bigraph n EmptyNDL n EmptyNDL. 
  Proof. 
  apply (Big n EmptyNDL n EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_-> Kappa*)
    (fun sn => match sn with |inr s => inr s | inl n => match n with end end) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition prime (m:nat) (X:NoDupList) :=  bigraph m EmptyNDL 1 EmptyNDL.

Definition merge' (n:nat) := placing n 1. (*manque la notion de node-free*)
Definition merge {n:nat} : bigraph n EmptyNDL 1 EmptyNDL. (* merge n+1 = join <<o>> (id 1 [] ⊗ merge n ) with merge 0 = 1 (1 root that's all)*)
  Proof. 
  apply (Big n EmptyNDL 1 EmptyNDL
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅ ->_Kappa*)
    (fun s => inr zero1) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. apply inner.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition big_1 := @merge 0.


Definition linking (i : NoDupList) (o : NoDupList) := bigraph 0 i 0 o. (*manque la notion de node-free*)

Lemma noDupSingle (n:Name) :  NoDup [n].
Proof. constructor; auto. constructor. Qed.

Definition substitution' (i:NoDupList) (name:Name) := linking i (mkNoDupList [name] (noDupSingle name)).
Definition substitution (i:NoDupList) (name:Name) : bigraph 0 i 0 (mkNoDupList [name] (noDupSingle name)).
  Proof. 
  apply (Big 0 i 0 (mkNoDupList [name] (noDupSingle name))
    voidfd (*node : ∅*)
    voidfd (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero)) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + left. exists name. simpl. left. reflexivity.
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition closure' (name:Name) := linking (mkNoDupList [name] (noDupSingle name)) EmptyNDL.
Definition closure (name:Name) : bigraph 0 (mkNoDupList [name] (noDupSingle name)) 0 EmptyNDL.
  Proof. 
  apply (Big 0 (mkNoDupList [name] (noDupSingle name)) 0 EmptyNDL
    voidfd (*node : ∅*)
    findec_unit (*edge : ∅*)
    (@void_univ_embedding _) (*control : ∅_Kappa*)
    (void_univ_embedding ||| (void_univ_embedding <o> bij_fin_zero)) (*parent : sites -> root*)
  ).
  - intros [inner | port]. (*link : ∅*)
  + right. simpl. exact tt. 
  + destruct port. destruct x.
  - intro n'. (*acyclic parent*)
  destruct n'.
  Defined.

Definition join_big := @merge 2. 

(* Definition symmetry_big {s i r o} : bigraph s i r o.
apply (Big s i r o 
voidfd (*node : ∅*)
voidfd (*edge : ∅*)
(@void_univ_embedding _) (*control : ∅_Kappa*)
(fun n => n + r). 
(*parent : id*)
) *)



Lemma partial_monoidal_category : forall A B C:FinDecType, 
  (* findec_sum A B <-> findec_sum B A /\ *)
  exists b:bijection (type (findec_sum A (findec_sum B C))) (type (findec_sum (findec_sum A B) C)), True /\
  findec_sum voidfd A = A /\
  findec_sum A voidfd = A /\ 
  findec_sum A voidfd = findec_sum voidfd A.
  intros. split.
  - unfold findec_sum. simpl. (* exists (bij_sum_assoc (type A + type B + type C)%type).  *) admit.
  - split. 
    + unfold findec_sum. simpl. admit.
    Admitted. 

End Bigraphs.

