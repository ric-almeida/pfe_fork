Set Warnings "-notation-overridden, -notation-overriden, -masking-absolute-name".

Require Import AbstractBigraphs.
Require Import Names.
Require Import SignatureBig.
Require Import Equality.
Require Import Bijections.
Require Import MyBasics.
Require Import TensorProduct.
Require Import MathCompAddings.


Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Lia.

Import ListNotations.
From mathcomp Require Import all_ssreflect.



Require Import List.

Module UnionPossible (s : SignatureParameter) (n : NamesParameter).

Module tp := TensorProduct s n.
Include tp.

Definition union_possible {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :=
  forall (i : NameSub (i1 ∩ i2)),
  match (get_link (bg:=b1) (inl (to_left i))) with
  | inr e => False
  | inl o1' => 
    match get_link (bg:=b2) (inl (to_right i)) with
    | inr e => False
    | inl o2' => proj1_sig o1' = proj1_sig o2' 
    end
  end.

Class UnionPossible {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  := { UP : union_possible b1 b2 }.



#[export] Instance disjoint_innernames_implies_union_possible {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2} :
  i1 # i2 -> UnionPossible b1 b2.
  Proof.
  intros.
  constructor.
  unfold union_possible.
  intros.
  destruct i0. exfalso.
  unfold intersectionNDL in i0.
  simpl in i0.
  rewrite (intersection_disjoint_empty_NDL H) in i0.
  apply i0.
  Qed. 

Lemma union_possible_commutes {s1 i1 r1 o1 s2 i2 r2 o2}
  {b1 : bigraph s1 i1 r1 o1} 
  {b2 : bigraph s2 i2 r2 o2} 
  (up12 : UnionPossible b1 b2):
  UnionPossible b2 b1.
  Proof.
    destruct up12 as [up12]. constructor.
    unfold union_possible in *.
    unfold NameSub in *.
    intros i.
    specialize (up12 (to_commute i)).
    unfold to_commute in up12.
    destruct i as [i H21].
    unfold to_left,to_right in *.
    destruct get_link eqn:E.
    - rewrite <- (innername_proof_irrelevant b2 (from_intersection_left H21)) in up12. 
    destruct (get_link (bg:=b2) (inl (exist (fun name : Name => In name i2) i (from_intersection_left H21)))). 
    + rewrite <- (innername_proof_irrelevant b1 (from_intersection_left (intersection_commutes H21))).
    rewrite E.
    destruct s0. destruct s3.
    simpl in *. symmetry. apply up12.
    + apply up12.
    - destruct (get_link (bg:=b2)
    (inl
      (exist (fun name : Name => In name i2) i
          (from_intersection_left H21)))) eqn:E'.
    + rewrite <- (innername_proof_irrelevant b1 (from_intersection_left (intersection_commutes H21))).
    rewrite E. apply up12.
    + apply up12.
  Qed.

#[export] Instance union_possible_dist {s1 i1o3 r1 o1 s2 i2o4 r2 o2 s3 r3 r4 i3 o3i1 s4 i4 o4i2} 
  {b1 : bigraph s1 i1o3 r1 o1} 
  {b2 : bigraph s2 i2o4 r2 o2} 
  {b3 : bigraph s3 i3 r3 o3i1} 
  {b4 : bigraph s4 i4 r4 o4i2}
  {p13 : PermutationNames (ndlist o3i1) (ndlist i1o3)}
  {p24 : PermutationNames (ndlist o4i2) (ndlist i2o4)}
  {eqs2r4 : MyEqNat s2 r4} {eqs1r3 : MyEqNat s1 r3} 
  (up12 : UnionPossible b1 b2) (up34 : UnionPossible b3 b4) :
  UnionPossible 
    (b1 <<o>> b3) 
    (b2 <<o>> b4).
  Proof.
    destruct up12 as [up12].
    destruct up34 as [up34].
    constructor.
    unfold union_possible, NameSub in *.
    unfold bigraph_composition.
    simpl. 
    intros.
    unfold funcomp, parallel, sequence, switch_link, permut_list_forward, bij_join_port_backward.
    unfold rearrange, extract1.
    simpl.
    specialize (up34 i0).
    destruct get_link eqn:E.
    - destruct s0 as [o' Ho'].
      destruct (in_dec EqDecN o' i2o4).
      + pose Ho' as Ho''.
        destruct p13 as [p13].
        apply (p13 o') in Ho''.
        specialize (up12 (to_intersection o' Ho'' i1)).
        unfold to_left, to_right, to_intersection in *. 
        rewrite <- (innername_proof_irrelevant b1 (from_intersection_left (in_both_in_intersection Ho'' i1))).
        destruct get_link eqn:E'.
        ++ destruct i0.
          destruct (get_link (bg:=b4) (inl (exist (fun name : Name => In name i4) x (from_intersection_right i0)))) eqn:E''.
          * destruct s5.
            simpl in up34. destruct up34.
            rewrite <- (innername_proof_irrelevant b2 (from_intersection_right
            (in_both_in_intersection Ho'' i1))).
            set (Tmp := from_intersection_right
            (in_both_in_intersection Ho'' i1)).
            fold Tmp in up12.
            assert (@from_intersection_right 
            (ndlist i1o3) (ndlist i2o4) o'
            (@in_both_in_intersection
               (ndlist
                  (@reverse_coercion NoDupList
                     (list Name) i1o3 
                     (ndlist i1o3))) 
               (ndlist i2o4) o' Ho'' i1) = Tmp).
               auto.
               rewrite H in up12.
            destruct (get_link (bg:=b2) (inl (exist (fun x : Name => In x i2o4) o' Tmp))) eqn:EI.
            ** apply up12.
            ** apply up12.
          * apply up34.
        ++ apply up12.
      + destruct i0.
      unfold to_left, to_right in *.
      destruct get_link; destruct get_link.
      * destruct s0. destruct s5. simpl in *. destruct up34.
      exfalso. apply n. destruct p24 as [p24]. apply (p24 o'). apply i2.
      * exfalso. apply up34.
      * simpl in s0. destruct s5. simpl in *. destruct up34.
      exfalso. apply n. destruct p24 as [p24]. apply (p24 o'). apply i1.
      * exfalso. apply up34.
    - apply up34.
  Qed.


#[export] Instance union_possible_id {X Y: NoDupList} :
  UnionPossible (@bigraph_id 0 X) (@bigraph_id 0 Y).
  constructor.
  unfold union_possible.
  intros [iXY Hi].
  simpl. reflexivity.
  Qed.

Class UnionPossiblePacked (b1 b2 : bigraph_packed) :=
  { upp :: UnionPossible (big b1) (big b2)}.
  
#[export] Instance unionpossible_packed (b1 b2 : bigraph_packed) (upp : UnionPossible (big b1) (big b2)) : 
  UnionPossiblePacked b1 b2.
  Proof.
  constructor. exact upp.
  Qed.

Record bigraph_packed_up_pair :=
  { 
    fst_ppair_pp  : bigraph_packed;
    snd_ppair_pp  : bigraph_packed;
    up_ppair_pp :: UnionPossiblePacked fst_ppair_pp snd_ppair_pp
  }.

Arguments Build_bigraph_packed_up_pair _ _ {up_ppair_pp}.
  
Record bigraph_packed_up_pair_equality (pp1 pp2 : bigraph_packed_up_pair) : Prop :=
  { 
    fst_ppair_pp_equ : bigraph_pkd_s_e (fst_ppair_pp pp1) (fst_ppair_pp pp2);
    snd_ppair_pp_equ : bigraph_pkd_s_e (snd_ppair_pp pp1) (snd_ppair_pp pp2)
  }.
  
Lemma bigraph_packed_up_pair_equality_refl (pp : bigraph_packed_up_pair) :
  bigraph_packed_up_pair_equality pp pp.
  Proof.
  constructor.
  + apply support_equivalence_refl.
  + apply support_equivalence_refl.
  Qed.

Lemma bigraph_packed_up_pair_equality_sym (pp1 pp2 : bigraph_packed_up_pair):
  bigraph_packed_up_pair_equality pp1 pp2 -> bigraph_packed_up_pair_equality pp2 pp1.
  Proof.
  intros H12.
  constructor.
  + symmetry.
    apply (fst_ppair_pp_equ _ _ H12).
  + symmetry.
    apply (snd_ppair_pp_equ _ _ H12).
  Qed.
  
Lemma bigraph_packed_up_pair_equality_trans (pp1 pp2 pp3 : bigraph_packed_up_pair):
  bigraph_packed_up_pair_equality pp1 pp2 -> bigraph_packed_up_pair_equality pp2 pp3 ->
    bigraph_packed_up_pair_equality pp1 pp3.
  Proof.
  intros H12 H23.
  constructor.
  + etransitivity.
    - apply (fst_ppair_pp_equ _ _ H12).
    - apply (fst_ppair_pp_equ _ _ H23).
  + etransitivity.
    - apply (snd_ppair_pp_equ _ _ H12).
    - apply (snd_ppair_pp_equ _ _ H23).
  Qed.
  
Add Parametric Relation : 
  bigraph_packed_up_pair bigraph_packed_up_pair_equality
  reflexivity proved by (bigraph_packed_up_pair_equality_refl)
  symmetry proved by (bigraph_packed_up_pair_equality_sym)
  transitivity proved by (bigraph_packed_up_pair_equality_trans)
    as bigraph_packed_up_pair_equality_rel.

End UnionPossible.