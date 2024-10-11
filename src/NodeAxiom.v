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


Module NodeAxiom (s : SignatureParameter) (n : NamesParameter).
Module tp := TensorProduct s n.
Include tp.

Set Typeclasses Unique Instances.
Set Typeclasses Iterative Deepening.


Definition rm_0_site {i o} (b: bigraph (0+0) i (0+0) o): 
  bigraph 0 i 0 o.
  exact b.
  Defined.


Definition merge_names {inner i outer o ndli ndlo} 
  (b: bigraph 0 (OneelNDL inner ∪ {| ndlist := i; nd := nodup_tl inner i ndli |}) 
              0 (OneelNDL outer ∪ {| ndlist := o; nd := nodup_tl outer o ndlo |})): 
    bigraph 0 {| ndlist := inner::i; nd := ndli |} 0 {| ndlist := outer::o; nd := ndlo |}.
  Proof.
  destruct b.
  rewrite NameSub_merge_proof_irrelevance in link0.
  rewrite NameSub_merge_proof_irrelevance in link0.
  apply (@Big _ _ _ _ node0 edge0 control0 parent0 link0 ap0).
Defined.

Check eq_rect.

Definition changeLink {inner i ndli outer o ndlo  edgeb nodeb} {controlb:nodeb->Kappa}
(linkb : NameSub (OneelNDL inner ∪ {|ndlist := i; nd := nodup_tl inner i ndli|}) + Port controlb ->
NameSub (OneelNDL outer ∪ {|ndlist := o; nd := nodup_tl outer o ndlo|}) + edgeb) :
NameSub {| ndlist := inner :: i; nd := ndli |} + Port (node:=nodeb) controlb ->
NameSub {| ndlist := outer :: o; nd := ndlo |} + edgeb.
rewrite NameSub_merge_proof_irrelevance in linkb.
rewrite NameSub_merge_proof_irrelevance in linkb.
exact linkb.
Defined.


Lemma changeLinkWf {inner i ndli outer o ndlo  edgeb nodeb} {controlb:nodeb->Kappa}
  (linkb : NameSub (OneelNDL inner ∪ {|ndlist := i; nd := nodup_tl inner i ndli|}) + Port controlb ->
  NameSub (OneelNDL outer ∪ {|ndlist := o; nd := nodup_tl outer o ndlo|}) + edgeb) :
  forall p, match linkb (inr p) with 
  |inl outer => match changeLink linkb (inr p) with 
    |inr _ => False 
    |inl outer' => sval outer = sval outer'
    end
  |inr ed => match changeLink linkb (inr p) with 
    |inl _ => False 
    |inr ed' => ed = ed'
    end
  end.
  Proof.
  intros.
  destruct linkb eqn:E.
  unfold changeLink.
  unfold eq_rect_r. 
  Abort.




Definition merge_names' {inner i outer o ndli ndlo} 
  (b: bigraph 0 (OneelNDL inner ∪ {| ndlist := i; nd := nodup_tl inner i ndli |}) 
              0 (OneelNDL outer ∪ {| ndlist := o; nd := nodup_tl outer o ndlo |})): 
    bigraph 0 {| ndlist := inner::i; nd := ndli |} 0 {| ndlist := outer::o; nd := ndlo |} :=
  match b with 
  | {|node:=nodeb ; edge:=edgeb ; control:=controlb ;parent:=parentb ;
  link:=linkb ;ap:=apb|} => 
    @Big 
    0 
    {| ndlist := inner::i; nd := ndli |} 
    0 
    {| ndlist := outer::o; nd := ndlo |}
    nodeb edgeb controlb parentb 
    (changeLink linkb) 
    apb
  end.

Print merge_names'.

Definition merge_names'' {inner i outer o ndli ndlo} 
  (b: bigraph 0 (OneelNDL inner ∪ {| ndlist := i; nd := nodup_tl inner i ndli |}) 
              0 (OneelNDL outer ∪ {| ndlist := o; nd := nodup_tl outer o ndlo |})): 
    bigraph 0 {| ndlist := inner::i; nd := ndli |} 0 {| ndlist := outer::o; nd := ndlo |}.
  Proof.
  unfold app_merge_NoDupList in b.
  unfold app_merge in b.
  simpl in b.
  assert (
    (mkNoDupList
      match @in_dec Name EqDecN inner i return (list Name) with
      | @left _ _ _ => i
      | @right _ _ _ => @cons Name inner i
      end
    (NoDup_app_merge (@cons Name inner (@nil Name)) i
    (@NoDup_cons Name inner (@nil Name) (fun H : False => H)
    (NoDup_nil Name)) (@nodup_tl Name inner i ndli))) 
    = 
      {| ndlist := (inner :: i); nd := ndli |}
    ).
    apply nodupproofirrelevant. simpl.
    clear b.
    destruct (@in_dec Name EqDecN inner i).
    rewrite (NoDup_cons_iff inner i) in ndli.
    destruct ndli. contradiction.
    reflexivity.
  rewrite H in b. clear H.
  assert (
    mkNoDupList
    match @in_dec Name EqDecN outer o return (list Name) with
    | @left _ _ _ => o
    | @right _ _ _ => @cons Name outer o
    end
      (NoDup_app_merge (@cons Name outer (@nil Name)) o
      (@NoDup_cons Name outer (@nil Name) (fun H : False => H)
      (NoDup_nil Name)) (@nodup_tl Name outer o ndlo))
    = 
      {| ndlist := (outer :: o); nd := ndlo |}
    ).
    apply nodupproofirrelevant. simpl.
    clear b.
    destruct (@in_dec Name EqDecN outer o).
    rewrite (NoDup_cons_iff outer o) in ndlo.
    destruct ndlo. contradiction.
    reflexivity.
  rewrite H in b. clear H.
  exact b.
Defined.

Lemma merge_names_wf {inner i outer o ndli ndlo} 
  (b: bigraph 0 (OneelNDL inner ∪ {| ndlist := i; nd := nodup_tl inner i ndli |}) 
              0 (OneelNDL outer ∪ {| ndlist := o; nd := nodup_tl outer o ndlo |})):
  support_equivalence
    b 
    (merge_names' b).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      b 
      (merge_names' b)
      (erefl) (*s*)
      (_) (*i*)
      (erefl) (*r*)
      (_) (*o*)
      (_) (*n*)
      (_) (*e*)
      (_) (*p*)
      _ _ _
    ).
  Unshelve.
    6:{ unfold merge_names'. destruct b. simpl. exact bij_id. }
    6:{ unfold merge_names'. destruct b. simpl. exact bij_id. }
    6:{ unfold merge_names'. destruct b. simpl. intros. exact bij_id. }
    4:{ simpl. destruct (in_dec EqDecN inner i). 
    inversion ndli. contradiction. apply permutation_id. }
    4:{ simpl. destruct (in_dec EqDecN outer o). 
    inversion ndlo. contradiction. apply permutation_id. }
    - destruct b.
    simpl. reflexivity.
    - destruct b.
    simpl. unfold parallel,funcomp. apply functional_extensionality.
    intros [n|v]. destruct parent0. reflexivity.
    destruct o0.
    discriminate i0.
    destruct v.
    discriminate i0.
    - simpl.
    unfold bij_subset_forward.
    apply functional_extensionality.
    intros [innern|ports].
    unfold funcomp,parallel,sequence,sum_shuffle,bij_subset_backward.
    destruct innern.
    simpl.
    unfold eq_ind_r,eq_rect_r. simpl.
    erewrite <- (innername_proof_irrelevant b _). 
    unfold merge_names'. simpl.
    destruct b.
    simpl.
    unfold changeLink.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold Logic.eq_sym.

    Abort.

Definition renaming_tp {s r} 
(a a':Name) (N N': NoDupList) 
{Ha: ~In a N} {Ha': ~In a' N'}
(b:bigraph s N r N') : bigraph s {| ndlist := a::N; nd := NoDup_cons a Ha (nd N) |} r {| ndlist := a'::N'; nd := NoDup_cons a' Ha' (nd N') |}. 
  Proof.
  eset (almost := bigraph_tensor_product (dis_i:=_) (dis_o:=_)
  (elementary_renaming a a') b   ).
  change (bigraph (0+s) {| ndlist := a :: N; nd := NoDup_cons a Ha (nd N) |} (0+r)
{| ndlist := a' :: N'; nd := NoDup_cons a' Ha' (nd N') |}).
  unfold app_merge_NoDupList in almost.
  assert (H := app_merge_cons_id (nd N) Ha).
  assert (
    {|
    ndlist := app_merge (OneelNDL a) N;
    nd := NoDup_app_merge (OneelNDL a) N (nd (OneelNDL a)) (nd N)
    |} = 
    {| ndlist := a :: N; nd := NoDup_cons a Ha (nd N) |}
  ). apply nodupproofirrelevant.
  simpl.
  destruct (in_dec EqDecN a N). contradiction.
  reflexivity.
  Abort.


Definition renaming (N N': NoDupList) {H: length N = length N'}: bigraph 0 N 0 N'.
  Proof.
  destruct N as [N ndl].
  revert N' H.
  induction N as [|a q IHN];intros [[|a' q'] ndl'] H; try discriminate H.
  - assert (forall NDL, {| ndlist := [::]; nd := NDL |} = EmptyNDL). {intros. apply nodupproofirrelevant. simpl. reflexivity. }
  rewrite H0.
  rewrite H0.
  exact bigraph_empty. 
  - simpl in *.
  specialize (IHN (nodup_tl a q ndl) ({|ndlist:=q'; nd := nodup_tl a' q' ndl'|})).
  simpl in IHN.
  inversion H.
  apply IHN in H1.
  eset (almost := bigraph_tensor_product (dis_i:=_) (dis_o:=_)
  (elementary_renaming a a')
  H1 
  ).
  Abort.



Definition renaming (N N': NoDupList) {H: length N = length N'}: bigraph 0 N 0 N'.
  Proof.
  destruct N as [l ndl]. 
  destruct N' as [l' ndl']. simpl in H. 
  revert l l' ndl ndl' H. induction l as [|a l0 IHl0].  
  - intros. simpl in *. symmetry in H.
  apply length_zero_iff_nil in H.
  subst l'.
  assert (forall NDL, {| ndlist := [::]; nd := NDL |} = EmptyNDL). {intros. apply nodupproofirrelevant. simpl. reflexivity. }
  rewrite H.
  rewrite H.
  exact bigraph_empty.
  
  - intros l0' ndl0 ndl0' H'.
  destruct l0' as [|a' l0']. 
  + exfalso. auto. discriminate H'.
  + specialize (IHl0 l0' (nodup_tl a l0 ndl0) (nodup_tl a' l0' ndl0')).
  assert (length l0 = length l0'). {inversion H'. reflexivity. }
  specialize (IHl0 H).
  clear H.
  exact (
    merge_names (
    rm_0_site 
      (bigraph_tensor_product 
        (dis_i := Disjoint_NoDuPlist) (dis_o := Disjoint_NoDuPlist) 
          (elementary_renaming a a') 
          IHl0))).
  Defined.

Definition renaming' (N N': NoDupList) {H: length N = length N'}: bigraph 0 N 0 N'.
  Proof.
  destruct N as [l ndl]. 
  destruct N' as [l' ndl']. simpl in H. 
  revert l l' ndl ndl' H. induction l as [|a l0 IHl0].  
  - intros. simpl in *. symmetry in H.
  apply length_zero_iff_nil in H.
  subst l'.
  assert (forall NDL, {| ndlist := [::]; nd := NDL |} = EmptyNDL). {intros. apply nodupproofirrelevant. simpl. reflexivity. }
  rewrite H.
  rewrite H.
  exact bigraph_empty.
  
  - intros l0' ndl0 ndl0' H'.
  destruct l0' as [|a' l0']. 
  + exfalso. auto. discriminate H'.
  + specialize (IHl0 l0' (nodup_tl a l0 ndl0) (nodup_tl a' l0' ndl0')).
  assert (length l0 = length l0'). {inversion H'. reflexivity. }
  specialize (IHl0 H).
  clear H.
  set (almost :=
      (bigraph_tensor_product 
        (dis_i := Disjoint_NoDuPlist) (dis_o := Disjoint_NoDuPlist) 
          (elementary_renaming a a') 
          IHl0)).
 
  destruct almost. 
  refine (@Big 0 {| ndlist := a :: l0; nd := ndl0 |} 0 {| ndlist := a' :: l0'; nd := ndl0'|} 
  node0 edge0 control0 parent0 _ ap0).
  - rewrite NameSub_merge_proof_irrelevance in link0. 
  rewrite NameSub_merge_proof_irrelevance in link0.
  intros ip.
  destruct (link0 ip) as [outer|edge].
  exact (inl outer).
  exact (inr edge).
  Defined.


Definition rewriteEqNat {lN lN' Ak} (H: lN = lN') (Hk : MyEqNat Ak lN) : MyEqNat Ak lN'.
  subst lN. apply Hk.
  Qed.

(* Lemma nth_port_renaming_nth_name {N N' H}:
  let bg:= @renaming N N' H in 
  forall n:get_node bg, forall i, 
  match get_link (bg:=bg) (inr (existT _ n i)) with 
  |inr _ => False 
  |inl (exist outer _) => outer = nth i N' DefaultName
  end.
  Proof.
  intros.
  destruct get_link eqn:E.
  2:{clear E. rewrite edgeRenamingVoid in s0. destruct s0.  }
  destruct s0.
  simpl in i0.
  destruct i0 as [i Hi]. simpl.
  simpl in E.
  unfold bg in E.
  unfold renaming in E.
  simpl in E. 
  destruct N.
  destruct N'.
  Abort. *)

Theorem nodeAxiomelementary {N N':Name} 
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) 1} : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗ (elementary_renaming N N'))
      <<o>> @discrete_ion _ tt k (OneelNDL N) Hk)
    (@discrete_ion _ tt k (OneelNDL N') (Hk)).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗ (elementary_renaming N N'))
      <<o>> @discrete_ion _ tt k (OneelNDL N) Hk)
      (@discrete_ion _ tt k (OneelNDL N') (Hk))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_left_neutral_neutral) (*o*)
      (bijection_nest_left_neutral) (*n*)
      (bijection_nest_left_neutral) (*e*)
      (_)  (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ intros. simpl in *. destruct n1 as [[v|v]|nodeion]; try destruct v.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1]; unfold extract1.
      + unfold bij_rew_forward. 
      rewrite eq_rect_ordinal. simpl.
      unfold fintype.split. simpl.
      destruct (ltnP 0 1).
      unfold unsplit,lshift.
      f_equal. apply val_inj. simpl. reflexivity.
      discriminate i0.
      reflexivity.
    - simpl.
      unfold parallel,funcomp,bij_subset_forward,switch_link. simpl.
      apply functional_extensionality.
      intros [v|port].
      exfalso.
      destruct v. apply f.
      unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward,bijection_nest_left_neutral.
      destruct port.
      simpl. unfold funcomp.
      unfold eq_rect_r.
      simpl.
      rewrite rew_const.
      destruct o0.
      unfold extract1,sum_shuffle,bij_list_backward',permut_list_forward.
      destruct m.
      destruct (in_dec EqDecN N EmptyNDL).
      elim i1.
      f_equal. unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      simpl.
      f_equal. 
      apply subset_eq_compat. simpl.
      destruct Hk.
      rewrite eqxy in i0.
      discriminate i0.
  Qed.

#[export] Instance permaxi {M N} {ndl : NoDup [M;N]} : 
PermutationNames {| ndlist := [:: M;  N]; nd := ndl |}
(EmptyNDL ∪ (OneelNDL M ∪ OneelNDL N)).
constructor.
simpl.
destruct (EqDecN N M ).
subst M.
apply NoDup_cons_iff in ndl.
destruct ndl.
elim H. constructor. reflexivity.
apply permutation_id.
Qed. 

Theorem nodeAxiomProductelementary {N N' M M':Name} 
  {ndl : NoDup [M;N]}
  {ndl' : NoDup [M';N']}
  {HN : (OneelNDL M) # (OneelNDL N)}
  {HN' : (OneelNDL M') # (OneelNDL N')}
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) 2}  : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗
       ((elementary_renaming M M') ⊗ (elementary_renaming N N')))
      <<o>> @discrete_ion _ tt k (mkNoDupList [M;N] ndl) Hk)
    (@discrete_ion _ tt k (mkNoDupList [M';N'] ndl') Hk).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗
       ((elementary_renaming M M') ⊗ (elementary_renaming N N')))
      <<o>> @discrete_ion _ tt k (mkNoDupList [M;N] ndl) Hk)
      (@discrete_ion _ tt k (mkNoDupList [M';N'] ndl') Hk)
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_commute (PN_P permaxi)) (*o*)
      (bij_node_axiom_product) (*n*)
      (bij_node_axiom_product) (*e*)
      (_)  (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ intros. simpl in *. destruct n1 as [[v|[v|v]]|nodeion]; try destruct v.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1]; unfold extract1.
      + unfold bij_rew_forward. 
      rewrite eq_rect_ordinal. simpl.
      unfold fintype.split. simpl.
      destruct (ltnP 0 1).
      unfold unsplit,lshift.
      f_equal. apply val_inj. simpl. reflexivity.
      discriminate i0.
      reflexivity.
    - simpl.
      unfold parallel,funcomp,bij_subset_forward,switch_link. simpl.
      apply functional_extensionality.
      intros [v|port].
      exfalso.
      destruct v. apply f.
      unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward,bijection_nest_left_neutral.
      destruct port.
      simpl. unfold funcomp.
      unfold eq_rect_r.
      simpl.
      rewrite rew_const.
      destruct o0.
      unfold extract1,sum_shuffle,bij_list_backward',permut_list_forward.
      simpl in Hk.
      destruct m.
      destruct (in_dec EqDecN M EmptyNDL).
      + elim i1.
      + simpl.
      destruct (EqDecN M M).
      f_equal.  unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      elim n0. reflexivity.
      simpl.
      simpl.
      destruct m.
      destruct (EqDecN M N).
      subst M.
      exfalso. 
      apply NoDup_cons_iff in ndl.
      destruct ndl.
      elim H. constructor. reflexivity.
      f_equal. unfold bij_list_forward.
      apply subset_eq_compat. reflexivity.
      simpl.
      destruct Hk.
      exfalso.
      rewrite eqxy in i0.
      discriminate i0.
  Qed.

#[export] Instance oneelndl {n i} {Hn: ~In n (ndlist i)} :
  OneelNDL n # i.
  constructor.
  intros.
  inversion H.
  subst n.
  contradiction.
  apply H1.
  Qed.

Definition casinductif (n n':Name) {s i r o} (b: bigraph s i r o) 
{Hn: ~In n i}
{Hn': ~In n' o} : bigraph s (OneelNDL n ∪ i) r (OneelNDL n' ∪ o) := bigraph_tensor_product 
  (dis_i := oneelndl (Hn:=Hn))
  (dis_o := oneelndl (Hn:=Hn'))
  (elementary_renaming n n') b.


Definition renaming_try {N N':NoDupList} 
  {Hlength: length N = length N'} : bigraph 0 N O N'.
  destruct N as [l ndl]. 
  destruct N' as [l' ndl']. simpl in Hlength. 
  revert l l' ndl ndl' Hlength. induction l as [|a l IHl].  
  - intros. simpl in *. symmetry in Hlength.
  apply length_zero_iff_nil in Hlength.
  subst l'.
  assert (forall NDL, {| ndlist := [::]; nd := NDL |} = EmptyNDL). {intros. apply nodupproofirrelevant. simpl. reflexivity. }
  rewrite H.
  rewrite H.
  exact bigraph_empty.
  
  - intros l' ndl ndl' H'.
  destruct l' as [|a' l']. 
  + exfalso. auto. discriminate H'.
  + specialize (IHl l' (nodup_tl a l ndl) (nodup_tl a' l' ndl')).
  assert (length l = length l'). {inversion H'. reflexivity. }
  specialize (IHl H).
  clear H.
  eset (almost := casinductif a a' IHl).
  destruct almost. 
  refine (@Big 0 {| ndlist := a :: l; nd := ndl |} 0 {| ndlist := a' :: l'; nd := ndl'|} 
  node0 edge0 control0 parent0 _ ap0).
  - rewrite NameSub_merge_proof_irrelevance in link0. 
  rewrite NameSub_merge_proof_irrelevance in link0.
  intros ip.
  destruct (link0 ip) as [outer|edge].
  exact (inl outer).
  exact (inr edge).
  Unshelve.
  simpl. inversion ndl. apply H1.
  simpl. inversion ndl'. apply H1.
  Defined.





Theorem nodeRenamingVoid (N N': NoDupList) {H: length N = length N'}: bijection (get_node (@renaming_try N N' H)) (void).
  Proof.
  unfold renaming_try.
  destruct N as [N NDN].
  destruct N' as [N' NDN'].
  simpl in H.  
  revert N' H NDN'.
  induction N as [|n N IHN];intros.
  - simpl in *.
  set (Hbis := H).
  unfold Hbis.
  symmetry in Hbis.
  apply length_zero_iff_nil in Hbis.
  subst N'.
  simpl. 
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  unfold eq_rect. simpl.
  destruct (@Logic.eq_sym NoDupList (mkNoDupList (@nil Name) NDN) EmptyNDL
    (nodupproofirrelevant (mkNoDupList (@nil Name) NDN) EmptyNDL
    (@Logic.eq_refl (list Name) (@nil Name)))).
  destruct (@Logic.eq_sym NoDupList (mkNoDupList (@nil Name) NDN') EmptyNDL
    (nodupproofirrelevant (mkNoDupList (@nil Name) NDN') EmptyNDL
    (@Logic.eq_refl (list Name) (@nil Name)))).
  apply (bij_id).
  
  
  - simpl.
  destruct N'.
  + exfalso. clear IHN.
  simpl in H.
  elim H. 
  discriminate H.
  + simpl.
  specialize (IHN (nodup_tl n N NDN) N').
  assert (H' : length N = length N'). 
  {inversion H. reflexivity. }
  specialize (IHN H' (nodup_tl n0 N' NDN')).
  rewrite (proof_irrelevance _ (match
    H in (@eq _ _ n1)
    return
    (forall _ : @eq nat n1 (S (@length Name N')),
    @eq nat (@length Name N) (@length Name N'))
    with
    | @Logic.eq_refl _ _ =>
    fun H0 : @eq nat (S (@length Name N)) (S (@length Name N'))
    =>
    @eq_ind nat (@length Name N)
    (fun n1 : nat => @eq nat (@length Name N) n1)
    (@Logic.eq_refl nat (@length Name N)) (@length Name N')
    (@f_equal nat nat
    (fun e : nat =>
    match e return nat with
    | @O =>
    (fix length (l : list Name) : nat :=
    match l return nat with
    | @nil _ => O
    | @cons _ _ l' => S (length l')
    end) N
    | @S n1 => n1
    end) (S (@length Name N)) (S (@length Name N')) H0)
    end (@Logic.eq_refl nat (S (@length Name N')))) H').
  apply (bij_sum_left IHN).
  Qed.

Theorem edgeRenamingVoid (N N': NoDupList) {H: length N = length N'}: bijection (get_edge (@renaming_try N N' H)) (void).
Proof.
  unfold renaming_try.
  destruct N as [N NDN].
  destruct N' as [N' NDN'].
  simpl in H.  
  revert N' H NDN'.
  induction N as [|n N IHN];intros.
  - simpl in *.
  set (Hbis := H).
  unfold Hbis.
  symmetry in Hbis.
  apply length_zero_iff_nil in Hbis.
  subst N'.
  simpl. 
  unfold eq_rect_r.
  rewrite <- eq_rect_eq.
  unfold eq_rect. simpl.
  destruct (@Logic.eq_sym NoDupList (mkNoDupList (@nil Name) NDN) EmptyNDL
    (nodupproofirrelevant (mkNoDupList (@nil Name) NDN) EmptyNDL
    (@Logic.eq_refl (list Name) (@nil Name)))).
  destruct (@Logic.eq_sym NoDupList (mkNoDupList (@nil Name) NDN') EmptyNDL
    (nodupproofirrelevant (mkNoDupList (@nil Name) NDN') EmptyNDL
    (@Logic.eq_refl (list Name) (@nil Name)))).
  apply (bij_id).
  
  
  - simpl.
  destruct N'.
  + exfalso. clear IHN.
  simpl in H.
  elim H. 
  discriminate H.
  + simpl.
  specialize (IHN (nodup_tl n N NDN) N').
  assert (H' : length N = length N'). 
  {inversion H. reflexivity. }
  specialize (IHN H' (nodup_tl n0 N' NDN')).
  rewrite (proof_irrelevance _ (match
    H in (@eq _ _ n1)
    return
    (forall _ : @eq nat n1 (S (@length Name N')),
    @eq nat (@length Name N) (@length Name N'))
    with
    | @Logic.eq_refl _ _ =>
    fun H0 : @eq nat (S (@length Name N)) (S (@length Name N'))
    =>
    @eq_ind nat (@length Name N)
    (fun n1 : nat => @eq nat (@length Name N) n1)
    (@Logic.eq_refl nat (@length Name N)) (@length Name N')
    (@f_equal nat nat
    (fun e : nat =>
    match e return nat with
    | @O =>
    (fix length (l : list Name) : nat :=
    match l return nat with
    | @nil _ => O
    | @cons _ _ l' => S (length l')
    end) N
    | @S n1 => n1
    end) (S (@length Name N)) (S (@length Name N')) H0)
    end (@Logic.eq_refl nat (S (@length Name N')))) H').
  apply (bij_sum_left IHN).
  Qed.


Fail Theorem linkRenaming :
get_link (bg:=renaming_try)
(inl (exist ((In (A:=Name))^~N) (nth ports N DefaultName) Hn))
= nth ports N' DefaultName.


Theorem nodeAxiom {N N':NoDupList} 
  {Hlenght: length N = length N'} 
  {k:Kappa} 
  {Hk : MyEqNat (Arity k) (length (ndlist N))} : 
  support_equivalence
    ((bigraph_id 1 EmptyNDL ⊗ (@renaming_try N N' Hlenght))
      <<o>> @discrete_ion _ tt k N Hk)
    (@discrete_ion _ tt k N' (rewriteEqNat Hlenght Hk)).
  Proof.
  refine (
    SupEq _ _ _ _ _ _ _ _
      ((bigraph_id 1 EmptyNDL ⊗ (@renaming_try N N' Hlenght))
      <<o>> @discrete_ion _ tt k N Hk)
      (@discrete_ion _ tt k N' (rewriteEqNat Hlenght Hk))
      (erefl) (*s*)
      (permutation_left_neutral_neutral) (*i*)
      (erefl) (*r*) 
      (permutation_left_neutral_neutral) (*o*)
      (_) (*n*)
      (_) (*e*)
      (_) (*p*)
      _ _ _
    ).
    Unshelve. 
    4:{ simpl.
      eapply (mkBijection _ _ 
        (_)
        (fun u => inr u)
        ).
        Unshelve. 3:{simpl. 
        intros [[v|n]|u].
        destruct v.
        set (v':= nodeRenamingVoid N N' n). destruct v'.
        exact u.
        }
      apply functional_extensionality;simpl.
      intros. unfold funcomp. reflexivity.
      apply functional_extensionality;simpl.
      intros  [[v|n]|u].
      destruct v.
      set (v':= nodeRenamingVoid N N' n). destruct v'.
      unfold funcomp. reflexivity.
    }
    4:{ simpl.
      eapply (mkBijection _ _ 
        (_)
        (fun u => inr u)
        ).
        Unshelve. 3:{simpl. 
        intros [[v|n]|u].
        destruct v.
        set (v':= edgeRenamingVoid N N' n). destruct v'.
        exact u.
        }
      apply functional_extensionality;simpl.
      intros. unfold funcomp. reflexivity.
      apply functional_extensionality;simpl.
      intros  [[v|n]|u].
      destruct v.
      set (v':= edgeRenamingVoid N N' n). destruct v'.
      unfold funcomp. reflexivity.
    }
    4:{ intros. simpl in *. destruct n1 as [[v|v]|nodeion]; try destruct v.
    exfalso. set (v':= nodeRenamingVoid N N' v). destruct v'.
    simpl. exact bij_id. }
    - simpl. unfold funcomp,join.
      apply functional_extensionality. intros nodeion.
      unfold eq_rect_r. reflexivity.
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1.
      simpl.
      apply functional_extensionality. intros [nodeion|site1].
      + unfold extract1,eq_rect_r. 
      unfold bij_rew_forward. rewrite eq_rect_ordinal.
      unfold fintype.split.
      simpl.
      destruct (ltnP 0 1).
      f_equal. unfold unsplit,lshift.
      apply val_inj. simpl. reflexivity. 
      + discriminate i0.
      reflexivity. 
    - simpl. unfold funcomp,join,parallel,sequence,sum_shuffle,extract1,switch_link,rearrange.
    simpl.
    apply functional_extensionality. intros [innervoide|ports].
    + destruct innervoide. elim f.
    + destruct ports as [nodeion ports].
    unfold bij_join_port_backward,bij_dep_sum_2_forward,bij_dep_sum_1_forward.    
    unfold eq_rect_r. unfold bijection_inv. simpl.
    rewrite rew_const.
    destruct ports as [ports Hports].
    unfold extract1. simpl.
    unfold bij_list_backward',permut_list_forward. 
    destruct N as [N NDL].
    destruct N' as [N' NDL'].
    destruct (in_dec EqDecN (nth ports N DefaultName) EmptyNDL).
    * elim i0.
    * erewrite <- (innername_proof_irrelevant renaming_try _). 

    unfold renaming_try. simpl. 
    destruct get_link as [outer|edge] eqn:E.
    ** f_equal.
    unfold bij_subset_forward,bij_list_forward.
    destruct outer.
    apply subset_eq_compat. simpl.

    Admitted.

End NodeAxiom.