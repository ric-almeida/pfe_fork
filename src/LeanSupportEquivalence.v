Set Warnings "-notation-overridden, -parsing, -masking-absolute-name, -cannot-define-projection".

Require Import AbstractBigraphs.
Require Import Bijections.
Require Import Names.
Require Import SignatureBig.
Require Import MyBasics.
Require Import MathCompAddings.
Require Import FunctionalExtensionality.
Require Import SupportEquivalence.


Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import ProofIrrelevance.


From mathcomp Require Import all_ssreflect.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div.


Import ListNotations.

(** This module implements equivalence between two bigraphs
  This section defines the equivalence relation between bigraphs. 
  We say there's an equivalence between two types if we give a bijection 
  (cf support_for_bigraphs) between the two types. To define the equivalence 
  between bigraphs, we want an equivalence between each Type and between 
  each function.
  To do that, we make definitions of equivalence between each function. 
  We coerce the Record support_equivalence into a Prop, which means that we can
  access the bjections, but also that their existence means the Prop is True.
  Note that our equivalence is heterogeneous. 
  We prove that our relation support_equivalence is reflexive, 
  symmetric and transitive. This is going to be useful to be able to rewrite 
  bigraphs at will. *)
Module LeanSupportEquivalence (s : SignatureParameter) (n : InfiniteParameter).
Module eb := SupportEquivalenceBigraphs s n.
Include eb. 

Parameter onto : forall [A : Type] (lA : list A), list { a : A | In a lA }.

Axiom onto_nil : forall {A : Type}, onto (@nil A) = nil.

Axiom onto_cons : forall [A : Type] (h : A) (t : list A),
  onto (h::t) = 
  (exist (fun a => In a (h::t)) h (in_eq h t)) :: 
    (map (fun (a_in_t : { a : A | In a t }) => 
      let (a, Ha) := a_in_t in exist _ a (List.in_cons _ _ _ Ha)) (onto t)).

Axiom onto_Onto : forall [A : Type] (lA : list A) (a : { a : A | In a lA }), In a (onto lA).




(*** GET LIST OF INNERNAMES ***)
Definition make_seq_ListType (l:list InfType) : list {n:InfType| In n l}
  := onto l.

Lemma wf_make_seq_ListType {l} (inner:ListType l) : 
  In inner (make_seq_ListType (ndlist l)).
  Proof.
  apply onto_Onto.
  Qed.


(*** GET LIST OF PORTS ***)
Definition make_seq_Port_for_node_n {s i r o} {b:bigraph s i r o} (n:get_node b) : 
  seq (Port (get_control (bg:=b))) := map 
    (fun port => existT (fun n => 'I_(Arity (get_control (bg:=b) n))) n (port)) 
    (ord_enum (Arity (get_control (bg:=b) n))).


Lemma wf_make_seq_Port {s i r o} (b:bigraph s i r o) 
  (node : get_node b)
  {Iport : 'I_(Arity (get_control (bg:=b) node))}
  : 
  In (existT (fun n : get_node b => 'I_(Arity (get_control (bg:=b) n))) node Iport) (make_seq_Port_for_node_n node).
  Proof.
  unfold make_seq_Port_for_node_n. 
  apply in_map.
  apply In_ord_enum.
  Qed.



(*** IDLE EDGES ***************************************)
Definition not_is_idle {s i r o} {b:bigraph s i r o} (e: get_edge b) : bool := 
  Coq.Lists.List.existsb 
    (A := ListType i)
    (fun i => match (get_link (bg:=b)) (inl i) with 
      |inl _ => false 
      |inr e' => e == e'
      end) 
    (make_seq_ListType (ndlist i))
  || 
  Coq.Lists.List.existsb 
    (A := get_node b)
    (fun n => 
      Coq.Lists.List.existsb 
        (A := Port (get_control (bg:=b)))
        (fun p => match (get_link (bg:=b)) (inr p) with 
          |inl _ => false 
          |inr e' => e == e'
          end) 
        (make_seq_Port_for_node_n n)) 
    (enum (get_node b)).



Lemma exists_inner_implies_not_idle {s i r o} {b:bigraph s i r o} (i':ListType i) (e: get_edge b) : 
  get_link (bg:=b) (inl i') = (inr e) -> 
    not_is_idle e.
  Proof.
  intros.
  simpl in *.
  unfold not_is_idle.  
  apply Bool.orb_true_intro. left.
  unfold List.existsb.
  apply existsb_exists. exists i'.
  rewrite H. split.
  - apply wf_make_seq_ListType.
  - by apply/eqP. 
  Qed.

Lemma exists_inner_implies_not_idle_exists {s i r o} {b:bigraph s i r o} (e: get_edge b) :
  (exists (i':ListType i),
  get_link (bg:=b) (inl i') = (inr e)) -> 
    not_is_idle e.
  Proof.
  intros. 
  destruct H.
  apply (exists_inner_implies_not_idle x). apply H.
  Qed.


Lemma exists_port_implies_not_idle {s i r o} {b:bigraph s i r o} (p:Port (get_control (bg:=b))) (e: get_edge b) : 
  get_link (bg:=b) (inr p) = (inr e) -> 
    not_is_idle e.
  Proof.
  intros.
  simpl in *.
  unfold not_is_idle.  
  apply Bool.orb_true_intro. right.
  unfold List.existsb.
  destruct p as [node Iport] eqn:PORT. 
  apply existsb_exists. exists node.
  split. 
  - apply In_enum.
  - apply existsb_exists. exists p.
  split.
  + subst p. apply wf_make_seq_Port.
  + subst p. destruct get_link.
  * discriminate H.
  * inversion H. by apply/eqP. 
  Qed. 

Lemma exists_port_implies_not_idle_exists {s i r o} {b:bigraph s i r o} (e: get_edge b) : 
  (exists (p:Port (get_control (bg:=b))),
  get_link (bg:=b) (inr p) = (inr e)) -> 
    not_is_idle e.
  Proof.
  intros. 
  destruct H.
  apply (exists_port_implies_not_idle x). apply H.
  Qed.


Lemma exist_implies_not_idle_exists {s i r o} {b:bigraph s i r o} (e: get_edge b) : 
  (exists (ip:ListType i + Port (get_control (bg:=b))),
  get_link (bg:=b) (ip) = (inr e)) -> 
    not_is_idle e.
  Proof.
  intros [[inner|port] H].
  apply (exists_inner_implies_not_idle inner e H).
  apply (exists_port_implies_not_idle port e H).
  Qed.


Lemma not_is_idle_implies_exists_inner_or_node {s i r o} {b:bigraph s i r o} (e: get_edge b) : 
  not_is_idle e -> 
    exists ip, get_link (bg:=b) ip = (inr e).
  Proof.
  intros.
  simpl in *.
  unfold not_is_idle in H.
  apply Bool.orb_prop in H.
  destruct H as [H|H].
  - unfold List.existsb in H.
  simpl in *.
  apply existsb_exists in H. destruct H as [inner [H H']]. 
  exists (inl inner).
  destruct (get_link).
  + discriminate H'.
  + f_equal. symmetry.
  by apply/eqP.
  - unfold List.existsb in H.
  simpl in *.
  apply existsb_exists in H. destruct H as [node [Hnode H]].
  apply existsb_exists in H. destruct H as [port [Hport H]].
  exists (inr port).
  destruct (get_link).
  + discriminate H.
  + f_equal. symmetry.
  by apply/eqP.
  Qed.
  
Definition get_edges_wo_idles {s i r o} (b:bigraph s i r o) := 
  {e : get_edge b | not_is_idle e}.



(*** LEAN SECTION ***)

Definition lean {s i r o} (b:bigraph s i r o) :
  bigraph s i r o.
  Proof.
  refine (@Big s i r o
    (get_node b)
    (get_edges_wo_idles b)
    (get_control (bg:=b))
    (get_parent (bg:=b))
    _
    (get_ap (bg:=b))).
  intros ip'.
  assert (exists ip'', get_link (bg:=b) ip'' = get_link (bg:=b) ip') as H; [ exists (ip'); reflexivity | ].  
  destruct (get_link (bg:=b) ip') as [o'|e'].
  + left. exact o'.
  + right. exists e'. (*le GOAL*) 
  apply (exist_implies_not_idle_exists). 
  exact H. 
  Defined.


Definition surjective {A B} (f : A -> B) := forall b, exists a, f a = b.
Definition surjective_link {I P O E} (f : I + P -> O + E) := 
  forall e:E, exists ip:I+P, f ip = inr e.

Definition is_lean {s i r o} (b:bigraph s i r o) := 
  surjective_link (get_link (bg:=b)).

Theorem lean_is_lean {s i r o} (b:bigraph s i r o) :
  is_lean (lean b).
  Proof.
  unfold is_lean,surjective_link.
  unfold lean. simpl.
  intros [nie Hnie]. simpl in nie. simpl.
  destruct (not_is_idle_implies_exists_inner_or_node nie Hnie) as [ip Hip].
  exists ip.
  generalize (ex_intro
    (fun ip'' : {inner : InfType | In inner i} +
    Port (get_control (bg:=b)) =>
    get_link (bg:=b) ip'' = get_link (bg:=b) ip) ip
    (erefl (get_link (bg:=b) ip))).
  intros X.
  destruct get_link.
  discriminate Hip.
  f_equal. apply subset_eq_compat. injection Hip. auto.
  Qed.

Record place_graph_support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigHalfEq
  {
    bij_s_h : s1 = s2 ;
    bij_i_h : permutation i1 i2 ; 
    bij_r_h : r1 = r2 ;
    bij_o_h : permutation o1 o2 ;
    bij_n_h : bijection (get_node b1) (get_node b2);
    bij_p_h : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n_h n1)))) ;
    big_control_eq_h : (bij_n_h -->> (@bij_id Kappa)) (get_control (bg:=b1)) = get_control (bg:=b2) ;
    big_parent_eq_h : ((bij_n_h <+> (bij_rew bij_s_h)) -->> (bij_n_h <+> ((bij_rew bij_r_h)))) (get_parent (bg:=b1)) = get_parent (bg:=b2) ;
  }.


Theorem lean_bigraph_same_bigraph {s i r o} (b:bigraph s i r o) :
  place_graph_support_equivalence b (lean b) /\ 
  forall (ip : ListType i + Port (get_control (bg := b))),
    match (get_link (bg:=b) ip) with 
    | inl outer => 
      match (get_link (bg:=lean b) ip) with  
        | inl outer' => sval outer = sval outer'
        | _ => False 
      end 
    | inr edg => 
      match (get_link (bg:=lean b) ip) with  
        | inr edg' => edg = sval edg'
        | _ => False 
      end
    end.
  Proof.
    split.
    eapply (
      BigHalfEq _ _ _ _ _ _ _ _ b (lean b)
        (erefl)
        (permutation_id i)
        (erefl)
        (permutation_id o)
        bij_id
        (fun _ => bij_id)
    ).
    - rewrite bij_fun_compose_id. reflexivity. 
    - rewrite bij_rew_id. rewrite bij_rew_id.
      rewrite bij_sum_compose_id.
      rewrite bij_sum_compose_id.
      rewrite bij_fun_compose_id.
      reflexivity.
    - intros ip.
      destruct get_link eqn:E; simpl.
      + generalize ((ex_intro
        (fun ip'' : {inner : InfType | In inner i} + Port (get_control (bg:=b))
        => get_link (bg:=b) ip'' = get_link (bg:=b) ip)
        ip (erefl (get_link (bg:=b) ip)))).
      intros.
      destruct get_link. inversion E.
      auto. discriminate E.
      + generalize (ex_intro
        (fun ip'' : {inner : InfType | In inner i} + Port (get_control (bg:=b))
        => get_link (bg:=b) ip'' = get_link (bg:=b) ip)
        ip (erefl (get_link (bg:=b) ip))).
      intros. destruct get_link.
      discriminate E.
      inversion E. auto.
  Qed.



(*LEAN SUPPORT EQUIVALENCE*)
Definition lean_support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) := 
  support_equivalence (lean b1) (lean b2).

Lemma build_twin_ordinal {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  {b1 : bigraph s1 i1 r1 o1} {b2 : bigraph s2 i2 r2 o2} 
  {bij_n : bijection (get_node b1) (get_node b2)}
  {n : get_node b2} (port : 'I_(Arity (get_control (bg:=b2) n))) :
  exists port':'I_(Arity (get_control (bg:=b2) (bij_n ((bij_n ⁻¹) n)))), 
  nat_of_ord port' = nat_of_ord port.
  Proof.
  destruct port as [port Hport]. simpl.
  eexists (Ordinal (m:=port) _).
  reflexivity.
  Unshelve.
  rewrite fob_funcomp_unfold. apply Hport. 
  Qed.


Lemma not_is_idle_imp {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  (bij_i : permutation i1 i2)
  (bij_o : permutation o1 o2)
  (bij_n : bijection (get_node b1) (get_node b2))
  (bij_e : bijection (get_edge b1) (get_edge b2))
  (bij_p : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n n1)))))
  (link_eq : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link (bg := b1)) = get_link (bg := b2)) : 
  forall a : get_edge b1,
    not_is_idle a -> not_is_idle (bij_e a).
  Proof.
    intros e H.  
    apply not_is_idle_implies_exists_inner_or_node in H.
    destruct H as [[[inner Hinner]|port] H].
    - destruct (bij_i inner). 
    eapply (exists_inner_implies_not_idle (exist _ inner (H0 Hinner))).
    rewrite <- link_eq.
    simpl.
    unfold parallel,funcomp, bij_subset_backward. simpl.
    rewrite <- (innername_proof_irrelevant b1 Hinner).
    destruct get_link.
    + discriminate H.
    + f_equal. f_equal.
    injection H. auto.
    - destruct port as [n port].
    set (n':= bij_n n).
    eapply (exists_port_implies_not_idle 
      (existT _ n' (bij_p n port))). 
    rewrite <- link_eq.
    simpl.
    unfold parallel,funcomp, bij_subset_backward. simpl.
    eassert (EA : eq_rect_r
    (fun n0 : get_node b2 => 'I_(Arity (get_control (bg:=b2) n0)))
    (bij_p n port)
    (equal_f (fob_id (get_node b1) (get_node b2) bij_n) n') = 
    bij_p ((bij_n ⁻¹) n') (Ordinal (m:=port) _)  
    ). 
      {unfold n'.
      apply val_inj. simpl.
      unfold eq_rect_r. unfold eq_rect.  
      destruct (Logic.eq_sym
      (equal_f (fob_id (get_node b1) (get_node b2) bij_n) (bij_n n))).
      f_equal. simpl. f_equal. 
      assert (forall x x' p p', x = x' 
      -> nat_of_ord p = nat_of_ord p' -> nat_of_ord (bij_p x p) = 
      nat_of_ord (bij_p x' p')).
        {intros.
        subst x. f_equal. f_equal. destruct p. destruct p'. apply val_inj.
        simpl. simpl in H1. auto. }
      apply H0.
      rewrite bof_funcomp_unfold. reflexivity. reflexivity. }
    Unshelve. 2:{unfold n'. rewrite bof_funcomp_unfold. 
    destruct port. simpl. apply i0. }
    
    rewrite EA. clear EA. 
    rewrite (bof_funcomp_unfold (bij_p ((bij_n ⁻¹) n'))).
    unfold n'.
    erewrite (port_proof_irrelevant_full (n:=(bij_n ⁻¹) (bij_n n)) (n':=n)).
    2:{ apply bof_funcomp_unfold. }
    Unshelve.
    3:{simpl. exact port. }
    destruct get_link.
    + discriminate H.
    + f_equal. f_equal. injection H. auto.
    simpl. reflexivity.
  Qed.


Lemma not_is_idle_is_imp {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  (bij_i : permutation i1 i2)
  (bij_o : permutation o1 o2)
  (bij_n : bijection (get_node b1) (get_node b2))
  (bij_e : bijection (get_edge b1) (get_edge b2))
  (bij_p : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n n1)))))
  (link_eq : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link (bg := b1)) = get_link (bg := b2)) : 
  forall a : get_edge b1,
    not_is_idle (bij_e a) -> not_is_idle a.
  Proof.
  intros e H.
  apply not_is_idle_implies_exists_inner_or_node in H.
    destruct H as [[[inner Hinner]|port] H].
    - destruct (bij_i inner). 
      eapply (exists_inner_implies_not_idle (exist _ inner (H1 Hinner))).
      rewrite <- link_eq in H.
      simpl in H.
      unfold parallel,funcomp, bij_subset_backward in H. simpl in H.
      rewrite <- (innername_proof_irrelevant b1 (H1 Hinner)) in H.
      destruct get_link.
      + discriminate H.
      + f_equal. injection H. apply (bij_injective bij_e _ _).
    - destruct port as [n port].
      set (n':= backward bij_n n).
      set (port' := build_twin_ordinal (b1 := b1) (bij_n := bij_n) port).
      destruct port' as [port' Hport'].
      eapply (exists_port_implies_not_idle 
        (existT _ (n') (backward (bij_p n') port'))). (*port*)
      rewrite <- link_eq in H.
      simpl in H.
      unfold parallel,funcomp, bij_subset_backward in H. simpl in H.
      unfold n'.
      assert (eq_rect_r
      (fun n : get_node b2 => 'I_(Arity (get_control (bg:=b2) n)))
      port (equal_f (fob_id (get_node b1) (get_node b2) bij_n) n)
        = port').
      { destruct port. destruct port'. 
      simpl in Hport'. 
      subst m0. apply val_inj. simpl.
      unfold eq_rect_r.
      unfold eq_rect. simpl. 
      destruct (Logic.eq_sym (equal_f (fob_id (get_node b1) (get_node b2) bij_n) n)).
      reflexivity. }
      rewrite H0 in H.
      clear H0.
      destruct get_link.
      + discriminate H.
      + f_equal. injection H. apply (bij_injective bij_e _ _).
  Qed.
(* 
  intros e.
  set (e' := bij_e e).
  assert (e = bijection_inv bij_e e').
    unfold e'.
    simpl.
    rewrite bof_funcomp_unfold.
    reflexivity.
  rewrite H.
  eapply (not_is_idle_imp b2 b1 (permutation_commute bij_i) (permutation_commute bij_o) (bijection_inv bij_n) (bijection_inv bij_e)).
  Unshelve.
  2:{ 
    intros n2.
    clear link_eq.
    specialize (bij_p (bijection_inv bij_n n2)).
    simpl in bij_p.
    rewrite fob_funcomp_unfold in bij_p.
    apply (bijection_inv bij_p).
  }
  rewrite <- link_eq.
  rewrite <- bij_compose_forward_simpl.
  rewrite bij_fun_compose_compose.
  rewrite bij_sum_compose_compose.
  rewrite bij_sum_compose_compose.
  rewrite bij_subset_compose_compose.
  rewrite bij_subset_compose_compose.
  rewrite bij_sigT_compose_compose.
  simpl.
  rewrite (bof_id _ _ bij_e) .
  apply functional_extensionality.
  intros ip.
  destruct ip as [(inner, Hinner) | (node, port)]; unfold parallel, funcomp; simpl.
  rewrite <- (innername_proof_irrelevant b1 Hinner).
  destruct get_link.
  f_equal. unfold bij_subset_forward.
  destruct s0. apply subset_eq_compat. reflexivity. reflexivity.
  erewrite (port_proof_irrelevant_full (n':=node) (port' := port)).
  Unshelve.
  2:{rewrite (bof_id _ _ bij_n). reflexivity. }
  2:{unfold eq_rect_r.
  (* erewrite (eq_rect_pi ( x:= node)).
  erewrite (eq_rect_pi ( x:= bij_n ((bij_n ⁻¹) (bij_n node)))). *)
  unfold funcomp.
  destruct port as [port Hport]. simpl in *.
  assert (eq_rect node
    (fun y : get_node b1 => 'I_(Arity (get_control (bg:=b1) y)))
    port ((bij_n ⁻¹) (bij_n ((bij_n ⁻¹) (bij_n node)))) ?[H'] = port).
  erewrite fob_funcomp_unfold at 9.
  rewrite fob_funcomp_unfold.
  unfold funcomp. 
  
  admit. }
  destruct get_link.
  f_equal. unfold bij_subset_forward.
  destruct s0. apply subset_eq_compat. reflexivity. reflexivity.
  Unshelve. rewrite (bof_id _ _ bij_n). reflexivity.
  Admitted. *)


Lemma not_is_idle_eq {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) 
  (bij_i : permutation i1 i2)
  (bij_o : permutation o1 o2)
  (bij_n : bijection (get_node b1) (get_node b2))
  (bij_e : bijection (get_edge b1) (get_edge b2))
  (bij_p : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n n1)))))
  (link_eq : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link (bg := b1)) = get_link (bg := b2)) : 
  forall a : get_edge b1,
    not_is_idle a <-> not_is_idle (bij_e a).
  Proof.
  split.
  apply (not_is_idle_imp b1 b2 bij_i bij_o bij_n bij_e bij_p link_eq).
  apply (not_is_idle_is_imp b1 b2 bij_i bij_o bij_n bij_e bij_p link_eq).
  Qed.


Theorem support_equivalence_implies_lean_support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : 
  support_equivalence b1 b2 -> lean_support_equivalence b1 b2.
  Proof.
  intros [bij_s bij_i bij_r bij_o bij_n bij_e bij_p control_eq parent_eq link_eq].
  unfold lean_support_equivalence.
  refine (
    SupEq _ _ _ _ _ _ _ _ (lean b1) (lean b2)
      bij_s bij_i bij_r bij_o bij_n _ bij_p control_eq parent_eq _
  ). 
  Unshelve.  
  2:{simpl.
    eapply (<{ bij_e | _ }>).
    Unshelve.
    apply (not_is_idle_eq b1 b2 bij_i bij_o bij_n bij_e bij_p link_eq).
  }    
  simpl.
  unfold parallel. 
  apply functional_extensionality.
  unfold funcomp;simpl. intros ipa.
  unfold bij_subset_backward, bij_subset_forward. simpl.
  generalize (ex_intro
    (fun ip'' : {inner : InfType | In inner i2} + Port (get_control (bg:=b2)) =>
    get_link (bg:=b2) ip'' = get_link (bg:=b2) ipa) ipa
    (erefl (get_link (bg:=b2) ipa))).
  intros.
  destruct get_link eqn:L2.
  unfold eq_ind_r.
  
  generalize ((@ex_intro (sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1)) (@get_control s1 r1 i1
    o1 b1))) (fun ip'' : sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (@get_control s1 r1 i1 o1 b1)) => @eq (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1))) (Finite.sort (@get_edge s1 r1 i1 o1 b1))) (@get_link s1 r1 i1 o1 b1 ip'') (@get_link s1 r1 i1 o1 b1 match ipa return
    (sum (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))))
    with | @inl _ _ a => @inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1))) (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    match a return (@sig InfType (fun name : InfType => @In InfType name
    (ndlist i1))) with | @exist _ _ b Qb =>  @exist InfType (fun name : InfType => @In InfType name (ndlist i1)) b (match bij_i b return (forall _ : @In InfType b (ndlist i2),  @In InfType b (ndlist i1)) with | @conj _ _ _ H => H  end
    (@eq_ind InfType b (fun y : InfType => @In InfType y (ndlist i2)) Qb b (@Logic.eq_sym InfType b b (@Logic.eq_refl InfType (@funcomp InfType InfType InfType (fun x : InfType => x) (fun x : InfType => x) b))))) end | @inr _ _ c => @inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1))) (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1)) (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) => ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) => ordinal (Arity
    (@get_control s2 r2 i2 o2 b2 (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1)) (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) => ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))) (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) => @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1
    a))) (ordinal (Arity (@get_control s2 r2 i2 o2 b2 (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1)) (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a)))) (bij_p a)) (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2 b2)) (Finite.sort (@get_node s1 r1 i1 o1 b1)) (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) => ordinal (Arity (@get_control s2 r2 i2 o2 b2 n))) (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1)) (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n) c)) end)) match ipa return
    (sum (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))) with | @inl _ _ a =>
    @inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1)) (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) => ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))) match a return (@sig InfType (fun name : InfType => @In InfType name
    (ndlist i1))) with | @exist _ _ b Qb => @exist InfType (fun name : InfType => @In InfType name (ndlist i1)) b (match bij_i b return (forall _ : @In InfType b (ndlist i2), @In InfType b (ndlist i1)) with | @conj _ _ _ H => H end
    (@eq_ind InfType b (fun y : InfType => @In InfType y (ndlist i2)) Qb b (@Logic.eq_sym InfType b b (@Logic.eq_refl InfType (@funcomp InfType InfType InfType (fun x : InfType => x) (fun x : InfType => x) b)))))
    end | @inr _ _ c => @inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1 a)))
    (ordinal (Arity (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (bij_p a)) (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2 b2))
    (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n)))
    (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n) c))
    end (@Logic.eq_refl (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1)))
    (Finite.sort (@get_edge s1 r1 i1 o1 b1)))
    (@get_link s1 r1 i1 o1 b1  match ipa return
    (sum (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))))
    with | @inl _ _ a => @inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    match a return (@sig InfType (fun name : InfType => @In InfType name
    (ndlist i1))) with | @exist _ _ b Qb => @exist InfType (fun name : InfType => @In InfType name (ndlist i1)) b (match bij_i b return
    (forall _ : @In InfType b (ndlist i2), @In InfType b (ndlist i1))
    with | @conj _ _ _ H => H end
    (@eq_ind InfType b (fun y : InfType => @In InfType y (ndlist i2))
    Qb b (@Logic.eq_sym InfType b b (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) b)))))
    end | @inr _ _ c => @inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1))) (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1
    a))) (ordinal (Arity (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2))
    bij_n a)))) (bij_p a))
    (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2
    b2)) (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n)))
    (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n) c))
    end)))).
  intros.
  destruct ipa as [ia | pa]. 
  destruct (@get_link s1 r1 i1 o1 b1
    (@inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    match ia return (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    with
    | @exist _ _ b Qb =>
    @exist InfType (fun name : InfType => @In InfType name (ndlist i1)) b
    (match
    bij_i b return (forall _ : @In InfType b (ndlist i2),
    @In InfType b (ndlist i1))
    with
    | @conj _ _ _ H => H
    end
    (@eq_ind InfType b (fun y : InfType => @In InfType y (ndlist i2)) Qb b
    (@Logic.eq_sym InfType b b
    (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) b)))))
    end)) eqn:E'.
  f_equal. 
  destruct s0. destruct s3. 
  apply subset_eq_compat.
  destruct ia as [ia Hia].
  simpl in L2.
  simpl in E'.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  rewrite <- (innername_proof_irrelevant b1 (match bij_i ia with
    | conj _ H => H
    end Hia)) in L2.
  destruct get_link.
  auto.
  inversion E'.
  subst s0.
  inversion L2.
  reflexivity.

 
  discriminate E'.

  exfalso.
  rewrite <- link_eq in L2.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  destruct ia as [ia Hia].
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  rewrite <- (innername_proof_irrelevant b1 ((match bij_i ia with
    | conj _ H => H
    end
    (eq_ind ia ((In (A:=InfType))^~ i2) Hia ia
    (Logic.eq_sym (erefl ((id <o> id) ia))))))) in L2. 
  destruct get_link.
  discriminate E'.

  discriminate L2.

  destruct (get_link (bg:=b1)
    (inr
    (bij_dep_sum_2_forward (fun a : get_node b1 => bijection_inv (bij_p a))
    (bij_dep_sum_1_forward (bijection_inv bij_n) pa)))) eqn:L1.
  destruct s0. destruct s3. f_equal. 
  apply subset_eq_compat.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  destruct pa as [pa Ipa].
  unfold bij_dep_sum_2_forward, bij_dep_sum_1_forward in L1.
  simpl in L1. 
  simpl in L2.
  destruct get_link.
  inversion L1.
  subst s0.
  inversion L2.
  reflexivity.

  discriminate L2.

  exfalso.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  destruct pa as [pa Ipa].
  unfold bij_dep_sum_2_forward, bij_dep_sum_1_forward in L1.
  simpl in L1. 
  simpl in L2.
  destruct get_link.
  discriminate L1.

  discriminate L2.

  destruct ipa as [[ia Hia] | [pa Hpa]].
  unfold eq_ind_r.
  generalize (@ex_intro
    (sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (@get_control s1 r1 i1 o1 b1)))
    (fun
    ip'' : sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (@get_control s1 r1 i1 o1 b1)) =>
    @eq
    (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1)))
    (Finite.sort (@get_edge s1 r1 i1 o1 b1))) (@get_link s1 r1 i1 o1 b1
    ip'')
    (@get_link s1 r1 i1 o1 b1
    (@inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@exist InfType (fun name : InfType => @In InfType name (ndlist i1)) ia
    (match
    bij_i ia
    return (forall _ : @In InfType ia (ndlist i2),
    @In InfType ia (ndlist i1))
    with
    | @conj _ _ _ H => H
    end
    (@eq_ind InfType ia (fun y : InfType => @In InfType y (ndlist i2))
    Hia ia
    (@Logic.eq_sym InfType ia ia
    (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) ia)))))))))
    (@inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@exist InfType (fun name : InfType => @In InfType name (ndlist i1)) ia
    (match
    bij_i ia
    return (forall _ : @In InfType ia (ndlist i2), @In InfType ia
    (ndlist i1))
    with
    | @conj _ _ _ H => H
    end
    (@eq_ind InfType ia (fun y : InfType => @In InfType y (ndlist i2)) Hia ia
    (@Logic.eq_sym InfType ia ia
    (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) ia)))))))
    (@Logic.eq_refl
    (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1)))
    (Finite.sort (@get_edge s1 r1 i1 o1 b1)))
    (@get_link s1 r1 i1 o1 b1
    (@inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@exist InfType (fun name : InfType => @In InfType name (ndlist i1)) ia
    (match
    bij_i ia
    return (forall _ : @In InfType ia (ndlist i2),
    @In InfType ia (ndlist i1))
    with
    | @conj _ _ _ H => H
    end
    (@eq_ind InfType ia (fun y : InfType => @In InfType y (ndlist i2))
    Hia ia
    (@Logic.eq_sym InfType ia ia
    (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) ia)))))))))).
  intros.
  destruct (@get_link s1 r1 i1 o1 b1
    (@inl (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@exist InfType (fun name : InfType => @In InfType name (ndlist i1)) ia
    (match
    bij_i ia return (forall _ : @In InfType ia (ndlist i2),
    @In InfType ia (ndlist i1))
    with
    | @conj _ _ _ H => H
    end
    (@eq_ind InfType ia (fun y : InfType => @In InfType y (ndlist i2)) Hia ia
    (@Logic.eq_sym InfType ia ia
    (@Logic.eq_refl InfType
    (@funcomp InfType InfType InfType (fun x : InfType => x)
    (fun x : InfType => x) ia)))))))) eqn:L1.
  exfalso.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  erewrite <- (innername_proof_irrelevant b1 (match bij_i ia with
    | conj _ x0 => x0
    end (eq_ind_r ((In (A:=InfType))^~ i2) Hia (erefl ia)))) in L1.
  destruct get_link.
  discriminate L2.

  discriminate L1.

  f_equal.
  apply subset_eq_compat.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  rewrite <- (innername_proof_irrelevant b1 (match bij_i ia with
    | conj _ x0 => x0
    end (eq_ind_r ((In (A:=InfType))^~ i2) Hia (erefl ia)))) in L1.
  destruct get_link.
  discriminate L1.

  inversion L2.
  inversion L1.
  subst s3.
  reflexivity.

  unfold eq_ind_r.
  generalize ((@ex_intro
    (sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (@get_control s1 r1 i1 o1 b1)))
    (fun
    ip'' : sum (@sig InfType (fun inner : InfType => @In InfType inner (ndlist i1)))
    (@Port (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (@get_control s1 r1 i1 o1 b1)) =>
    @eq
    (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1)))
    (Finite.sort (@get_edge s1 r1 i1 o1 b1))) (@get_link s1 r1 i1 o1 b1
    ip'')
    (@get_link s1 r1 i1 o1 b1
    (@inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1
    a)))
    (ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n
    a)))) (bij_p a))
    (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2
    b2))
    (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n)))
    (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n)
    (@existT (Finite.sort (@get_node s2 r2 i2 o2 b2))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n))) pa
    Hpa))))))
    (@inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1 a)))
    (ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (bij_p a))
    (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2 b2))
    (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n)))
    (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n)
    (@existT (Finite.sort (@get_node s2 r2 i2 o2 b2))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n))) pa Hpa))))
    (@Logic.eq_refl
    (sum (@sig InfType (fun outer : InfType => @In InfType outer (ndlist o1)))
    (Finite.sort (@get_edge s1 r1 i1 o1 b1)))
    (@get_link s1 r1 i1 o1 b1
    (@inr (@sig InfType (fun name : InfType => @In InfType name (ndlist i1)))
    (@sigT (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1))))
    (@bij_dep_sum_2_forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n a))))
    (fun n1 : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    ordinal (Arity (@get_control s1 r1 i1 o1 b1 n1)))
    (fun a : Finite.sort (@get_node s1 r1 i1 o1 b1) =>
    @bijection_inv (ordinal (Arity (@get_control s1 r1 i1 o1 b1
    a)))
    (ordinal
    (Arity
    (@get_control s2 r2 i2 o2 b2
    (@forward (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n
    a)))) (bij_p a))
    (@bij_dep_sum_1_forward (Finite.sort (@get_node s2 r2 i2 o2
    b2))
    (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n)))
    (@bijection_inv (Finite.sort (@get_node s1 r1 i1 o1 b1))
    (Finite.sort (@get_node s2 r2 i2 o2 b2)) bij_n)
    (@existT (Finite.sort (@get_node s2 r2 i2 o2 b2))
    (fun n : Finite.sort (@get_node s2 r2 i2 o2 b2) =>
    ordinal (Arity (@get_control s2 r2 i2 o2 b2 n))) pa
    Hpa)))))))).
  intros.
  destruct (get_link (bg:=b1)
    (inr
    (bij_dep_sum_2_forward (fun a : get_node b1 => bijection_inv (bij_p a))
    (bij_dep_sum_1_forward (bijection_inv bij_n)
    (existT (fun n : get_node b2 => 'I_(Arity (get_control (bg:=b2) n)))
    pa Hpa))))) eqn:L1.
  exfalso.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L1.
  simpl in L1.
  destruct get_link.
  discriminate L2.

  discriminate L1.

  f_equal.
  apply subset_eq_compat.
  rewrite <- link_eq in L2.
  simpl in L2.
  clear control_eq parent_eq e e0.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L2.
  simpl in L2.
  unfold funcomp in L2.
  unfold parallel, bij_subset_forward, bij_subset_backward, bij_dep_sum_2_forward, bij_dep_sum_1_forward in L1.
  simpl in L1.
  destruct get_link.
  discriminate L2.

  inversion L1.
  subst s3.
  inversion L2. reflexivity.
  Qed.




End LeanSupportEquivalence. 