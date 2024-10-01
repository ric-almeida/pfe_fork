Set Warnings "-notation-overridden, -parsing, -masking-absolute-name, -cannot-define-projection".

Require Import AbstractBigraphs.
Require Import Bijections.
Require Import Names.
Require Import SignatureBig.
Require Import MyBasics.
Require Import MathCompAddings.
Require Import FunctionalExtensionality.


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
Module EquivalenceBigraphs (s : SignatureParameter) (n : NamesParameter).
Module b := Bigraphs s n.
Include b. 

(** ** On the heterogeneous type *)
Record support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  SupEq
  {
    bij_s : s1 = s2 ;
    bij_i : permutation i1 i2 ; (*Permutation i1 i2*)
    bij_r : r1 = r2 ;
    bij_o : permutation o1 o2 ;
    bij_n : bijection (get_node b1) (get_node b2);
    bij_e : bijection (get_edge b1) (get_edge b2);
    bij_p : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n n1)))) ;
    big_control_eq : (bij_n -->> (@bij_id Kappa)) (get_control (bg:=b1)) = get_control (bg:=b2) ;
    big_parent_eq  : ((bij_n <+> (bij_rew bij_s)) -->> (bij_n <+> ((bij_rew bij_r)))) (get_parent (bg:=b1)) = get_parent (bg:=b2) ;
    big_link_eq    : ((<{bij_id | bij_i}> <+> <{ bij_n & bij_p }>) -->> (<{bij_id| bij_o}> <+> bij_e)) (get_link (bg := b1)) = get_link (bg := b2)
  }.
  
Lemma support_equivalence_refl {s r : nat} {i o : NoDupList} (b : bigraph s i r o) :
  support_equivalence b b.
  Proof.
  eapply (SupEq _ _ _ _ _ _ _ _ _ _ erefl _ erefl _ bij_id bij_id (fun _ => bij_id)).
  + rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_rew_id.
    rewrite bij_rew_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  + rewrite bij_sigT_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_subset_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_sum_compose_id.
    rewrite bij_fun_compose_id.
    reflexivity.
  Unshelve.
  - unfold permutation. intros. reflexivity.
  - unfold permutation. intros. reflexivity.
  Qed.

Lemma support_equivalence_sym {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
  support_equivalence b1 b2
      -> support_equivalence b2 b1.
  Proof.
  intro Heqb1b2.
  destruct Heqb1b2 as (bij_s, bij_i, bij_r, bij_o, bij_n, bij_e, bij_p, big_control_eq, big_parent_eq, big_link_eq).
  apply (SupEq _ _ _ _ _ _ _ _ b2 b1
          (esym bij_s)
          (adjunction_equiv bij_id bij_i)
          (esym bij_r)
          (adjunction_equiv (bij_id) bij_o)
          (bijection_inv bij_n)
          (bijection_inv bij_e)
          (adjunction_bij bij_n bij_p)).
  + simpl. 
    rewrite <- big_control_eq.
    simpl.
    rewrite comp_assoc.
    rewrite id_left_neutral.
    rewrite comp_assoc.
    rewrite id_left_neutral.
    rewrite bij_n.(bof_id _ _).
    rewrite id_right_neutral.
    reflexivity.
  + rewrite <- big_parent_eq.
    rewrite <- bij_inv_rew.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_rew.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_inv_left_simpl.
    reflexivity.
  + 
    rewrite <- bij_inv_sigT.
    change (
      (<{ (bijection_inv bij_id) | adjunction_equiv bij_id bij_i }> <+>
      bijection_inv <{ bij_n & bij_p }> -->>
      <{ (bijection_inv bij_id) | adjunction_equiv bij_id bij_o }> <+> bijection_inv bij_e)
        (get_link (bg:=b2)) = get_link (bg:=b1)
    ). (* just rewriting bij_id as bij_inv bij_id, TODO : look for more elegant way?*)
    rewrite <- bij_inv_subset.
    rewrite <- bij_inv_subset.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_sum.
    rewrite <- bij_inv_fun.
    rewrite <- big_link_eq.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_inv_left_simpl.
    reflexivity.
  Qed.

Lemma support_equivalence_trans 
  {s1 r1 s2 r2 s3 r3 : nat} {i1 o1 i2 o2 i3 o3: NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) (b3 : bigraph s3 i3 r3 o3):
    support_equivalence b1 b2
      -> support_equivalence b2 b3  
        -> support_equivalence b1 b3.
  Proof.
  intros Heqb1b2 Heqb2b3.
  destruct Heqb1b2 as (bij_s12, bij_i12, bij_r12, bij_o12, bij_n12, bij_e12, bij_p12, big_control_eq12, big_parent_eq12, big_link_eq12).
  destruct Heqb2b3 as (bij_s23, bij_i23, bij_r23, bij_o23, bij_n23, bij_e23, bij_p23, big_control_eq23, big_parent_eq23, big_link_eq23).
  apply (SupEq _ _ _ _ _ _ _ _ b1 b3
          (eq_trans bij_s12 bij_s23)
          (fun name : Name => @iff_trans 
            (@In Name name (ndlist i1)) 
            (@In Name name (ndlist i2))
            (@In Name (@forward Name Name (@bij_id Name) name) (ndlist i3))
            (bij_i12 name) (bij_i23 (@forward Name Name (@bij_id Name) name))
          )
          (eq_trans bij_r12 bij_r23)
          (fun a => iff_trans (bij_o12 a) (bij_o23 (bij_id a)))
          (bij_n23 <O> bij_n12)
          (bij_e23 <O> bij_e12)
          (fun n1 => (bij_p23 (bij_n12 n1)) <O> (bij_p12 n1))).
  + rewrite <- big_control_eq23.
    rewrite <- big_control_eq12.
    reflexivity.
  + rewrite <- big_parent_eq23.
    rewrite <- big_parent_eq12.
    rewrite <- bij_rew_compose.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_rew_compose.
    rewrite <- bij_sum_compose_compose.
    rewrite <- bij_fun_compose_compose.
    reflexivity.
  + rewrite <- (@bij_subset_compose_compose_id Name (fun name => In name i1) (fun name => In name i2) (fun name => In name i3) bij_i12 bij_i23). 
    rewrite <- (@bij_subset_compose_compose_id Name (fun name => In name o1) (fun name => In name o2) (fun name => In name o3) bij_o12 bij_o23). 
    rewrite <- big_link_eq23.
    rewrite <- big_link_eq12.
    rewrite <- bij_compose_forward_simpl.
    rewrite bij_fun_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sum_compose_compose.
    rewrite bij_sigT_compose_compose.
    reflexivity.
  Qed.

(** ** On the packed type 
  The issue with the previous relation is that a parametric relation asks for two 
  objects of the exact same Type and our equality is heterogeneous. The solution we 
  will implement is to create a "packed bigraph" Type that will hold the interfaces 
  inside of it. This is a WIP. *)
  
Record bigraph_packed : Type :=
  mkPacked
  {
  s: nat;
  i: NoDupList;
  r: nat;
  o: NoDupList;
  big : bigraph s i r o
  }.

Coercion packing {s i r o} (b : bigraph s i r o) := 
  (mkPacked s i r o b).

Definition unpacking (b : bigraph_packed) : bigraph (s b) (i b) (r b) (o b) := 
  big b.

Definition bigraph_pkd_s_e (bp1 bp2 : bigraph_packed) := 
  support_equivalence (big bp1) (big bp2).

Theorem eq_packed_eq_eq {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList}  
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
   support_equivalence b1 b2 <-> bigraph_pkd_s_e b1 b2.
   split. auto. auto. 
   Qed. 

Lemma bigraph_pkd_s_e_refl (bp : bigraph_packed) : bigraph_pkd_s_e bp bp.
  Proof.
  apply support_equivalence_refl.
  Qed.

Lemma bigraph_pkd_s_e_sym (bp1 bp2 : bigraph_packed) : bigraph_pkd_s_e bp1 bp2 -> bigraph_pkd_s_e bp2 bp1.
  Proof.
  apply support_equivalence_sym.
  Qed.

Lemma bigraph_pkd_s_e_trans (bp1 bp2 bp3 : bigraph_packed) : bigraph_pkd_s_e bp1 bp2 -> bigraph_pkd_s_e bp2 bp3 -> bigraph_pkd_s_e bp1 bp3.
  Proof.
  apply support_equivalence_trans.
  Qed. 

Add Parametric Relation: (bigraph_packed) (bigraph_pkd_s_e)
  reflexivity proved by (bigraph_pkd_s_e_refl)
  symmetry proved by (bigraph_pkd_s_e_sym)
  transitivity proved by (bigraph_pkd_s_e_trans)
    as bigraph_pkd_s_e_rel.

Lemma bigraph_pkd_s_e_dec  
  (b1 : bigraph_packed) (b2 : bigraph_packed) :
  {bigraph_pkd_s_e b1 b2} + {~ bigraph_pkd_s_e b1 b2}.
  Proof. (* same problem, bigraph_pkd_s_e not transparent enough *)
    Fail decide equality. 
  Abort.

#[export] Instance big_Equivalence: Equivalence bigraph_pkd_s_e.
  constructor. 
  exact @bigraph_pkd_s_e_refl. 
  exact @bigraph_pkd_s_e_sym. 
  exact @bigraph_pkd_s_e_trans. Defined. 







Section LeanSupportEquivalence.

Parameter onto : forall [A : Type] (lA : list A), list { a : A | In a lA }.

Axiom onto_nil : forall {A : Type}, onto (@nil A) = nil.

Axiom onto_cons : forall [A : Type] (h : A) (t : list A),
  onto (h::t) = 
  (exist (fun a => In a (h::t)) h (in_eq h t)) :: 
    (map (fun (a_in_t : { a : A | In a t }) => 
      let (a, Ha) := a_in_t in exist _ a (List.in_cons _ _ _ Ha)) (onto t)).

Axiom onto_Onto : forall [A : Type] (lA : list A) (a : { a : A | In a lA }), In a (onto lA).




(*** GET LIST OF INNERNAMES ***)
Definition make_seq_NameSub (l:list Name) : list {n:Name| In n l}
  := onto l.

Lemma wf_make_seq_NameSub {l} (inner:NameSub l) : 
  In inner (make_seq_NameSub (ndlist l)).
  Proof.
  apply onto_Onto.
  Qed.



(*** GET LIST OF PORTS ***)
Definition make_seq_Port_for_node_n {s i r o} {b:bigraph s i r o} (n:get_node b) : 
  seq (Port (get_control (bg:=b))).
  Proof.
  unfold Port.
  set (arity := Arity (get_control (bg:=b) n)).
  destruct (leq arity 0) eqn:E.
  + exact [::].
  + induction arity as [|ar] eqn:Har. 
  eapply [:: existT (fun n => 'I_(Arity (get_control (bg:=b) n))) n (Ordinal (m:=0) _)].
  eapply [:: existT (fun n => 'I_(Arity (get_control (bg:=b) n))) n (Ordinal (m:=ar) _)].
  Unshelve. 
  - exfalso. rewrite leq0n in E. discriminate E.
  - subst arity. rewrite Har. apply ltnSn.
  Defined. 

Definition make_seq_Port {s i r o} (b:bigraph s i r o) : 
  seq (Port (get_control (bg:=b))).
  Proof.
  set (nodes := enum (get_node b)).
  apply (fold_left 
    (fun qt n => make_seq_Port_for_node_n n ++ qt) 
    nodes
    []).
  Defined.

Lemma wf_make_seq_Port {s i r o} (b:bigraph s i r o) 
  (p:Port (get_control (bg:=b))) : 
  In p (make_seq_Port b).
  Proof.
  unfold make_seq_Port.
  unfold make_seq_Port_for_node_n. simpl.
  (*TODO*)
  Admitted.


(*** GET SEQ OF INNERS AND PORTS ***)
Definition make_seq_link_domain {s i r o} (b:bigraph s i r o) : 
  seq (NameSub i + Port (get_control (bg:=b))).
  Proof.
  exact (map inl (make_seq_NameSub (ndlist i)) ++ (map inr (make_seq_Port b))).
  Defined.


Lemma wf_make_seq_link_domain_inners {s i r o} (b:bigraph s i r o) 
  (inner:Name) (hin : In inner (ndlist i)) :  
    In (inl (exist ((In (A:=Name))^~ i) inner hin)) (make_seq_link_domain b).
  Proof.
    unfold make_seq_link_domain.
    apply in_or_app. left.
    apply in_map.
    apply wf_make_seq_NameSub.
  Qed.

Lemma wf_make_seq_link_domain_ports {s i r o} (b:bigraph s i r o) 
  (n:get_node b) (ar : 'I_(Arity (get_control (bg:=b) n))) :  
    In (inr (existT _ n ar)) (make_seq_link_domain b).
  Proof.
    unfold make_seq_link_domain.
    apply in_or_app. right.
    apply in_map.
    apply wf_make_seq_Port.
  Qed.



(*** IDLE EDGES ***************************************)
Definition not_is_idle {s i r o} {b:bigraph s i r o} (e: get_edge b) : bool := 
  Coq.Lists.List.existsb 
    (A := NameSub i + Port (get_control (bg:=b)))
    (fun ip => match (get_link (bg:=b)) ip with 
      |inl _ => false 
      |inr e' => e == e'
      end) 
    (make_seq_link_domain b).

Fail Fixpoint is_idle {s i r o} {b:bigraph s i r o} (e: get_edge b) : bool := 
  forall ip, match get_link (bg:=b) ip with 
  |inr e' => e' == e
  | _ => true
  end.


Lemma exists_inner_implies_not_idle {s i r o} {b:bigraph s i r o} (i':NameSub i) (e: get_edge b) : 
  get_link (bg:=b) (inl i') = (inr e) -> 
    not_is_idle e.
  Proof.
  intros.
  simpl in *.
  unfold not_is_idle. 
  unfold List.existsb.
  simpl.
  apply existsb_exists. exists (inl i').
  rewrite H. split.
  - unfold NameSub in i'.
  simpl in *.
  destruct i' as [i'' Hi'] eqn:E.
  apply wf_make_seq_link_domain_inners.
  - apply eq_refl.
  Qed.


Lemma exists_port_implies_not_idle {s i r o} {b:bigraph s i r o} (p:Port (get_control (bg:=b))) (e: get_edge b) : 
  get_link (bg:=b) (inr p) = (inr e) -> 
    not_is_idle e.
  Proof.
  Admitted. (*TODO*)


Lemma not_is_idle_implies_exists_inner_or_node {s i r o} {b:bigraph s i r o} (e: get_edge b) : 
  not_is_idle e -> 
    exists ip, get_link (bg:=b) ip = (inr e).
  Proof.
  intros.
  simpl in *.
  unfold not_is_idle in H. 
  unfold List.existsb in H.
  simpl in *.
  apply existsb_exists in H. destruct H as [ip [H H']]. exists ip.
  destruct (get_link (bg:=b) ip).
  - discriminate H'.
  - f_equal. symmetry.
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
  unfold get_edges_wo_idles. 
  intros [i'|p'].
  - destruct (get_link (bg:=b) (inl i')) as [o'|e'] eqn:El. 
  + left. exact o'.
  + right. exists e'. (*le GOAL*) 
  eapply (exists_inner_implies_not_idle _). simpl. apply El.
  - destruct (get_link (bg:=b) (inr p')) as [o'|e'] eqn:El.
  + left. exact o'.
  + right. unfold get_edges_wo_idles. exists e'. (*le GOAL*) 
  apply (exists_port_implies_not_idle p'). apply El.
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
  unfold lean.
  intros nie. simpl in nie. simpl.
  destruct nie as [nie Hnie].
  set (ip':= not_is_idle_implies_exists_inner_or_node nie Hnie).
  destruct ip' as [ip Hip].
  exists ip.
  destruct ip as [inner | port]; simpl.
  - destruct inner. simpl.
    admit. 
  - Fail rewrite Hip. admit. 
  Abort.

Definition get_site {s i r o} (b:bigraph s i r o) : nat := s.
Definition get_root {s i r o} (b:bigraph s i r o) : nat := r.
Definition get_innername {s i r o} (b:bigraph s i r o) : NoDupList := i.
Definition get_outername {s i r o} (b:bigraph s i r o) : NoDupList := o.

Record half_support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) : Prop :=
  BigHalfEq
  {
    bij_s_h : s1 = s2 ;
    bij_i_h : permutation i1 i2 ; (*Permutation i1 i2*)
    bij_r_h : r1 = r2 ;
    bij_o_h : permutation o1 o2 ;
    bij_n_h : bijection (get_node b1) (get_node b2);
    bij_p_h : forall (n1 : (get_node b1)), bijection ('I_(Arity (get_control (bg:=b1) n1))) ('I_(Arity (get_control (bg:=b2) (bij_n_h n1)))) ;
    big_control_eq_h : (bij_n_h -->> (@bij_id Kappa)) (get_control (bg:=b1)) = get_control (bg:=b2) ;
    big_parent_eq_h : ((bij_n_h <+> (bij_rew bij_s_h)) -->> (bij_n_h <+> ((bij_rew bij_r_h)))) (get_parent (bg:=b1)) = get_parent (bg:=b2) ;
  }.


Theorem lean_bigraph_same_bigraph {s i r o} (b:bigraph s i r o) :
  half_support_equivalence b (lean b) /\ 
  forall (ip : NameSub i + Port (get_control (bg := b))),
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
    - destruct ip as [inner|port].
      + destruct get_link eqn:E; simpl.
        * Fail destruct get_link. admit.
        * Fail destruct get_link. admit.
      + destruct get_link eqn:E; simpl.
        * Fail destruct get_link. admit.
        * Fail destruct get_link. admit.
  Admitted.


Definition lean_support_equivalence {s1 r1 s2 r2 : nat} {i1 o1 i2 o2 : NoDupList} 
  (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) := 
  support_equivalence (lean b1) (lean b2).

Lemma id_left_neutral : forall A B, forall f:A -> B, id <o> f =f. 
  Proof. intros. simpl; reflexivity. Qed.

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
  refine (<{ bij_e | _ }>).
  intros e. simpl. 
  split; intros.
  * apply not_is_idle_implies_exists_inner_or_node in H.
  destruct H as [[[inner Hinner]|[n [port Hport]]] H].
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
  - eapply (exists_port_implies_not_idle (existT _ (bij_n n) (Ordinal (m:=port) _))).
  Unshelve.
  3:{ rewrite <-control_eq. simpl. 
  rewrite (id_left_neutral _ _ (get_control (bg:=b1))).
  unfold funcomp.
  set (tmpH := equal_f (bof_id _ _ bij_n) (n)).
  unfold funcomp in tmpH.  
  rewrite tmpH.
  apply Hport. }
  rewrite <- link_eq.
  simpl.
  unfold parallel,funcomp, bij_subset_backward. simpl.
  unfold eq_rect_r.
  erewrite (port_proof_irrelevant_full (b:=b1) (n':=n)
  (port':=Ordinal (n:=Arity (get_control (bg:=b1) n)) (m:=port) Hport)).
  destruct get_link.
  + discriminate H.
  + f_equal. f_equal.
  injection H. auto.
  -- set (tmpH := equal_f (bof_id _ _ bij_n) (n)).
  unfold funcomp in tmpH.  
  apply tmpH.
  -- admit.

  * apply not_is_idle_implies_exists_inner_or_node in H.
  destruct H as [[[inner Hinner]|[n [port Hport]]] H].
  - destruct (bij_i inner). 
  eapply (exists_inner_implies_not_idle (exist _ inner (H1 Hinner))).
  rewrite <- link_eq in H.
  simpl in H.
  unfold parallel,funcomp, bij_subset_backward in H. simpl in H.
  rewrite <- (innername_proof_irrelevant b1 (H1 Hinner)) in H.
  destruct get_link.
  + discriminate H.
  + f_equal. injection H. apply (bij_injective bij_e _ _).
  - eapply (exists_port_implies_not_idle (existT _ (bij_n⁻¹ n) (Ordinal (m:=port) _))).
  Unshelve.
  2:{ clear H.
  rewrite <-control_eq in Hport. simpl in Hport. 
  rewrite (id_left_neutral _ _ (get_control (bg:=b1))) in Hport.
  unfold funcomp in Hport. apply Hport. }
  rewrite <- link_eq in H.
  simpl in H.
  unfold parallel,funcomp, bij_subset_backward in H. simpl in H.
  unfold eq_rect_r in H.
  admit.
  Admitted.



End LeanSupportEquivalence. 
End EquivalenceBigraphs.