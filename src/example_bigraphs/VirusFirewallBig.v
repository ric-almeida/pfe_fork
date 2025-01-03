(* This is an implementation of the initial bigraph (top_3_3) from the example BRS of a virus-and-firewall model from https://bitbucket.org/uog-bigraph/bigraph-tools/src/master/bigrapher/examples/virus-multifirewall.big *)

Set Warnings "-notation-overridden, -parsing".

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssreflect.fintype.

Require Import SignatureBig.
Require Import Names.
Require Import AbstractBigraphs.

Import ListNotations.


(* The bigraph controls/node types *)
Inductive kappa : Type := 
  Safe | Attacked | Infected | N | BasicFW | AdvFW.

Lemma kappa_dec : forall k1 k2 : kappa, {k1 = k2} + {k1 <> k2}.  
  Proof.  
    intros k1 k2. destruct k1 eqn:K1. 
    all: destruct k2 eqn:K2; try auto; right; intro H; discriminate. 
  Qed.

Module SP <: SignatureParameter.
  Definition Kappa := kappa.
  Definition EqDecK := kappa_dec.
  Definition Arity := 
    fun (k:Kappa) =>
      match k with 
      | N => 1 
      | _ => 0
      end. 
End SP.

Module NP <: NamesParameter.
  Definition Name := string. 
  Definition EqDecN := string_dec.
  Definition InfName : forall l:list Name, exists n:Name, ~ In n l.
    Proof. Admitted.
  Definition DefaultName := "l_0_0"%string.
  Definition freshName (l: list Name) := ""%string.
  Definition notInfreshName : forall l:list Name, ~ In (freshName l) l. 
    Proof. Admitted.
End NP.

Module bigs := Bigraphs SP NP.
Module names := Names NP.
Include bigs.

Definition numb_sites : nat := 0.
Definition inames_ls : list Name := [].
Program Definition inames : NoDupList := mkNoDupList inames_ls _.
  Next Obligation. 
    constructor.
  Qed.

Definition numb_roots : nat := 1.
Definition onames_ls : list Name := 
  ["l_6_7"%string; "l_3_6"%string; "l_7_8"%string; "l_4_7"%string; "l_0_3"%string; "l_3_4"%string; "l_5_8"%string; "l_4_5"%string; "l_1_4"%string; "l_0_1"%string; "l_1_2"%string; "l_2_5"%string].
Program Definition onames : NoDupList := mkNoDupList onames_ls _.
  Next Obligation.
    repeat (constructor;
    [ intro H; unfold In in H;
      repeat (destruct H as [H | H]; [ discriminate |]); assumption |]).
    constructor.
  Defined.

(* Nodes for the entities (Safe, Infected, BasicFW, AdvFW and N)
   #  7         8            9          (Top)
   ## 70 71 72  80 81 82 83  90 91
   #  4            5               6    (Mid)
   ## 40 41 42 43  50 51 52 53 54  60 61 62 63
   #  1         2            3          (Bottom)
   ## 10 11 12  20 21 22 23  30 31 32 *)
Definition nodes_seq : seq nat := 
  [:: 7; 8; 9;
      70; 71; 72; 80; 81; 82; 83; 90; 91;
      4; 5; 6;
      40; 41; 42; 43; 50; 51; 52; 53; 54; 60; 61; 62; 63;
      1; 2; 3;
      10; 11; 12; 20; 21; 22; 23; 30; 31; 32
      ].
Definition nodes := seq_sub nodes_seq.

(* No edge labels, since all links are open *)
Definition edges_seq : seq nat := [].
Definition edges := seq_sub edges_seq.

Definition my_control (n:nodes) : Kappa :=
  match n with 
  @SeqSub _ _ m _ => 
    if ((m =? 7)%nat || (m =? 8)%nat || (m =? 9)%nat || (m =? 4)%nat || (m =? 5)%nat || (m =? 6)%nat || (m =? 2)%nat || (m =? 3)%nat) then 
      Safe
    else if ((m =? 1)%nat) then 
      Infected
    else if ((m =? 70)%nat || (m =? 80)%nat || (m =? 90)%nat || (m =? 10)%nat || (m =? 20)%nat || (m =? 30)%nat) then 
      BasicFW
    else if ((m =? 40)%nat || (m =? 50)%nat || (m =? 60)%nat) then 
      AdvFW
    else 
      N
  end.

Program Definition my_parent (x : nodes + 'I_numb_sites) : nodes + 'I_numb_roots :=
  match x with  
  | inl (@SeqSub _ _ 70 _) => inl (@SeqSub _ nodes_seq 7 erefl)
  | inl (@SeqSub _ _ 71 _) => inl (@SeqSub _ nodes_seq 7 erefl)
  | inl (@SeqSub _ _ 72 _) => inl (@SeqSub _ nodes_seq 7 erefl)
  | inl (@SeqSub _ _ 80 _) => inl (@SeqSub _ nodes_seq 8 erefl)
  | inl (@SeqSub _ _ 81 _) => inl (@SeqSub _ nodes_seq 8 erefl)
  | inl (@SeqSub _ _ 82 _) => inl (@SeqSub _ nodes_seq 8 erefl)
  | inl (@SeqSub _ _ 83 _) => inl (@SeqSub _ nodes_seq 8 erefl)
  | inl (@SeqSub _ _ 90 _) => inl (@SeqSub _ nodes_seq 9 erefl)
  | inl (@SeqSub _ _ 91 _) => inl (@SeqSub _ nodes_seq 9 erefl)
  | inl (@SeqSub _ _ 40 _) => inl (@SeqSub _ nodes_seq 4 erefl)
  | inl (@SeqSub _ _ 41 _) => inl (@SeqSub _ nodes_seq 4 erefl)
  | inl (@SeqSub _ _ 42 _) => inl (@SeqSub _ nodes_seq 4 erefl)
  | inl (@SeqSub _ _ 43 _) => inl (@SeqSub _ nodes_seq 4 erefl)
  | inl (@SeqSub _ _ 50 _) => inl (@SeqSub _ nodes_seq 5 erefl)
  | inl (@SeqSub _ _ 51 _) => inl (@SeqSub _ nodes_seq 5 erefl)
  | inl (@SeqSub _ _ 52 _) => inl (@SeqSub _ nodes_seq 5 erefl)
  | inl (@SeqSub _ _ 53 _) => inl (@SeqSub _ nodes_seq 5 erefl)
  | inl (@SeqSub _ _ 54 _) => inl (@SeqSub _ nodes_seq 5 erefl)
  | inl (@SeqSub _ _ 60 _) => inl (@SeqSub _ nodes_seq 6 erefl)
  | inl (@SeqSub _ _ 61 _) => inl (@SeqSub _ nodes_seq 6 erefl)
  | inl (@SeqSub _ _ 62 _) => inl (@SeqSub _ nodes_seq 6 erefl)
  | inl (@SeqSub _ _ 63 _) => inl (@SeqSub _ nodes_seq 6 erefl)
  | inl (@SeqSub _ _ 10 _) => inl (@SeqSub _ nodes_seq 1 erefl)
  | inl (@SeqSub _ _ 11 _) => inl (@SeqSub _ nodes_seq 1 erefl)
  | inl (@SeqSub _ _ 12 _) => inl (@SeqSub _ nodes_seq 1 erefl)
  | inl (@SeqSub _ _ 20 _) => inl (@SeqSub _ nodes_seq 2 erefl)
  | inl (@SeqSub _ _ 21 _) => inl (@SeqSub _ nodes_seq 2 erefl)
  | inl (@SeqSub _ _ 22 _) => inl (@SeqSub _ nodes_seq 2 erefl)
  | inl (@SeqSub _ _ 23 _) => inl (@SeqSub _ nodes_seq 2 erefl)
  | inl (@SeqSub _ _ 30 _) => inl (@SeqSub _ nodes_seq 3 erefl)
  | inl (@SeqSub _ _ 31 _) => inl (@SeqSub _ nodes_seq 3 erefl)
  | inl (@SeqSub _ _ 32 _) => inl (@SeqSub _ nodes_seq 3 erefl)
  | _ => inr (@Ordinal numb_roots 0 _)
  end.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.
    Next Obligation.
    repeat (split; [ intros; intro H; inversion H |]).  
    intros; intro H; inversion H. Qed.

Program Definition my_link (x : NameSub inames + Port my_control) : NameSub onames + edges := 
  match x with 
  | inr (existT n y) =>
      match (n,y) with 
      | (@SeqSub _ _ 71 _, _) => inl (exist _ "l_3_6"%string _)
      | (@SeqSub _ _ 72 _, _) => inl (exist _ "l_6_7"%string _)
      | (@SeqSub _ _ 81 _, _) => inl (exist _ "l_4_7"%string _)
      | (@SeqSub _ _ 82 _, _) => inl (exist _ "l_6_7"%string _)
      | (@SeqSub _ _ 83 _, _) => inl (exist _ "l_7_8"%string _)
      | (@SeqSub _ _ 91 _, _) => inl (exist _ "l_5_8"%string _)
      | (@SeqSub _ _ 92 _, _) => inl (exist _ "l_7_8"%string _)
      | (@SeqSub _ _ 41 _, _) => inl (exist _ "l_0_3"%string _)
      | (@SeqSub _ _ 42 _, _) => inl (exist _ "l_3_4"%string _)
      | (@SeqSub _ _ 43 _, _) => inl (exist _ "l_3_6"%string _)
      | (@SeqSub _ _ 51 _, _) => inl (exist _ "l_3_4"%string _)
      | (@SeqSub _ _ 52 _, _) => inl (exist _ "l_4_5"%string _)
      | (@SeqSub _ _ 53 _, _) => inl (exist _ "l_1_4"%string _)
      | (@SeqSub _ _ 54 _, _) => inl (exist _ "l_4_7"%string _)
      | (@SeqSub _ _ 61 _, _) => inl (exist _ "l_4_5"%string _)
      | (@SeqSub _ _ 62 _, _) => inl (exist _ "l_2_5"%string _)
      | (@SeqSub _ _ 63 _, _) => inl (exist _ "l_5_8"%string _)
      | (@SeqSub _ _ 11 _, _) => inl (exist _ "l_0_1"%string _)
      | (@SeqSub _ _ 12 _, _) => inl (exist _ "l_0_3"%string _)
      | (@SeqSub _ _ 21 _, _) => inl (exist _ "l_0_1"%string _)
      | (@SeqSub _ _ 22 _, _) => inl (exist _ "l_1_2"%string _)
      | (@SeqSub _ _ 23 _, _) => inl (exist _ "l_1_4"%string _)
      | (@SeqSub _ _ 31 _, _) => inl (exist _ "l_1_2"%string _)
      | (@SeqSub _ _ 32 _, _) => inl (exist _ "l_2_5"%string _)      
      | _ => inl (exist _ "l_2_5"%string _)  (* no matches *)
      end    
  | inl _ => inl (exist _ "l_2_5"%string _)  (* no matches, since there are no innernames *)
  end.
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed. 
    Next Obligation. repeat (try (left; reflexivity); try reflexivity; right). Qed.     
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed.
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed.
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed.
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed.
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. 
      repeat (split; [ intros; auto; intro H; inversion H |]).
      intros; auto; intro H; inversion H. Qed. 
    Next Obligation. repeat (try (left; reflexivity); right). Qed.

Definition my_ap : MyBasics.FiniteParent my_parent.
  Proof.
  unfold MyBasics.FiniteParent.
  intro n.
  assert (Hroots: forall r, (r=S O \/ r=S (S O) \/ r=3 \/ r=4 \/ r=5 \/ r=6 \/ r=7 \/ r=8 \/ r=9) -> forall (ssvalP : r \in nodes_seq), Acc (fun n' n0 : nodes => my_parent (inl n0) = inl n') (@SeqSub _ nodes_seq r ssvalP)). 
  { intros r Hr.     
    repeat (try (destruct Hr as [ Hr | Hr]); 
      try (subst; intro H; apply Acc_intro; intros u P; simpl in P; discriminate)). }
  
  destruct n eqn:N. subst.
  unfold nodes_seq in ssvalP.
  assert (ssval \in [1; 2; 3; 4; 5; 6; 7; 8; 9] \/ ssval \in [10; 11; 12; 20; 21; 22; 23; 30; 31; 32; 40; 41; 42; 43; 50; 51; 52; 53; 54; 60; 61; 62; 63; 70; 71; 72; 80; 81; 82; 83; 90; 91]). 
  { unfold in_mem,mem in ssvalP.
    simpl in ssvalP. unfold orb in ssvalP.
    repeat (
      let P:=fresh "H" in 
      destruct (_ == _) eqn:P; 
      [ apply Nat.eqb_eq in P; subst; auto | clear P]). 
    discriminate. }

  destruct H as [H | H].
  { apply Hroots. unfold in_mem,mem in H. simpl in H.
    unfold orb in H. 
    repeat (
      let P:=fresh "H" in 
        destruct (_ == _) eqn:P; 
        [ apply Nat.eqb_eq in P; subst; tauto | clear P]).
    discriminate. }
     
  apply Acc_intro.
  intros u P. 
  unfold in_mem,mem in H. simpl in H.
  unfold orb in H.
  repeat (
    let H:=fresh "H" in 
      destruct (_ == _) eqn:H; 
      [ apply Nat.eqb_eq in H; subst; simpl in P; inversion P; apply Hroots; tauto | clear H]). 
  discriminate. 
Qed.

Definition big_top_3_3 : bigraph numb_sites inames numb_roots onames := 
  Big my_link my_ap.

