Require Import List. 
Import ListNotations. 

Fixpoint is_in (a: nat) (l : list nat) : Prop := 
  match l with 
  | [] => False
  | t::q => a = t \/ is_in a q
  end. 

Eval compute in (is_in 3 []).
Eval compute in (is_in 3 [1;2;3]).

Theorem is_in_ok (a: nat)(l: list nat) : 
  is_in a l -> exists l1 l2, l = l1++(a::l2). 
Proof. 
  intros. 
  induction l. 
  - inversion H. 
  - simpl in H. destruct H. 
    + rewrite H. exists []. exists l. auto.
    + destruct (IHl H) as [l1 [l2 H1]].
      exists (a0:: l1) ; exists l2. 
      simpl. rewrite H1. auto. 
Qed. 