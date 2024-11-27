Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import List.
Open Scope list_scope.
Import ListNotations.

Ltac disjunction H := destruct H as [ H | H ].

Definition cons_type {T} h t (e : { e : T | In e t }) : { e : T | In e (h :: t)} :=
  let (e, H__e) := e in exist _ e (in_cons h e t H__e).

Fixpoint onto {T : Type} (l : list T) : list { e : T | In e l } :=
  match l with
  | [] => []
  | h :: t => (exist _ h (in_eq h t)) :: (map (cons_type h t) (onto t))
  end.

Lemma onto_nil {T : Type} : @onto T nil = nil. Proof. reflexivity. Qed.

Lemma onto_cons {T : Type} (e : T) (l : list T) :
  onto (e :: l) = exist _ e (in_eq e l) :: map (cons_type _ _) (onto l).
Proof. reflexivity. Qed.

Lemma onto_correct {T : Type} (l : list T) (e : { x : T | In x l}) : In e (onto l).
Proof.
  destruct e as [e IN]. induction l as [| h t IH]; try contradiction. disjunction IN.
  - left. auto using subset_eq_compat.
  - right. apply in_map_iff. exists (exist (fun e : T => In e t) e IN).
    split; auto. apply subset_eq_compat; reflexivity.
Qed.

Lemma onto_complete {T : Type} (l : list T) (e : { x : T | In x l }) :
  In e (onto l) -> In (@proj1_sig T _ e) l.
Proof. destruct e as [e H]. auto. Qed.

Lemma onto_size {T : Type} (l : list T) : length l = length (onto l).
Proof. induction l; auto. simpl. rewrite map_length. auto. Qed.

Lemma onto_proj {T : Type} (l : list T) : map (@proj1_sig T _) (onto l) = l.
Proof.
  induction l as [| h t IH]; try reflexivity.
  unfold onto; fold (@onto T). rewrite map_cons. f_equal.
  rewrite map_map. rewrite <- IH at 2. f_equal.
  apply functional_extensionality. intros [x H__x]; reflexivity.
Qed.

Theorem onto_Onto : forall [A : Type] (lA : list A) (a : { a : A | In a lA }), In a (onto lA).
Proof.
  intros.
  apply onto_correct.
Qed.   