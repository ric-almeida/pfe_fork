Lemma if_then_else_rewrite:
  forall (b: bool) (T1 T2 E1 E2 : Prop),
    (T1 -> T2) ->
    (E1 -> E2) ->
    (if b then T1 else E1) ->
    (if b then T2 else E2).
Proof.
  destruct b; auto.
Qed.

Ltac ite_app1 Th :=
  match goal with
  | H:_ |- if ?b then ?T2 else ?E =>
    eapply if_then_else_rewrite with (E1 := E) (E2 := E);
    [eapply Th | eauto |]
   end.


Ltac ite_app2 Th :=
  match goal with
  | H:_ |- if ?b then ?T else ?E2 =>
    eapply if_then_else_rewrite with (T1 := T) (T2 := T);
    [eauto | eapply Th |]
   end.