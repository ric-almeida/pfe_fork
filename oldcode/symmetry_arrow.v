Definition symmetry_arrow (I J:Type) : bijection (I + J) (J + I).
  Proof. 
  apply (bij_sum_comm). 
  Defined.

Lemma symmetry_S1 {I}: 
  forall i:I, symmetry_arrow I void (inl i) = inr i.
  Proof.
  intros i.
  auto.
  Qed.
  
Lemma symmetry_S2 {I J}: 
  forall ij, 
    ((symmetry_arrow J I) <o> (symmetry_arrow I J)) ij = ij.
  Proof.
  intros [i|j];
  unfold funcomp; auto.
  Qed.

Lemma symmetry_S3 {I0 J0 I1 J1}
  {f : bijection I0 I1}
  {g : bijection J0 J1}: 
  symmetry_arrow I1 J1 <o> (f <+> g) = 
    (g <+> f) <o> symmetry_arrow I0 J0.
  Proof.
  simpl. unfold funcomp.
  apply functional_extensionality.
  intros [xi0 | xj0]; unfold parallel; reflexivity.
  Qed. 
  
Lemma symmetry_S4 {I J K} :
  forall x,
  (symmetry_arrow (I+J) K) x =
    ((bij_sum_assoc) <O> 
    ((symmetry_arrow I K) <+> (@bij_id J)) <O> 
    ((bijection_inv bij_sum_assoc) <O> 
    ((@bij_id I) <+> (symmetry_arrow J K)) 
    <O> bij_sum_assoc)) x. 
  Proof.
  intros [[i | j] | k];
  simpl; unfold parallel, funcomp; reflexivity.
  Qed.

