Record bigraph'  (site: FinDecType) 
(innername: FinDecType) 
(root: FinDecType) 
(outername: FinDecType)
(node: FinDecType)
(edge: FinDecType)
(kind: FinDecType) : Type := 
Big'  
{ 
arity' : @type kind -> nat ;
control' : @type node -> @type kind ;
parent' : @type node + @type site -> @type node + @type root ; 
link' : @type innername + Port (@type node) control' arity' -> @type outername + @type edge; 
ap' : acyclic (@type node) (@type site) (@type root) parent' ;
}.

Record MyRecord : Type := {
    field1 : nat;
    field2 : bool;
    field3 : Type;
    field4 : field3 -> nat
  }.


  Definition is_field3_the_same {t1 : Type}
    (mr1 : MyRecord) (mr2 : MyRecord) :=
    field3 mr1 = t1 /\ field3 mr2 = t1.


  (* Definition field4_equiv 
    (mr1 : MyRecord) (mr2 : MyRecord) :=
    is_field3_the_same mr1 mr2 ->  
    forall x : field3 mr1, forall y : field3 mr2, 
      x = y -> field4 mr1 x = field4 mr2 y. *)


  Inductive MyRecord_equiv : MyRecord -> MyRecord -> Prop :=
    | MyRecord_equiv_intro :
      forall r1 r2,
      field1 r1 = field1 r2 ->
      MyRecord_equiv r1 r2.

  Lemma MyRecord_equiv_refl : forall r, MyRecord_equiv r r.
  Proof.
    intros r.
    constructor. reflexivity.
  Qed.

  Lemma MyRecord_equiv_sym : forall r1 r2,
    MyRecord_equiv r1 r2 -> MyRecord_equiv r2 r1.
  Proof.
    intros r1 r2 H.
    inversion H. constructor.
    symmetry. assumption.
  Qed.

  Lemma MyRecord_equiv_trans : forall r1 r2 r3,
    MyRecord_equiv r1 r2 -> MyRecord_equiv r2 r3 -> MyRecord_equiv r1 r3.
  Proof.
    intros r1 r2 r3 H1 H2.
    inversion H1. inversion H2.
    constructor.
    transitivity (field1 r2); assumption.
  Qed.

  Add Parametric Relation: (MyRecord) (MyRecord_equiv)
      reflexivity proved by (MyRecord_equiv_refl)
      symmetry proved by (MyRecord_equiv_sym)
      transitivity proved by (MyRecord_equiv_trans)
        as MyRecord_equiv_rel.

  Lemma same_filelds_same_record:
    forall (g g': MyRecord),
    field1 g = field1 g' ->
    field2 g = true
      -> field2 g' = true
      -> MyRecord_equiv g g'.
  Proof.
    induction g; induction g'.
    simpl.
    intros H H0 H2. split. simpl. apply H. 
  Qed.

  (* Instance MyRecord_Setoid : Setoid MyRecord :=
    {
      equiv := MyRecord_equiv;
      setoid_equiv := MyRecord_equiv;
      setoid_refl := MyRecord_equiv_refl;
      setoid_sym := MyRecord_equiv_sym;
      setoid_trans := MyRecord_equiv_trans;
    }. *)


    Definition eq_Type (A:Type) (B:Type) : A = B. Admitted.
    (*:=
      match eq_dec A B with
      | left eq_proof => eq_proof
      | right _ => eq_refl
      end. *)
  
    Definition equiv_inter_type {A B: Type} (a:A) (b:B) : Prop. 
    Proof. destruct (eq_Type A B). exact (a=b). Defined.
  
    Lemma equiv_inter_type_refl {A : Type} (a:A) : equiv_inter_type a a.
    Proof. unfold equiv_inter_type. 
    Admitted.
  
    Lemma equiv_inter_type_sym {A B : Type} (a:A) (b:B) : 
      equiv_inter_type a b -> equiv_inter_type b a.
    Admitted.
    -
    Lemma equiv_inter_type_trans {A B C : Type} (a:A) (b:B) (c:C): 
      equiv_inter_type a b -> equiv_inter_type b c -> equiv_inter_type a c.
    Admitted.
  
    (* Add Parametric Relation (A:Type) : (equiv_inter_type A A)
        reflexivity proved by (equiv_inter_type_refl)
        symmetry proved by (equiv_inter_type_sym)
        transitivity proved by (equiv_inter_type_trans)
          as equiv_inter_type_rel. *)



          Definition equiv_inter_type' {A B: Type} {H:A=B} (a:A) (b:B) : Prop.
          Proof. destruct H. exact (a=b). Defined.


  Definition parent_node_equiv 
  {s i r o : FinDecType} 
  (b1 : bigraph s i r o) (b2 : bigraph s i r o) := 
  forall n1:get_node b1, forall n2:get_node b2,
  equiv_inter_type n1 n2 -> 
    equiv_inter_type (get_parent b1 (inl n1)) (get_parent b2 (inl n2)).

Definition parent_site_equiv 
  {s i r o : FinDecType} 
  (b1 : bigraph s i r o) (b2 : bigraph s i r o) := 
  forall site:(@type s), 
    equiv_inter_type (get_parent b1 (inr site)) (get_parent b2 (inr site)).


Definition parent_equiv {s i r o : FinDecType} 
  (b1 : bigraph s i r o) (b2 : bigraph s i r o) := 
  parent_node_equiv b1 b2 /\ parent_site_equiv b1 b2.

Definition parent_equiv' {s i r o n e k: FinDecType} 
  (b1 : bigraph' s i r o n e k) (b2 : bigraph' s i r o n e k) := 
  forall k_:(@type k), arity' s i r o n e k b1 k_ = arity' s i r o n e k b2 k_



  Inductive bigraph_type_equality {s i r o : FinDecType} : bigraph s i r o -> bigraph s i r o -> Prop :=
  | bigraph_type_equality_intro : forall b1 b2,
    get_node b1 = get_node b2 ->
    get_edge b1 = get_edge b2 ->
    get_kind b1 = get_kind b2 ->
    bigraph_type_equality b1 b2.

Lemma bigraph_type_equality_refl {s i r o : FinDecType} : 
  forall (b : bigraph s i r o), bigraph_type_equality b b.
  Proof.
    intros b.
    constructor; reflexivity.
  Qed.

Lemma bigraph_type_equality_sym {s i r o : FinDecType} : 
forall (b1 b2 : bigraph s i r o),
bigraph_type_equality b1 b2 -> bigraph_type_equality b2 b1.
  Proof.
    intros b1 b2 H.
    inversion H. constructor ;
    symmetry; assumption.
  Qed.

Lemma bigraph_type_equality_trans {s i r o : FinDecType} : 
forall (b1 b2 b3 : bigraph s i r o),
bigraph_type_equality b1 b2 -> bigraph_type_equality b2 b3 -> bigraph_type_equality b1 b3.
Proof.
  intros b1 b2 b3 H1 H2.
  inversion H1. inversion H2.
  constructor.
  - rewrite H. rewrite H6. reflexivity.
  - rewrite H0. rewrite H7. reflexivity.
  - rewrite H3. rewrite H8. reflexivity.
Qed.


Definition cast {A B: Type} (H : A = B ): A -> B. 
Proof. intros. rewrite <- H. apply X. Defined.

Definition rcast {A B: Type} (H : A = B ): B -> A. 
Proof. intros. rewrite -> H. apply X. Defined.

Lemma equal_is_bij {A B: Type} : 
A = B -> bijection A B.
Proof. intros H. rewrite <- H. apply bijection_id. Qed. 

Definition bigraph_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o)
(bij_n : bijection (get_node b1) (get_node b2))
(bij_e : bijection (get_edge b1) (get_edge b2))
(bij_k : bijection (get_kind b1) (get_kind b2))
(bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) : Prop :=
  bigraph_arity_equality b1 b2 bij_k /\ 
  bigraph_control_equality b1 b2 bij_n bij_k/\ 
  bigraph_parent_equality b1 b2 bij_n /\ 
  bigraph_link_equality b1 b2 bij_e bij_p.

  Lemma bigraph_equality_refl {s i r o : FinDecType} 
    (b : bigraph s i r o) :
    let bij_n := bijection_id  in
    let bij_e := bijection_id  in
    let bij_k := bijection_id  in
    let bij_p := bijection_id  in
    bigraph_equality b b bij_n bij_e bij_k bij_p.
    Proof.
      intros.
      constructor.   
      + apply arity_refl. 
      + split.
      ++ apply control_refl.
      ++ split. 
      +++ apply parent_refl.
      +++ apply link_refl.
      Qed.


      Lemma correct_node_type {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
      (b1 : bigraph s1 i1 r1 o1) (b2 : bigraph s2 i2 r2 o2) :
      get_node (b1 || b2) = ((get_node b1) + (get_node b2))%type.
      Proof. auto. Qed.