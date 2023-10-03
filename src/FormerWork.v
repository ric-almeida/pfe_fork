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

(* EQUIVALENCE *)
Definition bigraph_arity_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_k : bijection (get_kind b1) (get_kind b2)): Prop :=
  forall k1:get_kind b1, let k2 := bij_k.(forward (get_kind b1) (get_kind b2)) k1 in 
  get_arity b1 k1 = get_arity b2 k2.

Definition bigraph_control_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2))
(bij_k : bijection (get_kind b1) (get_kind b2)) : Prop :=
  forall n1:get_node b1, 
  let kind1 := get_control b1 n1 in
  let n2 := bij_n.(forward (get_node b1) (get_node b2)) n1 in 
  let kind2 := get_control b2 n2 in
  bij_k.(forward (get_kind b1) (get_kind b2)) kind1 = kind2.

Definition bigraph_parent_site_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2)) : Prop :=
  forall site:s, 
  match (get_parent b1 (inr site)),(get_parent b2 (inr site)) with
  | inr root1, inr root2  => root1 = root2
  | inl node1, inl node2  => bij_n.(forward (get_node b1) (get_node b2)) node1 = node2
  | _, _ => False
  end.

Definition bigraph_parent_node_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2)): Prop :=
  forall n1:get_node b1, 
  let n2 := bij_n.(forward (get_node b1) (get_node b2)) n1 in 
  match (get_parent b1 (inl n1)),(get_parent b2 (inl n2)) with
  | inr root1, inr root2  => root1 = root2
  | inl node1, inl node2  => bij_n.(forward (get_node b1) (get_node b2)) node1 = node2
  | _, _ => False
  end.

Definition bigraph_parent_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2)): Prop :=
bigraph_parent_node_equality b1 b2 bij_n /\ bigraph_parent_site_equality b1 b2 bij_n.

Definition bigraph_link_innername_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_e : bijection (get_edge b1) (get_edge b2)) : Prop :=
  forall inner:i, 
  match (get_link b1 (inl inner)),(get_link b2 (inl inner)) with
  | inr edge1, inr edge2  => bij_e.(forward (get_edge b1) (get_edge b2)) edge1 = edge2
  | inl outer1, inl outer2  => outer1 = outer2
  | _, _ => False
  end.

Definition bigraph_link_port_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) 
(bij_e : bijection (get_edge b1) (get_edge b2)): Prop :=
  forall p1:(Port (get_node b1) (get_control b1) (get_arity b1)), 
  let p2 := bij_p.(forward (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) p1 in
  match (get_link b1 (inr p1)),(get_link b2 (inr p2)) with
  | inr edge1, inr edge2  => bij_e.(forward (get_edge b1) (get_edge b2)) edge1 = edge2
  | inl outer1, inl outer2  => outer1 = outer2
  | _, _ => False
  end.

Definition bigraph_link_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_e : bijection (get_edge b1) (get_edge b2))
(bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) : Prop :=
bigraph_link_innername_equality b1 b2 bij_e /\ bigraph_link_port_equality b1 b2 bij_p bij_e.

Record bigraph_equality {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) : Prop :=
  BigEq 
  {
    bij_n : bijection (get_node b1) (get_node b2);
    bij_e : bijection (get_edge b1) (get_edge b2);
    bij_k : bijection (get_kind b1) (get_kind b2);
    bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)); 
    big_arity_eq : bigraph_arity_equality b1 b2 bij_k ; 
    big_control_eq : bigraph_control_equality b1 b2 bij_n bij_k ; 
    big_parent_eq : bigraph_parent_equality b1 b2 bij_n ;
    big_link_eq : bigraph_link_equality b1 b2 bij_e bij_p
  }.

(* EQUIVALENCE IS RELATION*)
Lemma arity_refl {s i r o : FinDecType} (b : bigraph s i r o) :
let bij_k := bijection_id  in
bigraph_arity_equality b b bij_k.
Proof. unfold bigraph_arity_equality. (* auto. *) 
intros. unfold bijection_id. simpl. unfold id. reflexivity. Qed.

Lemma control_refl {s i r o : FinDecType} (b : bigraph s i r o) :
let bij_n := bijection_id  in
let bij_k := bijection_id  in
bigraph_control_equality b b bij_n bij_k.
Proof. unfold bigraph_control_equality. (* auto. *) 
intros. unfold bijection_id. simpl. unfold id. reflexivity. Qed.

Lemma parent_refl {s i r o : FinDecType} (b : bigraph s i r o) :
let bij_n := bijection_id  in
bigraph_parent_equality b b bij_n.
Proof. unfold bigraph_parent_equality. split. 
  + unfold bigraph_parent_node_equality. intros. 
  unfold bijection_id. simpl. unfold id. 
  set (pn1 := get_parent b (inl n1)). 
  destruct pn1 as [pn1 | pr1]; reflexivity.
  + unfold bigraph_parent_site_equality. intros.
  unfold bijection_id. simpl. unfold id. 
  set (ps1 := get_parent b (inr site)). 
  destruct ps1 as [pn1 | pr1]; reflexivity. Qed.

Lemma link_refl {s i r o : FinDecType} (b : bigraph s i r o) :
let bij_e := bijection_id  in
let bij_p := bijection_id  in
bigraph_link_equality b b bij_e bij_p.
Proof. unfold bigraph_link_equality. split.
  + unfold bigraph_link_innername_equality. intros.
  unfold bijection_id. simpl. unfold id. 
  set (li1 := get_link b (inl inner)). 
  destruct li1 as [lo1 | le1]; reflexivity.
  + unfold bigraph_link_port_equality. intros.
  unfold bijection_id. simpl. unfold id. 
  set (lp1 := get_link b (inr p1)). 
  destruct lp1 as [lo1 | le1]; reflexivity. Qed.

Lemma bigraph_equality_refl {s i r o : FinDecType} 
(b : bigraph s i r o) :
bigraph_equality b b.
Proof.
apply (BigEq s i r o b b (bijection_id) (bijection_id) (bijection_id) (bijection_id)).   
+ apply arity_refl. 
+ apply control_refl.
+ apply parent_refl.
+ apply link_refl.
Qed.

Lemma arity_sym {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_k : bijection (get_kind b1) (get_kind b2)) :
bigraph_arity_equality b1 b2 (bij_k) -> bigraph_arity_equality b2 b1 (bijection_inv bij_k).
Proof. 
  unfold bigraph_arity_equality. 
  intros H k2. simpl.
  set (k1 := bij_k.(backward (get_kind b1) (get_kind b2)) k2).
  specialize (H k1). 
  rewrite H. 
  unfold k1.
  rewrite <- (@fob_a_eq_a (get_kind b1) (get_kind b2) bij_k).
  reflexivity.
  Qed.

Lemma control_sym {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2))
(bij_k : bijection (get_kind b1) (get_kind b2)) :
bigraph_control_equality b1 b2 (bij_n) (bij_k) -> bigraph_control_equality b2 b1 (bijection_inv bij_n) (bijection_inv bij_k).
Proof.
intros H.
unfold bigraph_control_equality in *. intros n2. simpl.
rewrite (bij_preserve_equality (bij_k)).
rewrite H.
rewrite <- (@fob_a_eq_a (get_kind b1) (get_kind b2) bij_k).
rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
reflexivity. Qed.

Lemma parent_sym {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_n : bijection (get_node b1) (get_node b2)) :
bigraph_parent_equality b1 b2 (bij_n) -> 
bigraph_parent_equality b2 b1 (bijection_inv bij_n).
Proof.
intros [Hn Hs].
unfold bigraph_parent_equality in *.
split.
- unfold bigraph_parent_node_equality in *. simpl.
  intros n2. 
  set (p2n2 := get_parent b2 (inl n2)).
  destruct p2n2 as [pn2 | pr2] eqn:E;
  unfold p2n2 in E;
  set (n1 := backward (get_node b1) (get_node b2) bij_n n2);
  specialize (Hn n1);
  destruct (get_parent b1 (inl n1)) as [pn2' | pr2'] eqn:E';
  unfold n1 in Hn;
  rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n) in Hn;
  rewrite E in Hn.
  + rewrite (bij_preserve_equality (bij_n)). 
    rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
    symmetry.
    apply Hn.
  + apply Hn.
  + apply Hn.
  +  rewrite Hn. reflexivity.
- unfold bigraph_parent_site_equality in *. simpl.
intros site. specialize (Hs site). 
set (p2s := get_parent b2 (inr site)).
destruct p2s as [p2n | p2r] eqn:E;
unfold p2s in E;
destruct (get_parent b1 (inr site)) as [psn | psr] eqn:E';
rewrite E in Hs.
  + rewrite (bij_preserve_equality (bij_n)). 
    rewrite <- (@fob_a_eq_a (get_node b1) (get_node b2) bij_n).
    symmetry. apply Hs.
  +  apply Hs.
  +  apply Hs.
  +  symmetry. apply Hs.
Qed.

        


Lemma link_sym {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) 
(bij_e : bijection (get_edge b1) (get_edge b2))
(bij_p : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) :
bigraph_link_equality b1 b2 (bij_e) (bij_p) -> bigraph_link_equality b2 b1 (bijection_inv bij_e) (bijection_inv bij_p).
Proof.
intros [Hi Hp].
unfold bigraph_link_equality in *.
split.
- unfold bigraph_link_innername_equality in *. simpl.
  intros inner. specialize (Hi inner). 
  set (l2i := get_link b2 (inl inner)).
  destruct l2i as [l2i_o | l2i_p] eqn:E;
  unfold l2i in E;
  destruct (get_link b1 (inl inner)) as [l1i_o | l1i_e] eqn:E';
  rewrite E in Hi.
  + symmetry. apply Hi.
  + apply Hi.
  + apply Hi.
  + rewrite (bij_preserve_equality (bij_e)). 
    rewrite <- (@fob_a_eq_a (get_edge b1) (get_edge b2) bij_e).
    symmetry. apply Hi.
- unfold bigraph_link_port_equality in *. simpl.
  intros port. 
  set (l2p := get_link b2 (inr port)).
  destruct l2p as [l2p_o | l2p_i] eqn:E;
  unfold l2p in E;
  set (p1 := backward (Port (get_node b1) (get_control b1) (get_arity b1))
  (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p port);
  specialize (Hp p1);
  destruct (get_link b1 (inr p1)) as [l1p_o | l1p_e] eqn:E';
  unfold p1 in Hp;
  rewrite <- (@fob_a_eq_a (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p) in Hp;
  rewrite E in Hp.
  + symmetry. apply Hp.
  + apply Hp.
  + apply Hp.
  + rewrite (bij_preserve_equality (bij_e)). 
    rewrite <- (@fob_a_eq_a (get_edge b1) (get_edge b2) bij_e).
    symmetry. apply Hp.
Qed.

Lemma bigraph_equality_sym {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) :
bigraph_equality b1 b2
    -> bigraph_equality b2 b1.
Proof.
  intros H. inversion H.
  apply (BigEq s i r o b2 b1 (bijection_inv bij_n) (bijection_inv bij_e) (bijection_inv bij_k) (bijection_inv bij_p)).
  + apply arity_sym. apply big_arity_eq.
  + apply control_sym. apply big_control_eq.
  + apply parent_sym. apply big_parent_eq.
  + apply link_sym. apply big_link_eq.
  Qed.

Lemma arity_trans {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
(bij_k12 : bijection (get_kind b1) (get_kind b2)) 
(bij_k23 : bijection (get_kind b2) (get_kind b3)):
bigraph_arity_equality b1 b2 (bij_k12) -> 
  bigraph_arity_equality b2 b3 (bij_k23) ->
    bigraph_arity_equality b1 b3 (bij_k23 <O> bij_k12).
Proof. unfold bigraph_arity_equality. intros H1 H2 k1.
simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

Lemma control_trans {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
(bij_n12 : bijection (get_node b1) (get_node b2)) 
(bij_n23 : bijection (get_node b2) (get_node b3)) 
(bij_k12 : bijection (get_kind b1) (get_kind b2)) 
(bij_k23 : bijection (get_kind b2) (get_kind b3)):
bigraph_control_equality b1 b2 (bij_n12) (bij_k12) -> 
  bigraph_control_equality b2 b3 (bij_n23) (bij_k23) ->
    bigraph_control_equality b1 b3 (bij_n23 <O> bij_n12) (bij_k23 <O> bij_k12).
Proof. unfold bigraph_control_equality. intros H1 H2 n1.
simpl. unfold funcomp. rewrite <- H2. rewrite <- H1. reflexivity. Qed. 

Lemma parent_trans {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
(bij_n12 : bijection (get_node b1) (get_node b2)) 
(bij_n23 : bijection (get_node b2) (get_node b3)) :
bigraph_parent_equality b1 b2 (bij_n12) -> 
  bigraph_parent_equality b2 b3 (bij_n23) ->
    bigraph_parent_equality b1 b3 (bij_n23 <O> bij_n12).
Proof. 
  unfold bigraph_parent_equality.   intros [H12n H12s] [H23n H23s].
  split.
  - unfold bigraph_parent_node_equality in *. intros n1. simpl.  
    specialize (H12n n1).
    unfold funcomp. 
    set (p1n1 := get_parent b1 (inl n1)).
    destruct p1n1 as [p1n1_n | p1n1_r] eqn:E;
    unfold p1n1 in E;
    rewrite E in H12n;
    set (n2 := forward (get_node b1) (get_node b2) bij_n12 n1);  
    fold n2 in H12n;
    specialize (H23n n2);
    set (p2n2 := get_parent b2 (inl n2));
    fold p2n2 in H12n;
    destruct p2n2 as [p2n2_n | p2n2_r] eqn:E' in H12n;
    unfold p2n2 in E';
    rewrite E' in H23n;
    destruct (get_parent b3 (inl (forward (get_node b2) (get_node b3) bij_n23 n2))) as [p3n3_n | p3n3_r]. 
    + rewrite H12n. rewrite H23n. reflexivity.
    + apply H23n.
    + exfalso. apply H23n. 
    + apply H12n.
    + apply H12n.
    + exfalso. apply H23n.
    + apply H23n.  
    + rewrite H12n. rewrite H23n. reflexivity.
  - unfold bigraph_parent_site_equality in *. intros site. simpl.  
    specialize (H12s site).
    specialize (H23s site).
    unfold funcomp. 
    set (p1s := get_parent b1 (inr site)).
    destruct p1s as [p1s_n | p1s_r] eqn:E;
    unfold p1s in E; rewrite E in H12s; 
    set (p2s := get_parent b2 (inr site));
    fold p2s in H12s;
    destruct p2s as [p2s_n | p2s_r] eqn:E' in H12s;
    unfold p2s in E'; 
    rewrite E' in H23s;
    destruct (get_parent b3 (inr site)) as [p3s_n | p3s_r].
    + rewrite H12s. rewrite H23s. reflexivity.
    + apply H23s.
    + exfalso. apply H23s. 
    + apply H12s.
    + apply H12s.
    + exfalso. apply H23s.
    + apply H23s.  
    + rewrite H12s. rewrite H23s. reflexivity.
  Qed.

Lemma link_trans {s i r o : FinDecType}  
(b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o) 
(bij_e12 : bijection (get_edge b1) (get_edge b2)) 
(bij_e23 : bijection (get_edge b2) (get_edge b3)) 
(bij_p12 : bijection (Port (get_node b1) (get_control b1) (get_arity b1)) (Port (get_node b2) (get_control b2) (get_arity b2))) 
(bij_p23 : bijection (Port (get_node b2) (get_control b2) (get_arity b2)) (Port (get_node b3) (get_control b3) (get_arity b3))):
bigraph_link_equality b1 b2 (bij_e12) (bij_p12) -> 
bigraph_link_equality b2 b3 (bij_e23) (bij_p23) ->
bigraph_link_equality b1 b3 (bij_e23 <O> bij_e12) (bij_p23 <O> bij_p12).
Proof. 
  unfold bigraph_link_equality. intros [H12i H12p] [H23i H23p].
  split.
  - unfold bigraph_link_innername_equality in *. intros inner. simpl.  
    specialize (H12i inner).
    specialize (H23i inner).
    unfold funcomp. 
    set (l1i := get_link b1 (inl inner)).
    destruct l1i as [l1i_o | l1i_e] eqn:E;
    unfold l1i in E;
    rewrite E in H12i;
    set (l2i := get_link b2 (inl inner));
    fold l2i in H12i;
    destruct l2i as [l2i_o | l2i_e] eqn:E' in H12i;
    unfold l2i in E'; 
    rewrite E' in H23i;
    destruct (get_link b3 (inl inner)) as [l3i_o | l3i_e].
    + rewrite H12i. rewrite H23i. reflexivity.
    + apply H23i.
    + exfalso. apply H23i. 
    + apply H12i.
    + apply H12i.
    + exfalso. apply H23i.
    + apply H23i.  
    + rewrite H12i. rewrite H23i. reflexivity.
  - unfold bigraph_link_port_equality in *. intros p1. simpl.  
    specialize (H12p p1).
    unfold funcomp. 
    set (l1p := get_link b1 (inr p1)).
    destruct l1p as [l1p_n | l1p_r] eqn:E;
    unfold l1p in E;
    rewrite E in H12p; 
    set (p2 := forward (Port (get_node b1) (get_control b1) (get_arity b1))
    (Port (get_node b2) (get_control b2) (get_arity b2)) bij_p12 p1);
    specialize (H23p p2);
    set (p3 := forward (Port (get_node b2) (get_control b2) (get_arity b2))
    (Port (get_node b3) (get_control b3) (get_arity b3)) bij_p23 p2);
    fold p2 in H12p;
    fold p3 in H23p;
    set (l2p2 := get_link b2 (inr p2));
    fold l2p2 in H12p;
    destruct l2p2 as [l2p2_o | l2p2_e] eqn:E' in H12p;
    unfold l2p2 in E'; 
    rewrite E' in H23p;
    destruct (get_link b3 (inr p3)).
    + rewrite H12p. rewrite H23p. reflexivity.
    + apply H23p.
    + exfalso. apply H23p. 
    + apply H12p.
    + apply H12p.
    + exfalso. apply H23p.
    + apply H23p.  
    + rewrite H12p. rewrite H23p. reflexivity.
  Qed.


Lemma bigraph_equality_trans {s i r o : FinDecType} 
(b1 : bigraph s i r o) (b2 : bigraph s i r o) (b3 : bigraph s i r o):
  bigraph_equality b1 b2
    -> bigraph_equality b2 b3  
      -> bigraph_equality b1 b3.
Proof.
  intros H12 H23. inversion H12. inversion H23.
  apply (BigEq s i r o b1 b3 (bij_n0 <O> bij_n) (bij_e0 <O> bij_e) (bij_k0 <O> bij_k) (bij_p0 <O> bij_p)).
  + apply arity_trans. apply big_arity_eq. apply big_arity_eq0.
  + apply control_trans. apply big_control_eq. apply big_control_eq0.
  + apply parent_trans. apply big_parent_eq. apply big_parent_eq0.
  + apply link_trans. apply big_link_eq. apply big_link_eq0.
  Qed.


  Lemma dis_port_commu_commu {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
  (b1 : bigraph s1 i1 r1 o1) 
  (b2 : bigraph s2 i2 r2 o2)
  (p12 : Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2))) : 
  mk_port_commu b2 b1 (mk_port_commu b1 b2 p12) = p12.
  Proof.
    destruct p12 as [[[n1 | n2] i12] P12];
    simpl in P12;
    unfold mk_port_commu;
    reflexivity. Qed.

    Lemma dis_port_commu {s1 i1 r1 o1 s2 i2 r2 o2 : FinDecType} 
    (b1 : bigraph s1 i1 r1 o1) 
    (b2 : bigraph s2 i2 r2 o2)
    (p12 : Port (get_node (b1 || b2)) (get_control (b1 || b2)) (get_arity (b1 || b2))) :
    match mk_dis_port b2 b1 (mk_port_commu b1 b2 p12) with
      | inl p2 => 
        match (mk_dis_port b1 b2 p12) with
        | inl p1' => False
        | inr p2' => p2 = p2'
        end
      | inr p1 => 
        match (mk_dis_port b1 b2 p12) with
        | inl p1' => p1 = p1'
        | inr p2' => False
        end
    end.
    Proof.
    destruct p12 as [[[n1 | n2] i12] P12]; simpl; reflexivity.
    Qed.
