Inductive term : Type :=
| tmtrue : term
| tmfalse : term
| tmif : term -> term -> term -> term
| tmzero : term
| tmsucc : term -> term
| tmpred : term -> term
| tmiszero : term -> term.

Inductive type : Type := Bool | Nat.

Inductive is_numeric_val : term -> Prop :=
| N_Zero :
    is_numeric_val tmzero
| N_Succ : forall t,
    is_numeric_val t ->
    is_numeric_val (tmsucc t).

Inductive is_val : term -> Prop :=
| V_True :
    is_val tmtrue
| V_False :
    is_val tmfalse
| V_numericalval : forall t,
    is_numeric_val t ->
    is_val t.

Inductive subterm : term -> term -> Prop :=
| S_IfCond : forall t t1 t2,
    subterm t (tmif t t1 t2)
| S_IfTrue : forall t t1 t2,
    subterm t1 (tmif t t1 t2)
| S_IfFalse : forall t t1 t2,
    subterm t2 (tmif t t1 t2)
| S_Succ : forall t,
    subterm t (tmsucc t)
| S_Pred : forall t,
    subterm t (tmpred t)
| S_IsZero : forall t,
    subterm t (tmiszero t).

Inductive typed : term -> type -> Prop :=
| T_True :
    typed tmtrue Bool
| T_False :
    typed tmfalse Bool
| T_Zero :
    typed tmzero Nat
| T_If : forall t t1 t2 T,
    typed t Bool ->
    typed t1 T ->
    typed t2 T ->
    typed (tmif t t1 t2) T
| T_Succ : forall t,
    typed t Nat ->
    typed (tmsucc t) Nat
| T_Pred : forall t,
    typed t Nat ->
    typed (tmpred t) Nat
| T_IsZero : forall t,
    typed t Nat ->
    typed (tmiszero t) Bool.

Lemma subterm_typed : forall t T, typed t T -> forall s, subterm s t -> exists U, typed s U.
  intros t T t_typed s s_t_subterm.
  inversion s_t_subterm; subst; inversion t_typed.
  -exists Bool; assumption.
  -exists T; assumption.
  -exists T; assumption.
  -exists Nat; assumption.
  -exists Nat; assumption.
  -exists Nat; assumption.
Qed.

Lemma typed_bool : forall t, typed t Bool -> is_val t -> t = tmtrue \/ t = tmfalse.
  intros t H_type H_val.
  induction H_val.
  -left; reflexivity. (* t is true*)
  -right; reflexivity. (* t is false *)
  -inversion H. (* t is a numeric value (contradiction) *)
   +rewrite <- H0 in H_type.
    inversion H_type.
   +rewrite <- H1 in H_type.
    inversion H_type.
Qed.

Lemma typed_numericval : forall t, typed t Nat -> is_val t -> is_numeric_val t.
  intros t H_type H_val.
  induction H_val.
  -inversion H_type. (* t is true (contradiction) *)
  -inversion H_type. (* t is false (contradiction) *)
  -assumption. (* t is a numeric value *)
Qed.

Reserved Notation "x --> y" (at level 80, no associativity).

Inductive step : term -> term -> Prop :=
| E_IfTrue : forall t t',
    (tmif tmtrue t t') --> t
| E_IfFalse : forall t t',
    (tmif tmfalse t t') --> t'
| E_If : forall t t' t1 t2,
    (t --> t') ->
    ((tmif t t1 t2) --> (tmif t' t1 t2))
| E_Succ : forall t t',
    (t --> t') ->
    tmsucc t --> tmsucc t'
| E_Pred : forall t t',
    (t --> t') ->
    tmpred t --> tmpred t'
| E_PredZero :
    tmpred tmzero --> tmzero
| E_PredSucc : forall nv,
    is_numeric_val nv ->
    tmpred (tmsucc nv) --> nv
| E_IsZeroZero :
    tmiszero tmzero --> tmtrue
| E_IsZeroSucc : forall nv,
    is_numeric_val nv ->
    tmiszero (tmsucc nv) --> tmfalse
| E_IsZero : forall t t',
    t --> t' ->
    tmiszero t --> tmiszero t'

where "x --> y" := (step x y).

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
    match type of T with Prop =>
                         solve [
                             inversion H;
                             match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
    end
  end.
Ltac solve_by_invert := solve_by_inverts 1.

Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  not (exists t', R t t').

Lemma numericval_no_eval : forall nv, is_numeric_val nv -> normal_form step nv.
  unfold normal_form.
  intros nv H.
  induction H.
  - unfold not. intro H. inversion H. inversion H0.
  - unfold not. intro H'. inversion H'. inversion H0.
    apply IHis_numeric_val.
    exists t'.
    assumption.
Qed.

Theorem value_is_nf : forall t, is_val t -> normal_form step t.
  intros t t_val.
  induction t_val.
  - unfold normal_form. unfold not. intro H'. inversion H'. inversion H.
  - unfold normal_form. unfold not. intro H'. inversion H'. inversion H.
  - apply (numericval_no_eval t H).
Qed.

Ltac find_eqn :=
  match goal with
  | IH: forall t, ?P t -> ?L = ?R, H: ?P ?X |- _ => rewrite (IH X H) in *
end.

Ltac find_succ :=
  match goal with
  | H1: is_numeric_val ?X, H2: ?X --> ?Y
    |- _ => destruct (value_is_nf _ (V_numericalval _ H1)); exists Y; assumption
  | H1: is_numeric_val ?X, H2: tmsucc ?X --> ?Y
    |- _ => inversion H2; find_succ
  end.

Lemma step_unique : forall t t1 t2, t --> t1 -> t --> t2 -> t1 = t2.
  intros t t' t'' t_step_t' t_step_t''.
  generalize dependent t''.
  induction t_step_t'; intros t'' t_step_t''; inversion t_step_t''; subst;
    try solve_by_invert; try find_eqn; try find_succ; auto.
Qed.

Theorem process : forall t T, typed t T -> is_val t \/ (exists t', t --> t').
  intros t T t_typed.
  induction t_typed.
  -left; constructor.
  -left; constructor.
  -left; constructor; constructor.
  -right.
   case IHt_typed1.
   +intro t_val.
    assert (t = tmtrue \/ t = tmfalse) as t_true_or_false.
    { apply (typed_bool t t_typed1 t_val). }
    case t_true_or_false.
    *intro t_true; exists t1; rewrite t_true; constructor.
    *intro t_false; exists t2; rewrite t_false; constructor.
   +intro t_process.
    destruct t_process as [t' t_process].
    exists (tmif t' t1 t2); constructor; assumption.
  -case IHt_typed.
   +intro t_val; left.
    constructor.
    constructor.
    apply (typed_numericval t t_typed t_val).
   +intro t_process; right.
    destruct t_process as [t' t_process].
    exists (tmsucc t'); constructor; assumption.
  -right.
   case IHt_typed.
   +intro t_val.
    assert (is_numeric_val t) as t_numeric.
    { apply (typed_numericval t t_typed t_val). }
    inversion t_numeric.
    *exists tmzero; constructor.
    *exists t0; constructor; assumption.
   +intro t_process.
    destruct t_process as [t' t_process].
    exists (tmpred t').
    apply (E_Pred t t' t_process).
  -case IHt_typed.
   +intro t_val; right.
    assert (is_numeric_val t) as t_numeric.
    { apply (typed_numericval t t_typed t_val). }
    inversion t_numeric.
    *exists tmtrue.
     constructor.
    *exists tmfalse.
     constructor; assumption.
   +intro t_process; right.
    destruct t_process as [t' t_process].
    exists (tmiszero t'); constructor; assumption.
Qed.

Hint Constructors typed.
Lemma numericval_nat : forall t, is_numeric_val t -> typed t Nat.
  intros t t_nv. induction t_nv; auto.
Qed.

Ltac find_process :=
  match goal with
  | Ht: typed ?X ?T, IH: forall t', ?X --> t' -> typed t' ?T, Hp: ?P ?X --> ?Y
                                                      |- _ => solve [ inversion Hp; constructor; auto ]
end.

Theorem preserve : forall t t' T, typed t T -> t --> t' -> typed t' T.
  intros t t' T t_typed t_process.
  generalize dependent t'.
  induction t_typed; intros t' t'_process; try solve_by_invert; try find_process; auto.
  - (* T_If *)
    inversion t'_process; try (rewrite <- H3; assumption).
    specialize (IHt_typed1 t'0).
    specialize (IHt_typed1 H3).
    apply (T_If t'0 t1 t2 T IHt_typed1 t_typed2 t_typed3).
  - (* T_Pred *)
    inversion t'_process; try constructor.
    + specialize (IHt_typed t'0). (* E_Pred *)
      specialize (IHt_typed H0). auto.
    +apply (numericval_nat t' H0). (* E_PredSucc *)
Qed.

Theorem preserve' : forall t t' T, typed t T -> t --> t' -> typed t' T.
  Hint Resolve numericval_nat.
  intros t t' T t_typed t_process.
  generalize dependent T.
  induction t_process; intros T t_typed; inversion t_typed; try constructor; auto.
Qed.
