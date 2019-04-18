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

Inductive one_step : term -> term -> Prop :=
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

where "x --> y" := (one_step x y).

Lemma numericval_no_eval : forall nv, is_numeric_val nv -> (forall t, not (nv --> t)).
  intros nv H.
  induction H; unfold not. intros.
  -inversion H.
  -intros t' H'.
   inversion H'; subst.
   specialize (IHis_numeric_val t'0).
   apply IHis_numeric_val.
   assumption.
Qed.

Lemma one_step_unique : forall t t1 t2, t --> t1 -> t --> t2 -> t1 = t2.
  intros t t1 t2 H1 H2.
  generalize dependent t2.
  induction H1.
  -intros t2 H2. (* E_IfTrue *)
   inversion H2.
   +reflexivity.
   +inversion H4.
  -intros t2 H2. (* E_IfFalse *)
   inversion H2; subst.
   +reflexivity.
   +inversion H4.
  -intros t0 H0. (* E_If *)
   inversion H0; subst.
   +inversion H1.
   +inversion H1.
   +specialize (IHone_step t'0).
    specialize (IHone_step H5).
    rewrite IHone_step.
    reflexivity.
  -intros t2 H. (* E_Succ *)
   inversion H; subst.
   specialize (IHone_step t'0).
   rewrite (IHone_step H2); reflexivity.
  -intros. (* E_Pred *)
   inversion H2; subst.
   +specialize (IHone_step t'0).
    rewrite (IHone_step H0); reflexivity.
   +inversion H1.
   +induction H0.
    *inversion H1; inversion H0.
    *inversion H1.
     inversion H3.
     apply (numericval_no_eval t H0) in H6.
     contradiction.
  -intros. (* E_PredZero *)
   inversion H2.
   +inversion H0.
   +reflexivity.
  -intros. (* E_PredSucc *)
   inversion H2; subst.
   +inversion H1; subst.
    apply (numericval_no_eval nv H) in H3.
    contradiction.
   +reflexivity.
  -intros. (* E_IsZeroZero *)
   inversion H2; subst.
   +reflexivity.
   +inversion H0.
  -intros. (* E_IsZeroSucc *)
   inversion H2; subst.
   +reflexivity.
   +inversion H1; subst.
    apply numericval_no_eval in H3.
    contradiction.
    apply numericval_no_eval in H3.
    assumption.
    apply numericval_no_eval in H3.
    contradiction.
    apply H.
  -intros t2 H. (* E_IsZero *)
   inversion H; subst.
   +inversion H1.
   +apply numericval_no_eval in H1.
    contradiction.
    apply N_Succ; assumption.
   +specialize (IHone_step t'0).
    rewrite (IHone_step H2).
    reflexivity.
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
