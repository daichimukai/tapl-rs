Inductive term : Type :=
| tmtrue : term
| tmfalse : term
| tmif : term -> term -> term -> term
| tmzero : term
| tmsucc : term -> term
| tmpred : term -> term
| tmiszero : term -> term.

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
  -intros. (* E_PredZero *)
   inversion H2; reflexivity.
  -intros. (* E_PredSucc *)
   inversion H2; subst; reflexivity.
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
