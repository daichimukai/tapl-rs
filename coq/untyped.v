Inductive term : Type :=
| tmtrue : term
| tmfalse : term
| tmif : term -> term -> term -> term
| tmzero : term
| tmsucc : term -> term
| tmpred : term -> term
| tmiszero : term -> term.

Definition subterm (s : term) (t : term) : Prop :=
  match t with
  | tmtrue => False
  | tmfalse => False
  | tmif t1 t2 t3 => t1 = s \/ t2 = s \/ t3 = s
  | tmzero => False
  | tmsucc t' => t' = s
  | tmpred t' => t' = s
  | tmiszero t' => t' = s
  end.

Theorem term_struct_ind : forall P : term -> Prop, (forall s : term, (forall r: term, subterm r s -> P r) -> P s) -> (forall t : term, P t).
  intros P H.
  induction t; apply H; intros r H'; simpl in H'; try contradiction.
  -repeat (destruct H' as [H' | H']; try (rewrite <- H'; assumption)).
  -repeat (rewrite <- H'; assumption).
  -rewrite <- H'; assumption.
  -rewrite <- H'; assumption.
Qed.
