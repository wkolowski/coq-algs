(* Formulas. *)
Inductive formula : Type :=
    | fFalse : formula
    | fTrue : formula
    | fVar : Prop -> formula
    | fNot : formula -> formula
    | fAnd : formula -> formula -> formula
    | fOr : formula -> formula -> formula
    | fImpl : formula -> formula -> formula.

Fixpoint formulaDenote (f : formula) : Prop :=
match f with
    | fFalse => False
    | fTrue => True
    | fVar P => P
    | fNot f' => ~ formulaDenote f'
    | fAnd f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | fOr f1 f2 => formulaDenote f1 \/ formulaDenote f2
    | fImpl f1 f2 => formulaDenote f1 -> formulaDenote f2
end.

Function simpFormula (f : formula) : formula :=
match f with
    | fFalse => fFalse
    | fTrue => fTrue
    | fVar P => fVar P
    | fNot f' =>
        match simpFormula f' with
            | fFalse => fTrue
            | fTrue => fFalse
            | f'' => fNot f''
        end
    | fAnd f1 f2 =>
        match simpFormula f1, simpFormula f2 with
            | fOr f11 f12, f2' => fOr (fAnd f11 f2') (fAnd f12 f2')
            | f1', fOr f21 f22 => fOr (fAnd f1' f21) (fAnd f1' f22)
            | fFalse, _ => fFalse
            | _, fFalse => fFalse
            | fTrue, f2' => f2'
            | f1', fTrue => f1'
            | f1', f2' => fAnd f1' f2'
        end
    | fOr f1 f2 =>
        match simpFormula f1, simpFormula f2 with
            | fAnd f11 f12, f2' => fAnd (fOr f11 f2') (fOr f12 f2')
            | f1', fAnd f21 f22 => fAnd (fOr f1' f21) (fOr f1' f22)
            | fFalse, f2' => f2'
            | f1', fFalse => f1'
            | fTrue, _ => fTrue
            | _, fTrue => fTrue
            | f1', f2' => fOr f1' f2'
        end
    | fImpl f1 f2 =>
        match simpFormula f1 with
            | fFalse => fTrue
            | fTrue => f2
            | fAnd f11 f12 => fImpl f11 (fImpl f12 f2)
            | fOr f11 f12 => fAnd (fImpl f11 f2) (fImpl f12 f2)
            | f1' => fImpl f1' f2
        end
end.

Theorem simpFormula_correct :
  forall f : formula, formulaDenote (simpFormula f) <-> formulaDenote f.
Proof.
  intros. functional induction simpFormula f; cbn.
  Time all: try tauto.
  repeat match goal with
      | : nat -> _, IH : forall' : nat -> _, _ |- _ =>
          specialize (IH)
      | e : simpFormula ?f = _,
        IH : formulaDenote _ (simpFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
    assert (eqExpDenote (simpHypEq (E e1 e2)) =
           (expDenote e1' = expDenote e2')).
      rewrite e0. cbn. trivial.
      rewrite <- H. rewrite simpHypEq_correct. cbn. reflexivity.
    assert (eqExpDenote (simpHypEq (E e1 e2)) <->
            eqExpDenote (E e1' e2')).
      rewrite e3. tauto.
      rewrite simpHypEq_correct in H. cbn in H. tauto.
Qed.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solveFormula
  {X : UCRing} (env : nat -> X) (f : formula)
  : option (formulaDenote f).
Proof.
  destruct f; cbn.
    apply None.
    apply Some. trivial.
    apply None.
      destruct (exp_eq_dec (simplifyExp e) (simplifyExp e0)).
        rewrite <- (simplifyExp_correct e),
                <- (simplifyExp_correct e0).
          rewrite e1. apply Some. trivial.
        apply None.
    apply None.
    destruct (solveFormula X f1), (solveFormula X f2).
      apply Some. split; assumption.
      1-3: apply None.
    destruct (solveFormula X f1).
      apply Some. left. assumption.
      destruct (solveFormula X f2).
        apply Some. right. assumption.
        apply None.
    destruct (solveFormula X f2).
      apply Some. intro. assumption.
      apply None.
Defined.

Theorem solveFormula_correct :
  forall (X : UCRing) (env : nat -> X) (f : formula),
    (exists p : formulaDenote f, solveFormula f = Some p) ->
      formulaDenote f.
Proof.
  intros. destruct H. assumption.
Qed.

(* Basic tactics for manipulating lists. *)
Ltac inList x l :=
match l with
    | [] => false
    | x :: _ => true
    | _ :: ?l' => inList x l'
end.

Ltac addToList x l :=
  let b := inList x l in
match b with
    | true => l
    | false => constr:(x :: l)
end.

Ltac lookup x l :=
match l with
    | x :: _ => constr:(0%nat)
    | _ :: ?l' => let n := lookup x l' in constr:(S n)
end.
