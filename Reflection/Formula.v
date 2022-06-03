From CoqAlgs Require Export Base.

Set Implicit Arguments.

(* Formulas. [not f] will be represented as [fImpl f fFalse] and
   [f1 <-> f2] as [fAnd (fImpl f1 f2) (fImpl f2 f1)]. *)
Inductive formula : Type :=
    | fFalse : formula
    | fTrue : formula
    | fVar : nat -> formula
    | fAnd : formula -> formula -> formula
    | fOr : formula -> formula -> formula
    | fImpl : formula -> formula -> formula.

Fixpoint formulaDenote (env : Env Prop) (f : formula) : Prop :=
match f with
    | fFalse => False
    | fTrue => True
    | fVar i => holds i env
    | fAnd f1 f2 => formulaDenote env f1 /\ formulaDenote env f2
    | fOr f1 f2 => formulaDenote env f1 \/ formulaDenote env f2
    | fImpl f1 f2 => formulaDenote env f1 -> formulaDenote env f2
end.

Function simplifyFormula (f : formula) : formula :=
match f with
    | fFalse => fFalse
    | fTrue => fTrue
    | fVar P => fVar P
    | fAnd f1 f2 =>
        match simplifyFormula f1, simplifyFormula f2 with
            | fOr f11 f12, f2' => fOr (fAnd f11 f2') (fAnd f12 f2')
            | f1', fOr f21 f22 => fOr (fAnd f1' f21) (fAnd f1' f22)
            | fFalse, _ => fFalse
            | _, fFalse => fFalse
            | fTrue, f2' => f2'
            | f1', fTrue => f1'
            | f1', f2' => fAnd f1' f2'
        end
    | fOr f1 f2 =>
        match simplifyFormula f1, simplifyFormula f2 with
            | fAnd f11 f12, f2' => fAnd (fOr f11 f2') (fOr f12 f2')
            | f1', fAnd f21 f22 => fAnd (fOr f1' f21) (fOr f1' f22)
            | fFalse, f2' => f2'
            | f1', fFalse => f1'
            | fTrue, _ => fTrue
            | _, fTrue => fTrue
            | f1', f2' => fOr f1' f2'
        end
    | fImpl f1 f2 =>
        match simplifyFormula f1 with
            | fFalse => fTrue
            | fTrue => f2
            | fAnd f11 f12 => fImpl f11 (fImpl f12 f2)
            | fOr f11 f12 => fAnd (fImpl f11 f2) (fImpl f12 f2)
            | f1' => fImpl f1' f2
        end
end.

Theorem simplifyFormula_correct :
  forall (f : formula) (env : Env Prop),
    formulaDenote env (simplifyFormula f) <-> formulaDenote env f.
Proof.
  intros. functional induction simplifyFormula f; cbn.
  all:
  repeat match goal with
      | e : simplifyFormula ?f = _,
        IH : formulaDenote _ (simplifyFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
Qed.

Definition solveHypothesis (env : Env Prop) :
  forall (proofs : Proofs) (hyp f : formula)
    (cont : forall proofs : Proofs,
      solution (allTrue env proofs -> formulaDenote env f)),
        solution (allTrue env proofs -> formulaDenote env hyp ->
          formulaDenote env f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (hyp f : formula)
      (cont : forall proofs : Proofs,
        solution (allTrue env proofs -> formulaDenote env f)) :
          solution (allTrue env proofs -> formulaDenote env hyp ->
            formulaDenote env f) :=
  match hyp with
      | fFalse => Yes
      | fTrue => Reduce (cont proofs)
      | fVar i => Reduce (cont (i :: proofs))
      | fAnd f1 f2 =>
          Reduce (solve proofs f1 (fImpl f2 f)
                        (fun proofs' => Reduce (cont proofs')))
      | fOr f1 f2 =>
          solve proofs f1 f cont &&&
          solve proofs f2 f cont
      | _ => No
  end).
  all: cbn in *; try tauto.
Defined.

Definition solveGoal (env : Env Prop)
  : forall (proofs : Proofs) (f : formula),
      solution (allTrue env proofs -> formulaDenote env f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (f : formula)
      : solution (allTrue env proofs -> formulaDenote env f) :=
  match f with
      | fFalse => No
      | fTrue => Yes
      | fVar i =>
          match in_dec Nat.eq_dec i proofs with
              | left _ => Yes
              | right _ => No
          end
      | fAnd f1 f2 => solve proofs f1 &&& solve proofs f2
      | fOr f1 f2 => solve proofs f1 ||| solve proofs f2
      | fImpl f1 f2 =>
          solveHypothesis env proofs f1 f2
            (fun proofs' => solve proofs' f2)
  end).
  all: cbn; try tauto.
    intro. apply find_spec with proofs; assumption.
Defined.

Definition solveFormula (env : Env Prop) (f : formula)
  : solution (formulaDenote env f).
Proof.
  refine (Reduce (solveGoal env [] f)). apply f0. cbn. trivial.
Defined.

Theorem solveFormula_correct :
  forall (env : Env Prop) (f : formula),
    (exists p : formulaDenote env f, solveFormula env f = Yes' p) ->
      formulaDenote env f.
Proof.
  intros. destruct H. assumption.
Qed.

Ltac allVarsFormula xs P :=
match P with
    | ~ ?P' => allVarsFormula xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | _ => addToList P xs
end.

Ltac reifyFormula xs P :=
match P with
    | False => constr:(fFalse)
    | True => constr:(fTrue)
    | ~ ?P' =>
        let e := reifyFormula xs P' in constr:(fImpl e fFalse)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fImpl e1 e2)
    | ?P1 <-> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in
          constr:(fAnd (fImpl e1 e2) (fImpl e2 e1))
    | _ =>
        let i := lookup P xs in constr:(fVar i)
end.

Ltac reflectFormula :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in
          change (formulaDenote xs f);
          rewrite <- simplifyFormula_correct; cbn
end.

Ltac solveGoal' :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in change (formulaDenote xs f);
          rewrite <- simplifyFormula_correct; cbn;
          try apply (unwrap (solveFormula xs (simplifyFormula f)))
end.

Ltac solveGoal := solveGoal'; fail.