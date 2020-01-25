

Require Import RCCBase.

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
  Time all:
  repeat match goal with
      | e : simplifyFormula ?f = _,
        IH : formulaDenote _ (simplifyFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
Qed.

Definition solveHypothesis (env : Env Prop) :
  forall (proofs : Proofs) (H : allTrue env proofs) (hyp f : formula)
    (cont : Proofs -> bool), bool.
Proof.
  refine (
  fix solve
    (proofs : Proofs) (H : allTrue env proofs) (hyp f : formula)
      (cont : Proofs -> bool) : bool :=
  match hyp with
      | fFalse => false
      | fTrue => cont proofs
      | fVar i => cont (i :: proofs)
      | fAnd f1 f2 =>
          solve proofs H f1 (fImpl f2 f)
                        (fun proofs' => cont proofs')
      | fOr f1 f2 =>
          andb (solve proofs H f1 f cont)
               (solve proofs H f2 f cont)
      | _ => false
  end).
Defined.

Definition solveGoal (env : Env Prop)
  : forall (proofs : Proofs) (H : allTrue env proofs) (f : formula), bool.
Proof.
  refine (
  fix solve
    (proofs : Proofs) (H : allTrue env proofs) (f : formula) : bool :=
  match f with
      | fFalse => false
      | fTrue => true
      | fVar i =>
          match in_dec Nat.eq_dec i proofs with
              | left _ => true
              | right _ => false
          end 
      | fAnd f1 f2 => andb (solve proofs H f1) (solve proofs H f2)
      | fOr f1 f2 => orb (solve proofs H f1) (solve proofs H f2)
 (*     | fImpl f1 f2 =>
          solveHypothesis env proofs H f1 f2
            (fun proofs' => solve proofs' _ f2)*)
      | _ => false
  end).
Defined.

Definition solveFormula (env : Env Prop) (f : formula) : bool.
Proof.
  refine (solveGoal env [] _ f). cbn. trivial.
Defined.

Theorem solveGoal_correct :
  forall (env : Env Prop) (proofs : Proofs) (H : allTrue env proofs)
  (f : formula),
    solveGoal env proofs H f = true -> formulaDenote env f.
Proof.
  induction f; cbn; intros; try congruence.
    trivial.
    destruct (in_dec Nat.eq_dec n proofs).
      apply find_spec with proofs; auto.
      congruence.
    rewrite andb_true_iff in H0. tauto.
    rewrite orb_true_iff in H0. tauto.
Qed.

Theorem solveFormula_correct :
  forall (env : Env Prop) (f : formula),
    solveFormula env f = true -> formulaDenote env f.
Proof.
  intros. destruct f; cbn in *; try congruence.
    trivial.
    rewrite andb_true_iff in H. destruct H.
      split; eapply solveGoal_correct; eauto.
    rewrite orb_true_iff in H. destruct H.
      left. eapply solveGoal_correct; eauto.
      right. eapply solveGoal_correct; eauto.
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

Ltac solveGoal :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in change (formulaDenote xs f);
          rewrite <- simplifyFormula_correct;
          apply solveFormula_correct; cbn; reflexivity
end.