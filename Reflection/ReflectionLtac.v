

Require Import RCCBase.

Inductive formula : Set :=
    | FConst : bool -> formula
    | FAnd : formula -> formula -> formula
    | FOr : formula -> formula -> formula
    | FImp : formula -> formula -> formula.

Fixpoint denote (f : formula) : Prop :=
match f with
    | FConst b => if b then True else False
    | FAnd f1 f2 => denote f1 /\ denote f2
    | FOr f1 f2 => denote f1 \/ denote f2
    | FImp f1 f2 => denote f1 -> denote f2
end.

Ltac reify P :=
lazymatch P with
    | True => constr:(FConst true)
    | False => constr:(FConst false)
    | ?P1 /\ ?P2 =>
        let f1 := reify P1 in
        let f2 := reify P2 in constr:(FAnd f1 f2)
    | ?P1 \/ ?P2 =>
        let f1 := reify P1 in
        let f2 := reify P2 in constr:(FOr f1 f2)
    | ?P1 -> ?P2 =>
        let f1 := reify P1 in
        let f2 := reify P2 in constr:(FImp f1 f2)
end.

Fixpoint solve (f : formula) : bool :=
match f with
    | FConst b => b
    | FAnd f1 f2 => andb (solve f1) (solve f2)
    | FOr f1 f2 => orb (solve f1) (solve f2)
    | FImp f1 f2 => implb (solve f1) (solve f2)
end.

Theorem denoteP :
  forall f : formula, reflect (denote f) (solve f).
Proof.
  induction f; simpl.
    destruct b; auto.
    destruct IHf1, IHf2; simpl; constructor; auto; tauto.
    destruct IHf1, IHf2; simpl; constructor; auto; tauto.
    destruct IHf1, IHf2; simpl; constructor; auto; tauto.
Qed.

Theorem solve_denote : forall f : formula,
    solve f = true -> denote f.
Proof.
  intros. destruct (denoteP f).
    assumption.
    inversion H.
Qed.

Ltac obvious :=
match goal with
    | |- ?P =>
        let f := reify P in
        change (denote f);
        apply solve_denote; reflexivity
end.

Theorem true_galore :
  (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof. tauto. Qed.

Theorem true_galore'
  : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  obvious.
Qed.