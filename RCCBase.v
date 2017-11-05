Require Export FunctionalExtensionality.

Ltac inv H := inversion H; subst.

Ltac gen x := generalize dependent x.

Ltac ext x := extensionality x.

Ltac term_contains t x :=
match t with
    | x => idtac
    | ?f x => idtac
    | ?f _ => term_contains f x
    | _ => fail
end.

Ltac gen_IH H :=
match reverse goal with
    | H : _ |- _ => fail
    | x : ?Tx |- _ =>
        match type of H with
            | ?TH => term_contains TH x
            | _ => generalize dependent x
        end
end.

Ltac gen_ind H :=
  try intros until H; gen_IH H; induction H; cbn; auto.


Ltac invs := repeat
match goal with
    | H : ?f ?x1 ?x2 ?x3 = ?f ?x1' ?x2' ?x3' |- _ => inv H
    | H : ?f ?x1 ?x2 = ?f ?x1' ?x2' |- _ => inv H
    | H : ?f ?x1 = ?f ?x1' |- _ => inv H
end.

Ltac replace_nonvars H :=
match H with
    | ?f ?x1 => is_var x1; replace_nonvars f
    | ?f ?x1 =>
        let x1' := fresh "x1" in
        let H1 := fresh "H1" in remember x1 as x1' eqn: H1; replace_nonvars f
    | _ => idtac
end.

Ltac clean_eqs := repeat
match goal with
    | H : ?x = ?x |- _ => clear H
    | H : ?x = ?x -> _ |- _ => specialize (H eq_refl)
    | H : forall x, ?y = ?y -> ?P |- _ =>
        assert (H' := fun x => H x eq_refl); clear H; rename H' into H
end.

Ltac ind' H :=
match type of H with
    | ?T => replace_nonvars T; induction H; subst; try congruence;
        invs; clean_eqs; eauto
end.

Ltac ind H := try intros until H; gen_IH H; ind' H.