Module Impossible.

CoInductive Impossible : Type :=
    | IM : Impossible -> Impossible.

Definition iid (s : Impossible) : Impossible :=
match s with
    | IM s' => IM s'
end.

Lemma sim :
  forall s : Impossible, s = iid s.
Proof.
  destruct s; trivial.
Defined.

Ltac step'_aux :=
fun n x =>
match goal with
    | |- context [x] =>
        do n (rewrite (sim x); cbn)
end.

Ltac step' n x := step'_aux ltac:(n) x.

Ltac step x := step'_aux ltac:(1) x.

CoFixpoint theChosenOne : Impossible :=
  IM theChosenOne.

CoFixpoint theChosenAnotherOne : Impossible :=
  IM (IM theChosenAnotherOne).

CoInductive Bisim : Impossible -> Impossible -> Prop :=
    | Bi : forall x y : Impossible, Bisim x y -> Bisim (IM x) (IM y).

Lemma Bisim_refl :
  forall x : Impossible, Bisim x x.
Proof.
  cofix.
  destruct x. constructor. auto.
Qed.

Lemma Bisim_sym :
  forall x y : Impossible,
    Bisim x y -> Bisim y x.
Proof.
  cofix.
  destruct 1. constructor. auto.
Qed.

Lemma Bisim_trans :
  forall x y z : Impossible,
    Bisim x y -> Bisim y z -> Bisim x z.
Proof.
  cofix.
  destruct 1. destruct z. intro. constructor.
  apply Bisim_trans with y.
    assumption.
    inversion H0; subst. assumption.
Qed.

Goal
  Bisim theChosenOne theChosenAnotherOne.
Proof.
  cofix.
  match goal with
      | |- Bisim ?x ?y => do 2 step x; step y
  end.
  do 2 constructor.
  assumption.
Qed.

Lemma all_chosen_aux :
  forall s : Impossible, Bisim theChosenOne s.
Proof.
  cofix.
  intro. step theChosenOne. destruct s. constructor. auto.
Qed.

Theorem all_chosen :
  forall x y : Impossible, Bisim x y.
Proof.
  intros. apply Bisim_trans with theChosenOne.
    apply Bisim_sym, all_chosen_aux.
    apply all_chosen_aux.
Qed.

Axiom Bisim_eq :
  forall x y : Impossible, Bisim x y -> x = y.

Theorem all_eq :
  forall x y : Impossible, x = y.
Proof.
  intros. apply Bisim_eq. apply all_chosen.
Qed.

Definition unit_to_Impossible (u : unit) : Impossible :=
  theChosenOne.

Definition Impossible_to_unit (s : Impossible) : unit := tt.

Require Import FinFun.

Theorem unit_is_Impossible :
  Bijective unit_to_Impossible.
Proof.
  red. exists Impossible_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.

End Impossible.