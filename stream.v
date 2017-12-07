Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Setoid.
Require Import FinFun.

Module Stream.


CoInductive stream (A : Type) : Type :=
    | scons : A -> stream A -> stream A.

Arguments scons [A].

Definition iid {A : Type} (s : stream A) : stream A :=
match s with
    | scons h t => scons h t
end.

Lemma iid_id :
  forall {A : Type} (s : stream A), s = iid s.
Proof.
  destruct s; trivial.
Defined.

Ltac step'_aux :=
fun n x =>
match goal with
    | |- context [x] =>
        do n (rewrite (iid_id x); cbn)
end.

Ltac step' n x := step'_aux ltac:(n) x.

Ltac step x := step'_aux ltac:(1) x.

Ltac step'_aux_hyp n x H :=
match goal with
    | H : context [x] |- _ =>
        do n (rewrite (iid_id x) in H; cbn in H)
end.

Ltac step'_hyp n x H := step'_aux_hyp ltac:(n) constr:(x) H.

Ltac step_hyp x H := step'_aux ltac:(1) constr:(x) H.

CoFixpoint theChosenOne : stream unit :=
  scons tt theChosenOne.

CoInductive sim {A : Type} : stream A -> stream A -> Prop :=
    | make_sim : forall (h1 h2 : A) (t1 t2 : stream A),
        h1 = h2 -> sim t1 t2 -> sim (scons h1 t1) (scons h2 t2).

Lemma sim_refl :
  forall (A : Type) (x : stream A), sim x x.
Proof.
  cofix.
  destruct x. constructor; auto.
Qed.

Lemma sim_sym :
  forall (A : Type) (x y : stream A),
    sim x y -> sim y x.
Proof.
  cofix.
  destruct 1. constructor; auto.
Qed.

Lemma sim_trans :
  forall (A : Type) (x y z : stream A),
    sim x y -> sim y z -> sim x z.
Proof.
  cofix.
  destruct 1; subst. destruct z. intro. constructor.
    inversion H; subst. trivial.
  apply sim_trans with t2.
    assumption.
    inversion H; subst. assumption.
Qed.

Instance Equiv_sim (A : Type) : Equivalence (@sim A).
Proof.
  split; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
Defined.

Lemma all_chosen_unit_aux :
  forall s : stream unit, sim s theChosenOne.
Proof.
  cofix.
  intro. step theChosenOne. destruct s, u. constructor; auto.
Qed.

Theorem all_chosen_unit :
  forall x y : stream unit, sim x y.
Proof.
  intros. apply sim_trans with theChosenOne.
    apply all_chosen_unit_aux.
    apply sim_sym, all_chosen_unit_aux.
Qed.

Axiom sim_eq :
  forall (A : Type) (x y : stream A), sim x y -> x = y.

Theorem all_eq :
  forall x y : stream unit, x = y.
Proof.
  intros. apply sim_eq. apply all_chosen_unit.
Qed.

Definition unit_to_stream (u : unit) : stream unit := theChosenOne.
Definition stream_to_unit (s : stream unit) : unit := tt.

Theorem unit_is_stream :
  Bijective unit_to_stream.
Proof.
  red. exists stream_to_unit.
  split; intros.
    destruct x; trivial.
    apply all_eq.
Qed.

CoFixpoint nts_aux (f : nat -> nat) (n : nat) : stream nat :=
  scons (f n) (nts_aux f (S n)).

CoFixpoint nts (f : nat -> nat) : stream nat :=
  nts_aux f 0.

Fixpoint stn (s : stream nat) (n : nat) : nat :=
match n, s with
    | 0, scons h _ => h
    | S n', scons _ t => stn t n'
end.

Fixpoint drop {A : Type} (n : nat) (s : stream A) : stream A :=
match n, s with
    | 0, _ => s
    | S n', scons _ t => drop n' t
end.

Lemma aux :
  forall (s : stream nat) (n : nat),
    sim (nts_aux (stn s) n) (drop n s).
Proof.
  cofix.
  intros. step (nts_aux (stn s) n). rewrite (iid_id s) at 3.
  destruct s. cbn. rewrite <- aux. step (nts_aux (stn (scons n0 s)) n).
  constructor; auto. apply sim_refl.
Restart.
  cofix.
  intros. destruct s as [h t], n as [| n']; cbn; intros.
    step (nts_aux (stn (scons h t)) 0). constructor; auto. apply aux.
    step (nts_aux (stn (scons h t)) (S n')). case_eq (drop n' t); intros.
      constructor.
        admit.
        induction n'; destruct t. cbn in H. (*
    rewrite <- aux. step (nts_aux (stn (scons h t)) (S n')).
      step (nts_aux (stn t) n'). constructor; auto.*)
Restart.
  intros s n. generalize dependent s.
  induction n as [| n']; cbn; intros.
    destruct s. step (nts_aux (stn (scons n s)) 0). constructor; auto.
Admitted.

Lemma auxzor :
  forall (f : nat -> nat) (n : nat),
    sim (nts_aux f n) (nts_aux (fun k : nat => f (n + k)) 0).
Proof.
  intros. remember 0 as w. generalize dependent w.
  cofix.
  intros.
  step (nts_aux f n). step (nts_aux (fun k : nat => f (n + k)) w).
  constructor.
    rewrite Heqw, <- plus_n_O. trivial.
Abort.

Lemma aux' :
  forall (f : nat -> nat) (n : nat),
    stn (nts_aux f n) = fun k : nat => f (k + n).
Proof.
  intros. extensionality k. generalize dependent n.
  induction k as [| k']; cbn; intros.
      trivial.
      rewrite IHk'. f_equal. omega.
Qed.

Theorem natfun_is_stream_nat :
  Bijective nts.
Proof.
  red. exists stn. split; intros.
    extensionality n. replace (nts x) with (nts_aux x 0).
      rewrite aux'. rewrite <- plus_n_O. trivial.
      step (nts x). step (nts_aux x 0). trivial.
    apply sim_eq. generalize dependent y. cofix. intro.
      step (nts (stn y)). destruct y. constructor.
        trivial.
        apply aux.
Defined.