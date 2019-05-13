Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.
Require Import Recdef.

Definition divF (f : nat -> forall k : nat, 0 < k -> nat)
  (n k : nat) (H : 0 < k) : nat :=
match le_lt_dec k n with
    | left _ => S (f (n - k) k H)
    | right _ => 0
end.
Arguments iter {A} _ _.

Theorem divF_terminates :
  forall (n k : nat) (H : 0 < k),
    {v : nat | exists p : nat, forall n_iter : nat, p < n_iter ->
      forall f : forall n k : nat, 0 < k -> nat,
         iter n_iter divF f n k H = v}.
Proof.
  intros. generalize dependent n.
  apply well_founded_induction_type with lt.
    apply lt_wf.
    intros. case_eq (le_lt_dec k x); intro.
      Focus 2. exists 0. exists 0. intros. destruct n_iter; cbn.
        omega.
        unfold divF. rewrite H1. trivial.
      destruct (H0 (x - k)) as [v Hv].
        omega.
        exists (S v). destruct Hv as [p Hp]. exists (S p). intros.
          destruct (n_iter); cbn.
            omega.
            unfold divF. rewrite H1. f_equal. apply Hp. omega.
Defined.

Definition div (n k : nat) (H : 0 < k) : nat :=
  proj1_sig (divF_terminates n k H).

Theorem div_fix : div = divF div.
Proof.
Admitted.

Lemma div_equation :
  forall (n k : nat) (H : 0 < k),
    div n k H =
    if le_lt_dec k n then S (div (n - k) k H) else 0.
Proof.
Admitted.

(* TODO: pursue general recursion. *)

Inductive f91_graph : nat -> nat -> Type :=
    | f91_graph_le100 :
        forall n r1 r2 : nat, n <= 100 ->
          f91_graph (11 + n) r1 -> f91_graph r1 r2 -> f91_graph n r2
    | f91_graph_gt100 :
        forall n : nat, 100 < n ->
          f91_graph n (n - 10).

Inductive f91_dom : nat -> Type :=
    | f91_dom_le100 :
        forall n : nat, n <= 100 ->
          f91_dom (11 + n) ->
          (forall r : nat, f91_graph (11 + n) r -> f91_dom r) ->
            f91_dom n
    | f91_dom_gt100 :
        forall n : nat, 100 < n ->
          f91_dom n.

Fixpoint f91_fun {n : nat} (H : f91_dom n) : {r : nat & f91_graph n r}.
Proof.
  destruct H as [n H_le100 | n H_gt100].
    destruct (f91_fun _ H) as [r1 Hr1].
      destruct (f91_fun _ (f _ Hr1)) as [r2 Hr2].
        exists r2. apply f91_graph_le100 with (r1 := r1); assumption.
    exists (n - 10). constructor. assumption.
Defined.

Lemma f91_graph_f91_dom_1 :
  forall n r : nat,
    f91_graph n r -> f91_dom n.
Proof.
Abort.

Lemma f91_dom_all :
  forall n : nat, f91_dom n.
Proof.
Abort.