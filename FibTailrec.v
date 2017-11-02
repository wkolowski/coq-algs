Require Export Coq.Program.Wf.
Require Export Recdef.

Inductive fib_contract (f: nat -> nat) : Prop :=
    | contract : f 0 = 0 -> f 1 = 1 ->
        (forall n : nat, f (S (S n)) = f n + f (S n)) -> fib_contract f.

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n' + fib n''
end.

Function fib_aux (n a b : nat) : nat :=
match n with
    | 0 => a
    | S n' => fib_aux n' b (a + b)
end.

Lemma fib_aux_0 :
  forall a b : nat, fib_aux 0 a b = a.
Proof.
  reflexivity.
Qed.

Lemma fib_aux_1 :
  forall a b : nat, fib_aux 1 a b = b.
Proof.
  reflexivity.
Qed.

Lemma fib_aux_2 :
  forall a b : nat, fib_aux 2 a b = a + b.
Proof.
  reflexivity.
Qed.

Theorem nat_ind2 :
  forall (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (HSS : forall n : nat, P n -> P (S (S n))),
    forall n : nat, P n.
Proof.
  fix IH 5. destruct n as [| [| n']]; auto.
    apply HSS. apply IH; auto.
Defined.

Lemma fib_aux_front :
  forall n a b : nat, fib_aux n (a + b) (b + (a + b)) =
    a + fib_aux n b (b + b).
Proof.
  induction n using nat_ind2; auto.
    Require Import Omega. intros. cbn. omega.
    intros. cbn. rewrite !IHn. rewrite plus_assoc_reverse. do 2 f_equal.
      replace (b + (a + b)) with (a + (b + b)).
Abort.

Lemma fib_aux_SS :
  forall n a b : nat, fib_aux (S (S n)) a b =
    fib_aux n a b + fib_aux (S n) a b.
Proof.
  induction n using nat_ind2; intros; auto.
    rewrite 2 fib_aux_equation.
    change (fib_aux (S (S (S n))) a b) with (fib_aux (S (S n)) b (a + b)).
      rewrite !IHn.
      simpl.
Abort.

Definition fib' (n : nat) := fib_aux n 0 1.

Theorem fib'_fib : forall n : nat, fib' n = fib n.
Proof.
  unfold fib'. induction n as [| n']; simpl.
    auto.
    destruct n'.
      simpl. auto.
Restart.
  unfold fib'. remember 0 as a. remember 1 as b.
  intro n. generalize dependent b. generalize dependent a.
  generalize dependent n.
  apply (well_founded_ind Wf_nat.lt_wf
    (fun n : nat => forall a : nat, a = 0 -> forall b : nat, b = 1 -> fib_aux n a (S a) = fib n)).
  destruct x as [| [| n']]; intros IH **.
    compute. auto.
    compute. auto.
    simpl. destruct n'.
      subst. compute. auto.