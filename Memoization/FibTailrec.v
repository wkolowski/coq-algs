Require Import Omega.

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n' + fib n''
end.

Fixpoint fib_aux (n a b : nat) : nat :=
match n with
    | 0 => a
    | S n' => fib_aux n' b (a + b)
end.

Definition fib' (n : nat) := fib_aux n 0 1.

Lemma fib_aux_spec :
  forall n k : nat, fib_aux (1 + k) (fib n) (fib (1 + n)) = fib (1 + k + n).
Proof.
  intros. generalize dependent n.
  induction k; intros.
    cbn. trivial.
    change (fib_aux (S k) (fib (1 + n)) (fib n + fib (1 + n)) =
            fib (1 + S k + n)).
      replace (fib n + fib (1 + n)) with (fib (2 + n)).
        rewrite IHk. f_equal. omega.
        cbn. omega.
Qed.

Theorem fib'_fib : forall n : nat, fib' n = fib n.
Proof.
  intros. unfold fib'. destruct n.
    cbn. trivial.
    change 1 with (fib 1). change 0 with (fib 0).
      rewrite fib_aux_spec. f_equal. cbn. omega.
Qed.