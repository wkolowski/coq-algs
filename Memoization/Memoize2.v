Require Import Control.

Set Universe Polymorphism.


Inductive Memoize (A : Type) : Type :=
    | Pure : A -> Memoize A
    | Call : forall B : Type, (B -> Memoize A) -> B -> Memoize A
    | Bind : forall B : Type, Memoize B -> (B -> Memoize A) -> Memoize A.

Arguments Pure {A}.
Arguments Call {A B}.
Arguments Bind {A B}.

Notation "x '<-' e1 ; e2" := (bind e1 (fun x => e2))
  (right associativity, at level 42, only parsing).
Notation "'do' e" := e.

Fixpoint fib (n : nat) : Memoize nat :=
match n with
    | 0 => Pure 0
    | 1 => Pure 1
    | S (S n2 as n1) =>
        Bind (fib n2) (fun r2 : nat =>
        Bind (fib n1) (fun r1 : nat => Pure (r2 + r1)))
end.

Fixpoint extract {A : Type} (x : Memoize A) : A :=
match x with
    | Pure a => a
    | Call f x => extract (f x)
    | Bind x f => extract (f (extract x))
end.

Compute extract (fib 20).

Definition fibF (self : nat -> Memoize nat) (n : nat) : Memoize nat :=
match n with
    | 0 => Pure 0
    | 1 => Pure 1
    | S (S n2 as n1) =>
        Bind (Call self n2) (fun r2 : nat =>
        Bind (Call self n1) (fun r1 : nat => Pure (r2 + r1)))
end.

Print Memoize.

Fixpoint fmap_Memoize
  {A B : Type} (f : A -> B) (x : Memoize A) : Memoize B :=
match x with
    | Pure a => Pure (f a)
    | @Call _ X g y => Call (fun x : X => fmap_Memoize f (g x)) y
    | @Bind _ X y g => Bind y (fun x : X => fmap_Memoize f (g x))
end.

Instance Functor_Memoize : Functor Memoize :=
{
    fmap := @fmap_Memoize;
}.
Proof.
  intros. ext x. induction x; cbn.
    reflexivity.
    unfold id. f_equal. ext x. apply H.
    unfold id. f_equal. ext a. apply H.
  intros. ext x. induction x; cbn.
    reflexivity.
    f_equal. ext x. apply H.
    f_equal. ext x'. apply H.
Defined.

Definition pure_Memoize {A : Type} (x : A) : Memoize A := Pure x.

Definition ap_Memoize
  {A B : Type} (f : Memoize (A -> B)) (x : Memoize A) : Memoize B :=
    Bind f (fun f : A -> B => Bind x (fun x : A => Call (f .> Pure) x)).