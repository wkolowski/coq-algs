Require Import List.
Import ListNotations.

Fixpoint nth {A : Type} (n : nat) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match n with
            | 0 => Some h
            | S n' => nth n' t
        end
end.

Definition sorted {A : Type} (l : list nat) : Prop :=
  forall i j : nat, i <= j ->
    forall n m : nat,
      nth i l = Some n -> nth j l = Some m -> n <= m.

Print nat.
(*
Inductive nat : Set := O : nat | S : nat -> nat
*)

Print le.
(*
Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m
*)

Print list.
(*
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A
*)