Require Import List.
Import ListNotations.

Fixpoint nth {A : Type} (n : nat) (l : list A) : option A :=
match l, n with
    | []    , _    => None
    | h :: _, 0    => Some h
    | _ :: t, S n' => nth n' t
end.

Definition sorted {A : Type} (l : list nat) : Prop :=
  forall i j : nat, i <= j ->
    forall n m : nat,
      nth i l = Some n -> nth j l = Some m -> n <= m.