Require Export CMon.
Require Export Sorting.InsertionSort.
Require Export Sorting.SortSpec.

Set Implicit Arguments.

Inductive exp (X : CMon) : Type :=
    | Id : exp X
    | Var : nat -> exp X
    | Op : exp X -> exp X -> exp X.

Arguments Id  {X}.
Arguments Var {X} _.
Arguments Op  {X} _ _.

Require Import CoqMTL.Base.

Fixpoint expDenote {X : CMon} (envX : Env X) (e : exp X) : X -> X :=
match e with
    | Id => id
    | Var n => fun x => op (nth n envX neutr) x
    | Op e1 e2 => expDenote envX e1 .> expDenote envX e2
end.

Definition reify {X : CMon} (f : X -> X) : X := f neutr.

Definition nbe {X : CMon} (e : exp X) : X := reify (expDenote [] e).

Section test.

Variables
  (X : CMon)
  (a b c : X).

(*
Goal
  forall (X : CMon) (a b c d : X),
    op a (op b (op c d)) = op (op (op a b) c) d.
Proof.
  intros.
  let e := constr:(nbe (Op a0 (Op b0 (Op c0 d))))
  in pose e.
  let e := constr:(Op (Op Id (Var 1)) (Op (Var 2) (Var 3)))
  in pose e.
  let e' := constr:(nbe e) in pose e'.
  cbn in c0.
  in pose x.
  cbn in c0. unfold compose in c0.
  let x := constr:(reify c0) in pose x.
  unfold c0, reify in c1. compute in c1. destruct X. cbn in *. cbn in c1.
Abort.
*)
End test.