Print list.
(*
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A
*)

Require Import List.
Import ListNotations.

Print app.
(*
fun A : Type =>
fix app (l m : list A) {struct l} : list A :=
  match l with
  | [] => m
  | a :: l1 => a :: app l1 m
  end
    : forall A : Type, list A -> list A -> list A
*)

Record rev_spec {A : Type} (f : list A -> list A) : Prop :=
{
    f_app_comm :
      forall l1 l2 : list A, f (l1 ++ l2) = f l2 ++ f l1;
    f_singl :
      forall x : A, f [x] = [x];
}.

Require Import Lia.

Lemma rev_unique :
  forall {A : Type} (f g : list A -> list A),
    rev_spec f -> rev_spec g ->
      forall l : list A, f l = g l.
Proof.
  intros A f g [Hfc Hfs] [Hgc Hgs].
  induction l as [| h t]; cbn.
    specialize (Hfc [] []); specialize (Hgc [] []); cbn in *.
      apply (f_equal (@length _)) in Hfc;
      apply (f_equal (@length _)) in Hgc.
      rewrite app_length in *.
      destruct (f []), (g []).
        reflexivity.
        1-3: cbn in *; lia.
    change (h :: t) with ([h] ++ t).
      rewrite Hfc, Hgc, Hfs, Hgs, IHt. reflexivity.
Qed.