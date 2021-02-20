Require Export List Permutation Lia Arith.
Export ListNotations.

Print list.
(*
Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A
*)

Print app.
(*
fix app {A : Type} (l1 l2 : list A) {struct l1} : list A :=
match l1 with
  | [] => l2
  | h :: t => h :: app t l2
end
*)

Record rev_spec {A : Type} (f : list A -> list A) : Prop :=
{
    f_app   : forall l1 l2 : list A, f (l1 ++ l2) = f l2 ++ f l1;
    f_singl : forall x : A, f [x] = [x];
}.

Theorem rev_spec_unique :
  forall {A : Type} (f g : list A -> list A),
    rev_spec f -> rev_spec g ->
      forall l : list A, f l = g l.
Proof.
  intros A f g [Hfc Hfs] [Hgc Hgs].
  induction l as [| h t]; cbn.
    specialize (Hfc [] []); specialize (Hgc [] []).
      apply (f_equal (@length _)) in Hfc;
      apply (f_equal (@length _)) in Hgc.
      cbn in *. rewrite app_length in *.
      destruct (f []), (g []).
        reflexivity.
        1-3: cbn in *; lia.
    change (h :: t) with ([h] ++ t).
      rewrite Hfc, Hgc, Hfs, Hgs, IHt. reflexivity.
Qed.