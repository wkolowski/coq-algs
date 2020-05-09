Require Import List.
Import ListNotations.

Require Import Lia.

Goal
  forall {A : Type} (f : list A -> list A),
    (forall l1 l2 : list A, f (l1 ++ l2) = f l2 ++ f l1) ->
      forall l : list A, f l = rev l.
Proof.
  induction l as [| h t]; cbn.
    specialize (H [] []). cbn in H.
      apply (f_equal (@length _)) in H. rewrite app_length in H.
      assert (length (f []) = 0) by lia.
      destruct (f []).
        reflexivity.
        inversion H0.
    assert ((forall P : Prop, P \/ ~ P) -> forall x : A, f [x] = [x]).
      intros LEM x. destruct (LEM (exists y : A, x <> y)).
        destruct H0 as [y 
    rewrite <- IHt. <- (H [h] t). cbn in H. rewrite H, ?IHt.
      f_equal.
Qed.