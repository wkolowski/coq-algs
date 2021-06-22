

Require Export CoqAlgs.Base.

Set Implicit Arguments.

Class CMon : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    neutr : carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z;
    neutr_l : forall x : carrier, op neutr x = x;
    neutr_r : forall x : carrier, op x neutr = x;
    comm : forall x y : carrier, op x y = op y x
}.

Coercion carrier : CMon >-> Sortclass.

Fixpoint expDenoteL {X : CMon} (envX : Env X) (l : list nat) : X :=
match l with
    | [] => neutr
    | h :: t => op (nth h envX neutr) (expDenoteL envX t)
end.

Lemma expDenoteL_app :
  forall (X : CMon) (envX : Env X) (l1 l2 : list nat),
    expDenoteL envX (l1 ++ l2) = op (expDenoteL envX l1) (expDenoteL envX l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Lemma expDenoteL_Permutation :
  forall (X : CMon) (envX : Env X) (l1 l2 : list nat),
    Permutation l1 l2 -> expDenoteL envX l1 = expDenoteL envX l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    rewrite !assoc. rewrite (comm (nth y envX neutr)). reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.