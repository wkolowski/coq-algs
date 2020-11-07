Require Export RedBlack.
Require Import ListLemmas.

Fixpoint toList'_aux {A : Type} (t : RBTree A) (acc : list A) : list A :=
match t with
    | E => acc
    | N _ l v r => toList'_aux l (v :: toList'_aux r acc)
end.

Definition toList' {A : Type} (t : RBTree A) : list A := toList'_aux t [].

Definition fromList' {A : TrichDec} (l : list A) : RBTree A :=
  fold_left (fun t x => ins x t) l E.

Definition fromList'' {A : TrichDec} (l : list A) : RBTree A :=
  fold_right (fun h t => ins h t) E l.

Lemma toList'_aux_spec :
  forall (A : Type) (t : RBTree A) (acc : list A),
    toList'_aux t acc = toList t ++ acc.
Proof.
  induction t; cbn; intros.
    trivial.
    rewrite IHt1, IHt2, <- app_assoc, <- app_comm_cons. trivial.
Qed.

Theorem toList'_spec : @toList' = @toList color.
Proof.
  ext A. ext t. unfold toList'.
  rewrite toList'_aux_spec, app_nil_r. trivial.
Qed.

#[refine]
Instance Sort_redblackSort (A : TrichDec) : Sort trich_le :=
{
    sort := @redblackSort A;
    Sorted_sort := @Sorted_redblackSort A;
}.
Proof.
  intros. apply perm_Permutation. rewrite <- perm_redblackSort. reflexivity.
Defined.