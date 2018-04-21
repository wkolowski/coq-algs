Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RedBlack.

Fixpoint toList'_aux {A : Type} (t : RBTree A) (acc : list A) : list A :=
match t with
    | E => acc
    | T _ l v r => toList'_aux l (v :: toList'_aux r acc)
end.

Definition toList' {A : Type} (t : RBTree A) : list A := toList'_aux t [].

Definition fromList' {A : LinDec} (l : list A) : RBTree A :=
  fold_left (fun t x => ins x t) l E.

Definition fromList'' {A : LinDec} (l : list A) : RBTree A :=
  fold_right (fun h t => ins h t) E l.

Lemma toList'_aux_spec :
  forall (A : Type) (t : RBTree A) (acc : list A),
    toList'_aux t acc = toList t ++ acc.
Proof.
  induction t; cbn; intros.
    trivial.
    rewrite IHt1, IHt2, <- app_assoc, <- app_comm_cons. trivial.
Qed.

Theorem toList'_spec : @toList' = @toList.
Proof.
  ext A. ext t. unfold toList'.
  rewrite toList'_aux_spec, app_nil_r. trivial.
Qed.

Require Import ListLemmas.

(*
Time Eval native_compute in redblackSort natle (cycle 2000 testl). (* 1.5 *)
Time Eval native_compute in redblackSort' natle (cycle 2000 testl). (* 1.4 *)
*)






Instance Sort_redblackSort : Sort :=
{
    sort := @redblackSort;
    sort_sorted := @redblackSort_sorted;
    sort_perm := @redblackSort_perm;
}.