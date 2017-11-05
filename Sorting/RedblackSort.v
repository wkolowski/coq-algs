Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RedBlack.

Function toList {A : Type} (t : RBTree A) : list A :=
match t with
    | E => []
    | T _ l v r => toList l ++ v :: toList r
end.

Fixpoint fromList {A : LinDec} (l : list A) : RBTree A :=
match l with
    | [] => E
    | h :: t => ins h (fromList t)
end.

Fixpoint toList'_aux {A : Type} (t : RBTree A) (acc : list A) : list A :=
match t with
    | E => acc
    | T _ l v r => toList'_aux l (v :: toList'_aux r acc)
end.

Definition toList' {A : Type} (t : RBTree A) : list A := toList'_aux t [].

Definition fromList' {A : LinDec} (l : list A) : RBTree A :=
  fold_left (fun t x => ins x t) l E.

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

Definition redblackSort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Definition redblackSort' (A : LinDec) (l : list A) : list A :=
  toList' (fromList' l).

Require Import ListLemmas.

Time Compute redblackSort natle (cycle 200 testl).
Time Compute redblackSort' natle (cycle 200 testl).