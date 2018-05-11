Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export BTree.
Require Export LinDec.
Require Export Sorting.Sort.

Require Export TrichDec.

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : nat -> A -> Tree A -> Tree A -> Tree A.

Arguments E {A}.
Arguments N {A} _ _ _ _.

(*Definition height {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N h _ _ _ => h
end.*)

Fixpoint height' {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N _ _ l r => 1 + max (height' l) (height' r)
end.

Definition balance {A : Type} (v : A) (l r : Tree A) : Tree A :=
  N (1 + max (height' l) (height' r)) v l r.

Function rotateLR {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ x (N _ y a b) c => balance y a (balance x b c)
    | _ => t
end.

Function rotateRL {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ x a (N _ y b c) => balance y (balance x a b) c
    | _ => t
end.

Function rebalance {A : Type} (v : A) (l r : Tree A) : Tree A :=
match height' l <?> height' r with
    | Lt =>
        match r with
            | N _ x a b => balance v (balance x l a) b
            | _ => balance v l r
        end
    | Eq => balance v l r
    | Gt =>
        match l with
            | N _ x a b => balance v a (balance x b r)
            | _ => balance v l r
        end
end.

Function insert {A : LinDec} (x : A) (t : Tree A) : Tree A :=
match t with
    | E => N 1 x E E
    | N _ v l r =>
        if x <=? v
        then rebalance v (insert x l) r
        else rebalance v l (insert x r)
end.

Lemma height'_balance :
  forall (A : Type) (v : A) (l r : Tree A),
    height' (balance v l r) = 1 + max (height' l) (height' r).
Proof.
  cbn. reflexivity.
Qed.

(*Lemma height_rotateLR :
  forall (A : Type) (t : Tree A),
    height' (rotateLR t) <= height' t.
Proof.
  intros. functional induction @rotateLR A t.
    rewrite !height'_balance. cbn. destruct (height' c).
      rewrite Max.max_0_r. apply le_n_S.
        apply le_trans with (max (S (height' a)) (S (height' b))).
          apply Nat.max_le_compat_r. apply le_S. apply le_n.
          cbn. reflexivity.
      apply le_n_S. Search (max _ _ <= _ <-> _). rewrite ?Nat.max_lub_iff. rewrite Nat.max_le_iff. destruct (height' b); cbn.
        rewrite Max.max_0_r. apply le_n_S.

*)

Lemma height_rebalance :
  forall (A : Type) (v : A) (l r : Tree A),
    height' (rebalance v l r) <= 1 + max (height' l) (height' r).
Proof.
  intros. functional induction @rebalance A v l r; trich; cbn in *.
    destruct (height' b).
      apply le_n_S. rewrite Max.max_0_r in *. apply le_S_n in e.
        rewrite ?Max.max_r; omega.
      apply le_n_S. apply le_S_n in e. rewrite !Nat.max_le_iff.
        right. apply le_n_S.
          repeat apply Max.max_lub; rewrite ?Nat.max_le_iff in *; omega.
    destruct (height' r).
      apply le_n_S. rewrite Max.max_0_r in *. apply le_S_n in e.
        apply le_trans with (max (S (height' a)) (S (height' b))).
          rewrite Nat.max_le_compat_r.
            reflexivity.
            apply le_S, le_n.
          cbn. reflexivity.
      apply le_n_S. apply lt_S_n in e.
        repeat apply Max.max_lub; rewrite ?Nat.max_le_iff in *.
          apply le_S. rewrite <- Max.max_assoc. apply Max.le_max_l.
          apply le_n_S. unfold lt in e.
            repeat apply Max.max_lub; rewrite ?Nat.max_le_iff in *.
             1-2: firstorder.
Qed.

Lemma height_insert :
  forall (A : LinDec) (x : A) (t : Tree A),
    height' (insert x t) <= 1 + height' t.
Proof.
  intros. functional induction @insert A x t; cbn.
    reflexivity.
    rewrite height_rebalance.