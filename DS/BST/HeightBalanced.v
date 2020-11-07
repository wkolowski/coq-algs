Require Export RCCBase.
Require Export TrichDec.
Require Export Data.EBTree.

Definition Tree (A : Type) : Type := EBTree nat A.

Definition height' {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N h _ _ _ => h
end.

Definition balance {A : Type} (l : Tree A) (v : A) (r : Tree A) : Tree A :=
  N (1 + max (height l) (height r)) l v r.

Function rotateLR {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ (N _ a y b) x c => balance a y (balance b x c)
    | _ => t
end.

Function rotateRL {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ a x (N _ b y c) => balance (balance a x b) y c
    | _ => t
end.

Function rebalance {A : Type} (l : Tree A) (v : A) (r : Tree A) : Tree A :=
match height l <?> height r with
    | Lt =>
        match r with
            | N _ a x b => balance (balance l x a) v b
            | _ => balance l v r
        end
    | Eq => balance l v r
    | Gt =>
        match l with
            | N _ a x b => balance a v (balance b x r)
            | _ => balance l v r
        end
end.

Function insert {A : TrichDec} (x : A) (t : Tree A) : Tree A :=
match t with
    | E => N 1 E x E
    | N _ l v r =>
        if x ≤? v
        then rebalance (insert x l) v r
        else rebalance l v (insert x r)
end.

Lemma height_balance :
  forall (A : Type) (v : A) (l r : Tree A),
    height (balance l v r) = 1 + max (height l) (height r).
Proof.
  cbn. reflexivity.
Qed.

(* TODO: height_rotate *)

Lemma height_rebalance :
  forall (A : Type) (v : A) (l r : Tree A),
    height (rebalance l v r) <= 1 + max (height l) (height r).
Proof.
  intros. functional induction @rebalance A l v r; trich; cbn in *.
    destruct (height b).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
    destruct (height r).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
Qed.

Lemma height_insert :
  forall (A : TrichDec) (x : A) (t : Tree A),
    height (insert x t) <= 1 + height t.
Proof.
  intros. functional induction insert x t;
  cbn; rewrite ?height_rebalance; lia.
Qed.