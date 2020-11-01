Require Export RCCBase.

Require Export BTree.
Require Export TrichDec.
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

Function insert {A : TrichDec} (x : A) (t : Tree A) : Tree A :=
match t with
    | E => N 1 x E E
    | N _ v l r =>
        if x ≤? v
        then rebalance v (insert x l) r
        else rebalance v l (insert x r)
end.

Lemma height'_balance :
  forall (A : Type) (v : A) (l r : Tree A),
    height' (balance v l r) = 1 + max (height' l) (height' r).
Proof.
  cbn. reflexivity.
Qed.

(* TODO: height_rotate *)

Lemma height_rebalance :
  forall (A : Type) (v : A) (l r : Tree A),
    height' (rebalance v l r) <= 1 + max (height' l) (height' r).
Proof.
  intros. functional induction @rebalance A v l r; trich; cbn in *.
    destruct (height' b).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
    destruct (height' r).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
Qed.

Lemma height_insert :
  forall (A : TrichDec) (x : A) (t : Tree A),
    height' (insert x t) <= 1 + height' t.
Proof.
  intros. functional induction insert x t;
  cbn; rewrite ?height_rebalance; lia.
Qed.