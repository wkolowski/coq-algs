Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export BTree.
Require Export LinDec.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : LinDec) : Type := BTree A.

Function bigger {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node v l r =>
        if v <=? pivot
        then bigger pivot r
        else
          match l with
              | empty => l
              | node v' l' r' =>
                  if v' <=? pivot
                  then node v (bigger pivot r') r
                  else node v' (bigger pivot l') (node v r' r)
          end
end.

Function smaller {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A := h.

Function partition {A : LinDec} (pivot : A) (h : SplayHeap A)
  : SplayHeap A * SplayHeap A :=
match h with
    | empty => (empty, empty)
    | node x a b =>
        if x <=? pivot
        then
          match b with
              | empty => (h, empty)
              | node y b1 b2 =>
                  if y <=? pivot
                  then
                    let '(small, big) := partition pivot b2
                    in (node y (node x a b1) small, big)
                  else
                    let '(small, big) := partition pivot b1
                    in (node x a small, node y big b2)
          end
        else
          match a with
              | empty => (empty, h)
              | node y a1 a2 =>
                  if y <=? pivot
                  then
                    let '(small, big) := partition pivot a2
                    in (node y a1 small, node x big b)
                  else
                    let '(small, big) := partition pivot a1
                    in (small, node y big (node x a2 b))
          end
end.

Definition insert {A : LinDec} (x : A) (h : SplayHeap A) : SplayHeap A :=
  let (smaller, bigger) := partition x h in node x smaller bigger.

Function findMin {A : LinDec} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin l
end.

Function deleteMin {A : LinDec} (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin' {A : LinDec} (h : SplayHeap A)
  : option A * SplayHeap A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.