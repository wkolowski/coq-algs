Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Export RCCBase.

Inductive Tree (A : Type) : Type :=
    | T : nat -> A -> list (Tree A) -> Tree A.

Arguments T [A] _ _ _.

Definition Heap (A : Type) : Type := list (Tree A).

Definition empty {A : Type} : Heap A := [].

Definition isEmpty {A : Type} (h : Heap A) : bool :=
match h with
    | [] => true
    | _ => false
end.

Definition rank {A : Type} (t : Tree A) : nat :=
match t with
    | T r _ _ => r
end.

Definition root {A : Type} (t : Tree A) : A :=
match t with
    | T _ x _ => x
end.

Function link {A : LinDec} (t1 t2 : Tree A) : Tree A :=
match t1, t2 with
    | T r x ts1, T _ y ts2 =>
        if x <=? y
        then T (S r) x (t2 :: ts1)
        else T (S r) y (t1 :: ts2)
end.

Fixpoint insTree {A : LinDec} (t : Tree A) (h : Heap A) : Heap A :=
match h with
    | [] => [t]
    | t' :: h' =>
        if rank t <? rank t'
        then t :: h
        else insTree (link t t') h'
end.

Definition insert {A : LinDec} (x : A) (h : Heap A) : Heap A :=
  insTree (T 0 x []) h.

Fixpoint merge {A : LinDec} (h1 h2 : Heap A) : Heap A :=
match h1 with
    | [] => h2
    | t1 :: h1' =>
        let
          aux := fix aux (h2 : Heap A) : Heap A :=
          match h2 with
              | [] => h1
              | t2 :: h2' =>
                  if rank t1 <? rank t2
                  then t1 :: merge h1' h2
                  else
                    if rank t2 <? rank t1
                    then t2 :: aux h2'
                    else insTree (link t1 t2) (merge h1' h2')
          end
        in aux h2
end.

(*Fixpoint merge {A : LinDec} (h1 h2 : Heap A) : Heap A :=
match h1, h2 with
    | [], _ => h2
    | _, [] => h1
    | t1 :: h1', t2 :: h2' =>
        if rank t1 <? rank t2
        then t1 :: merge h1' h2
        else
          if rank t2 <? rank t1
          then t2 :: merge h1 h2'
          else insTree (link t1 t2) (merge h1' h2')
end.*)

Lemma merge_spec :
  forall (A : LinDec) (h1 h2 : Heap A),
    merge h1 h2 =
    match h1, h2 with
        | [], _ => h2
        | _, [] => h1
        | t1 :: h1', t2 :: h2' =>
            if rank t1 <? rank t2
            then t1 :: merge h1' h2
            else
              if rank t2 <? rank t1
              then t2 :: merge h1 h2'
              else insTree (link t1 t2) (merge h1' h2')
    end.
Proof.
  destruct h1, h2; reflexivity.
Qed.

Fixpoint removeMinTree
  {A : LinDec} (h : Heap A) : option (Tree A * Heap A) :=
match h with
    | [] => None
    | [t] => Some (t, [])
    | t :: h' =>
        match removeMinTree h' with
            | None => None
            | Some (t', h'') =>
                if (root t <=? root t') && negb (root t =? root t')
                then Some (t, h')
                else Some (t', t :: h'')
        end
end.

Definition findMin {A : LinDec} (h : Heap A) : option A :=
match removeMinTree h with
    | None => None
    | Some (t, _) => Some (root t)
end.

Definition deleteMin {A : LinDec} (h : Heap A) : option (Heap A) :=
match removeMinTree h with
    | None => None
    | Some (T _ x h1, h2) => Some (merge h1 h2)
end.

Import PriorityQueue.