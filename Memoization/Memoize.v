Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n' + fib n''
end.

Fixpoint fromTo (a b : nat) : list nat :=
  if b <? a then [] else
match b with
    | 0 => [0]
    | S b' => fromTo a b' ++ [b]
end.

Definition test := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Time Compute map fib (fromTo 0 24).

Time Compute fib 24.

Fixpoint find {A : Type} (n : nat) (l : list (nat * A)) : option A :=
match l with
    | [] => None
    | (m, v) :: t => if n =? m then Some v else find n t
end.

Axiom wut : False.

Instance KVP (A : LinDec) (B : Type) : LinDec :=
{
    carrier := A * B;
    leq p1 p2 := fst p1 ≤ fst p2;
    leqb p1 p2 := fst p1 <=? fst p2;
}.
Proof.
  all: intros; repeat
  match goal with
      | p : _ * _ |- _ => destruct p
  end; cbn in *; dec.
  cut False.
    inversion 1.
    apply wut.
Defined.

Fixpoint aux (n : nat) (acc : list (nat * nat)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        match find n'' acc with
            | None =>
                let a := aux n'' acc in
                let b := aux n' ((n'', a) :: acc) in a + b
            | Some a =>
                match find n' acc with
                    | None =>
                        let b := aux n' acc in a + b
                    | Some b => a + b
                end
        end
end.

Definition fibM n := aux n [(0, 0); (1, 1)].

Compute map fibM test.
Time Compute fibM 24.

Let list_map := map.

Require Import BTree.
Require Import BST.
Require Import TrichDec.

Fixpoint find' {A : TrichDec} {B : Type} (k : A) (t : BTree (KVP A B))
  : option B :=
match t with
    | empty => None
    | node p l r =>
        match k <?> fst p with
            | Lt => find' k l
            | Eq => Some (snd p)
            | Gt => find' k r
        end
end.

Fixpoint aux' (n : nat) (acc : BTree (KVP natle natle)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        match find' n'' acc with
            | None =>
                let a := aux' n'' acc in
                let b := aux' n' (@BTree_ins (KVP natle natle) (n'', a) acc) in a + b
            | Some a =>
                match find' n' acc with
                    | None =>
                        let b := aux' n' acc in a + b
                    | Some b => a + b
                end
        end
end.

Time Compute list_map _ _
  (fun n => aux' n (@fromList (KVP natle natle) [(0, 0); (1, 1)]))
  (fromTo 0 24).

Definition bind {A : TrichDec} {B : Type} (a : A)
  (f : A -> BTree (KVP A B) -> B) (acc : BTree (KVP A B))
  : B * BTree (KVP A B) :=
match find' a acc with
    | None => let b := f a acc in (b, @BTree_ins (KVP A B) (a, b) acc)
    | Some b => (b, acc)
end.

Fixpoint aux2 (n : nat) (acc : BTree (KVP natle natle)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        let '(a, acc') := bind n'' aux2 acc in
        let '(b, acc'') := bind n' aux2 acc' in a + b
end.

Definition fib2M n := aux2 n (@fromList (KVP natle natle) [(0, 0); (1, 1)]).

Time Compute list_map _ _ fib (fromTo 0 24).
Time Compute list_map _ _ fib2M (fromTo 0 24).

Fixpoint wutzor (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n4 as n3) as n2) as n1) =>
        wutzor n4 + wutzor n3 + wutzor n2 + wutzor n1
end.

Fixpoint wutzor' (n : nat) (acc : BTree (KVP natle natle)) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n4 as n3) as n2) as n1) =>
        let (x1, acc1) := bind n4 wutzor' acc in
        let (x2, acc2) := bind n3 wutzor' acc1 in
        let (x3, acc3) := bind n2 wutzor' acc2 in
        let (x4, acc4) := bind n1 wutzor' acc3 in x1 + x2 + x3 + x4
end.


Time Compute wutzor 30.
Time Compute
  wutzor' 30
    (@fromList (KVP natle natle) [(0, 0); (1, 0); (2, 0); (3, 0)]).