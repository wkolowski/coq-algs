Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Arith.

Require Export Permutation.
Require Export Perm.
Require Export InsertionSort.

Require Export List.
Export ListNotations.

Require Export Equality.

Set Implicit Arguments.

Ltac inList x l :=
match l with
    | [] => false
    | x :: _ => true
    | _ :: ?l' => inList x l'
end.

Ltac addToList x l :=
  let b := inList x l in
match b with
    | true => l
    | false => constr:(x :: l)
end.

Ltac lookup x l :=
match l with
    | x :: _ => constr:(0)
    | _ :: ?l' => let n := lookup x l' in constr:(S n)
end.

Definition Env (X : Type) : Type := list X.