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

Definition holds (n : nat) (env : Env Prop) : Prop := nth n env False.

Definition Proofs : Type := list nat.

Fixpoint allTrue (env : Env Prop) (proofs : Proofs) : Prop :=
match proofs with
    | [] => True
    | h :: t => holds h env /\ allTrue env t
end.

Theorem find_spec :
  forall (n : nat) (env : Env Prop) (proofs : Proofs),
    allTrue env proofs -> In n proofs -> holds n env.
Proof.
  induction proofs as [| h t]; cbn.
    inversion 2.
    do 2 destruct 1; subst.
      unfold holds in H. apply H.
      apply IHt; assumption.
Qed.

Inductive solution (P : Prop) : Type :=
    | Yes' : P -> solution P
    | No' : solution P.

Arguments Yes' [P] _.
Arguments No' [P].

Notation "'Yes'" := (Yes' _).
Notation "'No'" := No'.

Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x && y" := (if x then Reduce y else No).
Notation "x || y" := (if x then Yes else Reduce y).

Definition unwrap {P : Prop} (s : solution P) :=
match s return if s then P else Prop with
    | Yes' p => p
    | _ => True
end.