Require Export RCCBase.

Inductive EBTree (M A : Type) : Type :=
    | E : EBTree M A
    | N : M -> EBTree M A -> A -> EBTree M A -> EBTree M A.

Arguments E {M A}.
Arguments N {M A} _ _ _ _.

Inductive Elem {M A : Type} (x : A) : EBTree M A -> Prop :=
    | Elem_root :
        forall (m : M) (l r : EBTree M A),
        Elem x (N m l x r)
    | Elem_left :
        forall (m : M) (v : A) (l r : EBTree M A),
        Elem x l -> Elem x (N m l v r)
    | Elem_right :
        forall (m : M) (v : A) (l r : EBTree M A),
        Elem x r -> Elem x (N m l v r).

Hint Constructors EBTree Elem : core.

Lemma Elem_N :
  forall {M A : Type} (m : M) (x v : A) (l r : EBTree M A),
    Elem x (N m l v r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  split; inv 1. inv H0.
Qed.

Lemma Elem_inv :
  forall (M A : Type) (P : A -> Prop) (m : M) (v : A) (l r : EBTree M A),
    (forall x : A, Elem x (N m l v r) -> P x) ->
      P v /\
      (forall x : A, Elem x l -> P x) /\
      (forall x : A, Elem x r -> P x).
Proof.
  repeat split; intros; apply H; auto.
Qed.

Ltac Elem :=
repeat match goal with
    | |- Elem ?x (N _ _ ?x _) => constructor
    | H : Elem _ E |- _ => inv H
    | H : Elem _ (N _ E _ E) |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : forall _, Elem _ (N _ _ _ _) -> _ |- _ =>
            apply Elem_inv in H; decompose [and] H; clear H
end; auto.

Ltac Elem' :=
repeat match goal with
    | |- Elem ?x (N _ _ ?x _) => constructor
    | H : Elem _ E             |- _ => inv H
    | H : Elem _ (N _ _ _ _)   |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : Elem _ _ \/ Elem _ _ |- _ => destruct H
    | H : forall _, Elem _ (N _ _ _ _) -> _ |- _ =>
            apply Elem_inv in H; decompose [and] H; clear H
    | H1 : forall _, Elem _ _ -> _, H2 : Elem _ _ |- _ =>
        specialize (H1 _ H2)
end; auto.

(* Inductive isBST {A : Ord} : EBTree M A -> Prop :=
    | isBST_E : isBST E
    | isBST_T : forall (c : color) (v : A) (l r : EBTree M A),
        (forall x : A, Elem x l -> x ≤ v) -> isBST l ->
        (forall x : A, Elem x r -> v ≤ x) -> isBST r ->
        isBST (T c l v r).
 *)
Definition isEmpty {M A : Type} (t : EBTree M A) : bool :=
match t with
    | E => true
    | _ => false
end.

Fixpoint height {M A : Type} (t : EBTree M A) : nat :=
match t with
    | E => 0
    | N _ l _ r => 1 + max (height l) (height r)
end.

Function toList {M A : Type} (t : EBTree M A) : list A :=
match t with
    | E => []
    | N _ l v r => toList l ++ v :: toList r
end.

Fixpoint countEBT {M A : Type} (p : A -> bool) (t : EBTree M A) : nat :=
match t with
    | E => 0
    | N _ l v r =>
(*         (if p v then S else id) (countEBT p l + countEBT p r) *)
        (if p v then 1 else 0) + countEBT p l + countEBT p r
end.