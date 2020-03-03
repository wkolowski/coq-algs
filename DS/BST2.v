Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

(*
Require Import ssreflect.
*)

Check compare.
Print comparison.
Search comparison.
Print CompareSpec.
Search compare.
Print compare.

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison} : BTree A -> Type :=
    | isBST_empty : isBST empty
    | isBST_node_l :
        forall (v x : A) (ll lr : BTree A),
          isBST (node x ll lr) -> cmp x v = Lt ->
            isBST (node v (node x ll lr) empty)
    | isBST_node_r :
        forall (v x : A) (rl rr : BTree A),
          isBST (node x rl rr) -> cmp x v = Gt ->
            isBST (node v empty (node x rl rr))
    | isBST_node_lr :
        forall (v xl xr : A) (ll lr rl rr : BTree A),
          isBST (node xl ll lr) -> cmp xl v = Lt ->
          isBST (node xr rl rr) -> cmp xr v = Gt ->
            isBST (node v (node xl ll lr) (node xr rl rr)).

Arguments isBST {A} _ _.

Hint Constructors elem isBST.

Record BST {A : Type} (cmp : A -> A -> comparison) : Type :=
{
    tree :> BTree A;
    prop : isBST cmp tree
}.

Fixpoint elem_dec
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        match cmp x v with
            | Lt => elem_dec cmp x l
            | Eq => true
            | Gt => elem_dec cmp x r
        end
end.

Lemma elem_dec_spec :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    (forall x y : A, CompareSpec (x = y) (cmp x y = Lt) (cmp x y = Gt) (cmp x y)) ->
      isBST cmp t -> BoolSpec (elem x t) (~ elem x t) (elem_dec cmp x t).
Proof.
  intros A cmp x t spec H.
  revert t H.
  induction t; intros; cbn.
    constructor. inversion 1.
    destruct (spec x a); subst.
      constructor. constructor.
      destruct IHt1.
        admit.
        do 2 constructor. assumption.
        constructor. inversion 1; subst.
          Search CompareSpec.
Abort.

Fixpoint BTree_ins
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => node x empty empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (BTree_ins cmp x l) r
            | Eq => node x l r
            | Gt => node v l (BTree_ins cmp x r)
        end
end.

(*
Lemma elem_ins : forall (A : LinDec) (x a : A) (t : BTree A),
    elem x (BTree_ins a t) -> x = a \/ elem x t.
Proof.
  move=> A x a t. elim: t => [| v l Hl r Hr] //=.
    inv 1.
    dec; inv H.
      case: Hl; auto.
      case: Hr; auto.
Qed.
*)

Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

(** [fromList] and its variants. *)
(*Function fromList (A : LinDec) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => BTree_ins h (fromList A t)
end.
*)