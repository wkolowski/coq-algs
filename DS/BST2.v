Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison} : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          isBST l -> (forall x : A, elem x l -> cmp x v = Lt) ->
          isBST r -> (forall x : A, elem x r -> cmp x v = Gt) ->
            isBST (node v l r).

Arguments isBST {A} _ _.

Hint Constructors elem isBST.

Record BST {A : Type} (cmp : A -> A -> comparison) : Type :=
{
    tree :> BTree A;
    prop : isBST cmp tree
}.

Function elem_dec
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

Function insert
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => node x empty empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (insert cmp x l) r
            | Eq => node x l r
            | Gt => node v l (insert cmp x r)
        end
end.

Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

(** [fromList] and its variants. *)
Fixpoint fromList
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.

Function removeMin
  {A : Type} (cmp : A -> A -> comparison)
  (t : BTree A) : option (A * BTree A) :=
match t with
    | empty => None
    | node x l r =>
        match removeMin cmp l with
            | None => Some (x, r)
            | Some (m, l') => Some (m, node x l' r)
        end
end.

Function BST_remove
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (BST_remove cmp x l) r
            | Gt => node v l (BST_remove cmp x r)
            | Eq =>
                match removeMin cmp l with
                    | None => r
                    | Some (m, l') => node m l' r
                end
        end
end.

Lemma elem_dec_spec :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    (forall x y : A, CompareSpec (x = y) (cmp x y = Lt) (cmp x y = Gt) (cmp x y)) ->
      isBST cmp t -> BoolSpec (elem x t) (~ elem x t) (elem_dec cmp x t).
Proof.
  intros A cmp x t spec H.
  functional induction (elem_dec cmp x t).
    constructor. inversion 1.
    inversion H; subst. specialize (IHb H3). destruct IHb.
      constructor. constructor 2. assumption.
      constructor. inversion 1; subst.
        admit.
        contradiction.
        specialize (H6 _ H7). congruence.
    constructor. destruct (spec x v); try congruence; subst. constructor.
    inversion H; subst. specialize (IHb H5). destruct IHb.
      constructor. constructor 3. assumption.
      constructor. inversion 1; subst.
        admit.
        specialize (H4 _ H7). congruence.
        contradiction.
Admitted.

Lemma elem_insert :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    isBST cmp t -> elem_dec cmp x (insert cmp x t) = true.
Proof.
  intros.
  functional induction (insert cmp x t); cbn.
    admit.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    admit.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
Admitted.

Lemma elem_remove :
  forall (A : Type) (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    isBST cmp t -> elem_dec cmp x (BST_remove cmp x t) = false.
Proof.
  intros.
  functional induction (BST_remove cmp x t); cbn.
    reflexivity.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    inversion H; subst.
      admit.
Abort.

