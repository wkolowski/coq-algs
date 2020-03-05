Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison}
  : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          isBST l -> (forall x : A, Elem x l -> cmp x v = Lt) ->
          isBST r -> (forall x : A, Elem x r -> cmp x v = Gt) ->
            isBST (node v l r).

Arguments isBST {A} _ _.

Hint Constructors Elem isBST.

Record BST {A : Type} (cmp : A -> A -> comparison) : Type :=
{
    tree :> BTree A;
    prop : isBST cmp tree
}.

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

Function remove
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (remove cmp x l) r
            | Gt => node v l (remove cmp x r)
            | Eq =>
                match removeMin cmp l with
                    | None => r
                    | Some (m, l') => node m l' r
                end
        end
end.

Function elem
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        match cmp x v with
            | Lt => elem cmp x l
            | Eq => true
            | Gt => elem cmp x r
        end
end.

Lemma elem_spec :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    (forall x y : A, CompareSpec (x = y) (cmp x y = Lt) (cmp x y = Gt) (cmp x y)) ->
      isBST cmp t -> BoolSpec (Elem x t) (~ Elem x t) (elem cmp x t).
Proof.
  intros A cmp x t spec H.
  functional induction (elem cmp x t).
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
    isBST cmp t -> elem cmp x (insert cmp x t) = true.
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
    isBST cmp t -> elem cmp x (remove cmp x t) = false.
Proof.
  intros.
  functional induction (remove cmp x t); cbn.
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

Lemma elem_insert' :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    x <> y -> elem cmp x (insert cmp y t) = elem cmp x t.
Proof.
  intros.
  functional induction (insert cmp y t); cbn.
    admit.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x y) eqn: Hxy, (cmp x v) eqn: Hxv.
      all: try reflexivity.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
Admitted.

Lemma elem_remove' :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    x <> y -> elem cmp x (remove cmp y t) = elem cmp x t.
Proof.
  intros.
  functional induction (remove cmp y t); cbn.
    reflexivity.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x v) eqn: Hxv.
      admit.
      admit.
      reflexivity.
    destruct (cmp x m) eqn: Hxm, (cmp x v) eqn: Hxv.
      all: try reflexivity.
Admitted.

Hint Extern 0 =>
  intros;
match goal with
    | H : Elem _ empty |- _ => inversion H
    | H : isBST _ (node _ ?l _) |- isBST _ ?l => inversion H; auto
    | H : isBST _ (node _ _ ?r) |- isBST _ ?r => inversion H; auto
end.

Lemma isBST_insert :
  forall (A : Type) (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t).
    auto.
    constructor; auto; intros.
      admit.
      inversion H; subst. apply H7. assumption.
    admit.
    constructor; auto; intros.
      inversion H; subst. apply H5. assumption.
      inversion H; subst. admit.
Admitted.

Lemma isBST_remove :
  forall (A : Type) (cmp : A -> A -> comparison) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (remove cmp x t).
Proof.
  intros.
  functional induction (remove cmp x t); auto.
    constructor; auto; intros.
      admit.
      inversion H; subst. apply H7. assumption.
    constructor; auto; intros.
      inversion H; subst. apply H5. assumption.
      admit.
    constructor; auto; intros.
      admit.
Abort.

Lemma isBST_removeMin :
  forall (A : Type) (cmp : A -> A -> comparison) (t t' : BTree A) (x : A),
    isBST cmp t -> removeMin cmp t = Some (x, t') -> isBST cmp t'.
Proof.
  intros. revert t' x H0.
  functional induction (removeMin cmp t); intros.
    inversion H0.
    inversion H0; subst. inversion H; subst. assumption.
    inversion H0; subst. inversion H; subst.
      specialize (IHo H4 l' x0 e0). constructor; auto.
        intros. apply H5. admit.
Admitted.

(* TODO theorems:

    min_spec
    forall (A : LinDec) (m : A) (bst : BTree A),
      is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.

    count
    count_ins

    Sortedness for TreeSort
*)

(** [fromList] and its variants. *)
Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

Fixpoint fromList
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.