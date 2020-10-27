Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Inductive Ok {A : Type} (R : A -> A -> Prop) (x : A) : BTree A -> Prop :=
    | Ok_empty : Ok R x empty
    | Ok_node  :
        forall (y : A) (l r : BTree A),
          R y x -> Ok R x (node y l r).

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison}
  : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          Ok (fun x y : A => cmp x y = Lt) v l ->
          Ok (fun x y : A => cmp x y = Gt) v r ->
            isBST l -> isBST r -> isBST (node v l r).

Arguments isBST {A} _ _.

Hint Constructors Ok Elem Ok isBST : core.

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
            | Eq => node v l r
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
                match removeMin cmp r with
                    | None => l
                    | Some (m, r') => node m l r'
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

Hint Extern 0 =>
  intros;
match goal with
    | H : Elem _ empty |- _ => inversion H
    | H : isBST _ (node _ ?l _) |- isBST _ ?l => inv H
    | H : isBST _ (node _ _ ?r) |- isBST _ ?r => inv H
end
  : core.

Lemma isBST_insert :
  forall
    {A : Type} {cmp : cmp_spec A} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t).
    1, 3: auto.
    inv H. constructor; auto. inv H3; cbn; auto.
      destruct (cmp x y); auto.
    inv H. constructor; auto. inv H4; cbn; auto.
      destruct (cmp x y); auto.
Qed.

Lemma isBST_removeMin :
  forall
    {A : Type} (cmp : cmp_spec A)
    (t t' : BTree A) (x : A),
      isBST cmp t -> removeMin cmp t = Some (x, t') -> isBST cmp t'.
Proof.
  intros. revert t' x H0 H.
  functional induction (removeMin cmp t);
  inv 1; inv 1.
  constructor; auto.
    inv H3; cbn in e0.
      inv e0.
      destruct (removeMin cmp l0).
        destruct p. inv e0.
        inv e0. inv H5. assumption.
  rewrite Ok_removeMin in H3; firstorder eauto.
Qed.

Lemma isBST_remove :
  forall (A : Type) (cmp : cmp_spec A) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (remove cmp x t).
Proof.
  intros. revert H.
  functional induction (remove cmp x t).
    1-4: inv 1.
    inv 1. constructor; auto.
Admitted.

Lemma Ok_Elem :
  forall {A : Type} {P : A -> Prop} {x : A} {t : BTree A},
    Ok P t -> Elem x t -> P x.
Proof.
  induction 1; inv 1.
Qed.

Lemma elem_spec :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x : A) (t : BTree A),
      isBST cmp t -> BoolSpec (Elem x t) (~ Elem x t) (elem cmp x t).
Proof.
  intros A cmp x t H.
  functional induction (elem cmp x t).
    constructor. inversion 1.
    inversion H; subst. specialize (IHb H5). destruct IHb.
      constructor. constructor 2. assumption.
      constructor. inversion 1; subst.
        rewrite cmp_spec3 in e0. congruence.
        contradiction.
        contradict e0. rewrite (Ok_Elem H4 H7). inv 1.
    constructor. apply cmp_spec1 in e0. subst. constructor.
    inversion H; subst. specialize (IHb H6). destruct IHb.
      constructor. constructor 3. assumption.
      constructor. inversion 1; subst.
        rewrite cmp_spec3 in e0. congruence.
        contradict e0. rewrite (Ok_Elem H3 H7). inv 1.
        contradiction.
Qed.

Lemma Sorted_BTree_toList :
  forall (A : Type) (p : A -> A -> comparison) (t : BTree A),
    isBST p t -> Sorted p (BTree_toList t).
Proof.
  induction t; inv 1; cbn.
    constructor.
    apply Sorted_app.
      apply IHt1. assumption.
      destruct (BTree_toList t2) eqn: Heq.
        constructor.
        constructor.
          red. unfold comparison2bool. destruct (p a a0) eqn: Hp.
            1-2: reflexivity.
            admit. (* TODO *)
          apply IHt2. assumption. Check In.
      admit.
Admitted.

(* TODO theorems:

    elem_remove
    min_spec
    forall (A : LinDec) (m : A) (bst : BTree A),
      is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.
*)