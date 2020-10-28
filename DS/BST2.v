Require Export RCCBase.
Require Import BTree.

Inductive All {A : Type} (P : A -> Prop) : BTree A -> Prop :=
    | All_empty : All P empty
    | All_node  :
        forall (x : A) (l r : BTree A),
          P x -> All P l -> All P r -> All P (node x l r).

Hint Constructors All : core.

Lemma All_spec :
  forall {A : Type} {P : A -> Prop} {t : BTree A},
    All P t <-> forall x : A, Elem x t -> P x.
Proof.
  split.
    induction 1; inv 1.
    intro H. induction t; auto.
Qed.

Lemma All_Elem :
  forall {A : Type} {P : A -> Prop} {x : A} {t : BTree A},
    All P t -> Elem x t -> P x.
Proof.
  induction 1; inv 1.
Qed.

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison} : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          All (fun x : A => cmp x v = Lt) l ->
          All (fun x : A => cmp x v = Gt) r ->
            isBST l -> isBST r -> isBST (node v l r).

Arguments isBST {A} _ _.

Hint Constructors All Elem isBST : core.

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

Lemma All_node' :
  forall {A : Type} {P : A -> Prop} {v : A} {l r : BTree A},
    All P (node v l r) <-> P v /\ All P l /\ All P r.
Proof.
  split; inv 1. inv H1.
Qed.

Lemma All_insert :
  forall
    {A : Type} {cmp : cmp_spec A} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST cmp t -> All P (insert cmp x t) <-> P x /\ All P t.
Proof.
  intros A cmp P x t H.
  functional induction (insert cmp x t);
  rewrite ?All_node', ?IHb; firstorder.
  replace x with v.
    assumption.
    symmetry. apply cmp_spec1. assumption.
Qed.

Lemma All_removeMin :
  forall
    {A : Type} {cmp : cmp_spec A} (P : A -> Prop)
    (m : A) (t t' : BTree A),
      isBST cmp t -> removeMin cmp t = Some (m, t') ->
        All P t <-> P m /\ All P t'.
Proof.
  intros until t. revert m.
  functional induction removeMin cmp t;
  inv 1; inv 1; rewrite ?All_node'.
    functional inversion e0. firstorder.
    rewrite IHo; firstorder eauto.
Qed.

Lemma All_remove :
  forall
    {A : Type} {cmp : cmp_spec A} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST cmp t -> All P t -> All P (remove cmp x t).
Proof.
  intros until t.
  functional induction remove cmp x t.
    1-4: inv 1; rewrite ?All_node', ?IHb; firstorder.
    inv 1; inv 1. rewrite ?All_node'.
      eapply (All_removeMin P) in e1; firstorder eauto.
Qed.

Lemma All_remove_conv :
  forall
    {A : Type} {cmp : cmp_spec A} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST cmp t -> All P (remove cmp x t) -> (P x -> All P t).
Proof.
  intros until t.
  functional induction remove cmp x t;
  inv 1; rewrite ?All_node'; firstorder.
    destruct (cmpr_spec x v); subst; auto; congruence.
    functional inversion e1; subst. constructor.
    destruct (cmpr_spec x v); subst; auto; congruence.
    eapply (All_removeMin P) in e1; firstorder eauto.
Qed.

Hint Resolve All_insert All_removeMin All_remove All_remove_conv : core.

Hint Extern 0 =>
match goal with
    | H : isBST _ (node _ _ _) |- _ => inv H
    | |- All _ (insert _ _ _) => rewrite ?All_insert
end
  : core.

Lemma isBST_insert :
  forall
    {A : Type} {cmp : cmp_spec A} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t); auto.
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
  rewrite All_removeMin in H3; firstorder eauto.
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
        contradict e0. rewrite All_spec in H4. rewrite H4; auto.
    constructor. apply cmp_spec1 in e0. subst. constructor.
    inversion H; subst. specialize (IHb H6). destruct IHb.
      constructor. constructor 3. assumption.
      constructor. inversion 1; subst.
        rewrite cmp_spec3 in e0. congruence.
        contradict e0. rewrite All_spec in H3. rewrite H3; auto.
        contradiction.
Qed.