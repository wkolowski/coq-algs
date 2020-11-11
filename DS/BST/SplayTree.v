Require Export RCCBase.
Require Export BTree.
Require Import BST.
Require Import Ord.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayTree (A : Type) : Type := BTree A.

Function splay {A : Type} (p : A -> A -> bool) (pivot : A) (h : SplayTree A)
  : SplayTree A * SplayTree A :=
match h with
    | empty => (empty, empty)
    | node x a b =>
        if p x pivot
        then
          match b with
              | empty => (h, empty)
              | node y b1 b2 =>
                  if p y pivot
                  then
                    let '(small, big) := splay p pivot b2
                    in (node y (node x a b1) small, big)
                  else
                    let '(small, big) := splay p pivot b1
                    in (node x a small, node y big b2)
          end
        else
          match a with
              | empty => (empty, h)
              | node y a1 a2 =>
                  if p y pivot
                  then
                    let '(small, big) := splay p pivot a2
                    in (node y a1 small, node x big b)
                  else
                    let '(small, big) := splay p pivot a1
                    in (small, node y big (node x a2 b))
          end
end.

Definition insert
  {A : Type} (p : A -> A -> bool) (x : A) (h : SplayTree A) : SplayTree A :=
    let
      (smaller, bigger) := splay p x h
    in
      node x smaller bigger.

Function merge {A : Type} (p : A -> A -> bool) (h1 h2 : SplayTree A) : SplayTree A :=
match h1 with
    | empty => h2
    | node v l r =>
        let
          (l', r') := splay p v h2
        in
          node v (merge p l l') (merge p r r')
end.

(** Properties of [isEmpty] *)

Lemma isEmpty_splay :
  forall {A : Type} {cmp : A -> A -> comparison} {x : A} {h l r : SplayTree A},
    splay cmp x h = (l, r) ->
      isEmpty h = isEmpty l && isEmpty r.
Proof.
  intros until h.
  functional induction splay cmp x h;
  inv 1. cbn.
    rewrite andb_false_r. reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty (insert p x h) = false.
Proof.
  intros. unfold insert. case_eq (splay p x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge :
  forall {A : Type} {cmp : A -> A -> bool} {h1 h2 : SplayTree A},
    isEmpty (merge cmp h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1; cbn.
    reflexivity.
    intro. destruct (splay _ _ _). cbn. reflexivity.
Qed.

(** Properties of [splay]. *)

Lemma Elem_splay :
  forall (A : Type) (p : A -> A -> bool) (x pivot : A) (h l r : SplayTree A),
    splay p pivot h = (l, r) ->
      Elem x h <-> Elem x l \/ Elem x r.
Proof.
  split; revert x l r H.
    functional induction @splay A p pivot h; inv 1;
      rewrite e3 in *; inv 1; inv H1; edestruct IHp0; eauto.
    functional induction @splay A p pivot h; inv 1; inv 1;
      rewrite ?e3 in *; inv H0; eauto 6; inv H1.
Qed.

Lemma isBST_splay :
  forall {A : Type} {cmp : A -> A -> comparison} {x : A} {h l r : SplayTree A},
    splay cmp x h = (l, r) ->
      isBST cmp h -> isBST cmp (node x l r).
Proof.
  intros until h.
  functional induction splay cmp x h;
  inv 1.
Admitted.

Lemma size_splay :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h h1 h2 : SplayTree A),
    splay p x h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  intros A p x h.
  functional induction splay p x h; inv 1; cbn;
  erewrite IHp0; eauto; lia.
Qed.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    Elem x (insert p x h).
Proof.
  intros. unfold insert. destruct (splay p x h). constructor.
Qed.

Lemma isBST_insert :
  forall (A : Type) (p : A -> A -> comparison) (x : A) (h : SplayTree A),
    isBST p h -> isBST p (insert p x h).
Proof.
  intros. unfold insert.
  destruct (splay p x h) eqn: Heq.
  eapply isBST_splay; eauto.
Qed.

Lemma size_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    size (insert p x h) = 1 + size h.
Proof.
  intros. unfold insert.
  destruct (splay p x h) as [smaller bigger] eqn: Heq.
  cbn. f_equal. symmetry.
  eapply size_splay. eassumption.
Qed.

(** Properties of [merge]. *)

Lemma Elem_merge :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h1 h2 : SplayTree A),
    Elem x (merge p h1 h2) <-> Elem x h1 \/ Elem x h2.
Proof.
  split; revert x.
    functional induction merge p h1 h2; inv 1.
      edestruct IHs; eauto. right. eapply Elem_splay; eauto.
      edestruct IHs0; eauto. right. eapply Elem_splay; eauto.
    functional induction merge p h1 h2; inv 1.
      inv H0.
      inv H0.
      erewrite (Elem_splay _ _ _ _ e0) in H0. inv H0.
Qed.

Lemma isBST_merge :
  forall (A : Type) (p : A -> A -> comparison) (h1 h2 : SplayTree A),
    isBST p h1 -> isBST p h2 -> isBST p (merge p h1 h2).
Proof.
  intros until h2.
  functional induction merge p h1 h2; inv 1; intro.
  constructor.
    apply IHs; eauto. eapply isBST_splay in e0; inv e0.
    intros. apply Elem_merge in H0. inv H0.
      apply isBST_splay in e0; auto. inv e0.
    apply IHs0; eauto. eapply isBST_splay in e0; inv e0.
    intros. apply Elem_merge in H0. inv H0.
      apply isBST_splay in e0; auto. inv e0.
Qed.

Lemma size_merge :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayTree A),
    size (merge p h1 h2) = size h1 + size h2.
Proof.
  intros. functional induction merge p h1 h2; cbn.
    reflexivity.
    apply size_splay in e0. lia.
Qed.