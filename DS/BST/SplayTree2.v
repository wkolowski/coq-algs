Require Export BTree.
Require Import BST.
Require Export Ord.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayTree (A : Ord) : Type := BTree A.

Function smaller
  {A : Ord} (pivot : A) (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node v l r =>
        if v ≤? pivot
        then
          match r with
              | empty => node v l empty
              | node v' l' r' =>
                  if v' ≤? pivot
                  then (* v <= v' <= pivot *)
                    node v' (node v l l') (smaller pivot r')
                  else (* v <= pivot < v' *)
                    node v l (smaller pivot l')
          end
        else smaller pivot l
end.

Function bigger
  {A : Ord} (pivot : A) (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node v l r =>
        if v ≤? pivot
        then bigger pivot r
        else
          match l with
              | empty => node v empty r
              | node v' l' r' =>
                  if v' ≤? pivot
                  then (* v' <= pivot < v *)
                    node v (bigger pivot r') r
                  else (* pivot < v' <= v *)
                    node v' (bigger pivot l') (node v r' r)
          end
end.

Definition splay
  {A : Ord} (x : A) (h : SplayTree A) : SplayTree A * SplayTree A:=
    (smaller x h, bigger x h).

Definition insert
  {A : Ord} (x : A) (h : SplayTree A) : SplayTree A :=
    let (smaller, bigger) := splay x h
    in node x smaller bigger.

Function merge {A : Ord} (h1 h2 : SplayTree A) : SplayTree A :=
match h1 with
    | empty => h2
    | node v l r =>
        let '(l', r') := splay v h2
        in node v (merge l l') (merge r r')
end.

(** Properties [bigger]. *)

Lemma Elem_bigger :
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h ->
      forall x : A,
        Elem x (bigger pivot h)
          <->
        Elem x h /\ x > pivot.
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST; intro;
  rewrite ?Elem_node, ?IHs; auto;
  split; Elems'.
Qed.

Lemma isBST_bigger :
  forall (A : Ord) (pivot : A) (h : SplayTree A),
    isBST cmp h -> isBST cmp (bigger pivot h).
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST'; auto; intros.
    apply Elem_bigger in H; firstorder.
    apply Elem_bigger in H; firstorder.
    inv H.
      trich.
      specialize (H6 _ H1). specialize (H4 v' ltac:(auto)). trich.
Qed.

(** Properties of [smaller]. *)

Lemma Elem_smaller : (* TODO: fix definition of isBST *)
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h ->
      forall x : A,
        Elem x (smaller pivot h)
          <->
        Elem x h /\ x < pivot.
Proof.
  intros until h.
  functional induction smaller pivot h;
  isBST; intro;
  rewrite ?Elem_node, ?IHs; auto;
  split; Elems'.
Admitted.

Lemma isBST_smaller :
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h -> isBST cmp (smaller pivot h).
Proof.
  intros until h.
  functional induction smaller pivot h;
  isBST'; try intro;
  rewrite ?Elem_smaller; Elems'.
    specialize (H6 v' ltac:(auto)). trich.
    specialize (H6 v' ltac:(auto)). trich.
Qed.

(** Properties of [splay]. *)

Lemma Elem_splay :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    splay pivot h = (l, r) ->
      isBST cmp h ->
        forall x : A, Elem x h <-> Elem x l \/ Elem x r.
Proof.
  unfold splay.
  inv 1. intros.
  rewrite Elem_smaller, Elem_bigger.
    2-3: assumption.
    firstorder. destruct (cmp_spec x pivot).
      admit. (* TODO: fix definition of isBST *)
      left. split; try left; auto.
      right; split; auto.
Admitted.

Lemma isBST_splay :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    splay pivot h = (l, r) ->
      isBST cmp h -> isBST cmp (node pivot l r).
Proof.
  unfold splay.
  inv 1. isBST'.
    apply isBST_smaller. assumption.
    intro. rewrite Elem_smaller; Elems'.
    apply isBST_bigger. assumption.
    intro. rewrite Elem_bigger; Elems'.
Qed.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall {A : Ord} {x : A} {h : SplayTree A},
    isBST cmp h ->
      forall y : A, Elem y (insert x h) <-> y = x \/ Elem y h.
Proof.
  unfold insert, splay. intros.
  rewrite Elem_node, Elem_smaller, Elem_bigger; auto. split.
    firstorder.
    destruct (cmp_spec y x); firstorder.
Qed.

Lemma isBST_insert :
  forall {A : Ord} {x : A} {h : SplayTree A},
    isBST cmp h -> isBST cmp (insert x h).
Proof.
  intros.
  unfold insert.
  destruct (splay x h) eqn: Heq.
  eapply isBST_splay; eassumption.
Qed.

(** Properties of [merge]. *)

Lemma Elem_merge :
  forall {A : Ord} {h1 h2 : SplayTree A} {x : A},
    isBST cmp h1 -> isBST cmp h2 ->
      Elem x (merge h1 h2)
        <->
      Elem x h1 \/ Elem x h2.
Proof.
  intros until h2.
  functional induction merge h1 h2;
  intro; isBST.
    split; Elems.
    {
      pose (isBST_splay e0 H). inv i.
      rewrite (Elem_splay e0 H), ?Elem_node, IHs, IHs0; auto.
      split; Elems''.
    }
Qed.

Lemma isBST_merge :
  forall {A : Ord} {h1 h2 : SplayTree A},
    isBST cmp h1 -> isBST cmp h2 ->
      isBST cmp (merge h1 h2).
Proof.
  intros until h2.
  functional induction merge h1 h2;
  isBST.
    assumption.
    pose (isBST_splay e0 H). isBST'.
      apply IHs; assumption.
      intro. rewrite Elem_merge; Elems.
      apply IHs0; assumption.
      intro. rewrite Elem_merge; Elems.
Qed.

(** Properties of [isEmpty] *)

Lemma isEmpty_smaller_true :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty h = true -> isEmpty (smaller x h) = true.
Proof.
  intros.
  functional induction smaller x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_smaller_false :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty (smaller x h) = false -> isEmpty h = false.
Proof.
  intros.
  functional induction smaller x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_bigger_true :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty h = true -> isEmpty (bigger x h) = true.
Proof.
  intros.
  functional induction smaller x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_bigger_false :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty (bigger x h) = false -> isEmpty h = false.
Proof.
  intros.
  functional induction smaller x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_splay :
  forall {A : Ord} {x : A} {h l r : SplayTree A},
    splay x h = (l, r) ->
      isEmpty h = isEmpty l && isEmpty r.
Proof.
  intros until h.
  unfold splay. inv 1.
  functional induction smaller x h;
  try destruct l; cbn; trich.
    destruct l2; cbn; trich.
    trich. rewrite andb_false_r. reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. case_eq (splay x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge :
  forall {A : Ord} {h1 h2 : SplayTree A},
    isEmpty (merge h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1; cbn; reflexivity.
Qed.