From CoqAlgs Require Export Ord.
From CoqAlgs Require Import BST.

Set Implicit Arguments.

Definition SplayTree (A : Type) : Type := BTree A.

Function smaller
  {A : Type} (leb : A -> A -> bool) (pivot : A) (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node v l r =>
        if leb v pivot
        then
          match r with
              | empty => node v l empty
              | node v' l' r' =>
                  if leb v' pivot
                  then (* v <= v' <= pivot *)
                    node v' (node v l l') (smaller leb pivot r')
                  else (* v <= pivot < v' *)
                    node v l (smaller leb pivot l')
          end
        else smaller leb pivot l
end.

Function bigger
  {A : Type} (leb : A -> A -> bool) (pivot : A) (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node v l r =>
        if leb v pivot
        then bigger leb pivot r
        else
          match l with
              | empty => node v empty r
              | node v' l' r' =>
                  if leb v' pivot
                  then (* v' <= pivot < v *)
                    node v (bigger leb pivot r') r
                  else (* pivot < v' <= v *)
                    node v' (bigger leb pivot l') (node v r' r)
          end
end.

Definition splay
  {A : Type} (leb : A -> A -> bool) (pivot : A) (h : SplayTree A) : SplayTree A * SplayTree A:=
    (smaller leb pivot h, bigger leb pivot h).

Definition insert
  {A : Type} (leb : A -> A -> bool) (x : A) (h : SplayTree A) : SplayTree A :=
    let (smaller, bigger) := splay leb x h
    in node x smaller bigger.

Function merge {A : Type} (leb : A -> A -> bool) (h1 h2 : SplayTree A) : SplayTree A :=
match h1 with
    | empty => h2
    | node v l r =>
        let '(l', r') := splay leb v h2
        in node v (merge leb l l') (merge leb r r')
end.

(** We can use [removeMin] and [remove] from BST.v *)
(* Print removeMin. *)
(* Print remove. *)

(** Properties [bigger]. *)

Lemma isEmpty_bigger_true :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty h = true -> isEmpty (bigger leb x h) = true.
Proof.
  intros.
  functional induction smaller leb x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_bigger_false :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty (bigger leb x h) = false -> isEmpty h = false.
Proof.
  intros.
  functional induction smaller leb x h;
  cbn in *; congruence.
Qed.

Lemma Elem_bigger :
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h ->
      forall x : A,
        Elem x (bigger cmp pivot h)
          <->
        Elem x h /\ x > pivot.
Proof.
  intros until h.
  functional induction bigger cmp pivot h;
  isBST; intro;
  rewrite ?Elem_node, ?IHs; auto;
  unfold comparison2bool in *;
  split; Elems'.
Qed.

Lemma isBST_bigger :
  forall (A : Ord) (pivot : A) (h : SplayTree A),
    isBST cmp h -> isBST cmp (bigger cmp pivot h).
Proof.
  intros until h.
  functional induction bigger cmp pivot h;
  isBST'; auto; intros.
    apply Elem_bigger in H; firstorder.
    apply Elem_bigger in H; firstorder.
    inv H.
      trich.
      specialize (H6 _ H1). specialize (H4 v' ltac:(auto)). trich.
Qed.

(** Properties of [smaller]. *)

Lemma isEmpty_smaller_true :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty h = true -> isEmpty (smaller leb x h) = true.
Proof.
  intros.
  functional induction smaller leb x h;
  cbn in *; congruence.
Qed.

Lemma isEmpty_smaller_false :
  forall {A : Type} {leb : A -> A -> bool} {x : A} {h : SplayTree A},
    isEmpty (smaller leb x h) = false -> isEmpty h = false.
Proof.
  intros.
  functional induction smaller leb x h;
  cbn in *; congruence.
Qed.

Lemma Elem_smaller : (* TODO: fix definition of isBST *)
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h ->
      forall x : A,
        Elem x (smaller cmp pivot h)
          <->
        Elem x h /\ x < pivot.
Proof.
  intros until h.
  functional induction smaller cmp pivot h;
  isBST; intro;
  rewrite ?Elem_node, ?IHs; auto;
  unfold comparison2bool in *;
  split; Elems'.
Admitted.

Lemma isBST_smaller :
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h -> isBST cmp (smaller cmp pivot h).
Proof.
  intros until h.
  functional induction smaller cmp pivot h;
  isBST'; try intro;
  rewrite ?Elem_smaller; Elems'.
    specialize (H6 v' ltac:(auto)). trich.
    specialize (H6 v' ltac:(auto)). trich.
Qed.

(** Properties of [splay]. *)

Lemma isEmpty_splay :
  forall {A : Type} {leb : A -> A -> bool} {x : A} {h l r : SplayTree A},
    splay leb x h = (l, r) ->
      isEmpty h = isEmpty l && isEmpty r.
Proof.
  intros until h.
  unfold splay. inv 1.
  functional induction smaller leb x h;
  try destruct l; cbn; trich.
    destruct (leb v x); cbn in *; congruence.
    destruct l2, (leb v x), (leb a x); cbn; trich.
      rewrite andb_false_r. reflexivity.
      destruct (leb a0 x); reflexivity.
      rewrite andb_false_r. reflexivity.
Qed.

Lemma Elem_splay :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    splay cmp pivot h = (l, r) ->
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
    splay cmp pivot h = (l, r) ->
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

Lemma isEmpty_insert :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty (insert leb x h) = false.
Proof.
  intros. unfold insert.
  destruct (splay leb x h).
  cbn. reflexivity.
Qed.

Lemma Elem_insert :
  forall {A : Ord} {x : A} {h : SplayTree A},
    isBST cmp h ->
      forall y : A, Elem y (insert cmp x h) <-> y = x \/ Elem y h.
Proof.
  unfold insert, splay. intros.
  rewrite Elem_node, Elem_smaller, Elem_bigger; auto. split.
    firstorder.
    destruct (cmp_spec y x); firstorder.
Qed.

Lemma isBST_insert :
  forall {A : Ord} {x : A} {h : SplayTree A},
    isBST cmp h -> isBST cmp (insert cmp x h).
Proof.
  intros.
  unfold insert.
  destruct (splay cmp x h) eqn: Heq.
  eapply isBST_splay; eassumption.
Qed.

(** Properties of [merge]. *)

Lemma isEmpty_merge :
  forall {A : Type} (leb : A -> A -> bool) (h1 h2 : SplayTree A),
    isEmpty (merge leb h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1; cbn; reflexivity.
Qed.

Lemma Elem_merge :
  forall {A : Ord} {h1 h2 : SplayTree A} {x : A},
    isBST cmp h1 -> isBST cmp h2 ->
      Elem x (merge cmp h1 h2)
        <->
      Elem x h1 \/ Elem x h2.
Proof.
  intros until h2.
  functional induction merge cmp h1 h2;
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
      isBST cmp (merge cmp h1 h2).
Proof.
  intros until h2.
  functional induction merge cmp h1 h2;
  isBST.
    assumption.
    pose (isBST_splay e0 H). isBST'.
      apply IHs; assumption.
      intro. rewrite Elem_merge; Elems.
      apply IHs0; assumption.
      intro. rewrite Elem_merge; Elems.
Qed.