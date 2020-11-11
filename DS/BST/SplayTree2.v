Require Export BTree.
Require Import BST.
Require Export Ord.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayTree (A : Ord) : Type := BTree A.

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

(* Compute bigger 2 (node 5 (node 2 empty empty) empty). *)

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

Definition partition
  {A : Ord} (x : A) (h : SplayTree A) : SplayTree A * SplayTree A:=
    (smaller x h, bigger x h).

Definition insert
  {A : Ord} (x : A) (h : SplayTree A) : SplayTree A :=
    let (smaller, bigger) := partition x h
    in node x smaller bigger.

Function findMin
  {A : Ord} (h : SplayTree A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin l
end.

Function deleteMin
  {A : Ord} (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin'
  {A : Ord} (h : SplayTree A) : option A * SplayTree A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.

Function merge {A : Ord} (h1 h2 : SplayTree A) : SplayTree A :=
match h1 with
    | empty => h2
    | node v l r =>
        let '(l', r') := partition v h2
        in node v (merge l l') (merge r r')
end.

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

Lemma isEmpty_partition_true :
  forall (A : Ord) (x : A) (h l r : SplayTree A),
    partition x h = (l, r) ->
      isEmpty h = true <-> isEmpty l = true /\ isEmpty r = true.
Proof.
  unfold partition. split; inv H; intros.
    split.
      apply isEmpty_smaller_true. assumption.
      apply isEmpty_bigger_true. assumption.
    destruct H.
    induction h as [| v l IHl r IHr]; cbn in *.
      reflexivity.
      trich; [destruct r | destruct l]; trich.
Qed.

Lemma isEmpty_partition_false :
  forall (A : Ord) (x : A) (h l r : SplayTree A),
    partition x h = (l, r) ->
      isEmpty h = false <-> isEmpty l = false \/ isEmpty r = false.
Proof.
  unfold partition. split; inv H; intros.
    induction h as [| v l IHl r IHr]; cbn in *.
      auto.
      trich; [destruct r | destruct l]; trich.
    destruct H.
      eapply isEmpty_smaller_false. eassumption.
      eapply isEmpty_bigger_false. eassumption.
Qed.

Lemma isEmpty_partition :
  forall {A : Ord} {x : A} {h l r : SplayTree A},
    partition x h = (l, r) ->
      isEmpty h = isEmpty l && isEmpty r.
Proof.
  intros until h.
  unfold partition. inv 1.
  functional induction smaller x h;
  try destruct l; cbn; trich.
    destruct l2; cbn; trich.
    trich. rewrite andb_false_r. reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : Ord) (x : A) (h : SplayTree A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. case_eq (partition x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : Ord) (h1 h2 : SplayTree A),
    isEmpty (merge h1 h2) = true <->
      isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_merge_false :
  forall (A : Ord) (h1 h2 : SplayTree A),
    isEmpty (merge h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_merge :
  forall {A : Ord} {h1 h2 : SplayTree A},
    isEmpty (merge h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1; cbn; reflexivity.
Qed.

Lemma isEmpty_size :
  forall (A : Ord) (h : SplayTree A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_countBT :
  forall (A : Ord) (p : A -> bool) (h : SplayTree A),
    isEmpty h = true -> countBT p h = 0.
Proof.
  destruct h; cbn; congruence.
Qed.

(** Properties [bigger]. *)

Lemma bigger_spec :
  forall (A : Ord) (pivot : A) (h : SplayTree A),
    isBST cmp h -> forall x : A, elem cmp x (bigger pivot h) ->
      pivot < x.
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST; cbn; intros; trich.
    specialize (IHs H8 _ H). trich.
    specialize (IHs H2 _ H). trich.
Qed.

Lemma Elem_bigger' :
  forall (A : Ord) (x pivot : A) (h : SplayTree A),
    isBST cmp h -> Elem x (bigger pivot h) -> Elem x h.
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST; inv 1.
    inv H1.
Qed.

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

Lemma bigger_elem' :
  forall (A : Ord) (x pivot : A) (h : SplayTree A),
    isBST cmp h -> elem cmp x h -> pivot ≤ x -> pivot <> x ->
      elem cmp x (bigger pivot h).
Proof.
  intros until h. revert x.
  functional induction bigger pivot h;
  intro; isBST.
    Elem.
    Elems. apply IHs; auto. trich.
    Elem. trich. apply IHs; auto. trich.
    Elem. trich; apply IHs; trich.
      specialize (H4 v' ltac:(auto)). trich.
      specialize (H4 v' ltac:(auto)). trich.
Qed.

(** Properties of [smaller]. *)

Lemma smaller_spec :
  forall {A : Ord} {pivot : A} {h : SplayTree A},
    isBST cmp h -> forall x : A, elem cmp x (smaller pivot h) -> x ≤ pivot.
Proof.
  intros until h.
  functional induction smaller pivot h;
  isBST; inv 1.
    trich.
    trich. specialize (IHs H8 _ H1). trich.
    trich. specialize (IHs H2 _ H1). trich.
Qed.

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

(** Properties of [partition]. *)

Lemma Elem_partition :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    partition pivot h = (l, r) ->
      isBST cmp h ->
        forall x : A, Elem x h <-> Elem x l \/ Elem x r.
Proof.
  unfold partition.
  inv 1. intros.
  rewrite Elem_smaller, Elem_bigger.
    2-3: assumption.
    firstorder. destruct (cmp_spec x pivot).
      admit. (* TODO: fix definition of isBST *)
      left. split; try left; auto.
      right; split; auto.
Admitted.

Lemma isBST_partition :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    partition pivot h = (l, r) ->
      isBST cmp h -> isBST cmp (node pivot l r).
Proof.
  unfold partition.
  inv 1. isBST'.
    apply isBST_smaller. assumption.
    intro. rewrite Elem_smaller; Elems'.
    apply isBST_bigger. assumption.
    intro. rewrite Elem_bigger; Elems'.
Qed.

Lemma size_partition :
  forall {A : Ord} {pivot : A} {h l r : SplayTree A},
    partition pivot h = (l, r) ->
      isBST cmp h -> size h = size l + size r.
Proof.
  unfold partition. inv 1.
  functional induction smaller pivot h;
  isBST; cbn; trich.
    rewrite IHs; auto; lia.
    functional induction bigger pivot l';
    cbn.
      lia.
      cbn in *.
Abort.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall {A : Ord} {x : A} {h : SplayTree A},
    isBST cmp h ->
      forall y : A, Elem y (insert x h) <-> y = x \/ Elem y h.
Proof.
  unfold insert, partition. intros.
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
  destruct (partition x h) eqn: Heq.
  eapply isBST_partition; eassumption.
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
      pose (isBST_partition e0 H). inv i.
      rewrite (Elem_partition e0 H), ?Elem_node, IHs, IHs0; auto.
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
    pose (isBST_partition e0 H). isBST'.
      apply IHs; assumption.
      intro. rewrite Elem_merge; Elems.
      apply IHs0; assumption.
      intro. rewrite Elem_merge; Elems.
Qed.