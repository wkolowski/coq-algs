Require Export BTree.
Require Import BST.
Require Export Ord.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : Ord) : Type := BTree A.

Function bigger
  {A : Ord} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
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
  {A : Ord} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
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

(* Compute smaller 4 (node 5 (node 2 empty empty) empty). *)

Definition partition
  {A : Ord} (x : A) (h : SplayHeap A) : SplayHeap A * SplayHeap A:=
    (smaller x h, bigger x h).

Definition isEmpty
  {A : Ord} (h : SplayHeap A) : bool :=
match h with
    | empty => true
    | _ => false
end.

Definition insert
  {A : Ord} (x : A) (h : SplayHeap A) : SplayHeap A :=
    let (smaller, bigger) := partition x h
    in node x smaller bigger.

Function findMin
  {A : Ord} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin l
end.

Function deleteMin
  {A : Ord} (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin'
  {A : Ord} (h : SplayHeap A) : option A * SplayHeap A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.

Function merge {A : Ord} (h1 h2 : SplayHeap A) : SplayHeap A :=
match h1 with
    | empty => h2
    | node v l r =>
        let '(l', r') := partition v h2
        in node v (merge l l') (merge r r')
end.

(** Properties of [bigger] and [smaller]. *)

Ltac aux := intros; repeat
match goal with
    | H : context [?x ≤? ?y] |- _ => trich
    | H : ~ _ ≤ _ |- _ => trich
    | H : elem _ ?t, H' : forall _, elem _ ?t -> _ |- _ =>
        specialize (H' _ H)
    | H : ?a ≤ ?b, H' : ?b ≤ ?c |- ?a ≤ ?c => trich
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ _ _) |- _ => inv H
    | H : isBST ?x, H' : isBST ?x -> _ |- _ => specialize (H' H)
    | H : isBST empty |- _ => inv H
    | H : isBST (node _ _ _) |- _ => inv H
end; auto.

(** Properties of [isEmpty] *)

Lemma isEmpty_smaller_true :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isEmpty h = true -> isEmpty (smaller x h) = true.
Proof.
  intros. functional induction @smaller A x h; cbn in *; aux.
Qed.

Lemma isEmpty_smaller_false :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isEmpty (smaller x h) = false -> isEmpty h = false.
Proof.
  intros. functional induction @smaller A x h; cbn in *; aux.
Qed.

Lemma isEmpty_bigger_true :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isEmpty h = true -> isEmpty (bigger x h) = true.
Proof.
  intros. functional induction @bigger A x h; cbn in *; aux.
Qed.

Lemma isEmpty_bigger_false :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isEmpty (bigger x h) = false -> isEmpty h = false.
Proof.
  intros. functional induction @bigger A x h; cbn in *; aux.
Qed.

Lemma isEmpty_partition_true :
  forall (A : Ord) (x : A) (h l r : SplayHeap A),
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
  forall (A : Ord) (x : A) (h l r : SplayHeap A),
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

Lemma isEmpty_insert :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. case_eq (partition x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : Ord) (h1 h2 : SplayHeap A),
    isEmpty (merge h1 h2) = true <->
      isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_merge_false :
  forall (A : Ord) (h1 h2 : SplayHeap A),
    isEmpty (merge h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_size :
  forall (A : Ord) (h : SplayHeap A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_countBT :
  forall (A : Ord) (p : A -> bool) (h : SplayHeap A),
    isEmpty h = true -> countBT p h = 0.
Proof.
  destruct h; cbn; congruence.
Qed.

(** Properties [bigger]. *)

Lemma bigger_spec :
  forall (A : Ord) (pivot : A) (h : SplayHeap A),
    isBST cmp h -> forall x : A, elem cmp x (bigger pivot h) ->
      pivot < x.
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST; cbn; intros; trich.
    specialize (IHs H8 _ H). trich.
    specialize (IHs H2 _ H). trich.
Qed.

Lemma bigger_elem :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST cmp h -> Elem x (bigger pivot h) -> Elem x h.
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST; inv 1.
    inv H1.
Qed.

Lemma bigger_elem' :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST cmp h -> elem cmp x h -> pivot ≤ x -> pivot <> x ->
      elem cmp x (bigger pivot h).
Proof.
  intros until h. revert x.
  functional induction bigger pivot h.
    Elem.
    Elem. cbn in *. apply IHs; isBST. cbn in *. trich.
    Elem.
    Elem. trich. apply IHs; isBST. trich.
    intros until 2.
Admitted.

Lemma isBST_bigger :
  forall (A : Ord) (pivot : A) (h : SplayHeap A),
    isBST cmp h -> isBST cmp (bigger pivot h).
Proof.
  intros until h.
  functional induction bigger pivot h;
  isBST.
    constructor; auto; intros. apply bigger_elem in H; auto.
    constructor; auto; intros.
      apply bigger_elem in H; auto.
Admitted.

(*
Lemma not_elem_countBT :
  forall (A : Ord) (p : A -> bool) (x : A) (t : BTree A),
    ~ elem cmp x t -> countBT p t = 0.
Proof.
  induction t; cbn; intros; rewrite ?IHt1, ?IHt2; trich.
  contradiction H. constructor.
Qed.

Lemma elem_lt_not_r :
  forall (A : Ord) (x v : A) (l r : BTree A),
    isBST (node v l r) -> x ≤ v -> x <> v -> ~ elem x r.
Proof.
  unfold not. intros. inv H.
Qed.

Hint Extern 0 =>
match goal with
    | H : elem _ empty |- _ => inv H
end.

Lemma countBT_node :
  forall (A : Ord) (p : A -> bool) (x v : A) (l r : BTree A),
    isBST (node v l r) -> x ≤ v -> x <> v ->
      countBT p (node v l r) = countBT p (node v l empty).
Proof.
  intros. destruct (elem_decb_reflect A x (node v l r)).
    Focus 2. rewrite !not_elem_countBT; auto.
      intro. apply n. inv H2.
    cbn. trich. rewrite (@not_elem_countBT _ _ r).
      reflexivity.
      intro. inv H.
Qed.

Lemma countBT_bigger :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST h -> pivot ≤ x -> x <> pivot ->
      countBT x (bigger pivot h) = countBT x h.
Proof.
  intros.
  destruct (elem_decb_reflect _ x h).
    Focus 2. rewrite !not_elem_countBT; auto.
      intro. apply n. eapply bigger_elem; eauto.
    functional induction bigger pivot h; cbn.
      reflexivity.
      2: trich.
      trich.
        contradiction H1. trich.
        inv H. inv e.
          contradiction H1. apply leq_antisym; auto.
            eapply leq_trans; eauto.
          rewrite (@not_elem_countBT _ _ l).
            rewrite IHs; auto.
            intro. trich.
      Focus 2. aux; trich.
Restart.
  intros.
  functional induction bigger pivot h; cbn; aux.
    trich; rewrite IHs; auto.
      contradiction H1. apply leq_antisym; auto.
      rewrite (@not_elem_countBT _ _ l).
        lia.
        intro. contradiction H1. apply leq_antisym; auto.
          eapply leq_trans; eauto.
    trich.
Abort.

(** Properties of [smaller]. *)
Lemma smaller_spec :
  forall (A : Ord) (pivot : A) (h h' : SplayHeap A),
    isBST h -> smaller pivot h = h' ->
      forall x : A, elem x h' -> x ≤ pivot.
Proof.
  intros until h. functional induction @smaller A pivot h; aux; eauto.
Qed.

Lemma smaller_elem :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x (smaller pivot h) -> elem x h.
Proof.
  intros. functional induction @smaller A pivot h; aux.
Qed.

Lemma smaller_elem' :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x h -> x ≤ pivot ->
      elem x (smaller pivot h).
Proof.
  intros. functional induction @smaller A pivot h; aux;
  contradiction H3; trich.
Qed.

Lemma isBST_smaller :
  forall (A : Ord) (pivot : A) (h : SplayHeap A),
    isBST h -> isBST (smaller pivot h).
Proof.
  intros. functional induction @smaller A pivot h; aux.
    repeat constructor; auto; intros.
      inv H. eauto.
      apply smaller_elem in H; auto.
    repeat constructor; auto; intros. apply smaller_elem in H; auto.
Qed.

(*Lemma smaller_countBT :
  forall (A : Ord) (x pivot : A) (h : SplayHeap A),
    isBST h -> x ≤ pivot *)

(** Properties of [partition]. *)

Lemma partition_elem :
  forall (A : Ord) (x pivot : A) (h l r : SplayHeap A),
    isBST h -> partition pivot h = (l, r) ->
      elem x h <-> elem x l \/ elem x r.
Proof.
  intros. inv H0. split; intros.
    destruct (leqb_spec x pivot).
      left. eapply smaller_elem'; aux.
      right. eapply bigger_elem'; aux.
    destruct H0.
      eapply smaller_elem; eauto.
      eapply bigger_elem; eauto.
Qed.

Lemma isBST_partition :
  forall (A : Ord) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) -> isBST h -> isBST (node x l r).
Proof.
  unfold partition. inversion 1; subst; clear H. constructor.
    eapply smaller_spec; eauto.
    apply smaller_is_bst. assumption.
    eapply bigger_spec; eauto.
    apply bigger_is_bst. assumption.
Qed.

Lemma size_partition :
  forall (A : Ord) (pivot : A) (h h1 h2 : SplayHeap A),
    partition pivot h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  unfold partition. intros. inv H.
  functional induction smaller pivot h; cbn; trich.
    destruct l'; cbn.
      rewrite <- plus_n_O. reflexivity.
      trich.
Abort.

(** Properties of [insert]. *)

Lemma elem_insert :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    elem x (insert x h).
Proof.
  intros. unfold insert. destruct (partition x h). constructor.
Qed.

Lemma isBST_insert :
  forall (A : Ord) (x : A) (h : SplayHeap A),
    isBST h -> isBST (insert x h).
Proof.
  intros. unfold insert. case_eq (partition x h); intros l r H'.
  eapply partition_is_bst; eauto.
Qed.

(** Properties of [merge]. *)

Lemma elem_merge :
  forall (A : Ord) (x : A) (h1 h2 : SplayHeap A),
    isBST h1 -> isBST h2 ->
      elem x (merge h1 h2) <-> elem x h1 \/ elem x h2.
Proof.
  split; revert x H H0.
    functional induction @merge A h1 h2; intros.
      right. assumption.
      assert (is_bst (node v l' r')) by (eapply partition_is_bst; eauto).
        aux; inv e0.
          destruct (IHs _ H10 H7 H4); aux. right.
            eapply smaller_elem; eauto.
          destruct (IHs0 _ H12 H9 H4); aux. right.
            eapply bigger_elem; eauto.
    functional induction @merge A h1 h2; intros.
      inv H1; inv H2.
      inv H. inv H1.
        apply partition_is_bst in e0; inv e0. inv H.
        rewrite partition_elem in H; eauto.
          apply partition_is_bst in e0; inv H; eauto.
Qed.

Lemma isBST_merge :
  forall (A : Ord) (h1 h2 : SplayHeap A),
    isBST h1 -> isBST h2 -> isBST (merge h1 h2).
Proof.
  induction h1 as [| v l IHl r IHr]; intros.
    assumption.
    unfold merge. case_eq (partition v h2); intros small big Hp; fold merge.
      apply partition_is_bst in Hp; aux. constructor; intros; auto.
        apply elem_merge in H; firstorder.
        apply elem_merge in H; firstorder.
Qed.
*)