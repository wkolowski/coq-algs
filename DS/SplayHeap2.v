Require Export BTree.
Require Import BST.
Require Export LinDec.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : LinDec) : Type := BTree A.

Function bigger
  {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node v l r =>
        if v <=? pivot
        then bigger pivot r
        else
          match l with
              | empty => node v empty r
              | node v' l' r' =>
                  if v' <=? pivot
                  then (* v' <= pivot < v *)
                    node v (bigger pivot r') r
                  else (* pivot < v' <= v *)
                    node v' (bigger pivot l') (node v r' r)
          end
end.

Compute bigger 2 (node 5 (node 2 empty empty) empty).

Function smaller
  {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node v l r =>
        if v <=? pivot
        then
          match r with
              | empty => node v l empty
              | node v' l' r' =>
                  if v' <=? pivot
                  then (* v <= v' <= pivot *)
                    node v' (node v l l') (smaller pivot r')
                  else (* v <= pivot < v' *)
                    node v l (smaller pivot l')
          end
        else smaller pivot l
end.

Compute smaller 4 (node 5 (node 2 empty empty) empty).

Definition partition
  {A : LinDec} (x : A) (h : SplayHeap A) : SplayHeap A * SplayHeap A:=
    (smaller x h, bigger x h).

Definition isEmpty
  {A : LinDec} (h : SplayHeap A) : bool :=
match h with
    | empty => true
    | _ => false
end.

Definition insert
  {A : LinDec} (x : A) (h : SplayHeap A) : SplayHeap A :=
    let (smaller, bigger) := partition x h
    in node x smaller bigger.

Function findMin
  {A : LinDec} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin l
end.

Function deleteMin
  {A : LinDec} (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin'
  {A : LinDec} (h : SplayHeap A) : option A * SplayHeap A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.

Function merge {A : LinDec} (h1 h2 : SplayHeap A) : SplayHeap A :=
match h1 with
    | empty => h2
    | node v l r =>
        let '(l', r') := partition v h2
        in node v (merge l l') (merge r r')
end.

(** Properties of [bigger] and [smaller]. *)

Ltac aux := intros; repeat
match goal with
    | H : context [?x <=? ?y] |- _ =>
        let H' := fresh "H" in
          destruct (leqb_spec x y) as [H' | H']; try congruence;
          clear H; rename H' into H
    | H : ~ _ ≤ _ |- _ => destruct (LinDec_not_leq_lt _ _ _ H); clear H
    | H : elem _ ?t, H' : forall _, elem _ ?t -> _ |- _ =>
        specialize (H' _ H)
    | H : ?a ≤ ?b, H' : ?b ≤ ?c |- ?a ≤ ?c =>
        apply leq_trans with b; assumption
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ _ _) |- _ => inv H
    | H : isBST ?x, H' : isBST ?x -> _ |- _ => specialize (H' H)
    | H : isBST empty |- _ => inv H
    | H : isBST (node _ _ _) |- _ => inv H
end; auto.

(** Properties of [isEmpty] *)

Lemma isEmpty_smaller_true :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isEmpty h = true -> isEmpty (smaller x h) = true.
Proof.
  intros. functional induction @smaller A x h; cbn in *; aux.
Qed.

Lemma isEmpty_smaller_false :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isEmpty (smaller x h) = false -> isEmpty h = false.
Proof.
  intros. functional induction @smaller A x h; cbn in *; aux.
Qed.

Lemma isEmpty_bigger_true :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isEmpty h = true -> isEmpty (bigger x h) = true.
Proof.
  intros. functional induction @bigger A x h; cbn in *; aux.
Qed.

Lemma isEmpty_bigger_false :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isEmpty (bigger x h) = false -> isEmpty h = false.
Proof.
  intros. functional induction @bigger A x h; cbn in *; aux.
Qed.

Lemma isEmpty_partition_true :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
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
      dec; [destruct r | destruct l]; dec.
Qed.

Lemma isEmpty_partition_false :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) ->
      isEmpty h = false <-> isEmpty l = false \/ isEmpty r = false.
Proof.
  unfold partition. split; inv H; intros.
    induction h as [| v l IHl r IHr]; cbn in *.
      auto.
      dec; [destruct r | destruct l]; dec.
    destruct H.
      eapply isEmpty_smaller_false. eassumption.
      eapply isEmpty_bigger_false. eassumption.
Qed.

Lemma isEmpty_insert :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. case_eq (partition x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    isEmpty (merge h1 h2) = true <->
      isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_merge_false :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    isEmpty (merge h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2);
  firstorder congruence.
Qed.

Lemma isEmpty_size :
  forall (A : LinDec) (h : SplayHeap A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_count_BTree :
  forall (A : LinDec) (p : A -> bool) (h : SplayHeap A),
    isEmpty h = true -> count_BTree p h = 0.
Proof.
  destruct h; cbn; congruence.
Qed.

(** Properties [bigger]. *)

(* TODO: fix elem
Lemma bigger_spec :
  forall (A : LinDec) (pivot : A) (h : SplayHeap A),
    isBST h -> forall x : A, elem x (bigger pivot h) ->
      pivot ≤ x /\ pivot <> x.
Proof.
  intros. functional induction @bigger A pivot h; aux;
  (split; [eauto | intro; subst; dec]).
Qed.

Lemma bigger_elem :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x (bigger pivot h) -> elem x h.
Proof.
  intros. functional induction @bigger A pivot h; aux.
Qed.

Lemma bigger_elem' :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x h -> pivot ≤ x -> pivot <> x ->
      elem x (bigger pivot h).
Proof.
  intros. functional induction @bigger A pivot h; aux;
  contradiction H2; dec.
Qed.

Lemma bigger_isBST :
  forall (A : LinDec) (pivot : A) (h : SplayHeap A),
    isBST h -> isBST (bigger pivot h).
Proof.
  intros. functional induction @bigger A pivot h; aux.
    repeat constructor; auto; intros. apply bigger_elem in H; auto.
    repeat constructor; auto; intros.
      apply bigger_elem in H; auto.
      inv H. eauto.
Qed.

(* wut *)

(*
Lemma not_elem_count_BTree :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    ~ elem x t -> count_BTree p t = 0.
Proof.
  induction t; cbn; intros; rewrite ?IHt1, ?IHt2; dec.
  contradiction H. constructor.
Qed.
*)

Lemma elem_lt_not_r :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    isBST (node v l r) -> x ≤ v -> x <> v -> ~ elem x r.
Proof.
  unfold not. intros. inv H.
Qed.

Hint Extern 0 =>
match goal with
    | H : elem _ empty |- _ => inv H
end.

(*
Lemma count_BTree_node :
  forall (A : LinDec) (p : A -> bool) (x v : A) (l r : BTree A),
    isBST (node v l r) -> x ≤ v -> x <> v ->
      count_BTree p (node v l r) = count_BTree p (node v l empty).
Proof.
  intros. destruct (elem_decb_reflect A x (node v l r)).
    Focus 2. rewrite !not_elem_count_BTree; auto.
      intro. apply n. inv H2.
    cbn. dec. rewrite (@not_elem_count_BTree _ _ r).
      reflexivity.
      intro. inv H.
Qed.
*)

(*
Lemma bigger_count_BTree :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> pivot ≤ x -> x <> pivot ->
      count_BTree x (bigger pivot h) = count_BTree x h.
Proof.
  intros.
  destruct (elem_decb_reflect _ x h).
    Focus 2. rewrite !not_elem_count_BTree; auto.
      intro. apply n. eapply bigger_elem; eauto.
    functional induction bigger pivot h; cbn.
      reflexivity.
      2: dec.
      dec.
        contradiction H1. dec.
        inv H. inv e.
          contradiction H1. apply leq_antisym; auto.
            eapply leq_trans; eauto.
          rewrite (@not_elem_count_BTree _ _ l).
            rewrite IHs; auto.
            intro. dec.
      Focus 2. aux; dec.
Restart.
  intros.
  functional induction bigger pivot h; cbn; aux.
    dec; rewrite IHs; auto.
      contradiction H1. apply leq_antisym; auto.
      rewrite (@not_elem_count_BTree _ _ l).
        lia.
        intro. contradiction H1. apply leq_antisym; auto.
          eapply leq_trans; eauto.
    dec.
Abort.
*)

(** Properties of [smaller]. *)
Lemma smaller_spec :
  forall (A : LinDec) (pivot : A) (h h' : SplayHeap A),
    isBST h -> smaller pivot h = h' ->
      forall x : A, elem x h' -> x ≤ pivot.
Proof.
  intros until h. functional induction @smaller A pivot h; aux; eauto.
Qed.

Lemma smaller_elem :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x (smaller pivot h) -> elem x h.
Proof.
  intros. functional induction @smaller A pivot h; aux.
Qed.

Lemma smaller_elem' :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> elem x h -> x ≤ pivot ->
      elem x (smaller pivot h).
Proof.
  intros. functional induction @smaller A pivot h; aux;
  contradiction H3; dec.
Qed.

Lemma smaller_isBST :
  forall (A : LinDec) (pivot : A) (h : SplayHeap A),
    isBST h -> isBST (smaller pivot h).
Proof.
  intros. functional induction @smaller A pivot h; aux.
    repeat constructor; auto; intros.
      inv H. eauto.
      apply smaller_elem in H; auto.
    repeat constructor; auto; intros. apply smaller_elem in H; auto.
Qed.

(*Lemma smaller_count_BTree :
  forall (A : LinDec) (x pivot : A) (h : SplayHeap A),
    isBST h -> x ≤ pivot *)

(** Properties of [partition]. *)

Lemma partition_elem :
  forall (A : LinDec) (x pivot : A) (h l r : SplayHeap A),
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

Lemma partition_isBST :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) -> isBST h -> isBST (node x l r).
Proof.
  unfold partition. inversion 1; subst; clear H. constructor.
    eapply smaller_spec; eauto.
    apply smaller_is_bst. assumption.
    eapply bigger_spec; eauto.
    apply bigger_is_bst. assumption.
Qed.

Lemma partition_size :
  forall (A : LinDec) (pivot : A) (h h1 h2 : SplayHeap A),
    partition pivot h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  unfold partition. intros. inv H.
  functional induction smaller pivot h; cbn; dec.
    destruct l'; cbn.
      rewrite <- plus_n_O. reflexivity.
      dec.
Abort.

(** Properties of [insert]. *)

Lemma insert_elem :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    elem x (insert x h).
Proof.
  intros. unfold insert. destruct (partition x h). constructor.
Qed.

Lemma insert_isBST :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    isBST h -> isBST (insert x h).
Proof.
  intros. unfold insert. case_eq (partition x h); intros l r H'.
  eapply partition_is_bst; eauto.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem :
  forall (A : LinDec) (x : A) (h1 h2 : SplayHeap A),
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

Lemma merge_isBST :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    isBST h1 -> isBST h2 -> isBST (merge h1 h2).
Proof.
  induction h1 as [| v l IHl r IHr]; intros.
    assumption.
    unfold merge. case_eq (partition v h2); intros small big Hp; fold merge.
      apply partition_is_bst in Hp; aux. constructor; intros; auto.
        apply merge_elem in H; firstorder.
        apply merge_elem in H; firstorder.
Qed.
*)