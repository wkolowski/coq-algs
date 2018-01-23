Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export BTree.
Require Import BST.
Require Export LinDec.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : LinDec) : Type := BTree A.

(* TODO: posibly remove *)
(*Function bigger {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node v l r =>
        if v <=? pivot
        then bigger pivot r
        else
          match l with
              | empty => l
              | node v' l' r' =>
                  if v' <=? pivot
                  then node v (bigger pivot r') r
                  else node v' (bigger pivot l') (node v r' r)
          end
end.

Function smaller {A : LinDec} (pivot : A) (h : SplayHeap A) : SplayHeap A := h.
*)

Function partition {A : LinDec} (pivot : A) (h : SplayHeap A)
  : SplayHeap A * SplayHeap A :=
match h with
    | empty => (empty, empty)
    | node x a b =>
        if x <=? pivot
        then
          match b with
              | empty => (h, empty)
              | node y b1 b2 =>
                  if y <=? pivot
                  then
                    let '(small, big) := partition pivot b2
                    in (node y (node x a b1) small, big)
                  else
                    let '(small, big) := partition pivot b1
                    in (node x a small, node y big b2)
          end
        else
          match a with
              | empty => (empty, h)
              | node y a1 a2 =>
                  if y <=? pivot
                  then
                    let '(small, big) := partition pivot a2
                    in (node y a1 small, node x big b)
                  else
                    let '(small, big) := partition pivot a1
                    in (small, node y big (node x a2 b))
          end
end.

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

(** Properties of [isEmpty] *)

Lemma isEmpty_partition_true :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) ->
      isEmpty h = true <-> isEmpty l = true /\ isEmpty r = true.
Proof.
  split; intros; functional induction @partition A x h; inv H; firstorder.
Qed.

Lemma isEmpty_partition_false :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) ->
      isEmpty h = false <-> isEmpty l = false \/ isEmpty r = false.
Proof.
  split; intros; functional induction @partition A x h; inv H; firstorder.
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
  destruct h1; cbn; intros; try destruct (partition c h2); firstorder.
Qed.

Lemma isEmpty_merge_false :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    isEmpty (merge h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition c h2); firstorder.
Qed.

(** Properties of [partition]. *)

Lemma partition_elem :
  forall (A : LinDec) (x pivot : A) (h l r : SplayHeap A),
    partition pivot h = (l, r) ->
      elem x h <-> elem x l \/ elem x r.
Proof.
  split.
    functional induction @partition A pivot h; inv H;
      rewrite e3 in *; dec; inv H; inv H1; edestruct IHp; eauto.
    functional induction @partition A pivot h; inv H;
      destruct 1; rewrite ?e3 in *; dec; inv H;
      try (edestruct IHp; eauto; fail); inv H1.
Qed.

Ltac aux := intros; repeat
match goal with
    | H : context [?x <=? ?y] |- _ =>
        let H' := fresh "H" in
          destruct (leqb_spec x y) as [H' | H']; try congruence;
          clear H; rename H' into H
    | H : ~ _ ≤ _ |- _ => apply LinDec_not_leq in H
    | H : elem _ ?t, H' : forall _, elem _ ?t -> _ |- _ =>
        specialize (H' _ H)
    | H : ?a ≤ ?b, H' : ?b ≤ ?c |- ?a ≤ ?c =>
        apply leq_trans with b; assumption
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ _ _) |- _ => inv H
    | H : is_bst ?x, H' : is_bst ?x -> _ |- _ => specialize (H' H)
    | H : is_bst empty |- _ => inv H
    | H : is_bst (node _ _ _) |- _ => inv H
end; auto.

Lemma partition_is_bst :
  forall (A : LinDec) (x : A) (h l r : SplayHeap A),
    partition x h = (l, r) -> is_bst h -> is_bst (node x l r).
Proof.
  intros. functional induction @partition A x h; inv H; aux;
  try specialize (IHp _ _ e3 H7); try specialize (IHp _ _ e3 H9);
  try inv IHp; repeat constructor; aux; eapply partition_elem in e3;
  firstorder dec.
Unshelve.
  all: assumption.
Qed.

(** Properties of [insert]. *)
Lemma insert_elem :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    elem x (insert x h).
Proof.
  intros. unfold insert. destruct (partition x h). constructor.
Qed.

Lemma insert_is_bst :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    is_bst h -> is_bst (insert x h).
Proof.
  intros. unfold insert. case_eq (partition x h); intros l r H'.
  eapply partition_is_bst; eauto.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem :
  forall (A : LinDec) (x : A) (h1 h2 : SplayHeap A),
    elem x (merge h1 h2) <-> elem x h1 \/ elem x h2.
Proof.
  split.
    functional induction @merge A h1 h2; intros; inv H;
      eapply partition_elem in e0.
      destruct (IHs _ H1); firstorder.
      destruct (IHs0 _ H1); firstorder.
    functional induction @merge A h1 h2; intros; inv H.
      inv H0.
      inv H0.
      rewrite (@partition_elem _ x v _ l' r') in H0; firstorder.
Qed.

Lemma merge_is_bst :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    is_bst h1 -> is_bst h2 -> is_bst (merge h1 h2).
Proof.
  induction h1 as [| v l IHl r IHr]; cbn; intros.
    assumption.
    case_eq (partition v h2); intros small big Hp.
      apply partition_is_bst in Hp; aux. constructor; intros; auto.
        apply merge_elem in H. firstorder.
        apply merge_elem in H. firstorder.
Qed.