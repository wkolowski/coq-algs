

Require Export BTree.
Require Import BST.
Require Export LinDec.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : LinDec) : Type := BTree A.

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

Function findMin'
  {A : LinDec} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin' l
end.

Function findMin
  {A : LinDec} (h : SplayHeap A) : option A :=
match h with
    | empty => None
(*    | node m empty _ => Some m
    | node _ l _ => findMin l*)
    | node v l r =>
        match findMin l with
            | None => Some v
            | Some m => Some m
        end
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

Function deleteMin2
  {A : LinDec} (h : SplayHeap A) : option (A * SplayHeap A) :=
match h with
    | empty => None
    | node v l r =>
        match deleteMin2 l with
            | None => Some (v, r)
            | Some (min, l') => Some (min, node v l' r)
        end
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

Lemma isEmpty_size :
  forall (A : LinDec) (h : SplayHeap A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_count_BTree :
  forall (A : LinDec) (x : A) (t : SplayHeap A),
    isEmpty t = true -> count_BTree x t = 0.
Proof.
  destruct t; dec.
Qed.

(** Properties of [partition]. *)

Lemma partition_elem :
  forall (A : LinDec) (x pivot : A) (h l r : SplayHeap A),
    partition pivot h = (l, r) ->
      elem x h <-> elem x l \/ elem x r.
Proof.
  split; revert x l r H.
    functional induction @partition A pivot h; inv 1;
      rewrite e3 in *; dec; inv H; inv H1; edestruct IHp; eauto.
    functional induction @partition A pivot h; inv 1;
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
  intros A x h. functional induction @partition A x h; inv 1; aux;
  try specialize (IHp _ _ e3 H7); try specialize (IHp _ _ e3 H9);
  try inv IHp; repeat constructor; aux; eapply partition_elem in e3;
  firstorder dec.
Unshelve.
  all: assumption.
Qed.

Lemma partition_size :
  forall (A : LinDec) (x : A) (h h1 h2 : SplayHeap A),
    partition x h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  intros A x h. functional induction partition x h; cbn;
  inv 1; dec; rewrite (IHp _ _ e3); omega.
Qed.

Lemma partition_count_BTree :
  forall (A : LinDec) (x pivot : A) (h h1 h2 : SplayHeap A),
    partition pivot h = (h1, h2) ->
      count_BTree x h = count_BTree x h1 + count_BTree x h2.
Proof.
  intros until h. revert x.
  functional induction partition pivot h; cbn;
  inv 1; dec; rewrite (IHp _ _ _ e3); omega.
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

Lemma insert_size :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    size (insert x h) = 1 + size h.
Proof.
  intros. unfold insert. case_eq (partition x h); intros smaller bigger H.
  cbn. f_equal. symmetry. eapply partition_size. eassumption.
Qed.

Lemma insert_count_BTree :
  forall (A : LinDec) (x y : A) (h : SplayHeap A),
    count_BTree x (insert y h) =
    (if x =? y then S else id) (count_BTree x h).
Proof.
  intros. unfold insert. case_eq (partition y h); intros.
  apply (partition_count_BTree x) in H. dec.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem :
  forall (A : LinDec) (x : A) (h1 h2 : SplayHeap A),
    elem x (merge h1 h2) <-> elem x h1 \/ elem x h2.
Proof.
  split; revert x.
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

Lemma merge_size :
  forall (A : LinDec) (h1 h2 : SplayHeap A),
    size (merge h1 h2) = size h1 + size h2.
Proof.
  intros. functional induction @merge A h1 h2; cbn.
    reflexivity. inv e0.
    rewrite IHs, IHs0. apply partition_size in H0. rewrite H0. omega.
Qed.

Lemma merge_count_BTree :
  forall (A : LinDec) (x : A) (h1 h2 : SplayHeap A),
    count_BTree x (merge h1 h2) = count_BTree x h1 + count_BTree x h2.
Proof.
  induction h1; cbn; intros.
    reflexivity.
    case_eq (partition a h2); cbn; intros.
      apply (partition_count_BTree x) in H. rewrite IHh1_1, IHh1_2, H. dec.
Qed.

(** Properties of [findMin] *)

Lemma findMin_elem :
  forall (A : LinDec) (m : A) (h : SplayHeap A),
    findMin h = Some m -> elem m h.
Proof.
  intros. functional induction @findMin A h; inv H.
Qed.

Lemma findMin_elem_node :
  forall (A : LinDec) (m v : A) (l r : SplayHeap A),
    findMin (node v l r) = Some m -> m = v \/ elem m l.
Proof.
  intros. remember (node v l r) as h. revert m v l r Heqh H.
  functional induction @findMin A h; inv 1; intros.
    inv H.
    inv H. destruct l0; cbn in *.
      congruence.
      destruct (findMin l0_1); inv e0.
        destruct (IHo _ _ _ _ eq_refl eq_refl); subst; auto.
Qed.

Lemma findMin_aux :
  forall (A : LinDec) (v : A) (l r : SplayHeap A),
    findMin (node v l r) = Some v \/
    findMin (node v l r) = findMin l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin A h; inv Heqh.
Qed.

Lemma findMin_spec :
  forall (A : LinDec) (m : A) (h : SplayHeap A),
    is_bst h -> findMin h = Some m ->
      forall x : A, elem x h -> m ≤ x.
Proof.
  intros A m h. revert m.
  functional induction @findMin A h; inv 1; intros.
    inv H.
      destruct l.
        inv H0. inv H1.
        cbn in e0. destruct (findMin l1); congruence.
    inv H. inv H0.
      apply H3. apply findMin_elem. assumption.
      aux. eapply leq_trans with v; try assumption.
        destruct l.
          cbn in e0. congruence.
          destruct (@findMin_aux _ c l1 l2).
            rewrite H in e0. inv e0.
            eapply leq_trans with c; eauto.
Qed.

(** Properties of [findMin']. *)
Lemma findMin'_elem :
  forall (A : LinDec) (m : A) (h : SplayHeap A),
    findMin' h = Some m -> elem m h.
Proof.
  intros. functional induction @findMin' A h; inv H.
Qed.

Lemma findMin'_elem_node :
  forall (A : LinDec) (m v : A) (l r : SplayHeap A),
    findMin' (node v l r) = Some m -> m = v \/ elem m l.
Proof.
  intros. remember (node v l r) as h. revert m v l r Heqh H.
  functional induction @findMin' A h; inv 1; intros.
    inv H.
    inv H. destruct l0; cbn in *.
      congruence.
        destruct (IHo _ _ _ _ eq_refl H1); subst; auto.
Qed.

Lemma findMin'_aux :
  forall (A : LinDec) (v : A) (l r : SplayHeap A),
    findMin' (node v l r) = Some v \/
    findMin' (node v l r) = findMin' l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin' A h; inv Heqh.
Qed.

Lemma findMin'_spec :
  forall (A : LinDec) (m : A) (h : SplayHeap A),
    is_bst h -> findMin' h = Some m ->
      forall x : A, elem x h -> m ≤ x.
Proof.
  intros A m h. revert m.
  functional induction @findMin' A h; do 3 inv 1.
    inv H1.
    apply H3. apply findMin'_elem. assumption.
    aux. eapply leq_trans; try eassumption. destruct l.
      contradiction.
      eapply leq_trans with c; eauto.
Qed.

(** Properties of [deleteMin2]. *)
Lemma deleteMin2_size :
  forall (A : LinDec) (m : A) (h h' : SplayHeap A),
    deleteMin2 h = Some (m, h') -> size h = 1 + size h'.
Proof.
  intros A m h. revert m.
  functional induction @deleteMin2 A h; cbn; inv 1.
    destruct l; cbn in *.
      reflexivity.
      destruct (deleteMin2 l1).
        destruct p. congruence.
        congruence.
    rewrite (IHo _ _ e0). cbn. reflexivity.
Qed.

Lemma deleteMin2_isEmpty_None :
  forall (A : LinDec) (h : SplayHeap A),
    deleteMin2 h = None -> isEmpty h = true.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_isEmpty_Some :
  forall (A : LinDec) (m : A) (h h' : SplayHeap A),
    deleteMin2 h = Some (m, h') -> isEmpty h = false.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_elem :
  forall (A : LinDec) (m : A) (h h' : SplayHeap A),
    deleteMin2 h = Some (m, h') -> elem m h.
Proof.
  intros A m h. revert m.
  functional induction @deleteMin2 A h; inv 1; eauto.
Qed.

Lemma deleteMin2_elem_node :
  forall (A : LinDec) (m v : A) (l r h' : SplayHeap A),
    deleteMin2 (node v l r) = Some (m, h') -> m = v \/ elem m l.
Proof.
  intros. remember (node v l r) as h. revert m v l r h' Heqh H.
  functional induction @deleteMin2 A h; inv 1; intros.
    inv H.
    inv H. destruct l0; cbn in *.
      congruence.
      destruct (deleteMin2 l0_1); inv e0. destruct p. inv H0.
        destruct (IHo _ _ _ _ _ eq_refl eq_refl); subst; auto.
Qed.

Lemma deleteMin2_aux :
  forall (A : LinDec) (v : A) (l r : SplayHeap A),
    deleteMin2 (node v l r) = Some (v, r) \/
    deleteMin2 (node v l r) =
      match deleteMin2 l with
          | None => Some (v, r)
          | Some (m, l') => Some (m, node v l' r)
      end.
Proof.
  intros. remember (node v l r) as h. revert v l r Heqh.
  functional induction @deleteMin2 A h; inv 1.
  destruct l0; cbn in *.
    congruence.
    specialize (IHo _ _ _ eq_refl). destruct (deleteMin2 l0_1).
      destruct p. inv e0.
      inv e0.
Qed.

Lemma deleteMin2_spec :
  forall (A : LinDec) (m : A) (h h' : SplayHeap A),
    is_bst h -> deleteMin2 h = Some (m, h') ->
      forall x : A, elem x h -> m ≤ x.
Proof.
  intros A m h. revert m.
  functional induction @deleteMin2 A h; inv 1; intros.
    inv H. inv H0. destruct l.
      inv H1.
      cbn in e0. destruct (deleteMin2 l1); try destruct p; congruence.
    inv H. inv H0.
      apply H3. eapply deleteMin2_elem. eassumption.
      eauto.
      aux. eapply leq_trans with v; try assumption.
        destruct l.
          cbn in e0. congruence.
          destruct (@deleteMin2_aux _ c l1 l2).
            rewrite H in e0. inv e0.
            eapply leq_trans with c; eauto.
Qed.

Lemma deleteMin2_count_BTree :
  forall (A : LinDec) (x m : A) (h h' : SplayHeap A),
    is_bst h -> deleteMin2 h = Some (m, h') ->
      count_BTree x h =
      (if x =? m then S else id) (count_BTree x h').
Proof.
  intros A x m h. revert x m.
  functional induction deleteMin2 h; cbn; inv 1; intros.
    destruct l; cbn in *.
      inv H. dec.
      destruct (deleteMin2 l1); try destruct p; inv e0.
    inv H. destruct l; cbn in *.
      inv e0.
      destruct (deleteMin2 l1); try destruct p;
      inv e0; specialize (IHo x _ _ ltac:(inv H4) eq_refl);
      rewrite IHo; dec.
Qed.