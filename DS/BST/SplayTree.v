Require Export RCCBase.
Require Export BTree.
Require Import BST.
Require Import Ord.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayTree (A : Type) : Type := BTree A.

Function partition {A : Type} (p : A -> A -> bool) (pivot : A) (h : SplayTree A)
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
                    let '(small, big) := partition p pivot b2
                    in (node y (node x a b1) small, big)
                  else
                    let '(small, big) := partition p pivot b1
                    in (node x a small, node y big b2)
          end
        else
          match a with
              | empty => (empty, h)
              | node y a1 a2 =>
                  if p y pivot
                  then
                    let '(small, big) := partition p pivot a2
                    in (node y a1 small, node x big b)
                  else
                    let '(small, big) := partition p pivot a1
                    in (small, node y big (node x a2 b))
          end
end.

Definition isEmpty
  {A : Type} (h : SplayTree A) : bool :=
match h with
    | empty => true
    | _ => false
end.

Definition insert
  {A : Type} (p : A -> A -> bool) (x : A) (h : SplayTree A) : SplayTree A :=
    let
      (smaller, bigger) := partition p x h
    in
      node x smaller bigger.

Function findMin'
  {A : Type} (h : SplayTree A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin' l
end.

Function findMin
  {A : Type} (h : SplayTree A) : option A :=
match h with
    | empty => None
    | node v l r =>
        match findMin l with
            | None => Some v
            | Some m => Some m
        end
end.

Function deleteMin
  {A : Type} (h : SplayTree A) : SplayTree A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin'
  {A : Type} (h : SplayTree A) : option A * SplayTree A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.

Function deleteMin2
  {A : Type} (h : SplayTree A) : option (A * SplayTree A) :=
match h with
    | empty => None
    | node v l r =>
        match deleteMin2 l with
            | None => Some (v, r)
            | Some (min, l') => Some (min, node v l' r)
        end
end.

Function merge {A : Type} (p : A -> A -> bool) (h1 h2 : SplayTree A) : SplayTree A :=
match h1 with
    | empty => h2
    | node v l r =>
        let
          (l', r') := partition p v h2
        in
          node v (merge p l l') (merge p r r')
end.

(** Properties of [isEmpty] *)

Lemma isEmpty_partition_true :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h l r : SplayTree A),
    partition p x h = (l, r) ->
      isEmpty h = true <-> isEmpty l = true /\ isEmpty r = true.
Proof.
  split; intros; functional induction @partition A p x h; inv H; firstorder.
    all: cbn in *; congruence.
Qed.

Lemma isEmpty_partition_false :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h l r : SplayTree A),
    partition p x h = (l, r) ->
      isEmpty h = false <-> isEmpty l = false \/ isEmpty r = false.
Proof.
  split; intros; functional induction @partition A p x h; inv H; firstorder.
Qed.

Lemma isEmpty_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    isEmpty (insert p x h) = false.
Proof.
  intros. unfold insert. case_eq (partition p x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayTree A),
    isEmpty (merge p h1 h2) = true <->
      isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  destruct h1; cbn; intros; try destruct (partition p a h2); firstorder.
    cbn in H. congruence.
Qed.

Lemma isEmpty_merge_false :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayTree A),
    isEmpty (merge p h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition p a h2); firstorder congruence. 
Qed.

Lemma isEmpty_size :
  forall (A : Type) (h : SplayTree A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_countBT :
  forall (A : Type) (p : A -> bool) (t : SplayTree A),
    isEmpty t = true -> countBT p t = 0.
Proof.
  destruct t; trich.
Qed.

(** Properties of [partition]. *)

Lemma Elem_partition :
  forall (A : Type) (p : A -> A -> bool) (x pivot : A) (h l r : SplayTree A),
    partition p pivot h = (l, r) ->
      Elem x h <-> Elem x l \/ Elem x r.
Proof.
  split; revert x l r H.
    functional induction @partition A p pivot h; inv 1;
      rewrite e3 in *; inv 1; inv H1; edestruct IHp0; eauto.
    functional induction @partition A p pivot h; inv 1; inv 1;
      rewrite ?e3 in *; inv H0; eauto 6; inv H1.
Qed.

Ltac aux := intros; repeat
match goal with
    | H : context [?x ≤? ?y] |- _ => trich
(*         let H' := fresh "H" in
          destruct (leqb_spec x y) as [H' | H']; try congruence;
          clear H; rename H' into H
 *)    | H : ~ _ ≤ _ |- _ => trich (* apply Ord_not_leq_lt in H *)
    | H : elem _ ?t, H' : forall _, elem _ ?t -> _ |- _ =>
        specialize (H' _ H)
    | H : ?a ≤ ?b, H' : ?b ≤ ?c |- ?a ≤ ?c => trich
(*         apply leq_trans with b; assumption *)
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ _ _) |- _ => inv H
    | H : isBST ?x, H' : isBST ?x -> _ |- _ => specialize (H' H)
    | H : isBST empty |- _ => inv H
    | H : isBST (node _ _ _) |- _ => inv H
end; auto.

Lemma isBST_partition :
  forall (A : Type) (p : A -> A -> comparison) (x : A) (h l r : SplayTree A),
    partition p x h = (l, r) -> isBST p h -> isBST p (node x l r).
Proof.
  intros until h.
  functional induction partition p x h;
  inv 1; isBST.
    isBST'; Elems''. trich.
(*   inv 1; inv 1; aux. constructor; auto.
  try specialize (IHp0 _ _ _ e3 H7); try specialize (IHp0 _ _ _ e3 H9);
  try inv IHp0; repeat constructor; aux. inv H.
 *)Admitted.

Lemma size_partition :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h h1 h2 : SplayTree A),
    partition p x h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  intros A p x h.
  functional induction partition p x h; inv 1; cbn;
  erewrite IHp0; eauto; lia.
Qed.

Lemma countBT_partition :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (pivot : A) (h h1 h2 : SplayTree A),
    partition cmp pivot h = (h1, h2) ->
      countBT p h = countBT p h1 + countBT p h2.
Proof.
  intros until h. revert p.
  functional induction partition cmp pivot h;
  inv 1; cbn; erewrite IHp; eauto;
  destruct (p x), (p y); cbn; unfold id; lia.
Qed.

(** Properties of [insert]. *)
Lemma Elem_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    Elem x (insert p x h).
Proof.
  intros. unfold insert. destruct (partition p x h). constructor.
Qed.

Lemma isBST_insert :
  forall (A : Type) (p : A -> A -> comparison) (x : A) (h : SplayTree A),
    isBST p h -> isBST p (insert p x h).
Proof.
  intros. unfold insert.
  destruct (partition p x h) eqn: Heq.
  eapply isBST_partition; eauto.
Qed.

Lemma size_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayTree A),
    size (insert p x h) = 1 + size h.
Proof.
  intros. unfold insert.
  destruct (partition p x h) as [smaller bigger] eqn: Heq.
  cbn. f_equal. symmetry.
  eapply size_partition. eassumption.
Qed.

Lemma countBT_insert :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (x : A) (h : SplayTree A),
    countBT p (insert cmp x h) =
    (if p x then 1 else 0) + countBT p h.
Proof.
  intros. unfold insert.
  destruct (partition cmp x h) eqn: Heq.
  apply (countBT_partition cmp p) in Heq.
  rewrite Heq. cbn. destruct (p x); reflexivity.
Qed.

(** Properties of [merge]. *)

Lemma Elem_merge :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h1 h2 : SplayTree A),
    Elem x (merge p h1 h2) <-> Elem x h1 \/ Elem x h2.
Proof.
  split; revert x.
    functional induction merge p h1 h2; inv 1.
      edestruct IHs; eauto. right. eapply Elem_partition; eauto.
      edestruct IHs0; eauto. right. eapply Elem_partition; eauto.
    functional induction merge p h1 h2; inv 1.
      inv H0.
      inv H0.
      erewrite (Elem_partition _ _ _ _ e0) in H0. inv H0.
Qed.

Lemma isBST_merge :
  forall (A : Type) (p : A -> A -> comparison) (h1 h2 : SplayTree A),
    isBST p h1 -> isBST p h2 -> isBST p (merge p h1 h2).
Proof.
  intros until h2.
  functional induction merge p h1 h2; inv 1; intro.
  constructor.
    apply IHs; eauto. eapply isBST_partition in e0; inv e0.
    intros. apply Elem_merge in H0. inv H0.
      apply isBST_partition in e0; auto. inv e0.
    apply IHs0; eauto. eapply isBST_partition in e0; inv e0.
    intros. apply Elem_merge in H0. inv H0.
      apply isBST_partition in e0; auto. inv e0.
Qed.

Lemma size_merge :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayTree A),
    size (merge p h1 h2) = size h1 + size h2.
Proof.
  intros. functional induction merge p h1 h2; cbn.
    reflexivity.
    apply size_partition in e0. lia.
Qed.

Lemma countBT_merge :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (h1 h2 : SplayTree A),
    countBT p (merge cmp h1 h2) = countBT p h1 + countBT p h2.
Proof.
  intros until h2.
  functional induction (merge cmp h1 h2); cbn.
    reflexivity.
    apply (countBT_partition cmp p) in e0.
      destruct (p v); unfold id; lia.
Qed.

(** Properties of [findMin] *)

Lemma Elem_findMin :
  forall (A : Type) (m : A) (h : SplayTree A),
    findMin h = Some m -> Elem m h.
Proof.
  intros. functional induction @findMin A h; inv H.
Qed.

Lemma Elem_findMin_node :
  forall (A : Type) (m v : A) (l r : SplayTree A),
    findMin (node v l r) = Some m -> m = v \/ Elem m l.
Proof.
  intros. remember (node v l r) as h. revert m v l r Heqh H.
  functional induction (findMin h); inv 1; inv 1.
  functional inversion e0; subst; eauto.
  edestruct IHo; eauto. subst. eauto.
Qed.

Lemma findMin_aux :
  forall (A : Type) (v : A) (l r : SplayTree A),
    findMin (node v l r) = Some v \/
    findMin (node v l r) = findMin l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin A h; inv Heqh.
Qed.

Lemma findMin_spec :
  forall {A : Ord} {h : SplayTree A} {m : A},
    findMin h = Some m ->
      isBST cmp h -> forall x : A, Elem x h -> cmp m x <> Gt.
Proof.
  intros A h.
  functional induction findMin h; inv 1; inv 1.
    inv 1.
      trich.
      functional inversion e0. subst. inv H1.
      specialize (H6 _ H1). intro. trich.
    inv 1.
      apply Elem_findMin in e0. rewrite (H4 _ e0). inv 1.
      apply Elem_findMin in e0. specialize (H4 _ e0). specialize (H6 _ H1).
        trich.
Qed.

(** Properties of [findMin']. *)

Lemma findMin'_elem :
  forall (A : Type) (m : A) (h : SplayTree A),
    findMin' h = Some m -> Elem m h.
Proof.
  intros. functional induction @findMin' A h; inv H.
Qed.

Lemma findMin'_elem_node :
  forall (A : Type) (m v : A) (l r : SplayTree A),
    findMin' (node v l r) = Some m -> m = v \/ Elem m l.
Proof.
  intros. remember (node v l r) as h. revert m v l r Heqh H.
  functional induction @findMin' A h; inv 1; intros.
    inv H.
    inv H. destruct l0; cbn in *.
      congruence.
        destruct (IHo _ _ _ _ eq_refl H1); subst; auto.
Qed.

Lemma findMin'_aux :
  forall (A : Type) (v : A) (l r : SplayTree A),
    findMin' (node v l r) = Some v \/
    findMin' (node v l r) = findMin' l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin' A h; inv Heqh.
Qed.

Lemma findMin'_spec :
  forall (A : Type) (cmp : A -> A -> comparison) (m : A) (h : SplayTree A),
    isBST cmp h -> findMin' h = Some m ->
      forall x : A, Elem x h -> cmp m x.
Proof.
  intros A cmp m h. revert m.
  functional induction findMin' h; inv 1; inv 1.
    inv 1.
      admit.
      inv H1.
      admit.
    specialize (H4 _ (findMin'_elem _ H1)). inv 1.
      red. rewrite H4. cbn. reflexivity.
      specialize (H6 _ H2). admit. (* transitivity *)
Admitted.

(** Properties of [deleteMin2]. *)

Lemma deleteMin2_size :
  forall (A : Type) (m : A) (h h' : SplayTree A),
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
  forall (A : Type) (h : SplayTree A),
    deleteMin2 h = None -> isEmpty h = true.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_isEmpty_Some :
  forall (A : Type) (m : A) (h h' : SplayTree A),
    deleteMin2 h = Some (m, h') -> isEmpty h = false.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_elem :
  forall (A : Type) (m : A) (h h' : SplayTree A),
    deleteMin2 h = Some (m, h') -> Elem m h.
Proof.
  intros A m h. revert m.
  functional induction @deleteMin2 A h; inv 1; eauto.
Qed.

Lemma deleteMin2_elem_node :
  forall (A : Type) (m v : A) (l r h' : SplayTree A),
    deleteMin2 (node v l r) = Some (m, h') -> m = v \/ Elem m l.
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
  forall (A : Type) (v : A) (l r : SplayTree A),
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
  forall (A : Type) (cmp : A -> A -> comparison) (m : A) (h h' : SplayTree A),
    isBST cmp h -> deleteMin2 h = Some (m, h') ->
      forall x : A, Elem x h -> cmp m x.
Proof.
  intros A cmp m h. revert m.
  functional induction deleteMin2 h; inv 1; intros.
    inv H. inv H0.
      admit.
      functional inversion e0; subst. inv H1.
      specialize (H6 _ H1). admit. (* flip H6 *)
      inv H. inv H0.
        rewrite H4. reflexivity. eapply deleteMin2_elem. eassumption.
        eapply IHo; eauto.
        specialize (H6 _ H1). apply deleteMin2_elem in e0. specialize (H4 _ e0). admit. (* transitivity *)
Admitted.

Lemma deleteMin2_countBT :
  forall (A : Type) (cmp : A -> A -> comparison) (p : A -> bool) (m : A) (h h' : SplayTree A),
    isBST cmp h -> deleteMin2 h = Some (m, h') ->
      countBT p h =
      (if p m then 1 else 0) + countBT p h'.
Proof.
(* TODO
  intros A p m h. revert p m.
  functional induction deleteMin2 h; cbn; inv 1; intros.
    destruct l; cbn in *.
      inv H. destruct (p m); reflexivity.
      destruct (deleteMin2 l1). try destruct p; inv e0.
    inv H. destruct l; cbn in *.
      inv e0.
      destruct (deleteMin2 l1); try destruct p;
      inv e0; specialize (IHo x _ _ ltac:(inv H4) eq_refl);
      rewrite IHo; trich.
*)
Admitted.