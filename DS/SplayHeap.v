Require Export BTree.
Require Import BST.
Require Export Sorting.Sort.

Set Implicit Arguments.

Definition SplayHeap (A : Type) : Type := BTree A.

Function partition {A : Type} (p : A -> A -> bool) (pivot : A) (h : SplayHeap A)
  : SplayHeap A * SplayHeap A :=
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
  {A : Type} (h : SplayHeap A) : bool :=
match h with
    | empty => true
    | _ => false
end.

Definition insert
  {A : Type} (p : A -> A -> bool) (x : A) (h : SplayHeap A) : SplayHeap A :=
    let
      (smaller, bigger) := partition p x h
    in
      node x smaller bigger.

Function findMin'
  {A : Type} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node m empty _ => Some m
    | node _ l _ => findMin' l
end.

Function findMin
  {A : Type} (h : SplayHeap A) : option A :=
match h with
    | empty => None
    | node v l r =>
        match findMin l with
            | None => Some v
            | Some m => Some m
        end
end.

Function deleteMin
  {A : Type} (h : SplayHeap A) : SplayHeap A :=
match h with
    | empty => empty
    | node _ empty r => r
    | node v l r => node v (deleteMin l) r
end.

Function deleteMin'
  {A : Type} (h : SplayHeap A) : option A * SplayHeap A :=
match h with
    | empty => (None, empty)
    | node m empty r => (Some m, r)
    | node v l r =>
        let '(min, l') := deleteMin' l in (min, node v l' r)
end.

Function deleteMin2
  {A : Type} (h : SplayHeap A) : option (A * SplayHeap A) :=
match h with
    | empty => None
    | node v l r =>
        match deleteMin2 l with
            | None => Some (v, r)
            | Some (min, l') => Some (min, node v l' r)
        end
end.

Function merge {A : Type} (p : A -> A -> bool) (h1 h2 : SplayHeap A) : SplayHeap A :=
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
  forall (A : Type) (p : A -> A -> bool) (x : A) (h l r : SplayHeap A),
    partition p x h = (l, r) ->
      isEmpty h = true <-> isEmpty l = true /\ isEmpty r = true.
Proof.
  split; intros; functional induction @partition A p x h; inv H; firstorder.
    all: cbn in *; congruence.
Qed.

Lemma isEmpty_partition_false :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h l r : SplayHeap A),
    partition p x h = (l, r) ->
      isEmpty h = false <-> isEmpty l = false \/ isEmpty r = false.
Proof.
  split; intros; functional induction @partition A p x h; inv H; firstorder.
Qed.

Lemma isEmpty_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : SplayHeap A),
    isEmpty (insert p x h) = false.
Proof.
  intros. unfold insert. case_eq (partition p x h); intros small big H.
  cbn. reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayHeap A),
    isEmpty (merge p h1 h2) = true <->
      isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  destruct h1; cbn; intros; try destruct (partition p a h2); firstorder.
    cbn in H. congruence.
Qed.

Lemma isEmpty_merge_false :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : SplayHeap A),
    isEmpty (merge p h1 h2) = false <->
      isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  destruct h1; cbn; intros; try destruct (partition p a h2); firstorder congruence. 
Qed.

Lemma isEmpty_size :
  forall (A : Type) (h : SplayHeap A),
    isEmpty h = true <-> size h = 0.
Proof.
  split; destruct h; cbn in *; intros; congruence.
Qed.

Lemma isEmpty_count_BTree :
  forall (A : Type) (p : A -> bool) (t : SplayHeap A),
    isEmpty t = true -> count_BTree p t = 0.
Proof.
  destruct t; dec.
Qed.

(** Properties of [partition]. *)

(* TODO: fix elem *)
Lemma partition_elem :
  forall (A : Type) (p : A -> A -> bool) (x pivot : A) (h l r : SplayHeap A),
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
    | H : isBST ?x, H' : isBST ?x -> _ |- _ => specialize (H' H)
    | H : isBST empty |- _ => inv H
    | H : isBST (node _ _ _) |- _ => inv H
end; auto.

(*
Check LinDec_not_leq.

Lemma partition_isBST :
  forall (A : Type) (p : A -> A -> comparison) (x : A) (h l r : SplayHeap A),
    partition p x h = (l, r) -> isBST p h -> isBST p (node x l r).
Proof.
  intros A p x h.
  functional induction @partition A p x h;
  inv 1; inv 1; aux. Focus 2.
  try specialize (IHp0 _ _ _ e3 H7); try specialize (IHp0 _ _ _ e3 H9);
  try inv IHp0; repeat constructor; aux. inv H.  Focus 2. eapply partition_elem in H0.
  firstorder. dec.
Unshelve.
  all: assumption.
Qed.

Lemma partition_size :
  forall (A : Type) (x : A) (h h1 h2 : SplayHeap A),
    partition x h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  intros A x h. functional induction partition x h; cbn;
  inv 1; dec; rewrite (IHp _ _ e3); lia.
Qed.

Lemma partition_count_BTree :
  forall (A : Type) (p : A -> bool) (pivot : A) (h h1 h2 : SplayHeap A),
    partition pivot h = (h1, h2) ->
      count_BTree p h = count_BTree p h1 + count_BTree p h2.
Proof.
  intros until h.
  functional induction partition pivot h; cbn; inv 1.
(*
 rewrite ?(IHp0 _ _ _ e3). cbn.  destruct (p x), (p y). lia.
*)
Admitted.

(** Properties of [insert]. *)
Lemma insert_elem :
  forall (A : Type) (x : A) (h : SplayHeap A),
    elem x (insert x h).
Proof.
  intros. unfold insert. destruct (partition x h). constructor.
Qed.

Lemma insert_isBST :
  forall (A : Type) (x : A) (h : SplayHeap A),
    isBST h -> isBST (insert x h).
Proof.
  intros. unfold insert. case_eq (partition x h); intros l r H'.
  eapply partition_isBST; eauto.
Qed.

Lemma insert_size :
  forall (A : Type) (x : A) (h : SplayHeap A),
    size (insert x h) = 1 + size h.
Proof.
  intros. unfold insert. case_eq (partition x h); intros smaller bigger H.
  cbn. f_equal. symmetry. eapply partition_size. eassumption.
Qed.

Lemma insert_count_BTree :
  forall (A : Type) (p : A -> bool) (x : A) (h : SplayHeap A),
    count_BTree p (insert x h) =
    (if p x then S else id) (count_BTree p h).
Proof.
  intros. unfold insert.
  case_eq (partition x h); intros.
  apply (partition_count_BTree p) in H. rewrite H.
  cbn. destruct (p x); reflexivity.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem :
  forall (A : Type) (x : A) (h1 h2 : SplayHeap A),
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

Lemma merge_isBST :
  forall (A : Type) (h1 h2 : SplayHeap A),
    isBST h1 -> isBST h2 -> isBST (merge h1 h2).
Proof.
  induction h1 as [| v l IHl r IHr]; cbn; intros.
    assumption.
    case_eq (partition v h2); intros small big Hp.
      apply partition_isBST in Hp; aux. constructor; intros; auto.
        apply merge_elem in H. firstorder.
        apply merge_elem in H. firstorder.
Qed.

Lemma merge_size :
  forall (A : Type) (h1 h2 : SplayHeap A),
    size (merge h1 h2) = size h1 + size h2.
Proof.
  intros. functional induction @merge A h1 h2; cbn.
    reflexivity. inv e0.
    rewrite IHs, IHs0. apply partition_size in H0. rewrite H0. lia.
Qed.

Lemma merge_count_BTree :
  forall (A : Type) (p : A -> bool) (h1 h2 : SplayHeap A),
    count_BTree p (merge h1 h2) = count_BTree p h1 + count_BTree p h2.
Proof.
  induction h1; cbn; intros.
    reflexivity.
    case_eq (partition a h2); cbn; intros.
      apply (partition_count_BTree p) in H.
      rewrite IHh1_1, IHh1_2, H.
      destruct (p a); lia.
Qed.

(** Properties of [findMin] *)

Lemma findMin_elem :
  forall (A : Type) (m : A) (h : SplayHeap A),
    findMin h = Some m -> elem m h.
Proof.
  intros. functional induction @findMin A h; inv H.
Qed.

Lemma findMin_elem_node :
  forall (A : Type) (m v : A) (l r : SplayHeap A),
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
  forall (A : Type) (v : A) (l r : SplayHeap A),
    findMin (node v l r) = Some v \/
    findMin (node v l r) = findMin l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin A h; inv Heqh.
Qed.

Lemma findMin_spec :
  forall (A : Type) (m : A) (h : SplayHeap A),
    isBST h -> findMin h = Some m ->
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
  forall (A : Type) (m : A) (h : SplayHeap A),
    findMin' h = Some m -> elem m h.
Proof.
  intros. functional induction @findMin' A h; inv H.
Qed.

Lemma findMin'_elem_node :
  forall (A : Type) (m v : A) (l r : SplayHeap A),
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
  forall (A : Type) (v : A) (l r : SplayHeap A),
    findMin' (node v l r) = Some v \/
    findMin' (node v l r) = findMin' l.
Proof.
  intros. remember (node v l r) as h.
  functional induction @findMin' A h; inv Heqh.
Qed.

Lemma findMin'_spec :
  forall (A : Type) (m : A) (h : SplayHeap A),
    isBST h -> findMin' h = Some m ->
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
  forall (A : Type) (m : A) (h h' : SplayHeap A),
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
  forall (A : Type) (h : SplayHeap A),
    deleteMin2 h = None -> isEmpty h = true.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_isEmpty_Some :
  forall (A : Type) (m : A) (h h' : SplayHeap A),
    deleteMin2 h = Some (m, h') -> isEmpty h = false.
Proof.
  intros. functional induction @deleteMin2 A h; cbn; inv H.
Qed.

Lemma deleteMin2_elem :
  forall (A : Type) (m : A) (h h' : SplayHeap A),
    deleteMin2 h = Some (m, h') -> elem m h.
Proof.
  intros A m h. revert m.
  functional induction @deleteMin2 A h; inv 1; eauto.
Qed.

Lemma deleteMin2_elem_node :
  forall (A : Type) (m v : A) (l r h' : SplayHeap A),
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
  forall (A : Type) (v : A) (l r : SplayHeap A),
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
  forall (A : Type) (m : A) (h h' : SplayHeap A),
    isBST h -> deleteMin2 h = Some (m, h') ->
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
  forall (A : Type) (p : A -> bool) (m : A) (h h' : SplayHeap A),
    isBST h -> deleteMin2 h = Some (m, h') ->
      count_BTree p h =
      (if p m then S else id) (count_BTree p h').
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
      rewrite IHo; dec.
*)
Admitted.
*)