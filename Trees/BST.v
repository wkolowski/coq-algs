Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

From mathcomp Require Import ssreflect.

Inductive is_bst {A : LinDec} : BTree A -> Prop :=
    | is_bst_empty : is_bst empty
    | is_bst_node : forall (v : A) (l r : BTree A),
        (forall x : A, elem x l -> leq x v) -> is_bst l ->
        (forall x : A, elem x r -> leq v x) -> is_bst r ->
        is_bst (node v l r).

Hint Constructors BTree elem is_bst.

Lemma is_bst_inv_l : forall (A : LinDec) (v : A) (l r : BTree A),
    is_bst (node v l r) -> is_bst l.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_bst_inv_r : forall (A : LinDec) (v : A) (l r : BTree A),
    is_bst (node v l r) -> is_bst r.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_bst_inv_leq_l : forall (A : LinDec) (a v : A) (l r : BTree A),
    is_bst (node v l r) -> elem a l -> leq a v.
Proof.
  inversion 1; auto.
Qed.

Lemma is_bst_inv_leq_r : forall (A : LinDec) (a v : A) (l r : BTree A),
    is_bst (node v l r) -> elem a r -> leq v a.
Proof.
  inversion 1; auto.
Qed.

Lemma is_bst_inv_elem_l :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    is_bst (node v l r) -> elem x (node v l r) ->
      leq x v -> x <> v -> elem x l.
Proof.
  inversion 1; inversion 1; subst; intros.
    1-2: by [].
    move: (H5 _ H9) => H'. have Heq : x = v by eapply leq_antisym.
      contradiction.
Qed.

Lemma is_bst_inv_elem_r :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    is_bst (node v l r) -> elem x (node v l r) ->
      leq v x -> x <> v -> elem x r.
Proof.
  do 2 inversion 1; subst; intros.
    contradiction.
    move: (H3 _ H9) => H'. have Heq : x = v by eapply leq_antisym.
      contradiction.
    by [].
Qed.

Hint Resolve is_bst_inv_l is_bst_inv_r.

Record BST (A : LinDec) : Type :=
{
    tree :> BTree A;
    prop : is_bst tree
}.

Theorem BST_elem_dec : forall {A : LinDec} (a : A) (t : BTree A),
    is_bst t -> {elem a t} + {~ elem a t}.
Proof.
  intros. elim: t H => [| v l Hl r Hr] H.
    right. inversion 1.
    case (LinDec_eqb_spec _ a v) => [-> | Hneq]; first by auto.
      case (leqb_spec a v) => [Hleq | Hnleq].
        case: Hl => [| H' | H']; eauto. right. inversion 1; subst; auto.
          eapply is_bst_inv_leq_r in H2; eauto.
        case: Hr => [| H' | H']; eauto. right. inversion 1; subst; auto.
          eapply is_bst_inv_leq_l in H2; eauto.
Restart.
  intros. elim: t H => [| v l Hl r Hr] H.
    right. inversion 1.
    case (LinDec_eqb_spec _ a v) => [-> | Hneq]; first by auto.
      case (leqb_spec a v) => [Hleq | Hnleq]; [case: Hl | case: Hr];
      eauto; right; inversion 1; subst; auto.
        eapply is_bst_inv_leq_r in H2; eauto.
        eapply is_bst_inv_leq_l in H2; eauto.
Defined.

Fixpoint BTree_ins {A : LinDec} (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => node x empty empty
    | node v l r =>
        if x <=? v
        then node v (BTree_ins x l) r
        else node v l (BTree_ins x r)
end.

Lemma elem_ins : forall (A : LinDec) (x a : A) (t : BTree A),
    elem x (BTree_ins a t) -> x = a \/ elem x t.
Proof.
  move=> A x a t. elim: t => [| v l Hl r Hr] //=.
    inversion 1; auto.
    dec; inversion H; subst; auto.
      case: Hl; auto.
      case: Hr; auto.
Qed.

Theorem BTree_ins_is_bst : forall (A : LinDec) (a : A) (bt : BTree A),
    is_bst bt -> is_bst (BTree_ins a bt).
Proof.
  move=> A a bt. elim: bt a => [| v l Hl r Hr] a //=.
    constructor; eauto; inversion 1.
    dec; inversion H; subst.
      1-2: constructor; auto; move=> x Helt;
      case: (elem_ins _ _ _ _ Helt) => [-> |]; eauto.
Qed.

Fixpoint min {A : Type} (bta : BTree A) : option A :=
match bta with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

Lemma min_elem_l :
    forall (A : LinDec) (t : BTree A) (m v v' : A) (ll lr r : BTree A),
    min t = Some m -> t = node v (node v' ll lr) r -> elem m (node v' ll lr).
Proof.
  destruct t.
    inversion 1.
    induction t1; intros; inversion H0; subst. destruct ll; simpl in *.
      inversion H. auto.
      apply elem_left. eapply IHt1_1; eauto.
Restart.
  inversion 2; subst; clear H1.
  elim: ll lr v' H; intros.
    inversion H. auto.
    constructor. apply (H b0 a). auto.
Qed.

Theorem bst_min_spec : forall (A : LinDec) (m : A) (bst : BTree A),
    is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.
Proof.
  induction 3.
    destruct l.
      simpl in *. inversion H0; auto.
      eapply is_bst_inv_leq_l. eauto. eapply min_elem_l; eauto.
    destruct l.
      inversion H1.
      apply IHelem; try eapply is_bst_inv_l; eauto.
    inversion H; subst. destruct l.
      inversion H0; subst. apply H7. assumption.
      apply leq_trans with v.
        eapply is_bst_inv_leq_l; eauto. eapply min_elem_l; eauto.
        apply H7. assumption.
Qed.

Theorem toList_sorted : forall (A : LinDec) (t : BTree A),
    is_bst t -> sorted A (toList t).
Proof.
  induction t as [| v l Hl r Hr]; intro.
    simpl. constructor.
    inversion H; subst; cbn. apply sorted_app_all; auto.
      Focus 2. intros. apply elem_In in H0. auto.
      case_eq (toList r); intros; subst; auto.
        constructor.
          apply H5. rewrite <- elem_In. rewrite H0. cbn. auto.
          rewrite <- H0. auto.
Qed.

Function fromList (A : LinDec) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => BTree_ins h (fromList A t)
end.

Definition treeSort (A : LinDec) (l : list A) : list A :=
    toList (fromList A l).

Fixpoint count_BTree (A : LinDec) (x : A) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        let n := count_BTree A x l in
        let m := count_BTree A x r in
        if x =? v then S (n + m) else n + m
end.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (toList t) = count_BTree A x t.
Proof.
  intros. elim: t x => [| v l Hl r Hr] //= x.
    by dec; rewrite count_app Hl //= Hr; dec.
Qed.

Lemma count_ins :
  forall (A : LinDec) (x h : A) (t : BTree A),
    count_BTree A x (BTree_ins h t) =
      if x =? h
      then S (count_BTree A x t)
      else count_BTree A x t.
Proof.
  intros. elim: t => [| v l Hl r Hr] //=; repeat dec.
Qed.

Theorem treeSort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (treeSort A l).
Proof.
  unfold treeSort, perm. intros.
  elim: l => [| h t IH] //=.
    by rewrite count_toList count_ins -count_toList -IH.
Qed.

Lemma fromList_is_bst :
  forall (A : LinDec) (l : list A), is_bst (fromList A l).
Proof.
  intros. elim: l => [| h t IH] //=.
    by apply BTree_ins_is_bst.
Qed.

Theorem treeSort_sorted :
  forall (A : LinDec) (l : list A), sorted A (treeSort A l).
Proof.
  unfold treeSort. intros. apply toList_sorted. apply fromList_is_bst.
Qed.

Instance Sort_treeSort : Sort :=
{
    sort := treeSort;
    sort_sorted := treeSort_sorted;
    sort_perm := treeSort_perm
}.