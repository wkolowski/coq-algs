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

(* toList, fromList and their variants *)
Function toList {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => toList l ++ v :: toList r
end.

Function fromList (A : LinDec) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => BTree_ins h (fromList A t)
end.

Function toList'_aux {A : LinDec} (t : BTree A) (acc : list A) : list A :=
match t with
    | empty => acc
    | node v l r => toList'_aux l (v :: toList'_aux r acc)
end.

Definition toList' {A : LinDec} (t : BTree A) : list A :=
  toList'_aux t [].

Function fromList' {A : LinDec} (l : list A) : BTree A :=
  fold_left (fun t x => BTree_ins x t) l empty.

(* Counting elements in a binary tree. *)
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

(* Lemmas for toList and others. *)
Lemma toList'_aux_spec :
  forall (A : LinDec) (t : BTree A) (acc : list A),
    toList'_aux t acc = toList t ++ acc.
Proof.
  intros. functional induction @toList'_aux A t acc; cbn.
    trivial.
    rewrite <- app_assoc. cbn. rewrite <- IHl, <- IHl0. trivial.
Qed.

Require Import FunctionalExtensionality.

Theorem toList'_spec : @toList' = @toList.
Proof.
  extensionality A. extensionality t. unfold toList'.
  rewrite toList'_aux_spec app_nil_r. trivial.
Qed.

Function merge {A : LinDec} (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => t2
    | node v l r => merge l (merge r (BTree_ins v t2))
end.

Lemma merge_empty_r :
  forall (A : LinDec) (t : BTree A),
    merge t empty = t.
Proof.
  intros. remember empty as t'.
  functional induction @merge A t t'.
    trivial.
Abort.

Lemma fromList'_spec :
  forall (A : LinDec) (l : list A) (t : BTree A),
    fold_left (fun t x => BTree_ins x t) l t = merge t (fromList A l).
Proof.
  intros. generalize dependent t.
  functional induction @fromList A l; cbn; intros.
    trivial.
Abort.

Theorem fromList_spec : @fromList' = @fromList.
Proof.
  extensionality A. extensionality l. unfold fromList'.
  remember empty as t. generalize dependent t.
  functional induction @fromList A l; cbn; intros.
    trivial.
    fold fromList'.
Abort.

Lemma toList_In_elem :
  forall (A : Type) (x : A) (t : BTree A),
    In x (toList t) <-> elem x t.
Proof.
  split.
    elim: t x => [| v l Hl r Hr] x H.
      inversion H.
      cbn in H. apply in_app_or in H. do 2 (destruct H; subst; auto).
    elim: t x => [| v l Hl r Hr] x H //=; inversion H; subst;
    apply in_or_app; cbn; eauto.
Qed.

Require Import RCCBase.

Theorem toList_sorted :
  forall (A : LinDec) (t : BTree A),
    is_bst t -> sorted A (@toList (@carrier A) t).
Proof.
  induction t as [| v l Hl r Hr]; cbn; intros.
    constructor.
    inv H. apply sorted_app_all; auto.
      case_eq (toList r); intros; subst; auto.
        constructor.
          apply H5. rewrite <- toList_In_elem. rewrite H0. cbn. auto.
          rewrite <- H0. auto.
      intros. apply toList_In_elem in H0. auto.
Qed.

Lemma fromList_is_bst :
  forall (A : LinDec) (l : list A), is_bst (fromList A l).
Proof.
  intros. elim: l => [| h t IH] //=.
    by apply BTree_ins_is_bst.
Qed.

Theorem toList'_sorted :
  forall (A : LinDec) (t : BTree A),
    is_bst t -> sorted A (toList' t).
Proof.
  rewrite toList'_spec. apply toList_sorted.
Qed.

Lemma fromList'_is_bst :
  forall (A : LinDec) (l : list A), is_bst (fromList' l).
Proof.
  intros. induction l as [| h t]; cbn.
    trivial.
Abort.