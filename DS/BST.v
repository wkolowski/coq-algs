Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

From mathcomp Require Import ssreflect.

(* TODO: fix the definition of [is_bst]. *)
Inductive is_bst {A : LinDec} : BTree A -> Prop :=
    | is_bst_empty : is_bst empty
    | is_bst_node : forall (v : A) (l r : BTree A),
        (forall x : A, elem x l -> leq x v) -> is_bst l ->
        (forall x : A, elem x r -> leq v x) -> is_bst r ->
        is_bst (node v l r).

Hint Constructors elem is_bst.

Lemma is_bst_inv_l : forall (A : LinDec) (v : A) (l r : BTree A),
    is_bst (node v l r) -> is_bst l.
Proof. inv 1. Qed.

Lemma is_bst_inv_r : forall (A : LinDec) (v : A) (l r : BTree A),
    is_bst (node v l r) -> is_bst r.
Proof. inv 1. Qed.

Lemma is_bst_inv_leq_l : forall (A : LinDec) (a v : A) (l r : BTree A),
    is_bst (node v l r) -> elem a l -> leq a v.
Proof. inv 1. Qed.

Lemma is_bst_inv_leq_r : forall (A : LinDec) (a v : A) (l r : BTree A),
    is_bst (node v l r) -> elem a r -> leq v a.
Proof. inv 1. Qed.

Lemma is_bst_inv_elem_l :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    is_bst (node v l r) -> elem x (node v l r) ->
      leq x v -> x <> v -> elem x l.
Proof.
  do 2 inv 1; intros. specialize (H5 _ H1). contradiction H0. dec.
Qed.

Lemma is_bst_inv_elem_r :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    is_bst (node v l r) -> elem x (node v l r) ->
      leq v x -> x <> v -> elem x r.
Proof.
  do 2 inv 1; intros. specialize (H3 _ H1). contradiction H0. dec.
Qed.

Hint Resolve is_bst_inv_l is_bst_inv_r.

Record BST (A : LinDec) : Type :=
{
    tree :> BTree A;
    prop : is_bst tree
}.

Theorem BST_elem_dec :
  forall {A : LinDec} (a : A) (t : BTree A),
    is_bst t -> {elem a t} + {~ elem a t}.
Proof.
  intros. elim: t H => [| v l Hl r Hr] H.
    right. inv 1.
    case (LinDec_eqb_spec _ a v) => [-> | Hneq]; first by auto.
      case (leqb_spec a v) => [Hleq | Hnleq].
        case: Hl => [| H' | H']; eauto. right. inv 1.
          eapply is_bst_inv_leq_r in H2; eauto.
        case: Hr => [| H' | H']; eauto. right. inv 1.
          eapply is_bst_inv_leq_l in H2; eauto.
Restart.
  intros. elim: t H => [| v l Hl r Hr] H.
    right. inv 1.
    case (LinDec_eqb_spec _ a v) => [-> | Hneq]; first by auto.
      case (leqb_spec a v) => [Hleq | Hnleq]; [case: Hl | case: Hr];
      eauto; right; inv 1.
        eapply is_bst_inv_leq_r in H2; eauto.
        eapply is_bst_inv_leq_l in H2; eauto.
Defined.

Function elem_decb_BST {A : LinDec} (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        if x <=? v
        then
          if v <=? x
          then true
          else elem_decb_BST x l
        else
          elem_decb_BST x r
end.

Inductive isBST {A : LinDec} : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, elem x l -> x ≤ v) -> isBST l ->
          (forall x : A, elem x r -> ~ x ≤ v) -> isBST r ->
            isBST (node v l r).

Lemma elem_decb_BST_reflect :
  forall (A : LinDec) (x : A) (t : BTree A),
    isBST t -> reflect (elem x t) (elem_decb_BST x t).
Proof.
  intros. functional induction @elem_decb_BST A x t; dec.
    constructor. inv 1.
    assert (x = v) by dec. subst. auto.
    destruct (IHb ltac:(inv H)); constructor.
      auto.
      inv 1. inv H.
    destruct (IHb ltac:(inv H)); constructor.
      auto.
      inv 1. inv H.
Qed.

Function elem_decb_aux_BST
  {A : LinDec} (x : A) (ocandidate : option A) (t : BTree A) : bool :=
match t with
    | empty =>
        match ocandidate with
            | None => false
            | Some x' => x =? x'
        end
    | node v l r =>
        if x <=? v
        then elem_decb_aux_BST x (Some v) l
        else elem_decb_aux_BST x ocandidate r
end.

Definition elem_decb'_BST
  {A : LinDec} (x : A) (t : BTree A) : bool :=
    elem_decb_aux_BST x None t.

(*Lemma elem_decb_aux_BST_spec :
  forall (A : LinDec) (x y : A) (t : BTree A),
    isBST t -> elem y t ->
      elem_decb_aux_BST x (Some y) t =
      (x =? y) || elem_decb_aux_BST x None t.
Proof.
  intros. gen y; gen x. induction t; cbn; intros.
    destruct (x =? y); reflexivity.
    inv H. inv H0.
      Focus 2. dec. rewrite IHt1.
Restart.
  induction 2; cbn.
    dec.
Abort.*)

Lemma elem_decb_aux_BST_true :
  forall (A : LinDec) (x : A) (t : BTree A),
    isBST t -> elem_decb_aux_BST x (Some x) t = true.
Proof.
  intros A x t; gen x.
  induction t; cbn; intros; dec.
Abort.

Lemma elem_decb_aux_BST_reflect :
  forall (A : LinDec) (x : A) (ocandidate : option A) (t : BTree A),
    isBST t -> 
(*    match ocandidate with
        | None => True
        | Some v => elem v t
    end ->*)
      reflect (elem x t) (elem_decb_aux_BST x ocandidate t).
Proof.
  intros. gen ocandidate; gen x.
  induction t as [| v l IHl r IHr]; intros.
    destruct ocandidate; cbn.
      dec; constructor.
        admit.
        inv 1.
      constructor. inv 1.
    cbn. dec.
      case_eq (x =? v); intros.
        dec. destruct (IHl ltac:(inv H) v (Some v)).
          auto.
          constructor. inversion 1; subst; try contradiction.
Abort.

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
    inv 1.
    dec; inv H.
      case: Hl; auto.
      case: Hr; auto.
Qed.

Theorem BTree_ins_is_bst : forall (A : LinDec) (a : A) (bt : BTree A),
    is_bst bt -> is_bst (BTree_ins a bt).
Proof.
  move=> A a bt. elim: bt a => [| v l Hl r Hr] a //=.
    constructor; eauto; inv 1.
    dec; inv H.
      1-2: constructor; auto; move=> x Helt;
      case: (elem_ins _ _ _ _ Helt) => [-> |]; eauto.
Qed.

Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

Lemma min_elem_l :
    forall (A : LinDec) (t : BTree A) (m v v' : A) (ll lr r : BTree A),
    min t = Some m -> t = node v (node v' ll lr) r -> elem m (node v' ll lr).
Proof.
  destruct t.
    inv 1.
    induction t1; intros; inv H0. destruct ll; simpl in *.
      inv H. auto.
      apply elem_left. eapply IHt1_1; eauto.
Restart.
  inv 2. clear H1. elim: ll lr v' H.
    inv 1.
    auto.
Qed.

Theorem bst_min_spec : forall (A : LinDec) (m : A) (bst : BTree A),
    is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.
Proof.
  induction 3.
    destruct l.
      simpl in *. inv H0.
      eapply is_bst_inv_leq_l. eauto. eapply min_elem_l; eauto.
    destruct l.
      inv H1.
      apply IHelem; try eapply is_bst_inv_l; eauto.
    inv H. destruct l.
      inv H0.
      apply leq_trans with v.
        eapply is_bst_inv_leq_l; eauto. eapply min_elem_l; eauto.
        apply H7. assumption.
Qed.

(** [fromList] and its variants. *)
Function fromList (A : LinDec) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => BTree_ins h (fromList A t)
end.

Definition fromList' {A : LinDec} (l : list A) : BTree A :=
  fold_right (fun h t => BTree_ins h t) empty l.

Lemma count_ins :
  forall (A : LinDec) (x h : A) (t : BTree A),
    count_BTree x (BTree_ins h t) =
      if x =? h
      then S (count_BTree x t)
      else count_BTree x t.
Proof.
  intros. elim: t => [| v l Hl r Hr] //=; repeat dec.
Qed.

Theorem fromList'_spec : @fromList' = @fromList.
Proof.
  ext A. ext l. unfold fromList'.
  remember empty as t. generalize dependent t.
  functional induction @fromList A l; cbn; intros.
    trivial.
    rewrite IHb; auto.
Qed.

Theorem BTree_toList_sorted :
  forall (A : LinDec) (t : BTree A),
    is_bst t -> sorted A (@BTree_toList (@carrier A) t).
Proof.
  induction t as [| v l Hl r Hr]; cbn; intros.
    constructor.
    inv H. apply sorted_app_all; auto.
      case_eq (BTree_toList r); intros; subst; auto. constructor.
        apply H5. rewrite <- toList_In_elem. rewrite H. cbn. auto.
        rewrite <- H. auto.
      intros. apply toList_In_elem in H. auto.
Qed.

Theorem BTree_toList'_sorted :
  forall (A : LinDec) (t : BTree A),
    is_bst t -> sorted A (BTree_toList' t).
Proof.
  rewrite BTree_toList'_spec. apply BTree_toList_sorted.
Qed.

Lemma fromList_is_bst :
  forall (A : LinDec) (l : list A), is_bst (fromList A l).
Proof.
  intros. elim: l => [| h t IH] //=.
    by apply BTree_ins_is_bst.
Qed.

Lemma fromList'_is_bst :
  forall (A : LinDec) (l : list A), is_bst (fromList' l).
Proof.
  intros. rewrite fromList'_spec. apply fromList_is_bst.
Qed.