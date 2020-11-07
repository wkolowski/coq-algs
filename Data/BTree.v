Require Import RCCBase.

Require Import Ord.
Require Import ListLemmas.
Require Import Sorting.Sort.

Require Export Classes.EquivDec.
(* Require Export Compare_trich. *)

Inductive BTree (A : Type) : Type :=
    | empty : BTree A
    | node : A -> BTree A -> BTree A -> BTree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

Inductive Elem {A : Type} (a : A) : BTree A -> Prop :=
    | Elem_root : forall l r : BTree A, Elem a (node a l r)
    | Elem_left : forall (v : A) (l r : BTree A),
        Elem a l -> Elem a (node v l r)
    | Elem_right : forall (v : A) (l r : BTree A),
        Elem a r -> Elem a (node v l r).

Hint Constructors Elem : core.

Lemma Elem_node :
  forall {A : Type} (x v : A) (l r : BTree A),
    Elem x (node v l r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  split; inv 1; firstorder.
Qed.

Definition singleton {A : Type} (x : A) : BTree A :=
  node x empty empty.

Fixpoint Elem_decb
  {A : Ord} (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        (x =? v) || Elem_decb x l || Elem_decb x r
end.

Definition root {A : Type} (bt : BTree A) : option A :=
match bt with
    | empty => None
    | node v l r => Some v
end.

Definition isEmpty {A : Type} (t : BTree A) : bool :=
match t with
    | empty => true
    | _ => false
end.

(* [BTree_toList], [fromList] and their variants *)
Function BTree_toList {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => BTree_toList l ++ v :: BTree_toList r
end.

Function BTree_toList'_aux
  {A : Ord} (t : BTree A) (acc : list A) : list A :=
match t with
    | empty => acc
    | node v l r => BTree_toList'_aux l (v :: BTree_toList'_aux r acc)
end.

Definition BTree_toList' {A : Ord} (t : BTree A) : list A :=
  BTree_toList'_aux t [].

(** [size] and counting. *)
Fixpoint size {A : Type} (bt : BTree A) : nat :=
match bt with
    | empty => 0
    | node _ l r => S (size l + size r)
end.

(* Fixpoint countBT {A : Type} (p : A -> bool) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        let n := countBT p l in
        let m := countBT p r in
        if p v then S (n + m) else n + m
end.
 *)

Fixpoint countBT {A : Type} (p : A -> bool) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        (if p v then 1 else 0) + countBT p l + countBT p r
end.

(** * Tactics *)
Ltac Elem :=
  intros; unfold singleton in *; cbn in *; subst; repeat
match goal with
    | |- Elem ?x (node ?x _ _) => constructor
    | H : Elem _ empty |- _ => inv H
    | H : Elem _ (node _ empty empty) |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : Elem _ _ \/ Elem _ _ |- _ => destruct H
end; auto.

(** * Theorems *)

(** Properties of [Elem] and [Elem_decb]. *)

Lemma Elem_decb_reflect :
  forall (A : Ord) (x : A) (t : BTree A),
    BoolSpec (Elem x t) (~ Elem x t) (Elem_decb x t).
Proof.
  induction t as [| v l IHl r IHr]; cbn.
    constructor. inv 1.
    unfold orb. trich. destruct IHl, IHr; auto.
      constructor. inv 1.
Qed.

(** Properties of casts to/from list. *)

Lemma BTree_toList'_aux_spec :
  forall (A : Ord) (t : BTree A) (acc : list A),
    BTree_toList'_aux t acc = BTree_toList t ++ acc.
Proof.
  intros. functional induction @BTree_toList'_aux A t acc; cbn.
    trivial.
    rewrite <- app_assoc. cbn. rewrite <- IHl, <- IHl0. trivial.
Qed.

Theorem BTree_toList'_spec : @BTree_toList' = @BTree_toList.
Proof.
  ext A. extensionality t. unfold BTree_toList'.
  rewrite BTree_toList'_aux_spec, app_nil_r. trivial.
Qed.

Lemma toList_In_Elem :
  forall (A : Type) (x : A) (t : BTree A),
    In x (BTree_toList t) <-> Elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; apply in_or_app; firstorder.
Qed.

(** Properties of [size]. *)

Lemma size_swap :
  forall (A : Type) (v : A) (l r : BTree A),
    size (node v l r) = size (node v r l).
Proof.
  intros. cbn. rewrite plus_comm. trivial.
Qed.

Lemma size_length :
  forall (A : Type) (t : BTree A),
    length (BTree_toList t) = size t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite !app_length. cbn. rewrite IHt1, IHt2. lia.
Qed.

Lemma count_toList :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    count p (BTree_toList t) = countBT p t.
Proof.
  induction t; cbn; rewrite ?count_app.
    reflexivity.
    cbn. rewrite IHt1, IHt2. destruct (p a); cbn.
      rewrite plus_n_Sm. reflexivity.
      reflexivity.
Qed.

(** Properties of [empty]. *)
Lemma Elem_empty :
  forall (A : Ord) (x : A), ~ Elem x empty.
Proof. inv 1. Qed.

Lemma size_empty :
  forall A : Ord, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma countBT_empty :
  forall (A : Type) (p : A -> bool),
    countBT p empty = 0.
Proof. reflexivity. Qed.

(** Properties of [singleton]. *)

Lemma Elem_singleton :
  forall (A : Ord) (x y : A),
    Elem x (singleton y) <-> x = y.
Proof.
  split; Elem.
Qed.

Lemma size_singleton :
  forall (A : Ord) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma countBT_singleton :
  forall (A : Type) (p : A -> bool) (x : A),
    countBT p (singleton x) = if p x then 1 else 0.
Proof.
  intros. unfold singleton. cbn. destruct (p x); reflexivity.
Qed.

(** Properties of [isEmpty]. *)

Lemma isEmpty_Elem_false :
  forall (A : Ord) (t : BTree A),
    isEmpty t = false <-> exists x : A, Elem x t.
Proof.
  split; destruct t; cbn; intros.
    congruence.
    eauto.
    inv H. inv H0.
    reflexivity.
Qed.

Lemma isEmpty_Elem_true :
  forall (A : Ord) (t : BTree A),
    isEmpty t = true <-> forall x : A, ~ Elem x t.
Proof.
  split; destruct t; cbn; firstorder.
    inv 1.
    congruence.
    contradiction (H c). constructor.
Qed.

Lemma isEmpty_empty :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> t = empty.
Proof.
  destruct t; cbn; firstorder congruence.
Qed.

Lemma isEmpty_singleton :
  forall (A : Type) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma isEmpty_size_false :
  forall (A : Type) (t : BTree A),
    isEmpty t = false <-> size t <> 0.
Proof.
  split; destruct t; cbn; firstorder congruence.
Qed.

Lemma isEmpty_size_true :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> size t = 0.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_countBT :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> forall p : A -> bool, countBT p t = 0.
Proof.
  split; destruct t; cbn; try congruence.
    intro. specialize (H (fun _ => true)). cbn in H. inversion H.
Qed.

(** [mirror] *)

Fixpoint mirror {A : Type} (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r => node v (mirror r) (mirror l)
end.

Lemma mirror_inv :
  forall (A : Type) (t : BTree A),
    mirror (mirror t) = t.
Proof.
  induction t; cbn; rewrite ?IHt1, ?IHt2; reflexivity.
Qed.

Lemma Elem_mirror :
  forall (A : Type) (x : A) (t : BTree A),
    Elem x (mirror t) <-> Elem x t.
Proof.
  assert (forall (A : Type) (x : A) (t : BTree A),
            Elem x t -> Elem x (mirror t)).
    induction 1; cbn; auto.
    split; intro.
      rewrite <- mirror_inv. apply H, H0.
      apply H, H0.
Qed.

Lemma size_mirror :
  forall (A : Type) (t : BTree A),
    size (mirror t) = size t.
Proof.
  induction t; cbn; rewrite ?IHt1, ?IHt2, 1?plus_comm; reflexivity.
Qed.

Lemma mirror_singleton :
  forall (A : Type) (x : A),
    mirror (singleton x) = singleton x.
Proof. reflexivity. Qed.

Lemma toList_mirror :
  forall (A : Type) (t : BTree A),
    BTree_toList (mirror t) = rev (BTree_toList t).
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2, rev_app_distr. cbn. rewrite <- app_assoc. cbn.
      reflexivity.
Qed.

(** [complete] *)

Fixpoint complete {A : Type} (n : nat) (x : A) : BTree A :=
match n with
    | 0 => empty
    | S n' => node x (complete n' x) (complete n' x)
end.

Function pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => 2 * pow2 n'
end.

Lemma pow2_1plus :
  forall (A : Type) (n : nat),
    exists m : nat, pow2 n = 1 + m.
Proof.
  induction n as [| n']; cbn.
    exists 0. reflexivity.
    destruct IHn' as [m IH]. rewrite !IH. exists (1 + 2 * m). cbn.
      rewrite <- plus_n_Sm, plus_0_r. reflexivity.
Qed.

Lemma size_complete :
  forall (A : Type) (n : nat) (x : A),
    size (complete n x) = pow2 n - 1.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite !IHn', plus_0_r. destruct (pow2_1plus A n').
      rewrite !H. cbn. rewrite <- !minus_n_O, plus_n_Sm. reflexivity.
Qed.

Lemma mirror_complete :
  forall (A : Type) (n : nat) (x : A),
    mirror (complete n x) = complete n x.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

(** [takeWhileBT] *)

Function takeWhileBT {A : Type} (p : A -> bool) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        if p v
        then node v (takeWhileBT p l) (takeWhileBT p r)
        else empty
end.

Lemma Elem_takeWhileBT :
  forall {A : Type} (p : A -> bool) (t : BTree A) (x : A),
    Elem x (takeWhileBT p t) -> Elem x t /\ p x = true.
Proof.
  intros until t.
  functional induction takeWhileBT p t;
  inv 1; firstorder.
Qed.

Lemma size_takeWhileBT :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    size (takeWhileBT p t) <= size t.
Proof.
  induction t; cbn.
    apply le_0_n.
    destruct (p a); cbn.
      apply le_n_S. lia.
      apply le_0_n.
Qed.

Lemma mirror_takeWhileBT :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    takeWhileBT p (mirror t) = mirror (takeWhileBT p t).
Proof.
  induction t; cbn; intros.
    reflexivity.
    destruct (p a).
      rewrite IHt1, IHt2. cbn. reflexivity.
      reflexivity.
Qed.

Fixpoint inorder {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => inorder l ++ v :: inorder r
end.

Fixpoint preorder {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => v :: (preorder l ++ preorder r)
end.

Fixpoint postorder {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => postorder l ++ postorder r ++ [v]
end.

Definition leaf {A : Type} (x : A) : BTree A :=
  node x empty empty.

Definition test :=
  node 1
    (node 2 (leaf 4) (leaf 5))
    (leaf 3).

Lemma preorder_mirror :
  forall (A : Type) (t : BTree A),
    preorder (mirror t) = rev (postorder t).
Proof.
  induction t; cbn.
    reflexivity.
    rewrite ?rev_app_distr, IHt1, IHt2. cbn. reflexivity.
Qed.

Lemma postorder_mirror :
  forall (A : Type) (t : BTree A),
    postorder (mirror t) = rev (preorder t).
Proof.
  intros. rewrite <- rev_involutive at 1. rewrite <- preorder_mirror.
  rewrite mirror_inv. reflexivity.
Qed.

Lemma inorder_mirror :
  forall (A : Type) (t : BTree A),
    inorder (mirror t) = rev (inorder t).
Proof.
  induction t; cbn.
    reflexivity.
    rewrite ?rev_app_distr, IHt1, IHt2. cbn.
      rewrite <- app_assoc. cbn. reflexivity.
Qed.

Fixpoint wut {A : Type} (t : BTree A) : nat :=
match t with
    | empty => 1
    | node v l r => 2 + wut l + wut r
end.

Fixpoint sumOfWuts {A : Type} (l : list (BTree A)) : nat :=
match l with
    | [] => 0
    | t :: ts => 1 + wut t + sumOfWuts ts
end.

Lemma sumOfWuts_app :
  forall (A : Type) (l1 l2 : list (BTree A)),
    sumOfWuts (l1 ++ l2) = sumOfWuts l1 + sumOfWuts l2.
Proof.
  induction l1 as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. rewrite plus_assoc. reflexivity.
Qed.

Function bfs_aux
  {A : Type} (ts : list (BTree A)) (acc : list A) {measure sumOfWuts ts}
  : list A :=
match ts with
    | [] => acc
    | empty :: ts' => bfs_aux ts' acc
    | node v l r :: ts' =>
        bfs_aux (ts' ++ [l; r]) (v :: acc)
end.
Proof.
  intros. subst. cbn. apply le_S, le_n.
  intros. subst. cbn. rewrite sumOfWuts_app. cbn. lia.
Defined.

Definition bfs {A : Type} (t : BTree A) : list A :=
  rev (bfs_aux A [t] []).


(*
Compute inorder test.
Compute preorder test.
Compute postorder test.
Compute bfs test.
Compute bfs (mirror test).
*)

Fixpoint sumOfSizes {A : Type} (l : list (BTree A)) : nat :=
match l with
    | [] => 0
    | h :: t => size h + sumOfSizes t
end.

Lemma sumOfSizes_app :
  forall (A : Type) (l1 l2 : list (BTree A)),
    sumOfSizes (l1 ++ l2) = sumOfSizes l1 + sumOfSizes l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1. apply plus_assoc.
Qed.

Lemma length_bfs_aux :
  forall (A : Type) (l : list (BTree A)) (acc : list A),
    length (bfs_aux A l acc) = sumOfSizes l + length acc.
Proof.
  intros. functional induction bfs_aux A l acc; cbn.
    reflexivity.
    apply IHl0.
    rewrite IHl0, sumOfSizes_app. cbn. lia.
Qed.

Lemma length_bfs :
  forall (A : Type) (t : BTree A),
    length (bfs t) = size t.
Proof.
  intros. unfold bfs.
  rewrite rev_length, length_bfs_aux.
  cbn. rewrite ?plus_0_r. reflexivity.
Qed.

Fixpoint intersperse {A : Type} (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        node v
          (node x (intersperse x l) (intersperse x l))
          (node x (intersperse x r) (intersperse x r))
end.

Fixpoint height {A : Type} (t : BTree A) : nat :=
match t with
    | empty => 0
    | node _ l r => 1 + max (height l) (height r)
end.

Lemma height_complete :
  forall (A : Type) (n : nat) (x : A),
    height (complete n x) = n.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn', Nat.max_id. reflexivity.
Qed.

Lemma max_height_intersperse :
  forall (A : Type) (x : A) (t1 t2 : BTree A),
    height t1 <= height t2 ->
      height (intersperse x t1) <= height (intersperse x t2).
Proof.
  induction t1; cbn; intros.
    apply le_0_n.
    destruct t2; cbn in *.
      inv H.
      repeat apply le_n_S; repeat apply le_S_n in H.
        rewrite !Nat.max_id. apply Max.max_lub.
          destruct (Max.max_dec (height t2_1) (height t2_2)).
            apply Max.max_lub_l in H. rewrite e in H. apply IHt1_1 in H.
              rewrite H. apply Max.le_max_l.
            apply Max.max_lub_l in H. rewrite e in H. apply IHt1_1 in H.
              rewrite H. apply Max.le_max_r.
          destruct (Max.max_dec (height t2_1) (height t2_2)).
            apply Max.max_lub_r in H. rewrite e in H. apply IHt1_2 in H.
              rewrite H. apply Max.le_max_l.
            apply Max.max_lub_r in H. rewrite e in H. apply IHt1_2 in H.
              rewrite H. apply Max.le_max_r.
Qed.

Lemma height_intersperse :
  forall (A : Type) (x : A) (t : BTree A),
    height (intersperse x t) = 2 * height t.
Proof.
  induction t; cbn.
    reflexivity.
    repeat match goal with
        | |- context [max ?n ?m] =>
            let H := fresh "H" in
              destruct (Max.max_dec n m) as [H | H]; rewrite ?H
    end;
    rewrite ?IHt1, ?IHt2, ?plus_0_r, ?Nat.mul_max_distr_l,
            ?Nat.mul_cancel_l, ?Nat.max_id in *;
    lia.
Qed.

Lemma S_pow_minus_1 :
  forall n : nat,
    S (2 ^ n - 1) = 2 ^ n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite plus_0_r, Nat.add_sub_swap.
      rewrite <- Nat.add_succ_l, IHn'. reflexivity.
      lia.
Qed.

Lemma size_intersperse_complete :
  forall (A : Type) (x y : A) (n : nat),
    size (intersperse x (complete n y)) = pow 2 (2 * n) - 1.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. rewrite !(plus_comm _ (S _)). cbn.
      rewrite !plus_0_r, <- 4!Nat.add_succ_l.
      rewrite S_pow_minus_1, plus_n_Sm, S_pow_minus_1.
      rewrite Nat.add_succ_l, plus_n_Sm, <- Nat.add_succ_l, S_pow_minus_1.
        lia.
Qed.

Lemma mirror_intersperse :
  forall (A : Type) (x : A) (t : BTree A),
    mirror (intersperse x t) = intersperse x (mirror t).
Proof.
  induction t; cbn; rewrite ?IHt1, ?IHt2; reflexivity.
Qed.

Fixpoint take {A : Type} (n : nat) (t : BTree A) : BTree A :=
match n, t with
    | 0, _ => empty
    | _, empty => empty
    | S n', node v l r =>
        node v (take n' l) (take n' r)
end.

Lemma height_take :
  forall (A : Type) (n : nat) (t : BTree A),
    height (take n t) <= n.
Proof.
  induction n as [| n']; cbn.
    trivial.
    destruct t; cbn.
      apply le_0_n.
      apply le_n_S, Max.max_lub; auto.
Qed.

Lemma take_mirror :
  forall (A : Type) (n : nat) (t : BTree A),
    take n (mirror t) = mirror (take n t).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct t; cbn; rewrite ?IHn'; reflexivity.
Qed.

Function drop {A : Type} (n : nat) (t : BTree A) : list (BTree A) :=
match n, t with
    | 0, _ => [t]
    | _, empty => []
    | S n', node _ l r =>
        drop n' l ++ drop n' r
end.

Lemma height_drop :
  forall (A : Type) (h : nat) (t : BTree A),
    height t < h -> drop h t = [].
Proof.
  intros. functional induction @drop A h t.
    destruct _x; inv H.
    reflexivity.
    cbn in *. apply lt_S_n in H. rewrite IHl, IHl0. reflexivity.
      eapply Nat.le_lt_trans.
        apply Max.le_max_r.
        eexact H.
      eapply Nat.le_lt_trans.
        apply Max.le_max_l.
        eassumption.
Qed.

Lemma drop_mirror :
  forall (A : Type) (n : nat) (t : BTree A),
    drop n (mirror t) = rev (map mirror (drop n t)).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    destruct t; cbn.
      reflexivity.
      rewrite ?IHn'. rewrite map_app, rev_app_distr. reflexivity.
Qed.

Fixpoint zipWith
  {A B C : Type} (f : A -> B -> C)
  (ta : BTree A) (tb : BTree B) : BTree C :=
match ta, tb with
    | empty, _ => empty
    | _, empty => empty
    | node a la ra, node b lb rb =>
        node (f a b) (zipWith f la lb) (zipWith f ra rb)
end.

Lemma height_zipWith :
  forall
    (A B C : Type) (f : A -> B -> C)
    (ta : BTree A) (tb : BTree B),
      height (zipWith f ta tb) <= height ta /\
      height (zipWith f ta tb) <= height tb.
Proof.
  induction ta; cbn.
    intros. split; apply le_0_n.
    destruct tb; cbn.
      split; apply le_0_n.
      edestruct IHta1, IHta2. split; apply le_n_S.
        apply Nat.max_le_compat; eauto.
        apply Nat.max_le_compat; eauto.
Qed.

Lemma zipWith_mirror :
  forall (A B C : Type) (f : A -> B -> C) (ta : BTree A) (tb : BTree B),
    zipWith f (mirror ta) (mirror tb) =
    mirror (zipWith f ta tb).
Proof.
  induction ta; cbn; intros.
    reflexivity.
    destruct tb; cbn.
      reflexivity.
      rewrite IHta1, IHta2. reflexivity.
Qed.

Function find {A : Type} (p : A -> bool) (t : BTree A) : option A :=
match t with
    | empty => None
    | node v l r =>
        if p v
        then Some v
        else
          match find p l, find p r with
              | Some x, _ => Some x
              | _, Some x => Some x
              | _, _ => None
          end
end.

Inductive Any {A : Type} (P : A -> Prop) : BTree A -> Prop :=
    | Any_root :
        forall (v : A) (l r : BTree A),
          P v -> Any P (node v l r)
    | Any_child_l :
        forall (v : A) (l r : BTree A),
          Any P l -> Any P (node v l r)
    | Any_child_r :
        forall (v : A) (l r : BTree A),
          Any P r -> Any P (node v l r).

Hint Constructors Any : core.

Lemma Any_find :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (t : BTree A),
    (forall x : A, reflect (P x) (p x)) ->
      reflect (Any P t) (match find p t with
                             | None => false
                             | _ => true
                         end).
Proof.
  intros. induction t; cbn.
    constructor. inv 1.
    destruct (p a) eqn: Hpa.
      do 2 constructor. specialize (X a). inv X.
      destruct (find p t1).
        inv IHt1.
        destruct (find p t2).
          inv IHt2.
          constructor. inv IHt1; inv IHt2. inv 1.
            specialize (X a). inv X.
Qed.

Inductive Dup {A : Type} : BTree A -> Prop :=
    | Dup_root_l :
        forall (v : A) (l r : BTree A),
          Elem v l -> Dup (node v l r)
    | Dup_root_r :
        forall (v : A) (l r : BTree A),
          Elem v r -> Dup (node v l r)
    | Dup_l :
        forall (v : A) (l r : BTree A),
          Dup l -> Dup (node v l r)
    | Dup_r :
        forall (v : A) (l r : BTree A),
          Dup r -> Dup (node v l r).

Inductive Exactly {A : Type} (P : A -> Prop) : nat -> BTree A -> Prop :=
    | Exactly_empty : Exactly P 0 empty
    | Exactly_node_yes :
        forall (n m : nat) (v : A) (l r : BTree A),
          P v -> Exactly P n l -> Exactly P m r ->
            Exactly P (1 + n + m) (node v l r)
    | Exactly_node_no :
        forall (n m : nat) (v : A) (l r : BTree A),
          ~ P v -> Exactly P n l -> Exactly P m r ->
            Exactly P (n + m) (node v l r).

Lemma Exactly_0_False :
  forall (A : Type) (t : BTree A),
    Exactly (fun _ => False) 0 t.
Proof.
  induction t.
    constructor.
    change 0 with (0 + 0). constructor; try intro; assumption.
Qed.

Lemma Exactly_count :
  forall
    (A : Type) (P : A -> Prop) (p : A -> bool) (n : nat) (t : BTree A),
      (forall x : A, reflect (P x) (p x)) ->
        Exactly P n t <-> countBT p t = n.
Proof.
  split.
    induction 1; cbn.
      reflexivity.
      destruct (p v) eqn: Hpv; rewrite ?IHExactly1, ?IHExactly2.
        reflexivity.
        specialize (X v). inv X.
      destruct (p v) eqn: Hpv; rewrite ?IHExactly1, ?IHExactly2.
        specialize (X v). inv X.
        reflexivity.
    gen n. induction t; cbn; intros; subst.
      constructor.
      destruct (p a) eqn: Hpa; constructor; auto.
        1-2: specialize (X a); inv X.
Qed.

Inductive All {A : Type} (P : A -> Prop) : BTree A -> Prop :=
    | All_empty : All P empty
    | All_node :
        forall (v : A) (l r : BTree A),
          P v -> All P l -> All P r -> All P (node v l r).

Lemma count_size :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    countBT p t <= size t.
Proof.
  induction t; cbn.
    reflexivity.
    destruct (p a).
      apply le_n_S. apply plus_le_compat; assumption.
      unfold id. apply le_S. apply plus_le_compat; assumption.
Qed.

Lemma count_size_aux :
  forall (A : Type) (p : A -> bool) (t1 t2 : BTree A),
    countBT p t1 + countBT p t2 = size t1 + size t2 ->
      countBT p t1 = size t1 /\ countBT p t2 = size t2.
Proof.
  induction t1; cbn; intros.
    split; [reflexivity | assumption].
    destruct (p a) eqn: Hpa.
      inv H. specialize (IHt1_1 (node a t1_2 t2)). cbn in *.
        rewrite Hpa in *. destruct (IHt1_1 ltac:(lia)). inv H0.
        destruct (IHt1_2 _ H3). lia.
      assert (S (size t1_1 + size t1_2 + size t2) <=
                (size t1_1 + size t1_2 + size t2)).
        rewrite <- H. unfold id.
          repeat apply plus_le_compat; apply count_size.
        lia.
Qed.

Lemma All_count :
  forall (A : Type) (P : A -> Prop) (p : A -> bool) (t : BTree A),
    (forall x : A, reflect (P x) (p x)) ->
      All P t <-> countBT p t = size t.
Proof.
  split.
    induction 1; cbn.
      reflexivity.
      destruct (p v) eqn: Hpv.
        rewrite ?IHAll1, ?IHAll2. reflexivity.
        specialize (X v). inv X.
    induction t; cbn; intros.
      constructor.
      destruct (p a) eqn: Hpa; inv H.
        apply count_size_aux in H1.
          destruct H1. constructor; auto. specialize (X a). inv X.
        assert (S (size t1 + size t2) <=
                  (size t1 + size t2)).
          rewrite <- H1. unfold id.
            apply plus_le_compat; apply count_size.
          lia.
Qed.

Inductive SameStructure {A B : Type} : BTree A -> BTree B -> Prop :=
    | SS_empty : SameStructure empty empty
    | SS_node :
        forall (v1 : A) (l1 r1 : BTree A) (v2 : B) (l2 r2 : BTree B),
          SameStructure l1 l2 ->
          SameStructure r1 r2 ->
            SameStructure (node v1 l1 r1) (node v2 l2 r2).

Lemma zipWith_swap :
  forall (A B C : Type) (f : A -> B -> C) (ta : BTree A) (tb : BTree B),
    zipWith f ta tb = zipWith (fun b a => f a b) tb ta.
Proof.
  induction ta; destruct tb; cbn; intros; f_equal; auto.
Qed.

Inductive subtree {A : Type} : BTree A -> BTree A -> Prop :=
    | subtree_l :
        forall (v : A) (l r : BTree A),
          subtree l (node v l r)
    | subtree_r :
        forall (v : A) (l r : BTree A),
          subtree r (node v l r)
    | subtree_trans :
        forall t1 t2 t3 : BTree A,
          subtree t1 t2 -> subtree t2 t3 -> subtree t1 t3.

Lemma size_subtree :
  forall (A : Type) (t1 t2 : BTree A),
    subtree t1 t2 -> size t1 < size t2.
Proof.
  induction 1; cbn.
    apply le_n_S, le_plus_l.
    apply le_n_S, le_plus_r.
    apply lt_trans with (size t2); assumption.
Qed.

Lemma height_subtree :
  forall (A : Type) (t1 t2 : BTree A),
    subtree t1 t2 -> height t1 < height t2.
Proof.
  induction 1; cbn.
    apply le_n_S, Max.le_max_l.
    apply le_n_S, Max.le_max_r.
    apply lt_trans with (height t2); assumption.
Qed.

(** [removeMin] moved from BST.v *)

Function leftmost {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => leftmost l
end.

Function removeMin
  {A : Type} (t : BTree A) : option (A * BTree A) :=
match t with
    | empty => None
    | node x l r =>
        match removeMin l with
            | None => Some (x, r)
            | Some (m, l') => Some (m, node x l' r)
        end
end.

Lemma Elem_removeMin :
  forall
    {A : Type} {t t' : BTree A} {m : A},
      removeMin t = Some (m, t') ->
        forall x : A, Elem x t <-> x = m \/ Elem x t'.
Proof.
  intros A t.
  functional induction removeMin t;
  inv 1; intro; rewrite ?Elem_node;
  firstorder.
    functional inversion e0. subst. inv H.
Qed.

(** * [filterBT] *)

Function filterBT
  {A : Type} (p : A -> bool) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        let l' := filterBT p l in
        let r' := filterBT p r in
          if p v
          then node v l' r'
          else
            match removeMin r' with
                | None => l'
                | Some (m, r'') => node m l' r''
            end
end.

Lemma Elem_filterBT :
  forall (A : Type) (p : A -> bool) (t : BTree A) (x : A),
    Elem x (filterBT p t) <-> Elem x t /\ p x = true.
Proof.
  intros until t.
  functional induction filterBT p t;
  intros;
    rewrite ?Elem_node, ?IHb, ?IHb0.
    firstorder. inv H.
    firstorder. congruence.
    firstorder.
      congruence.
      functional inversion e1; subst.
        assert (Elem x empty).
          rewrite H1, IHb0. split; assumption.
          inv H2.
    pose (Elem_removeMin e1). firstorder.
      congruence.
Qed.

(* TODO: drop using cmp *)

(* TODO: nth, modify, splitAt, insert, replace, modify *)

Inductive All2 {A B : Type} (R : A -> B -> Prop) : BTree A -> BTree B -> Prop :=
    | All2_empty : All2 R empty empty
    | All2_node  :
        forall
          (va : A) (la ra : BTree A)
          (vb : B) (lb rb : BTree B),
            R va vb -> All2 R la lb -> All2 R ra rb ->
              All2 R (node va la ra) (node vb lb rb).

Inductive Ex2 {A B : Type} (R : A -> B -> Prop) : BTree A -> BTree B -> Prop :=
    | Ex2_node  :
        forall
          (va : A) (la ra : BTree A)
          (vb : B) (lb rb : BTree B),
            R va vb \/ Ex2 R la lb \/ Ex2 R ra rb ->
              Ex2 R (node va la ra) (node vb lb rb).

Inductive PermutationBT {A : Type} : BTree A -> BTree A -> Prop :=
    | PermutationBT_empty : PermutationBT empty empty
    | PermutationBT_skip  :
        forall (v : A) (l1 l2 r1 r2 : BTree A),
          PermutationBT l1 l2 -> PermutationBT r1 r2 ->
            PermutationBT (node v l1 r1) (node v l2 r2)
    | PermutationBT_swapl :
        forall (x y : A) (yl yr xr : BTree A),
          PermutationBT (node y (node x yl yr) xr) (node x (node y yl yr) xr)
    | PermutationBT_swapr :
        forall (x y : A) (xl yl yr : BTree A),
          PermutationBT (node y xl (node x yl yr)) (node x xl (node y yl yr))
    | PermutationBT_trans :
        forall t1 t2 t3 : BTree A,
          PermutationBT t1 t2 -> PermutationBT t2 t3 -> PermutationBT t1 t3.

Lemma PermutationBT_refl :
  forall {A : Type} (t : BTree A),
    PermutationBT t t.
Proof.
  induction t; constructor; assumption.
Qed.

Lemma PermutationBT_sym :
  forall {A : Type} {t1 t2 : BTree A},
    PermutationBT t1 t2 -> PermutationBT t2 t1.
Proof.
  induction 1; econstructor; eassumption.
Qed.

Lemma count_PermutationBT :
  forall {A : Type} {t1 t2 : BTree A},
    PermutationBT t1 t2 ->
      forall p : A -> bool, countBT p t1 = countBT p t2.
Proof.
  induction 1; cbn; intro;
  rewrite ?IHPermutationBT1, ?IHPermutationBT2;
  try reflexivity;
  destruct (p x), (p y); unfold id; lia.
Qed.

Inductive AtLeast {A : Type} (P : A -> Prop) : BTree A -> nat -> Prop :=
    | AtLeast_empty :
        forall t : BTree A, AtLeast P t 0
    | AtLeast_node_yes  :
        forall (v : A) (l r : BTree A) (n m : nat),
          P v -> AtLeast P l n -> AtLeast P r m -> AtLeast P (node v l r) (S (n + m))
    | AtLeast_node_skip :
        forall (v : A) (l r : BTree A) (n m : nat),
          AtLeast P l n -> AtLeast P r m -> AtLeast P (node v l r) (n + m).

Hint Constructors AtLeast : core.

Fixpoint toList {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => toList l ++ v :: toList r
end.

Lemma PermutationBT_toList :
  forall {A : Type} {t1 t2 : BTree A},
    PermutationBT t1 t2 -> Permutation (toList t1) (toList t2).
Proof.
  induction 1; cbn.
    constructor.
    apply Permutation_app; auto.
    rewrite <- ?app_assoc. apply Permutation_app.
      reflexivity.
      {
        rewrite Permutation_app_comm.
        cbn. constructor.
        rewrite Permutation_app_comm, (Permutation_app_comm (toList yr)).
        cbn. constructor.
        apply Permutation_app_comm.
      }
    apply Permutation_app.
      reflexivity.
      rewrite 2!Permutation_middle. apply Permutation_app.
        reflexivity.
        constructor.
    rewrite IHPermutationBT1, IHPermutationBT2. reflexivity.
Qed.

Lemma PermutationBT_toList_conv :
  forall {A : Type} {t1 t2 : BTree A},
    Permutation (toList t1) (toList t2) -> PermutationBT t1 t2.
Proof.
  induction 1; cbn.
Abort.

Definition PermutationBT' {A : Type} (t1 t2 : BTree A) : Prop :=
    forall (P : A -> Prop) (n : nat),
      Exactly P n t1 <-> Exactly P n t2.

Lemma Permutation_PermutationBT' :
  forall {A : Type} {t1 t2 : BTree A},
    PermutationBT t1 t2 -> PermutationBT' t1 t2.
Proof.
  unfold PermutationBT'.
  induction 1; split; inv 1; try constructor; firstorder.
Abort.

Definition PermutationBT'' {A : Type} (t1 t2 : BTree A) : Prop :=
    forall (P : A -> Prop) (n : nat),
      AtLeast P t1 n <-> AtLeast P t2 n.

Lemma Permutation_PermutationBT'' :
  forall {A : Type} {t1 t2 : BTree A},
    PermutationBT t1 t2 -> PermutationBT'' t1 t2.
Proof.
  unfold PermutationBT''.
  induction 1; split; inv 1;
  try (constructor 2; firstorder; fail);
  try (constructor 3; firstorder; fail).
    inv H5. cbn. change (S m) with (1 + m). constructor 3.
      change 1 with (1 + 0). constructor; auto. auto.
Abort.