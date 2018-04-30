Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Require Import LinDec.
Require Import ListLemmas.
Require Import Sorting.Sort.

Require Export Classes.EquivDec.
Require Export Compare_dec.

Inductive BTree (A : Type) : Type :=
    | empty : BTree A
    | node : A -> BTree A -> BTree A -> BTree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

Inductive elem {A : Type} (a : A) : BTree A -> Prop :=
    | elem_root : forall l r : BTree A, elem a (node a l r)
    | elem_left : forall (v : A) (l r : BTree A),
        elem a l -> elem a (node v l r)
    | elem_right : forall (v : A) (l r : BTree A),
        elem a r -> elem a (node v l r).

Inductive isHeap {A : LinDec} : BTree A -> Prop :=
    | isHeap_empty : isHeap empty
    | isHeap_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, elem x l -> v ≤ x) -> isHeap l ->
          (forall x : A, elem x r -> v ≤ x) -> isHeap r ->
            isHeap (node v l r).

Hint Constructors elem isHeap.

Definition singleton {A : Type} (x : A) : BTree A :=
  node x empty empty.

Fixpoint elem_decb
  {A : LinDec} (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        (x =? v) || elem_decb x l || elem_decb x r
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
  {A : LinDec} (t : BTree A) (acc : list A) : list A :=
match t with
    | empty => acc
    | node v l r => BTree_toList'_aux l (v :: BTree_toList'_aux r acc)
end.

Definition BTree_toList' {A : LinDec} (t : BTree A) : list A :=
  BTree_toList'_aux t [].

(** [size] and counting. *)
Fixpoint size {A : Type} (bt : BTree A) : nat :=
match bt with
    | empty => 0
    | node _ l r => S (size l + size r)
end.

Fixpoint count_BTree {A : LinDec} (x : A) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        let n := count_BTree x l in
        let m := count_BTree x r in
        if x =? v then S (n + m) else n + m
end.

(** * Tactics *)
Ltac elem :=
  intros; unfold singleton in *; cbn in *; subst; repeat
match goal with
    | |- elem ?x (node ?x _ _) => constructor
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ empty empty) |- _ => inv H
    | H : elem _ _ /\ elem _ _ |- _ => destruct H
    | H : elem _ _ \/ elem _ _ |- _ => destruct H
end; auto.

(** * Theorems *)

(** Properties of [elem] and [elem_decb]. *)
Lemma elem_decb_reflect :
  forall (A : LinDec) (x : A) (t : BTree A),
    reflect (elem x t) (elem_decb x t).
Proof.
  induction t as [| v l IHl r IHr]; cbn.
    constructor. inv 1.
    dec. destruct IHl, IHr; auto.
      constructor. inv 1.
Qed.

(** Properties of casts to/from list. *)

Lemma BTree_toList'_aux_spec :
  forall (A : LinDec) (t : BTree A) (acc : list A),
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

Lemma toList_In_elem :
  forall (A : Type) (x : A) (t : BTree A),
    In x (BTree_toList t) <-> elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; firstorder.
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
    rewrite !app_length. cbn. rewrite IHt1, IHt2. omega.
Qed.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (BTree_toList t) = count_BTree x t.
Proof.
  induction t; cbn; rewrite ?count_app; dec.
Qed.

(** Properties of [empty]. *)
Lemma empty_elem :
  forall (A : LinDec) (x : A), ~ elem x empty.
Proof. inv 1. Qed.

Lemma empty_isHeap :
  forall A : LinDec, isHeap (@empty A).
Proof. constructor. Qed.

Lemma empty_size :
  forall A : LinDec, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma empty_count_BTree :
  forall (A : LinDec) (x : A),
    count_BTree x empty = 0.
Proof. reflexivity. Qed.

(** Properties of [singleton]. *)

Lemma singleton_elem :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  split; elem.
Qed.

Lemma singleton_isHeap :
  forall (A : LinDec) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton. constructor; auto; inv 1.
Qed.

Lemma singleton_size :
  forall (A : LinDec) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma singleton_count_BTree :
  forall (A : LinDec) (x y : A),
    count_BTree x (singleton y) = if x =? y then 1 else 0.
Proof. dec. Qed.

(** Properties of [isEmpty]. *)

Lemma isEmpty_elem_false :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = false <-> exists x : A, elem x t.
Proof.
  split; destruct t; cbn; firstorder.
    eauto.
    inv H.
Qed.

Lemma isEmpty_elem_true :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true <-> forall x : A, ~ elem x t.
Proof.
  split; destruct t; cbn; firstorder.
    inv 1.
    contradiction (H c). auto.
Qed.

Lemma isEmpty_isHeap :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true -> isHeap t.
Proof.
  destruct t; firstorder.
Qed.

Lemma isEmpty_empty :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> t = empty.
Proof.
  destruct t; cbn; firstorder. inv H.
Qed.

Lemma isEmpty_singleton :
  forall (A : Type) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma isEmpty_size_false :
  forall (A : Type) (t : BTree A),
    isEmpty t = false <-> size t <> 0.
Proof.
  split; destruct t; cbn; firstorder.
Qed.

Lemma isEmpty_size_true :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> size t = 0.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_count_BT :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true <-> forall x : A, count_BTree x t = 0.
Proof.
  split; destruct t; cbn; try congruence.
    intro. specialize (H c). dec.
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

Lemma elem_mirror :
  forall (A : Type) (x : A) (t : BTree A),
    elem x (mirror t) <-> elem x t.
Proof.
  assert (forall (A : Type) (x : A) (t : BTree A),
            elem x t -> elem x (mirror t)).
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

(** [takeWhile] *)

Fixpoint takeWhile {A : Type} (p : A -> bool) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        if p v
        then node v (takeWhile p l) (takeWhile p r)
        else empty
end.

Lemma size_takeWhile :
  forall (A : Type) (p : A -> bool) (t : BTree A),
    size (takeWhile p t) <= size t.
Proof.
  induction t; cbn.
    apply le_0_n.
    destruct (p a); cbn.
      apply le_n_S. omega.
      apply le_0_n.
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

Let test :=
  node 1
    (node 2 (leaf 4) (leaf 5))
    (leaf 3).

Compute inorder test.
Compute preorder test.
Compute postorder test.

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
  intros. subst. cbn. rewrite sumOfWuts_app. cbn. omega.
Defined.

Definition bfs {A : Type} (t : BTree A) : list A :=
  rev (bfs_aux A [t] []).

Compute bfs test.

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
    rewrite IHl0, sumOfSizes_app. cbn. omega.
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

Compute size (intersperse 1 (complete 5 0)).

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
        rewrite ?Nat.max_le_iff, ?Nat.max_lub_iff in *.
Restart.
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

Search (max _ _ <= _).
Search (_ <= max _ _).

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
    omega.
Qed.

(* TODO *) Lemma size_intersperse_complete :
  forall (A : Type) (x y : A) (n : nat),
    size (intersperse x (complete n y)) = pow 2 (2 * n) - 1.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. rewrite !(plus_comm _ (S _)). cbn.
      rewrite !plus_0_r.
Abort.

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

Function drop {A : Type} (n : nat) (t : BTree A) : list (BTree A) :=
match n, t with
    | 0, _ => [t]
    | _, empty => []
    | S n', node _ l r =>
        drop n' l ++ drop n' r
end.

Print test.
Compute drop 4 test.

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

(* [filter] makes no sense. *)

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

Fixpoint find {A : Type} (p : A -> bool) (t : BTree A) : option A :=
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

Inductive Dup {A : Type} : BTree A -> Prop :=
    | Dup_root_l :
        forall (v : A) (l r : BTree A),
          elem v l -> Dup (node v l r)
    | Dup_root_r :
        forall (v : A) (l r : BTree A),
          elem v r -> Dup (node v l r)
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

