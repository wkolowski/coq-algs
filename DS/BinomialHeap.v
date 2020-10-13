Require Export LinDec.
Require Export RCCBase.

Inductive Tree (A : Type) : Type :=
    | T : nat -> A -> list (Tree A) -> Tree A.

Arguments T [A] _ _ _.

Inductive elemTree {A : Type} (x : A) : Tree A -> Prop :=
    | elemTree_root :
        forall (n : nat) (l : list (Tree A)), elemTree x (T n x l)
    | elemTree_child :
        forall (n : nat) (y : A) (l : list (Tree A)) (t : Tree A),
          elemTree x t -> In t l -> elemTree x (T n y l).

Hint Constructors elemTree.

Definition Heap (A : Type) : Type := list (Tree A).

Definition elem {A : Type} (x : A) (h : Heap A) : Prop :=
  exists t : Tree A, elemTree x t /\ In t h.

Inductive elemTree' {A : Type} (x : A) : Tree A -> Prop :=
    | elemTree'_root :
        forall (n : nat) (l : list (Tree A)), elemTree' x (T n x l)
    | elemTree'_heap :
        forall h : Heap A, elemHeap x h ->
          forall (n : nat) (y : A), elemTree' x (T n y h)

with elemHeap {A : Type} (x : A) : Heap A -> Prop :=
    | elemHeap_here :
        forall (t : Tree A) (h' : Heap A),
          elemTree' x t -> elemHeap x (t :: h')
    | elemHeap_there :
        forall (t : Tree A) (h' : Heap A),
          elemHeap x h' -> elemHeap x (t :: h').

Hint Constructors elemTree' elemHeap.

Definition empty {A : Type} : Heap A := [].

Definition isEmpty {A : Type} (h : Heap A) : bool :=
match h with
    | [] => true
    | _ => false
end.

Definition rank {A : Type} (t : Tree A) : nat :=
match t with
    | T r _ _ => r
end.

Definition root {A : Type} (t : Tree A) : A :=
match t with
    | T _ x _ => x
end.

(*Function link {A : LinDec} (t1 t2 : Tree A) : Tree A :=
match t1, t2 with
    | T r x ts1, T _ y ts2 =>
        if x <=? y
        then T (S r) x (t2 :: ts1)
        else T (S r) y (t1 :: ts2)
end.*)

Function link {A : LinDec} (t1 t2 : Tree A) : Tree A :=
match t1, t2 with
    | T r1 x ts1, T r2 y ts2 =>
        if x <=? y
        then T (S r1) x (t2 :: ts1)
        else T (S r2) y (t1 :: ts2)
end.

Fixpoint insTree {A : LinDec} (t : Tree A) (h : Heap A) : Heap A :=
match h with
    | [] => [t]
    | t' :: h' =>
        if rank t <? rank t'
        then t :: h
        else insTree (link t t') h'
end.

Definition insert {A : LinDec} (x : A) (h : Heap A) : Heap A :=
  insTree (T 0 x []) h.

Fixpoint merge {A : LinDec} (h1 h2 : Heap A) : Heap A :=
match h1 with
    | [] => h2
    | t1 :: h1' =>
        let
          aux := fix aux (h2 : Heap A) : Heap A :=
          match h2 with
              | [] => h1
              | t2 :: h2' =>
                  if rank t1 <? rank t2
                  then t1 :: merge h1' h2
                  else
                    if rank t2 <? rank t1
                    then t2 :: aux h2'
                    else insTree (link t1 t2) (merge h1' h2')
          end
        in aux h2
end.

Function removeMinTree
  {A : LinDec} (h : Heap A) : option (Tree A * Heap A) :=
match h with
    | [] => None
    | [t] => Some (t, [])
    | t :: h' =>
        match removeMinTree h' with
            | None => None
            | Some (t', h'') =>
                if (root t <=? root t') && negb (root t =? root t')
                then Some (t, h')
                else Some (t', t :: h'')
        end
end.

Definition findMin {A : LinDec} (h : Heap A) : option A :=
match removeMinTree h with
    | None => None
    | Some (t, _) => Some (root t)
end.

Definition deleteMin {A : LinDec} (h : Heap A) : option (Heap A) :=
match removeMinTree h with
    | None => None
    | Some (T _ x h1, h2) => Some (merge (rev h1) h2)
end.

Definition unMin {A : LinDec} (h : Heap A) : option (A * Heap A) :=
match removeMinTree h with
    | None => None
    | Some (T _ x h1, h2) => Some (x, merge h1 h2)
end.

(** spec of merge *)

Lemma merge_spec :
  forall (A : LinDec) (h1 h2 : Heap A),
    merge h1 h2 =
    match h1, h2 with
        | [], _ => h2
        | _, [] => h1
        | t1 :: h1', t2 :: h2' =>
            if rank t1 <? rank t2
            then t1 :: merge h1' h2
            else
              if rank t2 <? rank t1
              then t2 :: merge h1 h2'
              else insTree (link t1 t2) (merge h1' h2')
    end.
Proof.
  destruct h1, h2; reflexivity.
Qed.

(** Properties of [isEmpty]. *)

Lemma isEmpty_elem :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = true <-> forall x : A, ~ elem x h.
Proof.
  split; intro.
    inv 1. inv H1. destruct h; cbn in *.
      assumption.
      congruence.
    induction h; intros.
      reflexivity.
      destruct h; cbn in *.
        destruct a. specialize (H c). contradict H.
          red. exists (T n c l). split; cbn; auto.
        apply IHh. do 2 intro. apply (H x). red. inv H0. inv H1.
          exists x0. cbn. auto.
Qed.

Lemma isEmpty_elemHeap :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = true <-> forall x : A, ~ elemHeap x h.
Proof.
  split; intro.
    inv 1; cbn in *; congruence.
    induction h; intros.
      cbn. reflexivity.
      specialize (H (root a)). contradiction H. destruct a. cbn.
        apply elemHeap_here. auto.
Qed.

Lemma isEmpty_empty_false :
  forall {A : LinDec} (h : Heap A),
    isEmpty h = false <-> h <> empty.
Proof.
  destruct h; compute; firstorder congruence.
Qed.

Lemma isEmpty_empty_true :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = true <-> h = empty.
Proof.
  destruct h; compute; firstorder congruence.
Qed.

Lemma isEmpty_insTree :
  forall (A : LinDec) (t : Tree A) (h : Heap A),
    isEmpty (insTree t h) = false.
Proof.
  intros A t h; gen t.
  induction h as [| t' h']; cbn; intros.
    reflexivity.
    destruct t'; cbn. destruct n as [| n'].
      apply IHh'.
      destruct t. cbn. destruct (leb n n').
        cbn. reflexivity.
        apply IHh'.
Qed.

Lemma isEmpty_insert :
  forall {A : LinDec} (x : A) (h : Heap A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. apply isEmpty_insTree.
Qed.

Lemma isEmpty_merge :
  forall {A : LinDec} (h1 h2 : Heap A),
    isEmpty (merge h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1, h2; rewrite merge_spec; cbn; auto.
  repeat match goal with
      | |- context [if ?x then _ else _] => destruct x
  end; cbn.
    1-2: reflexivity.
    rewrite isEmpty_insTree. reflexivity.
Qed.

Lemma isEmpty_removeMinTree_false :
  forall (A : LinDec) (t : Tree A) (h h' : Heap A),
    removeMinTree h = Some (t, h') -> isEmpty h = false.
Proof.
  intros. destruct h; cbn in *; congruence.
Qed.

Lemma isEmpty_removeMinTree_false' :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = false <->
    exists (t : Tree A) (h' : Heap A), removeMinTree h = Some (t, h').
Proof.
  split.
    functional induction @removeMinTree A h; cbn; intros; eauto.
      congruence.
      rewrite e0 in IHo. destruct h'; cbn in *.
        contradiction.
        apply IHo. reflexivity.
    destruct 1 as [t [h' H]]. destruct h; cbn in *; congruence.
Qed.

Lemma isEmpty_removeMinTree_true :
  forall (A : LinDec) (h : Heap A),
    removeMinTree h = None <-> isEmpty h = true.
Proof.
  split.
    functional induction @removeMinTree A h; cbn; try congruence.
      destruct h'; auto.
    destruct h; cbn; congruence.
Qed.

Lemma isEmpty_unMin_false :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = false <->
    exists (m : A) (h' : Heap A), unMin h = Some (m, h').
Proof.
  split; unfold unMin; intros.
    apply isEmpty_removeMinTree_false' in H. destruct H as [t [h' H]].
      destruct t as [r x h'']. exists x, (merge h'' h'). rewrite H. auto.
    destruct H as [m [h' H]]. apply isEmpty_removeMinTree_false'.
      case_eq (removeMinTree h); intros.
        destruct p. eauto.
        rewrite H0 in H. congruence.
Qed.

Lemma isEmpty_unMin_true :
  forall (A : LinDec) (h : Heap A),
    isEmpty h = true <-> unMin h = None.
Proof.
  unfold unMin; split; intros.
    apply isEmpty_removeMinTree_true in H. rewrite H. reflexivity.
    case_eq (removeMinTree h); intros.
      rewrite H0 in H. destruct p, t. inv H.
      apply isEmpty_removeMinTree_true. assumption.
Qed.

(** Properties of [link]. *)

Lemma link_elemTree :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    elemTree x (link t1 t2) <-> elemTree x t1 \/ elemTree x t2.
Proof.
  split.
    destruct t1, t2; cbn; intro; dec.
      inv H. inv H4. eauto.
      inv H. inv H4. eauto.
    inv 1.
      destruct t1, t2; cbn; dec.
        inv H0. eapply elemTree_child; cbn; eauto.
        inv H0.
          eapply elemTree_child; cbn; eauto.
          eapply elemTree_child.
            exact H2.
            cbn.

Abort.

Ltac tree :=
repeat match goal with
    | H : context [if ?x then _ else _] |- _ => destruct x
    | |- context [if ?x then _ else _] => destruct x
end; auto.

Ltac tree' := intros; cbn in *;
repeat match goal with
    | H : context [if ?x then _ else _] |- _ => destruct x
    | |- context [if ?x then _ else _] => destruct x
    | H : _ \/ _ |- _ => inv H
    | H : elemTree' _ (T _ _ _) |- _ => inv H
    | H : elemHeap _ [] |- _ => inv H
    | H : elemHeap _ (_ :: _) |- _ => inv H
end; auto.

Lemma link_elemTree' :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    elemTree' x (link t1 t2) <-> elemTree' x t1 \/ elemTree' x t2.
Proof.
  split; destruct t1, t2; cbn; intros; dec; tree'.
Qed.

Hint Extern 0 =>
match goal with
    | |- context [elemTree' _ (link _ _)] =>
        rewrite link_elemTree'
end.

Lemma insTree_elemHeap :
  forall (A : LinDec) (x : A) (t : Tree A) (h : Heap A),
    elemHeap x (insTree t h) <-> elemTree' x t \/ elemHeap x h.
Proof.
  split.
    gen t; gen x. induction h as [| t' h']; tree'.
      specialize (IHh' _ _ H). rewrite link_elemTree' in IHh'.
        firstorder.
    gen t; gen x. induction h as [| t' h']; tree'.
Restart.
  split; gen t; gen x; induction h as [| t' h']; tree'.
  specialize (IHh' _ _ H). rewrite link_elemTree' in IHh'. firstorder.
Qed.

Lemma insert_elemTree' :
  forall (A : LinDec) (x : A) (h : Heap A),
    elemHeap x (insert x h).
Proof.
  intros. unfold insert. rewrite insTree_elemHeap. auto.
Qed.

Lemma merge_elemHeap :
  forall (A : LinDec) (x : A) (h1 h2 : Heap A),
    elemHeap x (merge h1 h2) <-> elemHeap x h1 \/ elemHeap x h2.
Proof.
  split; gen h2.
    induction h1.
      cbn. auto.
      intros. induction h2.
        auto.
        cbn in H. tree'.
          specialize (IHh1 _ H1). firstorder.
          specialize (IHh2 H1). inv IHh2.
          rewrite insTree_elemHeap, link_elemTree' in H.
            decompose [or] H; clear H; auto. specialize (IHh1 _ H0). inv IHh1.
Restart.
  split; gen h2.
    induction h1; induction h2; tree'.
      specialize (IHh1 _ H1). firstorder.
      specialize (IHh2 H1). inv IHh2.
      clear IHh2. rewrite insTree_elemHeap, link_elemTree' in H.
        decompose [or] H; clear H; auto. specialize (IHh1 _ H0). inv IHh1.
    induction h1; induction h2; tree';
      rewrite insTree_elemHeap, link_elemTree'; auto.
Qed.

Lemma removeMinTree_elemHeap :
  forall (A : LinDec) (x : A) (t : Tree A) (h h' : Heap A),
    removeMinTree h = Some (t, h') ->
      elemHeap x h <-> elemTree' x t \/ elemHeap x h'.
Proof.
  split; revert x t h' H.
    functional induction @removeMinTree A h; inv 1; intro; inv H.
      specialize (IHo _ _ _ e0 H1). inv IHo.
    functional induction @removeMinTree A h; inv 1; intro; inv H.
      specialize (IHo x _ _ e0 ltac:(auto)). inv IHo.
      inv H0. specialize (IHo x _ _ e0 ltac:(auto)). inv IHo.
Qed.

Lemma unMin_elemHeap :
  forall (A : LinDec) (x m : A) (h h' : Heap A),
    unMin h = Some (m, h') ->
      elemHeap x h <-> x = m \/ elemHeap x h'.
Proof.
  unfold unMin. split.
    case_eq (removeMinTree h); intros; rewrite H0 in *.
      destruct p, t. inv H.
        apply removeMinTree_elemHeap with (x := x) in H0.
        rewrite merge_elemHeap. firstorder. inv H.
      congruence.
    case_eq (removeMinTree h); intros; rewrite H0 in *.
      destruct p, t. inv H. rewrite merge_elemHeap in *.
        apply removeMinTree_elemHeap with (x := x) in H0.
        firstorder; subst; auto.
      congruence.
Qed.

Lemma removeMinTree_insTree :
  forall (A : LinDec) (t : Tree A) (h : Heap A),
    removeMinTree (insTree t h) <> None.
Proof.
  repeat intro. apply isEmpty_removeMinTree_true in H.
  rewrite isEmpty_insTree in H. congruence.
Qed.

Lemma unMin_insTree :
  forall (A : LinDec) (t : Tree A) (h : Heap A),
    unMin (insTree t h) <> None.
Proof.
  intros. unfold unMin.
  case_eq (removeMinTree (insTree t h)); intros.
    destruct p, t0. inv 1.
    apply removeMinTree_insTree in H. contradiction.
Qed.

Lemma unMin_insert :
  forall (A : LinDec) (x : A) (h : Heap A),
    unMin (insert x h) <> None.
Proof.
  intros. unfold insert. apply unMin_insTree.
Qed.

Lemma unMin_merge :
  forall (A : LinDec) (h1 h2 : Heap A),
    unMin (merge h1 h2) = None <->
    unMin h1 = None /\ unMin h2 = None.
Proof.
  intros. rewrite <- !isEmpty_unMin_true, isEmpty_merge.
  destruct h1, h2; cbn; firstorder congruence.
Qed.

(** Counting shiet. *)

Fixpoint count_Tree {A : LinDec} (x : A) (t : Tree A) : nat :=
match t with
    | T _ x' l =>
        (if x =? x' then S else id)
          (fold_right (fun t ts => count_Tree x t + ts) 0 l)
end.

Definition count_Heap {A : LinDec} (x : A) (h : Heap A) : nat :=
  fold_right (fun t ts => count_Tree x t + ts) 0 h.

Lemma isEmpty_count_Tree :
  forall (A : LinDec) (t : Tree A),
    isEmpty [t] = true <-> forall x : A, count_Tree x t = 0.
Proof.
  split; cbn; intros.
    congruence.
    specialize (H (root t)). destruct t. cbn in H. dec.
Qed.

Lemma count_Tree_link :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    count_Tree x (link t1 t2) = count_Tree x t1 + count_Tree x t2.
Proof.
  destruct t1, t2. cbn. do 2 dec; unfold id; lia.
Qed.

Lemma insTree_Some :
  forall (A : LinDec) (t : Tree A) (h : Heap A),
    exists (t' : Tree A) (h' : Heap A),
      insTree t h = t' :: h'.
Proof.
  intros A t h; gen t. induction h as [| t' h']; tree'; eauto.
Qed.

Lemma count_Heap_insTree :
  forall (A : LinDec) (x : A) (t : Tree A) (h : Heap A),
    count_Heap x (insTree t h) = count_Tree x t + count_Heap x h.
Proof.
  intros A x t h; gen t; gen x.
  induction h as [| t' h']; cbn; intros.
    reflexivity.
    tree'. unfold count_Heap in *. rewrite IHh'.
      rewrite count_Tree_link. lia.
Qed.

Lemma count_Heap_insert :
  forall (A : LinDec) (x y : A) (h : Heap A),
    count_Heap x (insert y h) =
    (if x =? y then S else id) (count_Heap x h).
Proof.
  intros. unfold insert. rewrite count_Heap_insTree. cbn. dec.
Qed.

Inductive validTree' {A : Type} : nat -> Tree A -> Prop :=
    | validTree'0 :
        forall x : A, validTree' 0 (T 0 x [])
    | validTree'S :
        forall (r : nat) (x : A) (l : list (Tree A)),
          validForest r l -> validTree' r (T r x l)

with validForest {A : Type} : nat -> list (Tree A) -> Prop :=
    | validForest0 : validForest 0 []
    | validForestS :
        forall (r : nat) (t : Tree A) (l : list (Tree A)),
          validTree' r t -> validForest r l -> validForest (S r) (t :: l).

Definition validTree {A : Type} (t : Tree A) : Prop :=
  validTree' (rank t) t.

Inductive heapOrdered {A : LinDec} : Tree A -> Prop :=
    | heapOrderedC :
        forall (r : nat) (x : A) (l : list (Tree A)),
          Forall (fun t => x ≤ root t /\ heapOrdered t) l ->
            heapOrdered (T r x l).

Hint Constructors validTree' validForest heapOrdered.

Definition isHeap {A : LinDec} (h : Heap A) : Prop :=
  Forall (fun t => validTree t /\ heapOrdered t) h.

Hint Unfold validTree isHeap.

Lemma empty_isHeap :
  forall A : LinDec, isHeap (@empty A).
Proof.
  intro. unfold isHeap, empty. constructor.
Qed.

Require Import Max.

Lemma link_validTree' :
  forall (A : LinDec) (t1 t2 : Tree A) (r : nat),
    validTree' r t1 -> validTree' r t2 ->
      validTree' (S r) (link t1 t2).
Proof.
  do 2 inv 1; dec.
Admitted.

Lemma rank_link :
  forall (A : LinDec) (t1 t2 : Tree A),
    rank (link t1 t2) = 1 + rank t1.
Proof.
  destruct t1, t2. cbn. dec.
Admitted.

(** TODO WUT ACHTUNG: changed [link]. *)
Lemma insTree_isHeap :
  forall (A : LinDec) (t : Tree A) (h : Heap A),
    validTree t -> heapOrdered t -> isHeap h ->
      isHeap (insTree t h).
Proof.
  intros A t h; gen t.
  induction h as [| t' h']; cbn; intros.
    auto.
    match goal with
        | |- context [if ?x then _ else _] => destruct x
    end.
      auto.
      apply IHh'.
        red. rewrite rank_link. apply link_validTree'; auto. inv H1. inv H4.
Abort.