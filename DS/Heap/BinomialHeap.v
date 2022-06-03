From CoqAlgs Require Export Base.
From CoqAlgs Require Export Ord.

Inductive Tree (A : Type) : Type :=
    | T : nat -> A -> list (Tree A) -> Tree A.

Arguments T [A] _ _ _.

Definition Forest (A : Type) : Type := list (Tree A).
Definition BinomialHeap (A : Type) : Type := list (Tree A).

Definition rank {A : Type} (t : Tree A) : nat :=
match t with
    | T r _ _ => r
end.

Definition root {A : Type} (t : Tree A) : A :=
match t with
    | T _ x _ => x
end.

Inductive elemTree {A : Type} (x : A) : Tree A -> Prop :=
    | elemTree_root :
        forall (n : nat) (l : list (Tree A)), elemTree x (T n x l)
    | elemTree_child :
        forall (n : nat) (y : A) (l : list (Tree A)) (t : Tree A),
          elemTree x t -> In t l -> elemTree x (T n y l).

Definition elem {A : Type} (x : A) (h : Forest A) : Prop :=
  exists t : Tree A, elemTree x t /\ In t h.

Inductive elemTree' {A : Type} (x : A) : Tree A -> Prop :=
    | elemTree'_root :
        forall (n : nat) (l : list (Tree A)), elemTree' x (T n x l)
    | elemTree'_heap :
        forall h : Forest A, ElemForest x h ->
          forall (n : nat) (y : A), elemTree' x (T n y h)

with ElemForest {A : Type} (x : A) : Forest A -> Prop :=
    | ElemForest_here :
        forall (t : Tree A) (h' : Forest A),
          elemTree' x t -> ElemForest x (t :: h')
    | ElemForest_there :
        forall (t : Tree A) (h' : Forest A),
          ElemForest x h' -> ElemForest x (t :: h').

Inductive isBinomialTree' {A : Type} : nat -> Tree A -> Prop :=
    | isBinomialTree'0 :
        forall x : A, isBinomialTree' 0 (T 0 x [])
    | isBinomialTree'S :
        forall (r : nat) (x : A) (l : list (Tree A)),
          isBinomialForest' (S r) l -> isBinomialTree' (S r) (T (S r) x l)

with isBinomialForest' {A : Type} : nat -> list (Tree A) -> Prop :=
    | isBinomialForest'_nil : isBinomialForest' 0 []
    | isBinomialForest'_cons :
        forall (r : nat) (t : Tree A) (l : list (Tree A)),
          isBinomialTree' r t -> isBinomialForest' r l -> isBinomialForest' (S r) (t :: l).

Definition isBinomialTree {A : Type} (t : Tree A) : Prop :=
  isBinomialTree' (rank t) t.

(* Definition isBinomialForest {A : Type} (h : Forest A) : Prop :=
  isBinomialForest' (rank t) t.
 *)

Inductive isHeap {A : Ord} : Tree A -> Prop :=
    | isHeapC :
        forall (r : nat) (x : A) (l : list (Tree A)),
          Forall (fun t => x ≤ root t /\ isHeap t) l ->
            isHeap (T r x l).

Definition isForestOfHeaps {A : Ord} (f : Forest A) : Prop :=
  Forall (fun t : Tree A => isHeap t) f.

Ltac isHeap :=
repeat match goal with
    | H : isHeap (T _ _ _) |- _                => inv H
    |                      |- _ -> _           => intros
    |                      |- isHeap (T _ _ _) => constructor
end.

Definition isBinomialHeap {A : Ord} (h : Forest A) : Prop :=
  Forall (fun t => isBinomialTree t /\ isHeap t) h.

#[global] Hint Constructors elemTree elemTree' ElemForest isBinomialTree' isBinomialForest' isHeap : core.

#[global] Hint Unfold isBinomialTree isBinomialHeap : core.

(** * Implementation *)

Definition empty {A : Type} : Forest A := [].

Definition isEmpty {A : Type} (h : Forest A) : bool :=
match h with
    | [] => true
    | _ => false
end.

Function link {A : Ord} (t1 t2 : Tree A) : Tree A :=
match t1, t2 with
    | T r1 x ts1, T r2 y ts2 =>
        if x ≤? y
        then T (S r1) x (t2 :: ts1)
        else T (S r2) y (t1 :: ts2)
end.

Function insTree {A : Ord} (t : Tree A) (h : BinomialHeap A) : BinomialHeap A :=
match h with
    | [] => [t]
    | t' :: h' =>
        if Nat.ltb (rank t) (rank t')
        then t :: h
        else insTree (link t t') h'
end.

Definition insert {A : Ord} (x : A) (h : Forest A) : Forest A :=
  insTree (T 0 x []) h.

Fixpoint merge {A : Ord} (h1 h2 : Forest A) : Forest A :=
match h1 with
    | [] => h2
    | t1 :: h1' =>
        let
          aux := fix aux (h2 : Forest A) : Forest A :=
          match h2 with
              | [] => h1
              | t2 :: h2' =>
                  if Nat.ltb (rank t1) (rank t2)
                  then t1 :: merge h1' h2
                  else
                    if Nat.ltb (rank t2) (rank t1)
                    then t2 :: aux h2'
                    else insTree (link t1 t2) (merge h1' h2')
          end
        in aux h2
end.

(* Functional Scheme merge_ind := Induction for merge Sort Prop. *)

Function removeMinTree
  {A : Ord} (h : Forest A) : option (Tree A * Forest A) :=
match h with
    | [] => None
    | [t] => Some (t, [])
    | t :: h' =>
        match removeMinTree h' with
            | None => None
            | Some (t', h'') =>
                if (root t ≤? root t') && negb (root t =? root t')
                then Some (t, h')
                else Some (t', t :: h'')
        end
end.

Definition findMin {A : Ord} (h : Forest A) : option A :=
match removeMinTree h with
    | None => None
    | Some (t, _) => Some (root t)
end.

Definition deleteMin {A : Ord} (h : Forest A) : option (Forest A) :=
match removeMinTree h with
    | None => None
    | Some (T _ x h1, h2) => Some (merge (rev h1) h2)
end.

Definition extractMin {A : Ord} (h : Forest A) : option (A * Forest A) :=
match removeMinTree h with
    | None => None
    | Some (T _ x h1, h2) => Some (x, merge h1 h2)
end.

(** spec of merge *)

Lemma merge_spec :
  forall (A : Ord) (h1 h2 : Forest A),
    merge h1 h2 =
    match h1, h2 with
        | [], _ => h2
        | _, [] => h1
        | t1 :: h1', t2 :: h2' =>
            if Nat.ltb (rank t1) (rank t2)
            then t1 :: merge h1' h2
            else
              if Nat.ltb (rank t2) (rank t1)
              then t2 :: merge h1 h2'
              else insTree (link t1 t2) (merge h1' h2')
    end.
Proof.
  destruct h1, h2; reflexivity.
Qed.

(** * Properties of [isEmpty] *)

Lemma isEmpty_empty_false :
  forall {A : Ord} (h : Forest A),
    isEmpty h = false <-> h <> empty.
Proof.
  destruct h; compute; firstorder congruence.
Qed.

Lemma isEmpty_empty_true :
  forall (A : Ord) (h : Forest A),
    isEmpty h = true <-> h = empty.
Proof.
  destruct h; compute; firstorder congruence.
Qed.

Lemma isEmpty_elem :
  forall (A : Ord) (h : Forest A),
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

Lemma isEmpty_ElemForest :
  forall (A : Ord) (h : Forest A),
    isEmpty h = true <-> forall x : A, ~ ElemForest x h.
Proof.
  split; intro.
    inv 1; cbn in *; congruence.
    induction h; intros.
      cbn. reflexivity.
      specialize (H (root a)). contradiction H. destruct a. cbn.
        apply ElemForest_here. auto.
Qed.

Lemma isBinomialHeap_empty :
  forall A : Ord, isBinomialHeap (@empty A).
Proof.
  intro. unfold isBinomialHeap, empty. constructor.
Qed.

(** * Properties of [link]. *)

Ltac tree' := intros; cbn in *;
repeat match goal with
    | H : context [if ?x then _ else _] |- _ => destruct x
    | |- context [if ?x then _ else _] => destruct x
    | H : _ \/ _ |- _ => inv H
    | H : elemTree' _ (T _ _ _) |- _ => inv H
    | H : ElemForest _ [] |- _ => inv H
    | H : ElemForest _ (_ :: _) |- _ => inv H
end; auto.

Lemma elemTree_link :
  forall (A : Ord) (x : A) (t1 t2 : Tree A),
    elemTree x (link t1 t2) <-> elemTree x t1 \/ elemTree x t2.
Proof.
  split.
    destruct t1, t2; cbn; intro; trich.
      inv H. inv H5. eauto.
      inv H. inv H5. eauto.
    inv 1.
      destruct t1, t2; cbn; trich.
        inv H0. eapply elemTree_child; cbn; eauto.
        inv H0.
          eapply elemTree_child; cbn; eauto.
          eapply elemTree_child with (T n c l).
            econstructor; eauto.
            left. reflexivity.
      destruct t1, t2; cbn; trich.
        inv H0.
          eapply elemTree_child; cbn; eauto.
          eapply elemTree_child with (T n0 c0 l0).
            econstructor; eauto.
            left. reflexivity.
        inv H0. eapply elemTree_child; cbn; eauto.
Qed.

Lemma elemTree'_link :
  forall (A : Ord) (x : A) (t1 t2 : Tree A),
    elemTree' x (link t1 t2) <-> elemTree' x t1 \/ elemTree' x t2.
Proof.
  split; destruct t1, t2; cbn; intros; trich; tree'.
Qed.

Lemma isBinomialTree'_link :
  forall (A : Ord) (t1 t2 : Tree A) (r : nat),
    isBinomialTree' r t1 -> isBinomialTree' r t2 ->
      isBinomialTree' (S r) (link t1 t2).
Proof.
  do 2 inv 1; trich.
Qed.

Lemma isHeap_link :
  forall {A : Ord} {t1 t2 : Tree A},
    isHeap t1 -> isHeap t2 ->
      isHeap (link t1 t2).
Proof.
  intros until t2.
  functional induction link t1 t2;
  isHeap.
    constructor.
      split; trich.
      assumption.
    constructor.
      split; trich.
      assumption.
Qed.

Lemma rank_link :
  forall {A : Ord} {t1 t2 : Tree A} {r : nat},
    isBinomialTree' r t1 -> isBinomialTree' r t2 ->
      isBinomialTree' (S r) (link t1 t2).
Proof.
  intros until t2.
  functional induction link t1 t2;
  inv 1; inv 1.
Qed.

(** * Properties of [insTree] *)

Lemma isEmpty_insTree :
  forall (A : Ord) (t : Tree A) (h : Forest A),
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

Lemma ElemForest_insTree :
  forall (A : Ord) (h : Forest A) (x : A) (t : Tree A),
    ElemForest x (insTree t h) <-> elemTree' x t \/ ElemForest x h.
Proof.
  split; revert x t.
    induction h as [| t' h']; tree'.
      specialize (IHh' _ _ H). rewrite elemTree'_link in IHh'. firstorder.
    induction h as [| t' h']; tree';
      apply IHh'; rewrite elemTree'_link; auto.
Qed.

Lemma isBinomialForest'_insTree :
  forall {A : Ord} {t : Tree A} {f : Forest A} {r1 r2 : nat},
    isBinomialTree' r1 t -> isBinomialForest' r2 f ->
      exists r : nat,
        isBinomialForest' r (insTree t f).
Proof.
  intros * H1 H2. revert t r1 H1.
  induction H2; intros.
    cbn. exists (S r1). constructor.
      assumption.
      clear H1. induction r1.
        constructor.
(*
        constructor 2. assumption.
    eapply IHisBinomialForest'. eassumption.
    {
      destruct (IHisBinomialForest' _ _ H1) as [r' IH'].
      simpl. destruct (Nat.ltb_spec (rank t0) (rank t)).
        exists (S r). constructor 2.
*)
Admitted.

Lemma isForestOfHeaps_insTree :
  forall {A : Ord} {t : Tree A} {f : Forest A},
    isHeap t -> isForestOfHeaps f ->
      isForestOfHeaps (insTree t f).
Proof.
  intros until f.
  functional induction insTree t f;
  inv 2.
    constructor; auto.
    constructor; auto.
    apply IHb.
      apply isHeap_link; assumption.
      assumption.
Qed.

(** * Properties of [insert] *)

Lemma isEmpty_insert :
  forall {A : Ord} (x : A) (h : Forest A),
    isEmpty (insert x h) = false.
Proof.
  intros. unfold insert. apply isEmpty_insTree.
Qed.

Lemma ElemForest_insert :
  forall (A : Ord) (x : A) (h : Forest A),
    ElemForest x (insert x h).
Proof.
  intros. unfold insert. rewrite ElemForest_insTree. auto.
Qed.

Lemma isBinomialForest_insert :
  forall {A : Ord} {x : A} {f : Forest A} {r : nat},
    isBinomialForest' r f ->
      isBinomialForest' r (insert x f).
Proof.
  intros.
  unfold insert.
Admitted.

Lemma isForestOfHeaps_insert :
  forall {A : Ord} {x : A} {f : Forest A},
    isForestOfHeaps f ->
      isForestOfHeaps (insert x f).
Proof.
  intros. unfold insert.
  apply isForestOfHeaps_insTree.
    constructor; auto.
    assumption.
Qed.

(** * Properties of [merge] *)

Lemma isEmpty_merge :
  forall {A : Ord} (h1 h2 : Forest A),
    isEmpty (merge h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1, h2; rewrite merge_spec; cbn; auto.
  repeat match goal with
      | |- context [if ?x then _ else _] => destruct x
  end; cbn.
    1-2: reflexivity.
    rewrite isEmpty_insTree. reflexivity.
Qed.

Lemma ElemForest_merge :
  forall (A : Ord) (x : A) (h1 h2 : Forest A),
    ElemForest x (merge h1 h2) <-> ElemForest x h1 \/ ElemForest x h2.
Proof.
  split; gen h2.
    induction h1; induction h2; tree'.
      specialize (IHh1 _ H1). firstorder.
      specialize (IHh2 H1). inv IHh2.
      clear IHh2. rewrite ElemForest_insTree, elemTree'_link in H.
        decompose [or] H; clear H; auto. specialize (IHh1 _ H0). inv IHh1.
    induction h1; induction h2; tree';
      rewrite ElemForest_insTree, elemTree'_link; auto.
Qed.

Lemma isBinomialForest'_merge :
  forall {A : Ord} {f1 f2 : Forest A} {r1 r2 : nat},
    isBinomialForest' r1 f1 -> isBinomialForest' r2 f2 ->
      exists r : nat, isBinomialForest' r (merge f1 f2).
Proof.
  intros until 1. revert r2 f2.
  induction H.
    intros. cbn. exists r2. assumption.
(*
    intros. eapply IHisBinomialForest'. eassumption.
    induction 1.
      cbn. exists (S r). constructor; assumption.
      apply IHisBinomialForest'0.
*)
Admitted.

Lemma isForestOfHeaps_merge :
  forall {A : Ord} {f1 f2 : Forest A},
    isForestOfHeaps f1 -> isForestOfHeaps f2 ->
      isForestOfHeaps (merge f1 f2).
Proof.
  intros A f1 f2 H1 H2. revert f2 H2.
  induction H1; intros f2 H2.
    cbn. assumption.
    induction H2.
      cbn. constructor; assumption.
      simpl. destruct (Nat.ltb_spec (rank x) (rank x0)).
        constructor.
          assumption.
          apply IHForall. constructor; assumption.
Admitted.

(** * Properties of [removeMinTree] *)

Lemma isEmpty_removeMinTree_false :
  forall (A : Ord) (t : Tree A) (h h' : Forest A),
    removeMinTree h = Some (t, h') -> isEmpty h = false.
Proof.
  intros. destruct h; cbn in *; congruence.
Qed.

Lemma isEmpty_removeMinTree_false' :
  forall (A : Ord) (h : Forest A),
    isEmpty h = false <->
    exists (t : Tree A) (h' : Forest A), removeMinTree h = Some (t, h').
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
  forall (A : Ord) (h : Forest A),
    removeMinTree h = None <-> isEmpty h = true.
Proof.
  split.
    functional induction @removeMinTree A h; cbn; try congruence.
      destruct h'; auto.
    destruct h; cbn; congruence.
Qed.

Lemma ElemForest_removeMinTree :
  forall (A : Ord) (x : A) (t : Tree A) (h h' : Forest A),
    removeMinTree h = Some (t, h') ->
      ElemForest x h <-> elemTree' x t \/ ElemForest x h'.
Proof.
  split; revert x t h' H.
    functional induction @removeMinTree A h; inv 1; intro; inv H.
      specialize (IHo _ _ _ e0 H1). inv IHo.
    functional induction @removeMinTree A h; inv 1; intro; inv H.
      specialize (IHo x _ _ e0 ltac:(auto)). inv IHo.
      inv H0. specialize (IHo x _ _ e0 ltac:(auto)). inv IHo.
Qed.

Lemma isBinomialForest'_removeMinTree :
  forall {A : Ord} {f f' : Forest A} {t : Tree A},
    removeMinTree f = Some (t, f') ->
      forall {r : nat}, isBinomialForest' r f ->
        exists r' : nat, isBinomialForest' r' f'.
Proof.
  intros until 2.
  revert f' t H.
  induction H0.
    inv 1.
    intros. eapply IHisBinomialForest'.
Admitted.

Lemma isForestOfHeaps_removeMinTree :
  forall {A : Ord} {f f' : Forest A} {t : Tree A},
    removeMinTree f = Some (t, f') ->
      isForestOfHeaps f -> isForestOfHeaps f'.
Proof.
  intros until f.
  functional induction removeMinTree f;
  inv 1; inv 1.
  constructor.
    assumption.
    eapply IHo; eassumption.
Qed.

Lemma removeMinTree_insTree :
  forall (A : Ord) (t : Tree A) (h : Forest A),
    removeMinTree (insTree t h) <> None.
Proof.
  repeat intro. apply isEmpty_removeMinTree_true in H.
  rewrite isEmpty_insTree in H. congruence.
Qed.

(** * Properties of [findMin] *)

(** * Properties of [deleteMin] *)

(** * Properties of [extractMin] *)

Lemma isEmpty_extractMin_false :
  forall (A : Ord) (h : Forest A),
    isEmpty h = false <->
    exists (m : A) (h' : Forest A), extractMin h = Some (m, h').
Proof.
  split; unfold extractMin; intros.
    apply isEmpty_removeMinTree_false' in H. destruct H as [t [h' H]].
      destruct t as [r x h'']. exists x, (merge h'' h'). rewrite H. auto.
    destruct H as [m [h' H]]. apply isEmpty_removeMinTree_false'.
      case_eq (removeMinTree h); intros.
        destruct p. eauto.
        rewrite H0 in H. congruence.
Qed.

Lemma isEmpty_extractMin_true :
  forall (A : Ord) (h : Forest A),
    isEmpty h = true <-> extractMin h = None.
Proof.
  unfold extractMin; split; intros.
    apply isEmpty_removeMinTree_true in H. rewrite H. reflexivity.
    case_eq (removeMinTree h); intros.
      rewrite H0 in H. destruct p, t. inv H.
      apply isEmpty_removeMinTree_true. assumption.
Qed.

Lemma ElemForest_extractMin :
  forall (A : Ord) (x m : A) (h h' : Forest A),
    extractMin h = Some (m, h') ->
      ElemForest x h <-> x = m \/ ElemForest x h'.
Proof.
  unfold extractMin. split.
    case_eq (removeMinTree h); intros; rewrite H0 in *.
      destruct p, t. inv H.
        apply ElemForest_removeMinTree with (x := x) in H0.
        rewrite ElemForest_merge. firstorder. inv H.
      congruence.
    case_eq (removeMinTree h); intros; rewrite H0 in *.
      destruct p, t. inv H. rewrite ElemForest_merge in *.
        apply ElemForest_removeMinTree with (x := x) in H0.
        firstorder; subst; auto.
      congruence.
Qed.

Lemma extractMin_insTree :
  forall (A : Ord) (t : Tree A) (h : Forest A),
    extractMin (insTree t h) <> None.
Proof.
  intros. unfold extractMin.
  case_eq (removeMinTree (insTree t h)); intros.
    destruct p, t0. inv 1.
    apply removeMinTree_insTree in H. contradiction.
Qed.

Lemma extractMin_insert :
  forall (A : Ord) (x : A) (h : Forest A),
    extractMin (insert x h) <> None.
Proof.
  intros. unfold insert. apply extractMin_insTree.
Qed.

Lemma extractMin_merge :
  forall (A : Ord) (h1 h2 : Forest A),
    extractMin (merge h1 h2) = None <->
    extractMin h1 = None /\ extractMin h2 = None.
Proof.
  intros. rewrite <- !isEmpty_extractMin_true, isEmpty_merge.
  destruct h1, h2; cbn; firstorder congruence.
Qed.









(** Counting shiet. *)

Fixpoint countTree {A : Ord} (x : A) (t : Tree A) : nat :=
match t with
    | T _ x' l =>
        (if x =? x' then 1 else 0) +
          fold_right (fun t ts => countTree x t + ts) 0 l
end.

Definition countForest {A : Ord} (x : A) (h : Forest A) : nat :=
  fold_right (fun t ts => countTree x t + ts) 0 h.

Lemma isEmpty_countTree :
  forall (A : Ord) (t : Tree A),
    isEmpty [t] = true <-> forall x : A, countTree x t = 0.
Proof.
  split; cbn; intros.
    congruence.
    specialize (H (root t)). destruct t. cbn in H. trich.
Qed.

Lemma countTree_link :
  forall (A : Ord) (x : A) (t1 t2 : Tree A),
    countTree x (link t1 t2) = countTree x t1 + countTree x t2.
Proof.
  destruct t1, t2. cbn. do 2 trich; unfold id; lia.
Qed.

Lemma insTree_Some :
  forall (A : Ord) (t : Tree A) (h : Forest A),
    exists (t' : Tree A) (h' : Forest A),
      insTree t h = t' :: h'.
Proof.
  intros A t h; gen t. induction h as [| t' h']; tree'; eauto.
Qed.

Lemma countForest_insTree :
  forall (A : Ord) (x : A) (t : Tree A) (h : Forest A),
    countForest x (insTree t h) = countTree x t + countForest x h.
Proof.
  intros A x t h; gen t; gen x.
  induction h as [| t' h']; cbn; intros.
    reflexivity.
    tree'. unfold countForest in *. rewrite IHh'.
      rewrite countTree_link. lia.
Qed.

Lemma countForest_insert :
  forall (A : Ord) (x y : A) (h : Forest A),
    countForest x (insert y h) =
      (if x =? y then 1 else 0) + countForest x h.
Proof.
  intros. unfold insert. rewrite countForest_insTree. cbn. trich.
Qed.