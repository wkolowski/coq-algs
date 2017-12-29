Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export SplayHeap.

Set Implicit Arguments.

Fixpoint size {A : LinDec} (h : SplayHeap A) : nat :=
match h with
    | empty => 0
    | node _ l r => 1 + size l + size r
end.

Lemma size_partition :
  forall (A : LinDec) (x : A) (h h1 h2 : SplayHeap A),
    partition x h = (h1, h2) -> size h = size h1 + size h2.
Proof.
  intros. functional induction partition x h; cbn;
  inv H; dec; rewrite (IHp _ _ e3); omega.
Qed.

Lemma size_insert :
  forall (A : LinDec) (x : A) (h : SplayHeap A),
    size (insert x h) = S (size h).
Proof.
  intros. unfold insert. case_eq (partition x h); intros.
  cbn. apply size_partition in H. omega.
Qed.

Lemma size_deleteMin :
  forall (A : LinDec) (h : SplayHeap A),
    size (deleteMin h) = pred (size h).
Proof.
  intros. functional induction deleteMin h; cbn; trivial.
  rewrite IHs. destruct l; cbn.
    contradiction.
    trivial.
Qed.

Lemma size_deleteMin' :
  forall (A : LinDec) (h h' : SplayHeap A),
    h' = snd (deleteMin' h) -> size h' = pred (size h).
Proof.
  intros. functional induction deleteMin' h; cbn; inv H; trivial.
  destruct l; cbn.
    contradiction.
    rewrite e0 in IHp. cbn in IHp. rewrite IHp; trivial.
Qed.

Function toList {A : LinDec} (h : SplayHeap A) {measure size h} : list A :=
match h with
    | empty => []
    | _ =>
        match findMin h with
            | None => []
            | Some m => m :: toList (deleteMin h)
        end
end.
Proof.
  intros. subst. rewrite size_deleteMin. cbn. apply le_n.
Defined.

Function toList' {A : LinDec} (h : SplayHeap A) {measure size h} : list A :=
match h with
    | empty => []
    | _ =>
        match deleteMin' h with
            | (None, _) => []
            | (Some m, h') => m :: toList' h'
        end
end.
Proof.
  intros. subst. rewrite size_deleteMin' with (h := node c b b0).
    cbn. apply le_n.
    rewrite teq0. cbn. trivial.
Defined.

Fixpoint fromList {A : LinDec} (l : list A) : SplayHeap A :=
match l with
    | [] => empty
    | h :: t => insert h (fromList t)
end.

Definition splaySort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Definition splaySort' (A : LinDec) (l : list A) : list A :=
  toList' (fromList l).