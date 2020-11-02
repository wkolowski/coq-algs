Require Import RCCBase.

Require Import TrichDec.

Require Import Sorting.Sort.

Module Type PriorityQueue.

Parameter PQ : TrichDec -> Type.

Parameter empty :
  forall {A : TrichDec}, PQ A.

Parameter insert :
  forall {A : TrichDec}, A -> PQ A -> PQ A.

Parameter unMin :
  forall {A : TrichDec}, PQ A -> option (A * PQ A).

Parameter findMin :
  forall {A : TrichDec}, PQ A -> option A.

Parameter deleteMin :
  forall {A : TrichDec}, PQ A -> PQ A.

(** Secondary. *)
Parameter isEmpty :
  forall {A : TrichDec}, PQ A -> bool.

Parameter size :
  forall {A : TrichDec}, PQ A -> nat.

(** Derived operations. *)
Definition singleton {A : TrichDec} (x : A) : PQ A :=
  insert x empty.

Fixpoint fromList {A : TrichDec} (l : list A) : PQ A :=
match l with
    | [] => empty
    | h :: t => insert h (fromList t)
end.

Parameter elem :
  forall {A : TrichDec}, A -> PQ A -> Prop.

(** Properties of [unMin]. *)

Parameter unMin_empty :
  forall {A : TrichDec},
    unMin (@empty A) = None.

Parameter unMin_insert :
  forall {A : TrichDec} (x : A) (q : PQ A),
    unMin (insert x q) <> None.

(*Parameter unMin_insert' :
  forall {A : TrichDec} (x : A) (q : PQ A),
    exists (m : A) (q' : PQ A), unMin (insert x q) = Some (m, q').*)

Parameter unMin_singleton :
  forall {A : TrichDec} (x : A),
    unMin (singleton x) = Some (x, empty).

(** Properties of [isEmpty]. *)

Parameter isEmpty_empty_false :
  forall {A : TrichDec} (q : PQ A),
    isEmpty q = false <-> q <> empty.

Parameter isEmpty_empty_true :
  forall (A : TrichDec) (q : PQ A),
    isEmpty q = true <-> q = empty.

Parameter isEmpty_insert :
  forall {A : TrichDec} (x : A) (q : PQ A),
    isEmpty (insert x q) = false.

Parameter isEmpty_unMin_false :
  forall (A : TrichDec) (q : PQ A),
    isEmpty q = false <->
    exists (m : A) (q' : PQ A), unMin q = Some (m, q').

Parameter isEmpty_unMin_true :
  forall (A : TrichDec) (q : PQ A),
    isEmpty q = true <-> unMin q = None.

Lemma isEmpty_singleton :
  forall (A : TrichDec) (x : A),
    isEmpty (singleton x) = false.
Proof.
  intros. unfold singleton. rewrite isEmpty_insert. reflexivity.
Qed.

(** Properties of [size]. *)

Parameter size_empty :
  forall {A : TrichDec},
    size (@empty A) = 0.

Parameter size_empty_general :
  forall {A : TrichDec} (q : PQ A),
    size q = 0 <-> q = empty.

Parameter size_insert :
  forall (A : TrichDec) (x : A) (q : PQ A),
    size (insert x q) = 1 + size q.

Parameter size_unMin :
  forall (A : TrichDec) (m : A) (q q' : PQ A),
    unMin q = Some (m, q') -> size q = S (size q').

Parameter size_isEmpty_false :
  forall (A : TrichDec) (q : PQ A),
    isEmpty q = false <-> size q <> 0.

Parameter size_isEmpty_true :
  forall (A : TrichDec) (q : PQ A),
    isEmpty q = true <-> size q = 0.

Lemma size_singleton :
  forall (A : TrichDec) (x : A),
    size (singleton x) = 1.
Proof.
  intros. unfold singleton. rewrite size_insert, size_empty. reflexivity.
Qed.

(** More derived operations. *)

Function toList {A : TrichDec} (q : PQ A) {measure size q} : list A :=
match unMin q with
    | None => []
    | Some (m, q') => m :: toList q'
end.
Proof.
  intros. apply size_unMin in teq. rewrite teq. apply le_n.
Defined.

Arguments toList {x} _.

Definition priorityQueueSort (A : TrichDec) (l : list A) : list A :=
  toList (fromList l).

Parameter unMin_spec :
  forall (A : TrichDec) (m : A) (q q' : PQ A),
    unMin q = Some (m, q') ->
      forall x : A, elem x q -> m ≤ x.

Parameter unMin_elem :
  forall (A : TrichDec) (x m : A) (q q' : PQ A),
    unMin q = Some (m, q') -> elem x q <-> x = m \/ elem x q'.

Lemma Sorted_toList :
  forall (A : TrichDec) (q : PQ A), Sorted trich_le (toList q).
Proof.
  intros. functional induction @toList A q.
    constructor.
    rewrite toList_equation in *. destruct (unMin q') eqn: H.
      2: constructor.
      destruct p. constructor; auto. apply (unMin_spec A m q q').
        assumption.
        rewrite (unMin_elem _ c m q q').
          right. rewrite (unMin_elem _ c c q' p).
            left. reflexivity.
            assumption.
          assumption.
Qed.

Lemma Sorted_priorityQueueSort :
  forall (A : TrichDec) (l : list A),
    Sorted trich_le (priorityQueueSort A l).
Proof.
  intros. unfold priorityQueueSort. apply Sorted_toList.
Qed.

(*Parameter count_toList_insert :
  forall (A : TrichDec) (x h : A) (l : list A),
    count (fun y => y =? x) (toList (insert h (fromList l))) =
    (if x =? h then S else id) (count (fun y => y =? x) l).*)

Parameter count_toList_insert :
  forall (A : TrichDec) (p : A -> bool) (h : A) (l : list A),
    count p (toList (insert h (fromList l))) =
    (if p h then S else id) (count p l).

Lemma priorityQueueSort_perm :
  forall (A : TrichDec) (l : list A),
    perm l (priorityQueueSort A l).
Proof.
  unfold perm, priorityQueueSort. intros.
  induction l as [| h t]; cbn.
    rewrite toList_equation, unMin_empty. cbn. reflexivity.
    rewrite count_toList_insert. destruct (p h); reflexivity.
Qed.

Lemma Permutation_priorityQueueSort :
  forall (A : TrichDec) (l : list A),
    Permutation (priorityQueueSort A l) l.
Proof.
  intros. apply perm_Permutation.
  rewrite <- priorityQueueSort_perm.
  reflexivity.
Qed.

#[refine]
Instance Sort_priorityQueueSort (A : TrichDec) : Sort trich_le :=
{
    sort := @priorityQueueSort A;
}.
Proof.
  all: intros.
    apply Sorted_priorityQueueSort.
    apply Permutation_priorityQueueSort.
Defined.

End PriorityQueue.

Module Type Ordered.

Parameter Elem : TrichDec.

End Ordered.

Module Type MergeablePriorityQueue (PQ : PriorityQueue).

Import PQ.

Parameter merge :
  forall {A : TrichDec}, PQ A -> PQ A -> PQ A.

Parameter isEmpty_merge :
  forall (A : TrichDec) (q1 q2 : PQ A),
    isEmpty (merge q1 q2) = isEmpty q1 && isEmpty q2.

Parameter isEmpty_merge' :
  forall (A : TrichDec) (q1 q2 : PQ A),
    isEmpty (merge q1 q2) = true <->
    isEmpty q1 = true /\ isEmpty q2 = true.

Parameter size_merge :
  forall (A : TrichDec) (q1 q2 : PQ A),
    size (merge q1 q2) = size q1 + size q2.

End MergeablePriorityQueue.

Module Type PriorityQueue2 (O : Ordered).

Parameter PQ : TrichDec.

Parameter empty : PQ.

Parameter insert : O.Elem -> PQ -> PQ.

Parameter min : PQ -> option (O.Elem * PQ).

Parameter findMin : PQ -> option O.Elem.

Parameter deleteMin : PQ -> option PQ.

(** Secondary. *)
Parameter isEmpty : PQ -> bool.

Definition singleton (x : O.Elem) : PQ := insert x empty.

End PriorityQueue2.