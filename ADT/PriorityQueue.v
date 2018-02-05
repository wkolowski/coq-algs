Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Require Import LinDec.

(* TODO *) Module Type PriorityQueue.

Parameter PQ : LinDec -> LinDec.

Parameter empty :
  forall {A : LinDec}, PQ A.

Parameter insert :
  forall {A : LinDec}, A -> PQ A -> PQ A.

Parameter unMin :
  forall {A : LinDec}, PQ A -> option (A * PQ A).

Parameter findMin :
  forall {A : LinDec}, PQ A -> option A.

Parameter deleteMin :
  forall {A : LinDec}, PQ A -> PQ A.

(** Secondary. *)
Parameter isEmpty :
  forall {A : LinDec}, PQ A -> bool.

Parameter size :
  forall {A : LinDec}, PQ A -> nat.

(** Derived operations. *)
Definition singleton {A : LinDec} (x : A) : PQ A :=
  insert x empty.

Fixpoint fromList {A : LinDec} (l : list A) : PQ A :=
match l with
    | [] => empty
    | h :: t => insert h (fromList t)
end.

(** Properties of [unMin]. *)

Parameter unMin_empty :
  forall {A : LinDec},
    unMin (@empty A) = None.

Parameter unMin_insert :
  forall {A : LinDec} (x : A) (q : PQ A),
    unMin (insert x q) <> None.

(*Parameter unMin_insert' :
  forall {A : LinDec} (x : A) (q : PQ A),
    exists (m : A) (q' : PQ A), unMin (insert x q) = Some (m, q').*)

Parameter unMin_singleton :
  forall {A : LinDec} (x : A),
    unMin (singleton x) = Some (x, empty).

(** Properties of [isEmpty]. *)

Parameter isEmpty_empty_false :
  forall {A : LinDec} (q : PQ A),
    isEmpty q = false <-> q <> empty.

Parameter isEmpty_empty_true :
  forall (A : LinDec) (q : PQ A),
    isEmpty q = true <-> q = empty.

Parameter isEmpty_insert :
  forall {A : LinDec} (x : A) (q : PQ A),
    isEmpty (insert x q) = false.

Parameter isEmpty_unMin_false :
  forall (A : LinDec) (q : PQ A),
    isEmpty q = true <-> unMin q = None.

Parameter isEmpty_unMin_true :
  forall (A : LinDec) (q : PQ A),
    isEmpty q = false <->
    exists (m : A) (q' : PQ A), unMin q = Some (m, q').

Lemma isEmpty_singleton :
  forall (A : LinDec) (x : A),
    isEmpty (singleton x) = false.
Proof.
  intros. unfold singleton. rewrite isEmpty_insert. reflexivity.
Qed.

(** Properties of [size]. *)

Parameter size_empty :
  forall {A : LinDec},
    size (@empty A) = 0.

Parameter size_empty_general :
  forall {A : LinDec} (q : PQ A),
    size q = 0 <-> q = empty.

Parameter size_insert :
  forall (A : LinDec) (x : A) (q : PQ A),
    size (insert x q) = 1 + size q.

Parameter size_unMin :
  forall (A : LinDec) (m : A) (q q' : PQ A),
    unMin q = Some (m, q') -> size q = S (size q').

Parameter size_isEmpty_false :
  forall (A : LinDec) (q : PQ A),
    isEmpty q = false <-> size q <> 0.

Parameter size_isEmpty_true :
  forall (A : LinDec) (q : PQ A),
    isEmpty q = true <-> size q = 0.

Lemma size_singleton :
  forall (A : LinDec) (x : A),
    size (singleton x) = 1.
Proof.
  intros. unfold singleton. rewrite size_insert, size_empty. reflexivity.
Qed.

(** More derived operations. *)

Function toList {A : LinDec} (q : PQ A) {measure size q} : list A :=
match unMin q with
    | None => []
    | Some (m, q') => m :: toList q'
end.
Proof.
  intros. apply size_unMin in teq. rewrite teq. apply le_n.
Defined.

Arguments toList {x} _.

Definition priorityQueueSort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Require Import Sorting.Sort.

Lemma toList_sorted :
  forall (A : LinDec) (q : PQ A), sorted A (toList q).
Proof.
  intros. functional induction @toList A q.
    constructor.
    rewrite toList_equation in *. destruct (unMin q').
      destruct p. constructor; auto. (*apply unMin_spec.*) admit.
      constructor.
Admitted.

Lemma priorityQueueSort_sorted :
  forall (A : LinDec) (l : list A),
    sorted A (priorityQueueSort A l).
Proof.
  intros. unfold priorityQueueSort. apply toList_sorted.
Qed.

Lemma priorityQueueSort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (priorityQueueSort A l).
Proof.
  unfold perm, priorityQueueSort. intros.
  induction l as [| h t]; cbn.
    rewrite toList_equation, unMin_empty. cbn. reflexivity.
    admit.
Admitted.

Instance Sort_priorityQueueSort : Sort :=
{
    sort := @priorityQueueSort;
}.
Proof.
  all: intros.
    apply priorityQueueSort_sorted.
    apply priorityQueueSort_perm.
Defined.

End PriorityQueue.

Module Type Ordered.

Parameter Elem : LinDec.

End Ordered.

Module Type MergeablePriorityQueue (PQ : PriorityQueue).

Import PQ.

Parameter merge :
  forall {A : LinDec}, PQ A -> PQ A -> PQ A.

Parameter isEmpty_merge :
  forall (A : LinDec) (q1 q2 : PQ A),
    isEmpty (merge q1 q2) = isEmpty q1 && isEmpty q2.

Parameter isEmpty_merge' :
  forall (A : LinDec) (q1 q2 : PQ A),
    isEmpty (merge q1 q2) = true <->
    isEmpty q1 = true /\ isEmpty q2 = true.

Parameter size_merge :
  forall (A : LinDec) (q1 q2 : PQ A),
    size (merge q1 q2) = size q1 + size q2.

End MergeablePriorityQueue.

Module Type PriorityQueue2 (O : Ordered).

Parameter PQ : LinDec.

Parameter empty : PQ.

Parameter insert : O.Elem -> PQ -> PQ.

Parameter min : PQ -> option (O.Elem * PQ).

Parameter findMin : PQ -> option O.Elem.

Parameter deleteMin : PQ -> option PQ.

(** Secondary. *)
Parameter isEmpty : PQ -> bool.

(** wut *)
Definition singleton (x : O.Elem) : PQ := insert x empty.

End PriorityQueue2.

(*Module wut : PriorityQueue.

Require Import PQ.

(** Error: The kernel does not recognize yet that a parameter can be
    instantiated by an inductive type. Hint: you can rename the inductive
    type and give a definition to map the old name to the new name. *)
(* Inductive PQ := wut : PQ. *)

Definition PQ (A : LinDec) := PQ A.

Definition singleton {A : LinDec} (x : A) : PQ A :=
  node x empty empty.

End wut.*)