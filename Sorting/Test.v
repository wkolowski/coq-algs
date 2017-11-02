Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort.
Require Import Heapsort.

Require Import BST.
Require Import ListLemmas.

Set Implicit Arguments.

Require Import Coq.Sorting.Heap.

Lemma my_le_trans :
  forall a b c : nat, a <= b -> b <= c -> a <= c.
Proof.
  induction a as [| a']; simpl; intros.
    omega.
    omega.
Defined.


(*Time Compute hms2 128 natle (cycle 100 testl).
Time Compute ms natle (cycle 100 testl).
Time Compute ms2 natle (cycle 100 testl).
Time Compute hms 128 natle (cycle 100 testl). *)

(*Time Compute insertionSort natle (cycle 2500 testl).
Time Compute treeSort natle (cycle 2500 testl).*)

(*Time Compute leftistHeapsort natle (cycle 1 testl).

Time Compute qs natle (cycle 5 testl).
Time Compute qs2 natle (cycle 5 testl).

Time Compute insertionSort natle (cycle 5 testl).
Time Compute ss natle (cycle 5 testl).

Time Compute leftistHeapsort natle (cycle 2 testl).

Time Compute hqs 2048 natle (cycle 750 testl).
Time Compute hqs2 2048 natle (treeSort natle) (cycle 750 testl).
Time Compute treeSort natle (cycle 750 testl).
Time Compute hqs2 16 natle (leftistHeapsort natle) (cycle 100 testl).
Time Compute hms 1024 natle (cycle 100 testl).
Time Compute treeSort natle (cycle 100 testl).
Time Compute leftistHeapsort natle (cycle 20 testl).

Time Compute hqs 1024 natle (cycle 2000 [1]).
Time Compute hms 1024 natle (cycle 2000 [1]).
Time Compute treeSort natle (cycle 2000 [1]).*)