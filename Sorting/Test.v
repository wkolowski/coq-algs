Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort.

Require Import HybridSorts.

Set Implicit Arguments.

Time Eval compute in insertionSort natle testl.
Time Eval compute in ssFun natle testl.
Time Eval compute in qsFun natle testl.

Fixpoint cycle {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ cycle n' l
end.

Extraction Language Haskell.
Extraction hms2.

(*Time Compute hms2 128 natle (cycle 100 testl).
Time Compute ms natle (cycle 100 testl).
Time Compute ms2 natle (cycle 100 testl).
Time Compute hms 128 natle (cycle 100 testl).

Time Compute qs natle (cycle 500 testl).
Time Compute hqs natle 1024 (cycle 500 testl).
Time Compute insertionSort natle (cycle 500 testl).
Time Compute ssFun natle (cycle 200 testl).
Time Compute qs2 natle (cycle 200 testl).*)