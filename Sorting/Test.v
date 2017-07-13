Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort.

Require Import HybridSorts.

Set Implicit Arguments.

Fixpoint cycle {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ cycle n' l
end.

(*Time Compute hqs 128 natle (cycle 100 testl).
Time Compute hms 128 natle (cycle 100 testl).*)

(*Time Compute hms2 128 natle (cycle 100 testl).
Time Compute ms natle (cycle 100 testl).
Time Compute ms2 natle (cycle 100 testl).
Time Compute hms 128 natle (cycle 100 testl).

Time Compute qs natle (cycle 500 testl).
Time Compute insertionSort natle (cycle 500 testl).
Time Compute ssFun natle (cycle 200 testl).
Time Compute qs2 natle (cycle 200 testl).*)