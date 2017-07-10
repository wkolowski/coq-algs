Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort2.

Set Implicit Arguments.

Function hqs (A : LinDec) (n : nat) (l : list A) {measure length l} : list A :=
  if @leqb natle (length l) n
  then insertionSort A l
  else match l with
      | [] => []
      | h :: t =>
          let (lo, hi) := bifilter (fun x : A => x <=? h) t in
              hqs A n lo ++ h :: hqs A n hi
  end.
Proof.
  intros. rewrite bifilter_spec in teq1. inversion teq1.
    apply filter_lengthOrder.
  intros. rewrite bifilter_spec in teq1. inversion teq1.
    apply filter_lengthOrder.
Defined.