Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.

Require Import MergeSort.
Require Import QuickSort.

Require Import TreeSort.
Require Import Heapsort.
Require Import RedblackSort.

Require Import ListLemmas.

Require Import TrichQuicksort.

Set Implicit Arguments.

(*Require Import Coq.Sorting.Heap.

Lemma my_le_trans :
  forall a b c : nat, a <= b -> b <= c -> a <= c.
Proof.
  induction a as [| a']; simpl; intros.
    omega.
    omega.
Defined.*)

(* Slow sorts on small lists. *)
(*Time Compute ss natle (cycle 10 testl).
Time Compute insertionSort natle (cycle 10 testl).*)

(* Fast sorts on medium lists. *)
(*Time Compute ms natle (cycle 100 testl).
Time Compute ms2 natle (cycle 100 testl).

Time Compute qs natle (cycle 100 testl).
Time Compute qs2 natle (cycle 100 testl).

Time Compute tqs natlt (cycle 100 testl).

Time Compute treeSort natle (cycle 100 testl).
Time Compute treeSort' natle (cycle 100 testl).

Time Compute redblackSort natle (cycle 100 testl).
Time Compute redblackSort' natle (cycle 100 testl).

Time Eval lazy in leftistHeapsort natle (cycle 100 testl).
Time Eval lazy in leftistHeapsort' natle (cycle 100 testl).*)

(* Fast sorts on big lists. *)
(*Time Compute ms natle (cycle 200 testl).
Time Compute ms2 natle (cycle 200 testl).

Time Compute qs natle (cycle 200 testl).
Time Compute qs2 natle (cycle 200 testl).*)

(*Time Compute tqs natlt (cycle 1000 testl).

Time Compute treeSort natle (cycle 1000 testl).
Time Compute treeSort' natle (cycle 1000 testl).

Time Compute redblackSort natle (cycle 1000 testl).
Time Compute redblackSort' natle (cycle 1000 testl).

Time Eval lazy in leftistHeapsort' natle (cycle 300 testl).*)

(* Hybrid mergesort on big lists. *)
(*Time Compute @ghms 512 natle (insertionSort natle) (MsSplit natle)
  (cycle 200 testl).

Time Compute @ghms 1024 natle (treeSort natle) (MsSplit natle)
  (cycle 200 testl).

Time Compute @ghms 1024 natle (redblackSort natle) (MsSplit natle)
  (cycle 200 testl). *)

(* Bad
Time Compute @ghms 1024 natle (leftistHeapsort' natle) (MsSplit natle)
  (cycle 200 testl).
*)

(*Time Compute @hqs 1024 natle (insertionSort natle) (cycle 200 testl).

Time Compute @hqs 512 natle (treeSort natle) (cycle 200 testl).

Time Compute @hqs 512 natle (redblackSort natle) (cycle 200 testl).
*)

(* Bad
  Time Compute @hqs 256 natle (leftistHeapsort natle) (cycle 200 testl).
*)

(*Time Compute @htqs 1 natlt (insertionSort natle) (cycle 200 testl).

Time Compute @htqs 1 natlt (treeSort natle) (cycle 200 testl).

Time Compute @htqs 1 natlt (redblackSort natle) (cycle 200 testl).*)

(* Long lists made of one element. *)
Definition l1 := cycle 2500 [0].

(*Time Compute @ghms 64 natle (insertionSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natle (treeSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natle (redblackSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natle (leftistHeapsort' natle) (MsSplit natle) l1.

Time Compute @hqs 1024 natle (insertionSort natle) l1.

Time Compute @hqs 512 natle (treeSort natle) l1.

Time Compute @hqs 512 natle (redblackSort natle) l1.

Time Compute @htqs 0 natlt (insertionSort natle) l1.

Time Compute @htqs 0 natlt (treeSort natle) l1.

Time Compute @htqs 0 natlt (redblackSort natle) l1.*)

Fixpoint toN (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: toN n'
end.

(*CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).*)

Time Compute qs natle (toN 200).
Time Compute tqs natlt (toN 200).
Time Compute insertionSort natle (toN 500).
Time Compute treeSort natle (toN 500).
Time Compute redblackSort natle (toN 500).