Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.

Require Import MergeSort.
Require Import QuickSort.

Require Import TreeSort.
Require Import RedblackSort.

Require Import PairingSort.
Require Import SplaySort.

Require Import ListLemmas.

(*Require Import TrichQuicksort.*)

Require Import LeftistHeap.

Set Implicit Arguments.

(* Doesn't work at all. *)
(*
Require Import Coq.Sorting.Heap.

Theorem my_le_trans :
  forall a b c : nat, a <= b -> b <= c -> a <= c.
Proof.
  induction 2.
    assumption.
    apply le_S. assumption.
Defined.

Definition stdSort_nat (l : list nat) : list nat :=
match
  treesort natle leq eq (LinDec_leq_dec natle) LinDec_eq_dec my_le_trans l
with
    | exist2 l' _ _ => l'
end.

Time Compute stdSort_nat [].
*)

(* Slow sorts on small lists. *)

(*Time Compute ss natle (cycle 100 testl).
Time Compute ss' natle (cycle 100 testl).
Time Compute ss'' natle (cycle 100 testl).
Time Compute ss_bifilter natle (cycle 500 testl).
Time Compute ss_mins' natlt (cycle 500 testl).

Time Compute ss natle (cycle 10 testl).
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
(*Time Compute redblackSort' natle (cycle 100 testl).*)

Time Eval lazy in leftistHeapsort natle (cycle 100 testl).
(*Time Eval lazy in leftistHeapsort' natle (cycle 100 testl).*)
Time Compute leftistHeapsort3 natle (cycle 100 testl).

Time Eval lazy in splaySort natle (cycle 100 testl).

Time Eval lazy in pairingSort natle (cycle 100 testl).

*)

(* Fast sorts on big lists. *)

(*
Time Compute ms natle (cycle 200 testl).
Time Compute ms2 natle (cycle 200 testl).
Time Compute ums_wut (Small_recdepth natle 0) (redblackSort natle)
                     (MsSplit natle) (cycle 200 testl).
Time Compute trollms 1 (redblackSort natle) (MsSplit natle)
               (cycle 200 testl).


Time Compute qs natle (cycle 200 testl).
Time Compute qs2 natle (cycle 200 testl).
Time Compute ums 0 1 (treeSort natle) (MsSplit natle) (cycle 500 testl).
*)

(*
Time Compute treeSort natle (cycle 1000 testl).
Time Compute treeSort' natle (cycle 1000 testl).
*)

(*
Time Compute redblackSort natle (cycle 1000 testl).

Time Compute hqs 64 (Sort_redblackSort natle) (cycle 1000 testl).

Time Eval lazy in leftistHeapsort' natle (cycle 300 testl).
*)

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

(*
Time Compute @ghms 64 natle (insertionSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natle (treeSort natle) (MsSplit natle) l1.
Time Compute @ghms 64 natle (redblackSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natle (pairingSort natle) (MsSplit natle) l1.

Time Compute @hqs 1024 natle (Sort_insertionSort natle) l1.
*)

(*Time Compute @hqs 512 natle (Sort_treeSort natle) l1.*)

(*
Time Compute @hqs 512 natle (Sort_redblackSort natle) l1.

Time Compute @hqs 512 natle (Sort_pairingSort natle) l1.
*)

(*
Time Compute @htqs 0 natlt (insertionSort natle) l1.

Time Compute @htqs 0 natlt (treeSort natle) l1.

Time Compute @htqs 0 natlt (redblackSort natle) l1.

Time Compute @uqs natlt (Small_head natlt) (AdHocSort_id natlt)
                 (Pivot_head natlt) (Partition_trifilter natlt) l1.
*)

Fixpoint toN (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: toN n'
end.

(*CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).*)

(*Time Compute qs natle (toN 500).
Time Compute tqs natlt (toN 200).*)

(*Time Compute insertionSort natle (toN 500).

Time Compute treeSort natle (toN 500).
Time Compute redblackSort natle (toN 500).

Time Compute pairingSort natle (toN 500).*)