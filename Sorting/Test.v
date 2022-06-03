(*
From CoqAlgs Require Import InsertionSort.
From CoqAlgs Require Import SelectionSort.
*)

From CoqAlgs Require Import MergeSort.
From CoqAlgs Require Import QuickSort.

From CoqAlgs Require Import TreeSort.
From CoqAlgs Require Import RedblackSort.

From CoqAlgs Require Import PairingSort.
From CoqAlgs Require Import SplaySort.

From CoqAlgs Require Import ListLemmas.

(* From CoqAlgs Require Import TrichQuicksort. *)

From CoqAlgs Require Import LeftistHeap.

Set Implicit Arguments.

(* Slow sorts on small lists. *)

(*Time Compute ss natlt (cycle 100 testl).
Time Compute ss' natlt (cycle 100 testl).
Time Compute ss'' natlt (cycle 100 testl).
Time Compute ss_bifilter natlt (cycle 500 testl).
Time Compute ss_mins' natlt (cycle 500 testl).

Time Compute ss natlt (cycle 10 testl).
Time Compute insertionSort natlt (cycle 10 testl).*)

(* Fast sorts on medium lists. *)

(*Time Compute ms natlt (cycle 100 testl).
Time Compute ms2 natlt (cycle 100 testl).

Time Compute qs natlt (cycle 100 testl).
Time Compute qs2 natlt (cycle 100 testl).

Time Compute tqs natlt (cycle 100 testl).

Time Compute treeSort natlt (cycle 100 testl).
Time Compute treeSort' natlt (cycle 100 testl).

Time Compute redblackSort natlt (cycle 100 testl).
(*Time Compute redblackSort' natlt (cycle 100 testl).*)

Time Eval lazy in leftistHeapsort natlt (cycle 100 testl).
(*Time Eval lazy in leftistHeapsort' natlt (cycle 100 testl).*)
Time Compute leftistHeapsort3 natlt (cycle 100 testl).

Time Eval lazy in splaySort natlt (cycle 100 testl).

Time Eval lazy in pairingSort natlt (cycle 100 testl).

*)

(* Fast sorts on big lists. *)

(*
Time Compute ms natlt (cycle 200 testl).
Time Compute ms2 natlt (cycle 200 testl).
Time Compute ums_wut (Small_recdepth natlt 0) (redblackSort natle)
                     (MsSplit natlt) (cycle 200 testl).
Time Compute trollms 1 (redblackSort natlt) (MsSplit natle)
               (cycle 200 testl).


Time Compute qs natlt (cycle 200 testl).
Time Compute qs2 natlt (cycle 200 testl).
Time Compute ums 0 1 (treeSort natlt) (MsSplit natle) (cycle 500 testl).
*)

(*
Time Compute treeSort natlt (cycle 1000 testl).
Time Compute treeSort' natlt (cycle 1000 testl).
*)

(*
Time Compute redblackSort natlt (cycle 1000 testl).

Time Compute hqs 64 (Sort_redblackSort natlt) (cycle 1000 testl).

Time Eval lazy in leftistHeapsort' natlt (cycle 300 testl).
*)

(* Hybrid mergesort on big lists. *)
(*Time Compute @ghms 512 natlt (insertionSort natle) (MsSplit natle)
  (cycle 200 testl).

Time Compute @ghms 1024 natlt (treeSort natle) (MsSplit natle)
  (cycle 200 testl).

Time Compute @ghms 1024 natlt (redblackSort natle) (MsSplit natle)
  (cycle 200 testl). *)

(* Bad
Time Compute @ghms 1024 natlt (leftistHeapsort' natle) (MsSplit natle)
  (cycle 200 testl).
*)

(*Time Compute @hqs 1024 natlt (insertionSort natle) (cycle 200 testl).

Time Compute @hqs 512 natlt (treeSort natle) (cycle 200 testl).

Time Compute @hqs 512 natlt (redblackSort natle) (cycle 200 testl).
*)

(* Bad
  Time Compute @hqs 256 natlt (leftistHeapsort natle) (cycle 200 testl).
*)

(*Time Compute @htqs 1 natlt (insertionSort natlt) (cycle 200 testl).

Time Compute @htqs 1 natlt (treeSort natlt) (cycle 200 testl).

Time Compute @htqs 1 natlt (redblackSort natlt) (cycle 200 testl).*)

(* Long lists made of one element. *)
Definition l1 := cycle 2500 [0].

(*
Time Compute @ghms 64 natlt (insertionSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natlt (treeSort natle) (MsSplit natle) l1.
Time Compute @ghms 64 natlt (redblackSort natle) (MsSplit natle) l1.

Time Compute @ghms 64 natlt (pairingSort natle) (MsSplit natle) l1.

Time Compute @hqs 1024 natlt (Sort_insertionSort natle) l1.
*)

(*Time Compute @hqs 512 natlt (Sort_treeSort natle) l1.*)

(*
Time Compute @hqs 512 natlt (Sort_redblackSort natle) l1.

Time Compute @hqs 512 natlt (Sort_pairingSort natle) l1.
*)

(*
Time Compute @htqs 0 natlt (insertionSort natlt) l1.

Time Compute @htqs 0 natlt (treeSort natlt) l1.

Time Compute @htqs 0 natlt (redblackSort natlt) l1.

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

(*Time Compute qs natlt (toN 500).
Time Compute tqs natlt (toN 200).*)

(*Time Compute insertionSort natlt (toN 500).

Time Compute treeSort natlt (toN 500).
Time Compute redblackSort natlt (toN 500).

Time Compute pairingSort natlt (toN 500).*)