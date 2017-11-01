Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort.
Require Import Heap.

Require Import BST.

Set Implicit Arguments.

Fixpoint cycle {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ cycle n' l
end.

Require Import Coq.Sorting.Heap.

Lemma my_le_trans :
  forall a b c : nat, a <= b -> b <= c -> a <= c.
Proof.
  induction a as [| a']; simpl; intros.
    omega.
    omega.
Defined.

(* Definition hps (l : list nat) : list nat :=
  proj1_sig (sig_of_sig2
    (treesort nat le eq le_ge_dec Nat.eq_dec le_trans l)).

Compute hps [].


Definition heapsort (A : LinDec) (l : list A) : list A :=
  proj1_sig (sig_of_sig2
    (treesort A leq eq (LinDec_leq_dec A) (@LinDec_eq_dec A) leq_trans l)). *)


(*Time Compute hms2 128 natle (cycle 100 testl).
Time Compute ms natle (cycle 100 testl).
Time Compute ms2 natle (cycle 100 testl).
Time Compute hms 128 natle (cycle 100 testl). *)

Time Compute qs natle (cycle 50 testl).
Time Compute insertionSort natle (cycle 50 testl).
Time Compute ss natle (cycle 50 testl).
Time Compute qs2 natle (cycle 50 testl).

Time Compute leftistHeapsort natle (cycle 50 testl).

Time Compute hqs 1024 natle (cycle 100 testl).
Time Compute hms 1024 natle (cycle 100 testl).
Time Compute treeSort natle (cycle 100 testl).
Time Compute leftistHeapsort natle (cycle 20 testl).

Time Compute hqs 1024 natle (cycle 2000 [1]).
Time Compute hms 1024 natle (cycle 2000 [1]).
Time Compute treeSort natle (cycle 2000 [1]).

(* Slow. Change the implemenation to store the right spine. *)
Time Compute @leftistHeapsort natle (cycle 300 [1]).