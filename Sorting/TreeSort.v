Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Definition treeSort (A : LinDec) (l : list A) : list A :=
  toList (fromList A l).

Definition treeSort' (A : LinDec) (l : list A) : list A :=
  toList' (fromList' l).

Time Compute treeSort natle (cycle 100 testl).
Time Compute treeSort' natle (cycle 100 testl).
  