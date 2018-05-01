Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Definition treeSort (A : LinDec) (l : list A) : list A :=
  BTree_toList (fromList A l).

Definition treeSort' (A : LinDec) (l : list A) : list A :=
  BTree_toList' (fromList' l).