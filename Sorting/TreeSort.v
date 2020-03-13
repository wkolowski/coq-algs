Require Export LinDec.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Definition treeSort
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : list A :=
    BTree_toList (fromList cmp l).