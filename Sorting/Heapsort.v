Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export BTree.
Require Export BST.
Require Export LeftistHeap.

Set Implicit Arguments.

(* Leftist heapsort *)
Function fromList {A : LinDec} (l : list A) : BTree A :=
match l with
    | [] => emptyHeap
    | h :: t => insert' h (fromList t)
end.

Function toList {A : LinDec} (t : BTree A)
  {measure len t} : list A :=
match deleteMin t with
    | (None, _) => []
    | (Some m, t') => m :: toList t'
end.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  rewrite merge'_len. omega.
Defined.

Arguments toList [x] _.

Definition leftistHeapsort (A : LinDec) (l : list A)
  : list A := toList (fromList l).

Time Compute leftistHeapsort natle (cycle 25 testl).