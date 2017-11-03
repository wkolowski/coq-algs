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

Function fromList' {A : LinDec} (l : list A) : BTree A :=
  fold_left (fun t x => insert' x t) l empty.

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

Function toList'_aux {A : LinDec} (t : BTree A) (acc : list A)
  {measure len t} : list A :=
match deleteMin t with
    | (None, _) => acc
    | (Some m, t') => toList'_aux t' (m :: acc)
end.
Proof.
  destruct t; cbn; inversion 2; inversion 1; subst.
  rewrite merge'_len. omega.
Defined.

Definition toList' {A : LinDec} (t : BTree A) : list A :=
  toList'_aux A t [].

Definition leftistHeapsort (A : LinDec) (l : list A)
  : list A := toList (fromList l).

Definition leftistHeapsort' (A : LinDec) (l : list A)
  : list A := toList' (fromList' l).

Time Compute leftistHeapsort natle (cycle 50 testl).
Time Compute leftistHeapsort' natle (cycle 50 testl).
