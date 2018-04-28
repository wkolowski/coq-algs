Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.

Set Implicit Arguments.

Function ss (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => let m := min_dflt A h t in m :: ss A (removeFirst m l)
end.
Proof. intros. apply removeFirst_min_lengthOrder. Defined.

Lemma removeFirst_In' :
  forall (A : LinDec) (x h : A) (t : list A),
    In x t -> x <> h -> In x (removeFirst h t).
Proof.
  induction t as [| h' t']; cbn; intuition dec.
Qed.