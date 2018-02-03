Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Set Implicit Arguments.

Function ss (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => let m := min_dflt A h t in m :: ss A (remove_once m l)
end.
Proof. intros. apply remove_once_min_lengthOrder. Defined.

Function minmax (A : LinDec) (min : A) (max : A) (l : list A) : A * A :=
match l with
    | [] => (min, max)
    | h :: t =>
        if h <=? min
        then minmax A h max t
        else
          if max <=? h
          then minmax A min h t
          else minmax A min max t
end.

Lemma remove_once_In' :
  forall (A : LinDec) (x h : A) (t : list A),
    In x t -> x <> h -> In x (remove_once h t).
Proof.
  induction t as [| h' t']; cbn; intuition dec.
Qed.