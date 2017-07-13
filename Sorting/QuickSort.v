Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sort.
Require Export ListLemmas.

Require Import InsertionSort.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

(* Quicksort using Function. *)
Function qs (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => qs A (filter (fun x : A => leqb x h) t) ++
           h :: qs A (filter (fun x : A => negb (leqb x h)) t)
end.
Proof. all: simpl; auto. Defined.

Eval compute in qs natle testl.

Local Hint Extern 0 (length _ < length _) =>
match goal with
    | H : bifilter _ _ = _ |- _ => rewrite bifilter_spec in H; inversion H;
        apply filter_lengthOrder
end.

Function qs2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t =>
        let (lo, hi) := bifilter (fun x : A => x <=? h) t in
        qs2 A lo ++ h :: qs2 A hi
end.
Proof. all: auto. Defined.

Function qs3 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t =>
        let '(lo, eq, hi) := trifilter A h t in
          qs3 A lo ++ eq ++ qs3 A hi
end.
Proof.
Abort.

Function hqs (n : nat) (A : LinDec) (l : list A) {measure length l}
  : list A :=
  if @leqb natle (length l) n
  then insertionSort A l
  else match l with
      | [] => []
      | h :: t =>
          let (lo, hi) := bifilter (fun x : A => x <=? h) t in
              hqs n A lo ++ h :: hqs n A hi
  end.
Proof. all: auto. Defined.