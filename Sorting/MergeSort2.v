Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

Require Export Sort.
Require Export ListLemmas.

Set Implicit Arguments.

Function merge2 (A : LinDec) (l : list A * list A)
    {measure lenSum l} : list A :=
let (l1, l2) := l in match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h :: t, h' :: t' =>
        if h <=? h'
        then h :: merge2 A (t, l2)
        else h' :: merge2 A (l1, t')
end.
Proof.
  intros. unfold lenSum. simpl. omega.
  intros. unfold lenSum. simpl. omega.
Defined.

Function msFun2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
        let n := Nat.div2 (length l') in
        let l1 := take n l' in
        let l2 := drop n l' in
          merge2 A (msFun2 A l1, msFun2 A l2)
end.
Proof.
  intros. apply drop_length_lt. simpl. omega. inversion 1.
  intros. apply take_length_lt. apply lt_div2. simpl. omega.
Defined.

Compute msFun2 natle testl.