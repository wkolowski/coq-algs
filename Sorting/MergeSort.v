Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import InsertionSort.

Set Implicit Arguments.

Function merge (A : LinDec) (l : list A * list A)
    {measure lenSum l} : list A :=
let (l1, l2) := l in match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h :: t, h' :: t' =>
        if h <=? h'
        then h :: merge A (t, l2)
        else h' :: merge A (l1, t')
end.
Proof.
  intros. unfold lenSum. simpl. omega.
  intros. unfold lenSum. simpl. omega.
Defined.

Hint Extern 1 (length (drop _ _) < length _) =>
  apply drop_length_lt; simpl; [omega | inversion 1].

Hint Extern 1 (length (take _ _) < length _) =>
  apply take_length_lt; apply lt_div2; simpl; omega.

Function ms (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
      let n := div2 (length l') in
      let l1 := take n l' in
      let l2 := drop n l' in
      merge A (ms A l1, ms A l2)
end.
Proof. all: auto. Defined.

Hint Extern 1 (length _ < length _) =>
match goal with
    | H : context [ms_split] |- _ =>
        try (eapply ms_split_len1; eauto; fail);
        eapply ms_split_len2; eauto
end.

Function ms2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
        let (l1, l2) := ms_split l' in
          merge A (ms2 A l1, ms2 A l2)
end.
Proof. all: auto. Defined.

Hint Extern 1 (length _ < length _) =>
match goal with
    | H : (length ?l <=? S (S _)) = false |- _ =>
        destruct l as [| ? | ? ? ?] using list_ind2;
        simpl in H; inversion_clear H
end.

Function hms (n : nat) (A : LinDec) (l : list A) {measure length l}
  : list A :=
  if @leqb natle (length l) (S (S n))
  then insertionSort A l
  else  let n := Nat.div2 (length l) in
        let l1 := take n l in
        let l2 := drop n l in
          merge A (hms n A l1, hms n A l2).
Proof.
  all: auto.
Defined.

Function hms2 (n : nat) (A : LinDec) (l : list A) {measure length l}
  : list A :=
  if @leqb natle (length l) (S (S n))
  then insertionSort A l
  else let (l1, l2) := ms_split l in merge A (hms2 n A l1, hms2 n A l2).
Proof.
  all: auto.
Defined.