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

Function hms (n : nat) (A : LinDec) (sort : list A -> list A) (l : list A)
  {measure length l} : list A :=
  if @leqb natle (length l) (S (S n))
  then sort l
  else  let n := Nat.div2 (length l) in
        let l1 := take n l in
        let l2 := drop n l in
          merge A (hms n A sort l1, hms n A sort l2).
Proof.
  all: auto.
Defined. 

(* Parametrized mergesort *)
Function hms2 (n : nat) (A : LinDec) (sort : list A -> list A) (l : list A)
  {measure length l} : list A :=
  if @leqb natle (length l) (S (S n))
  then sort l
  else let (l1, l2) := ms_split l in
    merge A (hms2 n A sort l1, hms2 n A sort l2).
Proof.
  all: auto.
Defined.

Class Split (A : Type) : Type :=
{
    split' : list A -> list A * list A;
    spec1 : forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> length l1 < length l;
    spec2 : forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> length l2 < length l;
}.

Coercion split' : Split >-> Funclass.

Function ghms (n : nat) (A : LinDec)
  (sort : list A -> list A) (split : Split A)
  (l : list A) {measure length l} : list A :=
    if @leqb natle (length l) (S (S n))
    then sort l
    else let (l1, l2) := split l in
      merge A (ghms n A sort split l1, ghms n A sort split l2).
Proof.
  intros. apply spec2 with l1.
    assumption.
    destruct (@leqb_spec natle (length l) (S (S n))); cbn in *.
      congruence.
      omega.
  intros. apply spec1 with l2.
    assumption.
    destruct (@leqb_spec natle (length l) (S (S n))); cbn in *.
      congruence.
      omega.
Defined.

Instance MsSplit (A : LinDec) : Split A :=
{
    split' := ms_split
}.
Proof.
  intros. destruct l as [| x [| y t]]; cbn in *.
    omega.
    omega.
    eapply ms_split_len1. eauto.
  intros. destruct l as [| x [| y t]]; cbn in *.
    omega.
    omega.
    eapply ms_split_len2. eauto.
Defined.

Definition wut (A : LinDec) (l : list A) : list A :=
  ghms 0 A (fun l => l) (MsSplit A) l.

Compute wut natle testl.