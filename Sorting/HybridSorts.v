Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import InsertionSort.
Require Import SelectionSort.
Require Import QuickSort.
Require Import MergeSort2.

Set Implicit Arguments.

Function hqs (A : LinDec) (n : nat) (l : list A) {measure length l} : list A :=
  if @leqb natle (length l) n
  then insertionSort A l
  else match l with
      | [] => []
      | h :: t =>
          let (lo, hi) := bifilter (fun x : A => x <=? h) t in
              hqs A n lo ++ h :: hqs A n hi
  end.
Proof.
  intros. rewrite bifilter_spec in teq1. inversion teq1.
    apply filter_lengthOrder.
  intros. rewrite bifilter_spec in teq1. inversion teq1.
    apply filter_lengthOrder.
Defined.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_pres_le :
  forall n m : nat, n <= m -> Nat.div2 n <= Nat.div2 m.
Proof.
  intro. functional induction div2 n; intros.
    omega.
    omega.
    destruct m as [| [| m']].
      omega.
      omega.
      simpl. apply le_n_S. apply IHn0. omega.
Defined.

Function hms (A : LinDec) (n : nat) (l : list A) {measure length l}
  : list A :=
  if @leqb natle (length l) (S (S n))
  then insertionSort A l
  else  let n := Nat.div2 (length l) in
        let l1 := take n l in
        let l2 := drop n l in
          merge2 A (hms A n l1, hms A n l2).
Proof.
  intros. destruct (@leqb_spec natle (length l) (S (S n))).
    inversion teq.
    apply LinDec_not_leq in n0. apply drop_length_lt.
      unfold leqb in n0. simpl in n0. red. apply div2_pres_le in n0.
        simpl in n0. omega.
      destruct l as [| ? [| ? ?]]; simpl in n0; try omega. discriminate.
  intros. destruct (@leqb_spec natle (length l) (S (S n))).
    inversion teq.
    apply LinDec_not_leq in n0. apply take_length_lt.
      unfold leqb in n0. simpl in n0. apply lt_div2. omega.
Defined.