Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

Require Export Sort.
Require Export ListLemmas.

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

Function split {A : Type} (l : list A) : list A * list A :=
match l with
    | [] => ([], [])
    | [x] => ([x], [])
    | x :: y :: l' =>
        let (l1, l2) := split l' in (x :: l1, y :: l2)
end.

Lemma split_len1 :
  forall (A : Type) (x y : A) (l l1 l2 : list A),
    split (x :: y :: l) = (l1, l2) -> length l1 < length (x :: y :: l).
Proof.
  intros A x y l. functional induction @split A l.
    inversion 1; simpl; omega.
    inversion 1; simpl; omega.
    simpl in *. destruct (split l'). inversion 1; inversion e0; subst.
      specialize (IHp x0 y (x0 :: l1) (y :: l2) eq_refl). simpl in *.
        omega.
Qed.

Lemma split_len2 :
  forall (A : Type) (x y : A) (l l1 l2 : list A),
    split (x :: y :: l) = (l1, l2) -> length l2 < length (x :: y :: l).
Proof.
  intros A x y l. functional induction @split A l.
    inversion 1; simpl; omega.
    inversion 1; simpl; omega.
    simpl in *. destruct (split l'). inversion 1; inversion e0; subst.
      specialize (IHp x0 y (x0 :: l1) (y :: l2) eq_refl). simpl in *.
        omega.
Qed.

Function ms3 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
        let (l1, l2) := split l' in
          merge A (ms3 A l1, ms3 A l2)
end.
Proof.
  intros. eapply split_len2. eauto.
  intros. eapply split_len1. eauto.
Defined.

Compute ms3 natle testl.