Require Import Sort.

Theorem filter_length : forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); simpl; omega.
Qed.

Theorem filter_comm : forall (A : Type) (l : list A) (f g : A -> bool),
    filter f (filter g l) = filter g (filter f l).
Proof.
  induction l as [| h t]; intros.
    simpl. trivial.
    simpl. case_eq (f h); case_eq (g h); intros; simpl.
      rewrite H, H0, IHt. trivial.
      rewrite H, IHt. trivial.
      rewrite H0, IHt. trivial.
      rewrite IHt. trivial.
Qed.

Hint Resolve le_n_S filter_length.

(* Quicksort using Program Fixpoint *)
Program Fixpoint qs (A : LinDec) (l : list A) {measure (length l)} : list A :=
match l with
    | nil => nil
    | h :: t => qs A (filter (fun x : A => leqb x h) t) ++ [h]
             ++ qs A (filter (fun x : A => negb (leqb x h)) t)
end.
Next Obligation. simpl. unfold lt. auto. Qed.
Next Obligation. simpl. unfold lt. auto. Qed.

Eval compute in (qs natle testl).

(* Quicksort using fuel recursion. *)
Fixpoint qsortSub (A : LinDec) (fuel : nat) (l : list A) : list A :=
match fuel, l with
    | 0, _ => l
    | _, [] => []
    | _, [x] => [x]
    | S fuel', h :: t =>
        let lesser := qsortSub A fuel' (filter (fun x : A => leqb x h) t) in
        let greater := qsortSub A fuel' (filter (fun x : A => negb (leqb x h)) t) in
        lesser ++ [h] ++ greater
end.

Definition qs' (A : LinDec) (l : list A) : list A := qsortSub A (length l) l.

Eval compute in (qs' natle testl).

(* Quicksort using Bove-Capretta *)

Require Import Coq.Init.Wf.

Inductive qsDom (A : LinDec) : list A -> Type :=
    | qsDom0 : qsDom A nil
    | qsDom1 : forall (h : A) (t : list A),
        qsDom A (filter (fun x : A => leqb x h) t) ->
        qsDom A (filter (fun x : A => negb (leqb x h)) t) ->
        qsDom A (h :: t).

Fixpoint qs3' (A : LinDec) (l : list A) (dom : qsDom A l) : list A :=
match dom with
    | qsDom0 => nil
    | qsDom1 h t dom1 dom2 =>
        qs3' A (filter (fun x : A => leqb x h) t) dom1 ++ h ::
        qs3' A (filter (fun x : A => negb (leqb x h)) t) dom2
end.

Theorem all_qsDom : forall (A : LinDec) (l : list A), qsDom A l.
Proof.
  intro.
  apply well_founded_induction_type with (fun l1 l2 => length l1 < length l2).
    eapply well_founded_lt_compat. eauto.
    intros. destruct x as [| h t]; constructor.
      apply X. simpl. unfold lt. apply le_n_S. apply filter_length.
      apply X. simpl. unfold lt. apply le_n_S. apply filter_length.
Defined.

Definition qs3 (A : LinDec) (l : list A) : list A :=
    qs3' A l (all_qsDom A l).

Eval compute in qs3 natle testl.
