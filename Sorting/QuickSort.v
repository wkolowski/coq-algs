Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sort.
Require Export ListLemmas.

Set Implicit Arguments.

Hint Resolve le_n_S filter_length.

(* Quicksort using Program Fixpoint *)
Program Fixpoint qsPF (A : LinDec) (l : list A) {measure (length l)}
    : list A :=
match l with
    | [] => []
    | h :: t => qsPF A (filter (fun x : A => leqb x h) t) ++ [h]
             ++ qsPF A (filter (fun x : A => negb (leqb x h)) t)
end.
Next Obligation. simpl. unfold lt. auto. Qed.
Next Obligation. simpl. unfold lt. auto. Qed.

Eval compute in qsPF natle testl.

(* Quicksort using Function. *)
Function qsFun (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => qsFun A (filter (fun x : A => leqb x h) t) ++
           h :: qsFun A (filter (fun x : A => negb (leqb x h)) t)
end.
Proof.
  intros. unfold lt. simpl. apply le_n_S. apply filter_length.
  intros. unfold lt. simpl. apply le_n_S. apply filter_length.
Defined.

Eval compute in qsFun natle testl.

(* Quicksort using fuel recursion. *)
Fixpoint qsFuel' (A : LinDec) (fuel : nat) (l : list A) : list A :=
match fuel, l with
    | 0, _ => l
    | _, [] => []
    | _, [x] => [x]
    | S fuel', h :: t =>
        qsFuel' A fuel' (filter (fun x : A => leqb x h) t) ++ h ::
        qsFuel' A fuel' (filter (fun x : A => negb (leqb x h)) t)
end.

Definition qsFuel (A : LinDec) (l : list A) : list A :=
    qsFuel' A (length l) l.

Eval compute in (qsFuel natle testl).

(* Quicksort using well-founded recursion. *)
Definition qsWf (A : LinDec) : list A -> list A.
Proof.
  apply (Fix (@lengthOrder_wf A) _).
  intros l qsWf.
  destruct l as [| h t].
    exact [].
    pose (le := qsWf (filter (fun x : A => leqb x h) t)
        (filter_lengthOrder (fun x => leqb x h) h t)).
    pose (gt := qsWf (filter (fun x : A => negb (leqb x h)) t)
        (filter_lengthOrder (fun x : A => negb (leqb x h)) h t)).
    exact (le ++ h :: gt).
Defined.

Eval compute in qsWf natle testl.

(* Quicksort using wel-founded recursion and refine. *)
Definition qsWfRef (A : LinDec) : list A -> list A.
refine (Fix (@lengthOrder_wf A) _ (fun (l : list A) =>
match l with
    | [] => fun _ => []
    | h :: t => fun qs =>
        qs (filter (fun x : A => leqb x h) t) _ ++ h ::
        qs (filter (fun x : A => negb (leqb x h)) t) _
end)).
Proof.
  apply filter_lengthOrder.
  apply filter_lengthOrder.
Defined.

Eval compute in qsWfRef natle testl.

(* Quicksort using Bove-Capretta *)
Inductive qsDom {A : LinDec} : list A -> Type :=
    | qsDom0 : qsDom nil
    | qsDom1 : forall (h : A) (t : list A),
        qsDom (filter (fun x : A => leqb x h) t) ->
        qsDom (filter (fun x : A => negb (leqb x h)) t) ->
        qsDom (h :: t).

Fixpoint qsBC' {A : LinDec} (l : list A) (dom : qsDom l) : list A :=
match dom with
    | qsDom0 => nil
    | qsDom1 h t dom1 dom2 =>
        qsBC' dom1 ++ h :: qsBC' dom2
end.

Theorem all_qsDom : forall (A : LinDec) (l : list A), qsDom l.
Proof.
  intro. apply well_founded_induction_type with lengthOrder.
    apply lengthOrder_wf.
    intros. destruct x as [| h t]; constructor; apply X.
      simpl. unfold lt. apply le_n_S. apply filter_length.
      simpl. unfold lt. apply le_n_S. apply filter_length.
Defined.

Definition qsBC (A : LinDec) (l : list A) : list A :=
    @qsBC' A l (all_qsDom A l).

Eval compute in qsBC natle testl.

(* Now the serious part. TODO *)
Definition qs := qsFun.

Function bifilter {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t =>
        let (l1, l2) := bifilter p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.

Theorem bifilter_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    bifilter p l = (filter p l, filter (fun x : A => negb (p x)) l).
Proof.
  intros. functional induction @bifilter A p l; simpl;
  try rewrite e1; simpl; try rewrite e0 in IHp0; try inversion IHp0; auto.
Qed.

Function qs2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t =>
        let (lo, hi) := bifilter (fun x : A => x <=? h) t in
        qs2 A lo ++ h :: qs2 A hi
end.
Proof.
  intros. rewrite bifilter_spec in teq0. inversion teq0.
    apply filter_lengthOrder.
  intros. rewrite bifilter_spec in teq0. inversion teq0.
    apply filter_lengthOrder.
Defined.

Theorem qs2_is_qs :
  forall (A : LinDec) (l : list A), qs2 A l = qs A l.
Proof.
  intros. functional induction (qs2 A l).
    compute. trivial.
    unfold qs. rewrite qsFun_equation. rewrite bifilter_spec in e0.
      inversion e0. rewrite H0, H1. repeat f_equal; auto.
Qed.