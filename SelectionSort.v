Require Import Sort.

Fixpoint remove_once {A : LinDec} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if x =? h then t else h :: remove_once x t
end.

(* Useful lemmas for selection sort. *)
Lemma remove_length : forall (A : Type) (l : list A) (x : A)
    (eq_dec : forall x y : A, {x = y} + {x <> y}),
    length (remove eq_dec x l) <= length l.
Proof.
  induction l as [| h t]; simpl; intros; auto.
  destruct (eq_dec x h).
    apply le_S. apply IHt.
    simpl. apply le_n_S. apply IHt.
Defined.

Lemma remove_length2 : forall (A : Type) (l : list A) (x : A)
    (eq_dec : forall x y : A, {x = y} + {x <> y}),
    In x l -> length (remove eq_dec x l) < length l.
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    destruct H; subst.
      destruct (eq_dec x x). unfold lt. apply le_n_S. apply remove_length.
      contradiction n. auto.
    destruct (eq_dec x h); subst.
      unfold lt. apply le_n_S. apply remove_length.
      simpl. apply lt_n_S. apply IHt. assumption.
Defined.

Ltac dec :=
match goal with
    | |- context [?x =? ?y] =>
        case_eq (x =? y); intros; subst
end;
try match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
end.

Lemma remove_once_length : forall (A : LinDec) (x : A) (l : list A),
    length (remove_once x l) <= length l.
Proof.
  induction l as [| h t]; simpl; intros; auto. dec.
    apply le_S. apply le_n.
    simpl. apply le_n_S. apply IHt.
Defined.

Lemma remove_once_length2 : forall (A : LinDec) (x : A) (l : list A),
    In x l -> length (remove_once x l) < length l.
Proof.
  induction l as [| h t]; simpl; intros.
    inversion H.
    destruct H; subst; dec; try omega.
      simpl. apply lt_n_S. apply IHt. assumption.
Defined.

Lemma remove_once_min_lengthOrder : forall (A : LinDecMin) (l : list A),
    l <> [] -> lengthOrder (remove_once (min' A l) l) l.
Proof.
  red; intros. apply remove_once_length2. apply min'_In. assumption.
Defined.

Lemma cons_not_nil : forall (A : Type) (h : A) (t : list A),
    h :: t <> [].
Proof. inversion 1. Defined.

(* Selection sort using program fixpoint *)
Program Fixpoint selectionSort (A : LinDecMin) (l : list A)
    {measure (length l)} : list A :=
match l with
    | [] => []
    | _ => let m := min' A l in
        m :: selectionSort A (remove_once m l)
end.
Next Obligation. apply remove_once_length2. apply min'_In. auto. Qed.

Eval compute in selectionSort natle_min testl.

(* Selection sort using fuel recursion. *)
Fixpoint selectionSortFuel {A : LinDecMin} (n : nat) (l : list A)
    : option (list A) :=
match n with
    | 0 => None
    | S n' =>
        match l with
            | [] => Some []
            | _ => let m := min' A l in
                match selectionSortFuel n' (remove_once m l) with
                    | None => None
                    | Some l' => Some (m :: l')
                end
            end
end.

Eval compute in selectionSortFuel 3 [2; 1].

Lemma wut : forall (A : LinDecMin) (n : nat) (h : A) (t : list A),
    selectionSortFuel (S n) (h :: t) =
        (*let m := min' A (h :: t) in*)
        match selectionSortFuel n (remove_once (min' A (h :: t)) (h :: t)) with
            | None => None
            | Some l => Some (min' A (h :: t) :: l)
        end.
Proof.
  intros. reflexivity.
Qed.

Lemma remove_once_length3 : forall (A : LinDecMin) (x : A) (l : list A),
    In x l -> S (length (remove_once x l)) = length l.
Proof.
  induction l as [| h t]; simpl.
    inversion 1.
    destruct 1; destruct (x =? h); simpl; auto.
      subst. intuition.
Defined.

Theorem selectionSortFuel_extract : forall (A : LinDecMin) (l : list A),
    {l' : list A | selectionSortFuel (S (length l)) l = Some l'}.
Proof.
  intro. apply (Fix (@lengthOrder_wf A)). intros l H.
  destruct l as [| h t]; intros.
    simpl. exists []. trivial.
    pose (m := min' A (h :: t)). pose (r := remove_once m (h :: t)).
      destruct (H r).
        unfold r. apply remove_once_min_lengthOrder. inversion 1.
 	exists (min' A (h :: t) :: x). rewrite wut. fold m. fold r.
          replace (length (h :: t)) with (S (length r)).
            rewrite e. reflexivity.
            unfold r. rewrite remove_once_length3.
              trivial.
              unfold m. apply min'_In. inversion 1.
Defined.

Theorem ssfuel_none : forall (A : LinDecMin) (l : list A),
    selectionSortFuel (S (length l)) l <> None.
Proof.
  unfold not; intros.
  pose (H' := selectionSortFuel_extract A l).
  destruct H'. rewrite e in H. inversion H.
Defined.

Definition selectionSort4 {A : LinDecMin} (l : list A) : list A :=
    proj1_sig (selectionSortFuel_extract A l).

(* TODO : Eval compute in selectionSort4 [1]. *)

Definition selectionSort4' {A : LinDecMin} (l : list A) : list A.
Proof.
  case_eq (selectionSortFuel (S (length l)) l); intros.
    exact l0.
    apply ssfuel_none in H. destruct H.
Defined.

Eval compute in selectionSort4' [3; 1; 2; 3].

Fixpoint ssfuel2 {A : LinDecMin} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', _ => let m := min' A l in
        m :: ssfuel2 n' (remove_once m l)
end.

Eval compute in ssfuel2 100 testl.

(* Selection sort using well-founded recursion *)

Definition selectionSort3 {A : LinDecMin} : list A -> list A.
Proof.
  apply (Fix (@lengthOrder_wf A)). intros l selectionSort.
  destruct l as [| h t].
    exact [].
    pose (m := min' A (h :: t)). pose (r := remove_once m (h :: t)).
      pose (p := remove_once_min_lengthOrder A (h :: t) (cons_not_nil _ h t)).
      exact (m :: selectionSort r p).
      (*exact r.*)
Defined.

Print Assumptions selectionSort3.

Transparent selectionSort3.

(* TODO : Eval compute in selectionSort3 [2; 1].

Definition selectionSort3' {A : LinDecMin}
    : list A -> list A.
refine (Fix (@lengthOrder_wf A) _
(fun (l : list A) (ss : forall l' : list A, lengthOrder l' l -> list A) =>
    match l with
        | [] => []
        | h :: t => let m := min' A (h :: t) in m :: ss (remove_once m (h :: t)) _
    end)).
Proof.
  red. apply remove_once_length2. apply min'_In.
*)




(* Selection sort using Bove-Capretta *)

Inductive ssDom {A : LinDecMin} : list A -> Type :=
    | ssDomNil : ssDom []
    | ssDomRec : forall (l : list A),
        ssDom (remove_once (min' A l) l) -> ssDom l.

Fixpoint selectionSort2' {A : LinDecMin} {l : list A} (p : ssDom l)
    : list A :=
match p with
    | ssDomNil => []
    | ssDomRec l p => min' A l :: selectionSort2' p
end.

Theorem ssDom_all : forall (A : LinDecMin) (l : list A), ssDom l.
Proof.
  intro.
  apply well_founded_induction_type with (fun l1 l2 => length l1 < length l2).
    eapply well_founded_lt_compat. eauto.
    intros l ss. destruct l as [| h t]; constructor.
      apply ss. apply remove_once_length2. apply min'_In. inversion 1.
Defined. (*
  induction l as [| h t].
    constructor.
    apply ssDomRec. simpl. destruct t.
      dec. constructor.
Abort.*)

Fixpoint selectionSort2 {A : LinDecMin} (l : list A) : list A :=
    selectionSort2' (ssDom_all A l).

Eval compute in selectionSort2 testl.