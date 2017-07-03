Add Rec LoadPath "/home/zeimer/Code/Coq".

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
    destruct H; subst; dec; unfold lt; auto.
      apply le_n_S. apply IHt. assumption.
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
Program Fixpoint ssPF (A : LinDecMin) (l : list A)
    {measure (length l)} : list A :=
match l with
    | [] => []
    | _ => let m := min' A l in
        m :: ssPF A (remove_once m l)
end.
Next Obligation. apply remove_once_length2. apply min'_In. auto. Qed.

Eval compute in ssPF natle_min testl.

(* Selection sort using Function. *)

Require Import Recdef.

Function ssFun (A : LinDecMin) (l : list A)
    {wf (@lengthOrder A) l} : list A :=
match l with
    | [] => []
    | _ => let m := min' A l in m :: ssFun A (remove_once m l)
end.
Proof.
  intros. apply remove_once_length2. apply min'_In. inversion 1.
  intro. apply lengthOrder_wf.
Defined.

Check ssFun_equation.

Print Assumptions remove_once_min_lengthOrder.
Print Assumptions lengthOrder_wf.
Print Assumptions ssFun.

Goal ssFun natle_min [1] = [1].
Proof.
  rewrite ssFun_equation. simpl. reflexivity.
Defined.

Eval compute in ssFun natle_min testl.

(* Selection sort using fuel recursion. *)
Fixpoint ssFuelOpt {A : LinDecMin} (n : nat) (l : list A)
    : option (list A) :=
match n with
    | 0 => None
    | S n' =>
        match l with
            | [] => Some []
            | _ => let m := min' A l in
                match ssFuelOpt n' (remove_once m l) with
                    | None => None
                    | Some l' => Some (m :: l')
                end
            end
end.

Eval compute in ssFuelOpt 3 [2; 1].

Lemma wut : forall (A : LinDecMin) (n : nat) (h : A) (t : list A),
  ssFuelOpt (S n) (h :: t) =
    match ssFuelOpt n (remove_once (min' A (h :: t)) (h :: t)) with
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

Theorem ssFuelOpt_extract : forall (A : LinDecMin) (l : list A),
    {l' : list A | ssFuelOpt (S (length l)) l = Some l'}.
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

Theorem ssFuelOpt_None : forall (A : LinDecMin) (l : list A),
    ssFuelOpt (S (length l)) l <> None.
Proof.
  unfold not; intros.
  pose (H' := ssFuelOpt_extract A l).
  destruct H'. rewrite e in H. inversion H.
Defined.

Definition ssFuelOpt' {A : LinDecMin} (l : list A) : list A :=
    proj1_sig (ssFuelOpt_extract A l).

Eval compute in ssFuelOpt' testl.

Definition ssFuelOpt'' {A : LinDecMin} (l : list A) : list A.
Proof.
  case_eq (ssFuelOpt (S (length l)) l); intros.
    exact l0.
    apply ssFuelOpt_None in H. destruct H.
Defined.

Eval compute in ssFuelOpt'' testl.

(* Selection sort using fuel recursion without options. *)
Fixpoint ssFuel {A : LinDecMin} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', _ => let m := min' A l in
        m :: ssFuel n' (remove_once m l)
end.

Eval compute in ssFuel 100 testl.

(* Selection sort using well-founded recursion *)

Definition ssWf {A : LinDecMin} : list A -> list A.
Proof.
  apply (Fix (@lengthOrder_wf A)). intros l selectionSort.
  destruct l as [| h t].
    exact [].
    pose (m := min' A (h :: t)). pose (r := remove_once m (h :: t)).
      pose (p := remove_once_min_lengthOrder A (h :: t) (cons_not_nil _ h t)).
      exact (m :: selectionSort r p).
Defined.

Print Assumptions ssWf.

Eval compute in ssWf testl.

(* Selection sort using well-founded recursion and refine. *)
Definition ssWfRef {A : LinDecMin} : list A -> list A.
refine (Fix (@lengthOrder_wf A) _
  (fun (l : list A) =>
    match l with
        | [] => fun _ => []
        | h :: t =>
            fun ss : forall l' : list A, lengthOrder l' (h :: t) -> list A =>
              let m := min' A (h :: t) in m :: ss (remove_once m (h :: t)) _
    end)).
Proof.
  apply remove_once_min_lengthOrder. inversion 1.
Defined.

Eval compute in ssWfRef testl.

(* Selection sort using Bove-Capretta *)

Inductive ssDom {A : LinDecMin} : list A -> Type :=
    | ssDomNil : ssDom []
    | ssDomRec : forall (l : list A),
        ssDom (remove_once (min' A l) l) -> ssDom l.

Fixpoint ssBC' {A : LinDecMin} {l : list A} (p : ssDom l)
    : list A :=
match p with
    | ssDomNil => []
    | ssDomRec l p => min' A l :: ssBC' p
end.

Theorem ssDom_all : forall (A : LinDecMin) (l : list A), ssDom l.
Proof.
  intro.
  apply well_founded_induction_type with (fun l1 l2 => length l1 < length l2).
    eapply well_founded_lt_compat. eauto.
    intros l ss. destruct l as [| h t]; constructor.
      apply ss. apply remove_once_length2. apply min'_In. inversion 1.
Restart.
  intro. apply well_founded_induction_type with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intro IH; constructor.
      apply IH. apply remove_once_min_lengthOrder. inversion 1.
Defined.

Definition ssBC {A : LinDecMin} (l : list A) : list A :=
    ssBC' (ssDom_all A l).

Eval compute in ssBC testl.

Theorem ssFun_sorted : forall (A : LinDecMin) (l : list A),
  sorted A (ssFun A l).
Proof.
  intros. functional induction (ssFun A) l.
    constructor.
    inversion IHl0.
      constructor.
      constructor.
    destruct l.
      inversion y.
      inversion IHl0.
Restart.
  intros. rewrite ssFun_equation.
  induction l as [| h t].
    constructor.
    rewrite ssFun_equation.
    destruct t.
      simpl. destruct (h =? h).
        constructor.
        contradiction n. trivial.
      rewrite ssFun_equation.
Abort.