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

(*Theorem ssDom_all : forall (A : LinDecMin) (l : list A), ssDom l.
Proof.
  induction l as [| h t].
    constructor.
    apply ssDomRec. simpl. destruct t.
      dec. constructor.
      
Qed.

Fixpoint selectionSort2 {A : LinDecMin} (l : list A) : list A :=
match l with
    | [] => []
    | _ => let m := min l in selectionSort2'*)

(* Selection sort using well-founded recursion *)

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
    length l1 < length l2.

Lemma lengthOrder_wf' : forall (A : Type) (n : nat) (l : list A),
    length l <= n -> Acc lengthOrder l.
Proof.
  induction n as [| n'].
    inversion 1. destruct l; inversion H1. constructor. inversion 1.
    intros. destruct l.
      constructor. inversion 1.
      simpl in H. constructor. intros. apply IHn'.
        unfold lengthOrder in H0. simpl in H0. unfold lt in H0.
        apply le_S_n in H. apply le_S_n in H0. eapply Le.le_trans; eauto.
Defined.

Theorem lengthOrder_wf : forall (A : Type),
    well_founded (@lengthOrder A).
Proof.
  red. intros A l. apply lengthOrder_wf' with (length l). trivial.
Defined.

Lemma remove_once_min_lengthOrder : forall (A : LinDecMin) (l : list A),
    l <> [] -> lengthOrder (remove_once (min' A l) l) l.
Proof.
  red; intros. apply remove_once_length2. apply min'_In. assumption.
Defined.

Lemma cons_not_nil : forall (A : Type) (h : A) (t : list A),
    h :: t <> [].
Proof. inversion 1. Defined.

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

Eval compute in selectionSort3 [1; 2].

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


