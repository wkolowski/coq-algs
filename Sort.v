Require Export List.
Export ListNotations.

Require Export Bool.Bool.
Require Export Coq.Program.Wf.
Require Export Arith.
Require Export Arith.Div2.
Require Export Omega.
Require Import Numbers.Natural.Peano.NPeano.

Require Export Recdef.

Class Lin : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    leq_refl : forall x : carrier, leq x x;
    leq_antisym : forall x y : carrier, leq x y -> leq y x -> x = y;
    leq_trans : forall x y z : carrier, leq x y -> leq y z -> leq x z;
    leq_total : forall x y : carrier, leq x y \/ leq y x
}.

Coercion carrier : Lin >-> Sortclass.

Class LinDec : Type :=
{
    lin : Lin;
    leq_dec : forall x y : carrier, {leq x y} + {~ leq x y};
    leq_total_dec : forall x y : lin, {leq x y} + {leq y x}
}.

Coercion lin : LinDec >-> Lin.

Theorem LinDec_leqP : forall (A : LinDec) (x y : A),
    reflect (leq x y) (match leq_dec x y with | left _ => true | _ => false end).
Proof.
  intros. destruct (leq_dec x y); constructor; auto.
Defined.

Hint Resolve leq_refl leq_antisym leq_trans leq_total leq_dec LinDec_leqP.

Instance DualLin (A : Lin) : Lin.
refine
{|
    carrier := carrier;
    leq := fun x y : carrier => leq y x
|}.
Proof.
  intros. apply leq_refl.
  intros. apply leq_antisym; auto.
  intros. eapply leq_trans; eauto.
  intros. apply leq_total.
Defined.

Instance DualLinDec (A : LinDec) : LinDec.
refine
{|
    lin := DualLin A
|}.
Proof.
  intros. apply leq_dec.
  intros. apply leq_total_dec.
Defined.

Definition leqb {A : LinDec} (x y : A) : bool :=
match leq_dec x y with
    | left _ => true
    | right _ => false
end.

Hint Unfold leqb.

(*Notation "x <= y" := (le x y).*)
(*Notation "x <=? y" := (leb x y).*)

Definition LinDec_eq {A : LinDec} (x y : A) : bool :=
    andb (leqb x y) (leqb y x).

Lemma LinDec_not_leq : forall (A : LinDec) (x y : A),
    ~ leq x y -> leq y x.
Proof.
  intros. destruct (leq_dec y x). auto.
  destruct (leq_total_dec x y); contradiction.
Defined.

Definition LinDec_eq_dec : forall {A : LinDec} (x y : A),
    {x = y} + {x <> y}.
Proof.
  intros. destruct (leq_dec x y) as [H1 | H1], (leq_dec y x) as [H2 | H2].
    left; apply leq_antisym; auto.
    right. intro. apply H2. subst. auto.
    right. intro. apply H1. subst. auto.
    destruct (leq_total_dec x y); contradiction.
Defined.

Infix "=?" := LinDec_eq_dec.

Theorem LinDec_trichotomy : forall (A : LinDec) (x y : A),
    {leq x y /\ ~ x = y} + {x = y} + {leq y x /\ ~ x = y}.
Proof.
  intros. destruct (LinDec_eq_dec x y).
    left. right. assumption.
    destruct (leq_total_dec x y).
      do 2 left. split; assumption.
      right. split; auto.
Defined. 

Hint Unfold LinDec_eq LinDec_eq_dec.

Inductive sorted (A : LinDec) : list A -> Prop :=
    | sorted0 : sorted A nil
    | sorted1 : forall x : A, sorted A [x]
    | sorted2 : forall (x y : A) (l : list A),
        leq x y -> sorted A (y :: l) -> sorted A (x :: y :: l).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Theorem sorted_inv : forall (A : LinDec) (h : A) (t : list A),
    sorted A (h :: t) -> sorted A t.
Proof.
  intros. inversion H; auto with sort.
Defined.

Instance natle_lin : Lin.
refine
{|
    carrier := nat;
    leq := le
|}.
Proof.
  intros. apply le_n.
  intros. apply le_antisym; auto.
  intros. eapply le_trans; eauto.
  intros. destruct (le_gt_dec x y) as [H | H].
    left. auto. 
    right. unfold lt in H. apply le_Sn_le. auto.
Defined.

Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].

Instance natle : LinDec :=
{|
    lin := natle_lin;
    leq_dec := le_dec
|}.
Proof. intros; simpl. destruct (le_dec x y); auto; right; omega. Defined.

Lemma sort_2357 : sorted natle [2; 3; 5; 7; 9].
Proof. repeat constructor. Defined.

Ltac solve_nat_evenle := intros;
match goal with
    | H : _ /\ _ |- _ => destruct H; solve_nat_evenle
    | H : context [even ?x] |- _ => destruct (even x); solve_nat_evenle
    | |- context [even ?x] => destruct (even x); solve_nat_evenle
    | _ => try omega; try discriminate; auto
end.

Instance nat_evenle_lin : Lin.
refine
{|
    carrier := nat;
    leq := fun n m : nat => match even n, even m with
        | true, false => True
        | false, true => False
        | _, _ => n <= m
    end
|};
solve_nat_evenle.
Defined.

Instance nat_evenle : LinDec.
refine
{|
    lin := nat_evenle_lin
|}.
Proof.
  simpl. solve_nat_evenle; apply le_dec.
  simpl. solve_nat_evenle; apply (@leq_total_dec natle).
Defined.

Class LinDecMin : Type :=
{
    lindec : LinDec;
    min_elt : lindec;
    min_elt_is_min : forall x : lindec, leq x min_elt -> x = min_elt
}.

Coercion lindec : LinDecMin >-> LinDec.

Instance natle_min : LinDecMin :=
{
    lindec := natle;
    min_elt := 0
}.
Proof. inversion 1. auto. Defined.

Print fold_right.

Fixpoint min (A : LinDecMin) (l : list A) {struct l} : A :=
match l with
    | [] => min_elt
    | h :: t => fold_right (fun x y : A => if leqb x y then x else y) h t
end.

Eval cbv in min natle_min [98; 33; 98; 12; 56; 42].

Fixpoint min' (A : LinDecMin) (l : list A) : A :=
match l with
    | [] => min_elt
    | [x] => x
    | h :: t => if leqb h (min' A t) then h else min' A t
end.

Eval cbv in min' natle_min [5; 3; 19; 2; 14].

Theorem min'_In : forall (A : LinDecMin) (l : list A),
    l <> [] -> In (min' A l) l.
Proof.
  induction l as [| h t]; simpl; intros.
    contradiction H; auto.
    destruct t.
      left. auto.
      destruct (leqb h (min' A (c :: t))).
        left; auto.
        right. apply IHt. inversion 1.
Defined.

(*Theorem min_In : forall (A : LinDecMin) (l : list A),
    l <> [] -> In (min A l) l.
Proof.
  induction l as [| h t]; simpl; intros.
    contradiction H; auto.
    unfold fold. destruct t.
      left; auto.
      fold (fold (A := A) (B := A)). simpl in IHt. destruct IHt.
        inversion 1.
        repeat rewrite <- H0.
      destruct (leqb c (fold (fun x y : A => if leqb x y then x else y) t h)).
        right. simpl. left. auto.
        simpl in IHt. simpl. destruct IHt.
          inversion 1.
          right. left. assumption.
Defined.*)

Fixpoint nb_occ (A : LinDec) (x : A) (l : list A) : nat :=
match l with
    | nil => 0
    | h :: t => match LinDec_eq x h with
        | true => S (nb_occ A x t)
        | _ => nb_occ A x t
    end
end.

Definition perm (A : LinDec) (l1 l2 : list A) : Prop :=
    forall x : A, nb_occ A x l1 = nb_occ A x l2.

Lemma perm_refl : forall (A : LinDec) (l : list A), perm A l l.
Proof. unfold perm; auto. Defined.

Lemma perm_symm : forall (A : LinDec) (l1 l2 : list A),
    perm A l1 l2 -> perm A l2 l1.
Proof. unfold perm; auto. Defined.

Lemma perm_trans : forall (A : LinDec) (l1 l2 l3 : list A),
    perm A l1 l2 -> perm A l2 l3 -> perm A l1 l3.
Proof.
  unfold perm; intros. eapply eq_trans; auto.
Defined.

Lemma perm_cons : forall (A : LinDec) (x : A) (l1 l2 : list A),
    perm A l1 l2 -> perm A (x :: l1) (x :: l2).
Proof.
  unfold perm. intros. simpl. rewrite H. reflexivity.
Defined.

Lemma perm_swap : forall (A : LinDec) (x y : A) (l1 l2 : list A),
    perm A l1 l2 -> perm A (x :: y :: l1) (y :: x :: l2).
Proof.
  unfold perm; simpl; intros; destruct (LinDec_eq x0 x), (LinDec_eq x0 y);
  rewrite H; auto.
Defined.

Hint Resolve perm_cons perm_refl perm_swap : sort.

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
        apply le_S_n in H. apply le_S_n in H0. omega.
        (*Require Import Le. eapply le_trans; eauto.*)
Defined.

Theorem lengthOrder_wf : forall (A : Type),
    well_founded (@lengthOrder A).
Proof.
  red. intros A l. apply lengthOrder_wf' with (length l). trivial.
Restart.
  unfold lengthOrder. intro.
  apply (@well_founded_lt_compat _ (@length A)). trivial.
Defined.

Theorem perm_front :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    perm A (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    apply perm_refl.
    eapply perm_trans with (h1 :: x :: t1 ++ l2).
      apply perm_cons. apply IHt1.
      apply perm_swap. apply perm_refl.
Qed.

Theorem min'_split :
  forall (A : LinDecMin) (l : list A),
    l <> [] -> exists l1 l2 : list A, l = l1 ++ min A l :: l2.
Proof.
  induction l as [| h t].
    intro. contradiction H. reflexivity.
    destruct t as [| h' t']; intros _.
      exists [], []. simpl. reflexivity.
      edestruct IHt as [l1 [l2 H]].
        inversion 1.
Abort.