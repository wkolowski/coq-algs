From CoqAlgs Require Export ProveTermination.

(** * One induction to rule them all: functional induction *)

Inductive QSGraph (A : QSArgs) : list A -> list A -> Prop :=
    | ShortG :
        forall l : list A, short l = None -> QSGraph A l (adhoc l)
    | LongG :
        forall {l : list A},
          forall {h : A} {t : list A},
            short l = Some (h, t) ->
          forall (pivot : A) {rest : list A},
            choosePivot h t = (pivot, rest) ->
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          forall lt' gt' : list A,
            QSGraph A lt lt' -> QSGraph A gt gt' ->
              QSGraph A l (lt' ++ pivot :: eq ++ gt').

Lemma QSGraph_correct :
  forall (A : TerminatingQSArgs) (l : list A),
    QSGraph A l (qs A l).
Proof.
  intros. unfold qs. generalize (QSDom_all A l).
  induction q; cbn; econstructor; eassumption.
Qed.

Lemma QSGraph_det :
  forall (A : QSArgs) (l r1 r2 : list A),
    QSGraph A l r1 -> QSGraph A l r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    congruence.
    congruence.
    {
      rewrite H in H5. inversion H5; subst.
      rewrite H0 in H6. inversion H6; subst.
      rewrite H1 in H7; inversion H7; subst.
      repeat f_equal.
        apply IHQSGraph1. assumption.
        apply IHQSGraph2. assumption.
    }
Qed.

Lemma QSGraph_complete :
  forall (A : TerminatingQSArgs) (l r : list A),
    QSGraph A l r -> r = qs A l.
Proof.
  intros. apply QSGraph_det with l.
    assumption.
    apply QSGraph_correct.
Qed.

Lemma qs_ind :
  forall (A : TerminatingQSArgs) (P : list A -> list A -> Prop),
    (forall l : list A, short l = None -> P l (adhoc l)) ->
    (
      forall (l : list A) (h : A) (t : list A),
        short l = Some (h, t) ->
      forall (pivot : A) (rest : list A),
        choosePivot h t = (pivot, rest) ->
      forall lt eq gt : list A,
        partition pivot rest = (lt, eq, gt) ->
          P lt (qs A lt) -> P gt (qs A gt) ->
            P l (qs A lt ++ pivot :: eq ++ qs A gt)
    ) ->
      forall l : list A, P l (qs A l).
Proof.
  intros A P Hshort Hlong l.
  apply QSGraph_ind; intros.
    apply Hshort. assumption.
    apply QSGraph_complete in H2. apply QSGraph_complete in H4.
      subst. eapply Hlong; eassumption.
    apply QSGraph_correct.
Qed.

Lemma qs_eq :
  forall (A : TerminatingQSArgs) (l : list A),
    qs A l =
    match short l with
        | None => adhoc l
        | Some (h, t) =>
            let '(pivot, rest) := choosePivot h t in
            let '(lt, eq, gt)  := partition pivot rest in
              qs A lt ++ pivot :: eq ++ qs A gt
    end.
Proof.
  intros A l. apply qs_ind; intros.
    rewrite H. reflexivity.
    rewrite H, H0, H1. reflexivity.
Qed.

(** * Don't do this at home *)

Lemma qs'_ind :
  forall (A : TerminatingQSArgs) (P : list A -> list A -> Prop),
    (forall l : list A, short l = None -> P l (adhoc l)) ->
    (
      forall (l : list A) (h : A) (t : list A),
        short l = Some (h, t) ->
      forall (pivot : A) (rest : list A),
        choosePivot h t = (pivot, rest) ->
      forall
        (lt eq gt : list A)
        (ltd : QSDom A lt) (gtd : QSDom A gt) ,
          partition pivot rest = (lt, eq, gt) ->
            P lt (qs' ltd) -> P gt (qs' gtd) ->
              P l (qs' ltd ++ pivot :: eq ++ qs' gtd)
    ) ->
      forall (l : list A) (d : QSDom A l), P l (qs' d).
Proof.
  induction d; cbn.
    apply H. assumption.
    eapply H0; eassumption.
Qed.

Lemma qs_ind_bad :
  forall (A : TerminatingQSArgs) (P : list A -> list A -> Prop),
    (forall l : list A, short l = None -> P l (adhoc l)) ->
    (
      forall (l : list A) (h : A) (t : list A),
        short l = Some (h, t) ->
      forall (pivot : A) (rest : list A),
        choosePivot h t = (pivot, rest) ->
      forall lt eq gt : list A,
        partition pivot rest = (lt, eq, gt) ->
          P lt (qs A lt) -> P gt (qs A gt) ->
            P l (qs A lt ++ pivot :: eq ++ qs A gt)
    ) ->
      forall l : list A, P l (qs A l).
Proof.
  unfold qs. intros A P Hshort Hlong l.
  apply qs'_ind.
    apply Hshort.
    intros.
Abort.

Lemma isProp_QSDom :
  forall (A : TerminatingQSArgs) (l : list A) (d1 d2 : QSDom A l),
    d1 = d2.
Proof.
  induction d1; destruct d2.
    f_equal. admit.
    congruence.
    congruence.
      assert (h = h0) by congruence.
      assert (t = t0) by congruence.
      assert (pivot = pivot0) by congruence.
      assert (rest = rest0) by congruence.
      assert (lt = lt0) by congruence.
      assert (eq = eq0) by congruence.
      assert (gt = gt0) by congruence.
      subst. f_equal.
Abort.

(*
Lemma qs_ind_bad :
  forall (A : TerminatingQSArgs) (P : list A -> list A -> Prop),
    (forall l : list A, short l = None -> P l (adhoc l)) ->
    (
      forall (l : list A) (h : A) (t : list A),
        short l = Some (h, t) ->
      forall (pivot : A) (rest : list A),
        choosePivot h t = (pivot, rest) ->
      forall lt eq gt : list A,
        partition pivot rest = (lt, eq, gt) ->
          P lt (qs A lt) -> P gt (qs A gt) ->
            P l (qs A lt ++ pivot :: eq ++ qs A gt)
    ) ->
      forall l : list A, P l (qs A l).
Proof.
  intros.
  unfold qs.
  apply qs'_ind.
    apply H.
    {
      intros. unfold qs in *.
      replace ltd with (QSDom_all A lt) in * by apply isProp_QSDom.
      replace gtd with (QSDom_all A gt) in * by apply isProp_QSDom.
      eapply H0; eassumption.
    }
Qed.
*)

(** * Automating the boring stuff *)

Require Import Recdef.

Function qsf
  (A : TerminatingQSArgs) (l : list A) {measure length l} : list A :=
match short l with
    | None => adhoc l
    | Some (h, t) =>
        let '(pivot, rest) := choosePivot h t in
        let '(lt, eq, gt)  := partition pivot rest in
          qsf A lt ++ pivot :: eq ++ qsf A gt
end.
Proof.
  intros; subst. apply Nat.le_lt_trans with (length rest).
    apply (partition_len_gt teq2).
    rewrite (choosePivot_len teq1). apply (short_len teq).
  intros; subst. apply Nat.le_lt_trans with (length rest).
    apply (partition_len_lt teq2).
    rewrite (choosePivot_len teq1). apply (short_len teq).
Defined.

Compute qsf (TQSA_default nat leb) [4; 3; 2; 1].
(* ===> = [1; 2; 3; 4] *)

Module Function_failures.

Fail Function weird_id (n : nat) {measure id n} : nat :=
match n with
    | 0 => 0
    | S n' => S (weird_id (weird_id n'))
end.
(* ===> The command has indeed failed with message:
        on expr : weird_id n' check_not_nested: failure weird_id *)

Inductive Tr (A : Type) : Type :=
    | N : A -> list (Tr A) -> Tr A.

Arguments N {A} _ _.

Function tmap {A B : Type} (f : A -> B) (t : Tr A) : Tr B :=
match t with
    | N x l => N (f x) (map (tmap f) l)
end.
(* ===> tmap is defined
        tmap is recursively defined (guarded on 4th argument)
        Cannot define graph(s) for tmap [...]
        Cannot build inversion information [...] *)

End Function_failures.

(** * Hole-driven development and proof by admission *)

Theorem Permutation_qsf_first_try :
  forall (A : TerminatingQSArgs) (l : list A),
    Permutation l (qsf A l).
Proof.
  intros. functional induction (qsf A l).
    admit.
    eapply Permutation_trans with (lt ++ pivot :: eq ++ gt).
      admit.
      apply Permutation_app.
        assumption.
        constructor. apply Permutation_app.
          reflexivity.
          assumption.
Admitted.

Theorem Sorted_qsf_first_try :
  forall (A : TerminatingQSArgs) (R : A -> A -> Prop) (l : list A),
    Sorted R (qsf A l).
Proof.
  intros. functional induction (qsf A l).
    admit.
    cut (Sorted R (qsf A lt) /\
         Forall (fun x => R pivot x) (qsf A lt) /\
         Sorted R (pivot :: eq ++ qsf A gt)).
      admit.
      repeat split.
        assumption.
        apply (Permutation_Forall (Permutation_qsf_first_try A lt)).
          admit.
        cut (Sorted R (pivot :: eq) /\
             Forall (fun x => R pivot x) (qsf A gt)).
          admit.
          split.
            cut (Forall (fun x => x = pivot) eq).
              admit.
              admit.
            apply (Permutation_Forall (Permutation_qsf_first_try A gt)).
              admit.
Admitted.

Class VerifiedQSArgs : Type :=
{
    T : TerminatingQSArgs;

    Permutation_adhoc :
      forall {l : list T},
        short l = None ->
          Permutation l (adhoc l);

    Permutation_short :
      forall {l : list T} {h : T} {t : list T},
        short l = Some (h, t) ->
          Permutation l (h :: t);

    Permutation_choosePivot :
      forall {h : T} {t : list T} {pivot : T} {rest : list T},
        choosePivot h t = (pivot, rest) ->
          Permutation (h :: t) (pivot :: rest);

    Permutation_partition :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          Permutation (pivot :: rest) (lt ++ pivot :: eq ++ gt);

    R : T -> T -> Prop;

    R_refl :
      forall x : T, R x x;

    Sorted_adhoc :
      forall {l : list T},
        short l = None ->
          Sorted R (adhoc l);

    partition_pivot_lt :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          Forall (fun x => R x pivot) lt;

    partition_pivot_eq :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          Forall (fun x => pivot = x) eq;

    partition_pivot_gt :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          Forall (fun x => R pivot x) gt;
}.

Coercion T : VerifiedQSArgs >-> TerminatingQSArgs.
Coercion R : VerifiedQSArgs >-> Funclass.

#[global] Hint Constructors Sorted : core.

Lemma Sorted_app :
  forall
    {A : Type} {R : A -> A -> Prop}
    {pivot : A} {lt rest : list A},
      Forall (fun x => R x pivot) lt ->
      Sorted R lt ->
      Sorted R (pivot :: rest) ->
        Sorted R (lt ++ pivot :: rest).
Proof.
  induction 1; try inversion 1; subst; cbn; auto.
Qed.

Lemma Sorted_app_eq :
  forall
    {A : Type} {R : A -> A -> Prop}
    {pivot : A} {eq gt : list A},
      Forall (fun x => pivot = x) eq ->
      Forall (fun x => R pivot x) gt ->
      (forall x : A, R x x) ->
      Sorted R gt ->
        Sorted R (pivot :: eq ++ gt).
Proof.
  induction 1; cbn; inversion 1; subst; auto.
Qed.

Theorem Permutation_qsf :
  forall (A : VerifiedQSArgs) (l : list A),
    Permutation l (qsf A l).
Proof.
  intros.
  functional induction (qsf A l).
    eapply Permutation_adhoc. assumption.
    {
      apply Permutation_short in e.
      apply Permutation_choosePivot in e0.
      apply Permutation_partition in e1.
      rewrite e, e0, e1.
      apply Permutation_app.
        assumption.
        constructor. apply Permutation_app.
          reflexivity.
          assumption.
    }
Qed.

Theorem Sorted_qsf :
  forall (A : VerifiedQSArgs) (l : list A),
    Sorted A (qsf A l).
Proof.
  intros.
  functional induction (qsf A l).
    apply Sorted_adhoc. assumption.
    apply Sorted_app.
      apply (Permutation_Forall (Permutation_qsf A lt)).
        eapply partition_pivot_lt; eassumption.
      assumption.
      apply Sorted_app_eq.
        eapply partition_pivot_eq; eassumption.
        apply (Permutation_Forall (Permutation_qsf A gt)).
          eapply partition_pivot_gt; eassumption.
        apply R_refl.
        assumption.
Qed.

#[refine, export]
Instance Sort_qsf
  (A : VerifiedQSArgs) : Sort A (qsf A) := {}.
Proof.
  apply Sorted_qsf.
  apply Permutation_qsf.
Defined.

(** * Sanity check – concrete proofs *)

#[refine, export]
Instance VQSA_default
  {A : Type} (p : A -> A -> bool)
  (Hrefl : forall x : A, p x x = true)
  (Htotal : forall x y : A, p x y = false -> p y x = true)
  : VerifiedQSArgs :=
{
    T := TQSA_default A p;
    R x y := p x y = true;
    R_refl := Hrefl
}.
Proof.
  destruct l; inversion 1. constructor.
  destruct l; inversion 1. reflexivity.
  inversion 1. reflexivity.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn in *.
      reflexivity.
      destruct (p h pivot); cbn.
        rewrite perm_swap, <- IHt; reflexivity.
        {
          rewrite Permutation_app_comm.
          rewrite <- !app_comm_cons.
          rewrite perm_swap.
          rewrite (@perm_swap _ h pivot).
          constructor.
          rewrite app_comm_cons.
          rewrite Permutation_app_comm.
          assumption.
        }
  constructor.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn.
      constructor.
      destruct (p h pivot) eqn: Hp.
        constructor; assumption.
        assumption.
  inversion 1; subst; clear H. constructor.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn.
      constructor.
      destruct (p h pivot) eqn: Hp; cbn.
        assumption.
        constructor.
          apply Htotal in Hp. assumption.
          assumption.
Defined.

Lemma leb_total :
  forall x y : nat, leb x y = false -> leb y x = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete_conv in H.
  lia.
Qed.

Compute
  qsf (VQSA_default leb Nat.leb_refl leb_total) [1; 2; 666; 42; 0].
(* ===> = [0; 1; 2; 42; 666] *)