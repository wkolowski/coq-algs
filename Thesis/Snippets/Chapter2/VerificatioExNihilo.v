Require Export Lemmas ProveTermination Lia.

Class VerifiedQSArgs : Type :=
{
    T :> TerminatingQSArgs;

    (* TODO *)
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

    (* TODO 2: kwestia rozstrzygalności relacji *)
    R : T -> T -> Prop;

    R_refl :
      forall x : T, R x x;

    Sorted_adhoc :
      forall {l : list T},
        short l = None -> (* TODO 3: opisać to *)
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

#[refine]
Instance VQSA_nat : VerifiedQSArgs :=
{
    T := TQSA_nat;
}.
Proof.
  destruct l; inversion 1. constructor.
  destruct l; inversion 1. constructor.
  inversion 1. constructor.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn in *.
      constructor.
      destruct (h <=? pivot); cbn.
        eapply Permutation_trans.
          apply Permutation_swap.
          apply Permutation_cons. assumption.
        {
          rewrite Permutation_app_symm.
          rewrite <- !app_comm_cons.
          rewrite Permutation_swap.
          rewrite (@Permutation_swap _ h pivot).
          apply Permutation_cons. 
          rewrite app_comm_cons.
          rewrite Permutation_app_symm.
          assumption.
        }
  exact le.
  apply le_refl.
  constructor.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn.
      constructor.
      destruct (Nat.leb_spec h pivot).
        constructor; assumption.
        assumption.
  inversion 1; subst; clear H. constructor.
  inversion 1; subst; clear H.
    induction rest as [| h t]; cbn.
      constructor.
      destruct (Nat.leb_spec h pivot); cbn.
        assumption.
        constructor.
          lia.
          assumption.
Defined.

Compute qs VQSA_nat [4; 3; 2; 1].

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

(** It's possible to prove theorems using just QSDom_ind, but it's not
    very abstract or modular to do so. *)
Theorem Permutation_qs :
  forall
    (A : VerifiedQSArgs) (l : list A),
      Permutation l (qs A l).
Proof.
  unfold qs. intros. generalize (QSDom_all A l).
  induction q; cbn.
    eapply Permutation_adhoc. assumption.
    {
      apply Permutation_short in e.
      apply Permutation_choosePivot in e0.
      apply Permutation_partition in e1.
      rewrite e, e0, e1.
      apply Permutation_app.
        assumption.
        apply Permutation_cons, Permutation_app.
          apply Permutation_refl.
          assumption.
    }
Qed.

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
  intros; subst. apply le_lt_trans with (length rest).
    apply (partition_len_gt teq2).
    rewrite (choosePivot_len teq1). apply (short_len teq).
  intros; subst. apply le_lt_trans with (length rest).
    apply (partition_len_lt teq2).
    rewrite (choosePivot_len teq1). apply (short_len teq).
Defined.

Compute qsf (TQSA_default nat leb) [4; 3; 2; 1].
(* ===> = [1; 2; 3; 4] *)

Theorem Permutation_qsf :
  forall
    (A : VerifiedQSArgs) (l : list A),
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
        apply Permutation_cons, Permutation_app.
          apply Permutation_refl.
          assumption.
    }
Qed.

Lemma wut0 :
  forall (A : VerifiedQSArgs) (pivot : A) (lt eq gt : list A),
    Sorted A lt -> Sorted A (pivot :: eq ++ gt) ->
    Forall (fun x => A x pivot) lt ->
      Sorted A (lt ++ pivot :: eq ++ gt).
Proof.
  intros until 1. revert pivot eq gt.
  induction H; cbn; intros.
    assumption.
    inversion H0; subst. constructor; assumption.
    constructor.
      assumption.
      apply IHSorted.
        assumption.
        inversion H2; subst. assumption.
Qed.

Lemma wut1 :
  forall (A : VerifiedQSArgs) (pivot : A) (eq gt : list A),
    Sorted A gt ->
    Forall (fun x => pivot = x) eq ->
    Forall (fun x => A pivot x) gt ->
      Sorted A (pivot :: eq ++ gt).
Proof.
  induction eq as [| h t]; cbn; intros.
    inversion H1; subst.
      constructor.
      constructor; assumption.
    inversion H0; subst. constructor.
      apply R_refl.
      apply IHt; assumption.
Qed.

Lemma wut :
  forall (A : VerifiedQSArgs) (pivot : A) (lt gt : list A),
    Sorted A lt -> Sorted A (pivot :: gt) ->
    Forall (fun x => A x pivot) lt ->
      Sorted A (lt ++ pivot :: gt).
Proof.
  intros until 1. revert pivot gt.
  induction H; cbn; intros.
    assumption.
    inversion H0; subst. constructor; assumption.
    constructor.
      assumption.
      apply IHSorted.
        assumption.
        inversion H2; subst. assumption.
Qed.

Theorem Sorted_qsf :
  forall
    (A : VerifiedQSArgs) (l : list A),
      Sorted A (qsf A l).
Proof.
  intros.
  functional induction (qsf A l).
    apply Sorted_adhoc. assumption.
    apply wut0.
      assumption.
      apply wut1.
        assumption.
        eapply partition_pivot_eq; eassumption.
        apply (Permutation_Forall (Permutation_qsf A gt)).
          eapply partition_pivot_gt; eassumption.
      apply (Permutation_Forall (Permutation_qsf A lt)).
          eapply partition_pivot_lt; eassumption.
Qed.

#[refine]
Instance Sort_qsf
  (A : VerifiedQSArgs) : Sort A (qsf A) := {}.
Proof.
  apply Sorted_qsf.
  apply Permutation_qsf.
Qed.