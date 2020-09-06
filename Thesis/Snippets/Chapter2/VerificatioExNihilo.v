Require Import List Arith.
Import ListNotations.

Require Import Specification Lemmas.

Class VerifiedQSArgs : Type :=
{
    T : Type;
    short : list T -> option (T * list T);
    adhoc : list T -> list T;
    choosePivot : T -> list T -> T * list T;
    partition : T -> list T -> list T * list T * list T;

    short_len :
      forall {l : list T} {h : T} {t : list T},
        short l = Some (h, t) -> length t < length l;

    choosePivot_len :
      forall {h : T} {t : list T} {pivot : T} {rest : list T},
        choosePivot h t = (pivot, rest) ->
          length rest = length t;

    partition_len_lt :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          length lt <= length rest;

    partition_len_gt :
      forall {pivot : T} {rest lt eq gt : list T},
        partition pivot rest = (lt, eq, gt) ->
          length gt <= length rest;

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

    (* TODO 2 *)
    R : T -> T -> Prop;

    Sorted_adhoc :
      forall {l : list T},
        short l = None -> (* TODO 3: opisać to *)
          Sorted R (adhoc l);
}.

Coercion T : VerifiedQSArgs >-> Sortclass.
Coercion R : VerifiedQSArgs >-> Funclass.

Inductive QSDom (A : VerifiedQSArgs) : list A -> Type :=
    | Short :
        forall l : list A, short l = None -> QSDom A l
    | Long :
        forall {l : list A},
          forall {h : A} {t : list A},
            short l = Some (h, t) ->
          forall (pivot : A) {rest : list A},
            choosePivot h t = (pivot, rest) ->
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          QSDom A lt -> QSDom A gt -> QSDom A l.

Fixpoint qs'
  {A : VerifiedQSArgs} {l : list A} (d : QSDom A l) : list A :=
match d with
    | Short _ _ _ => adhoc l
    | Long _ _ pivot _ eq _ ltd gtd =>
        qs' ltd ++ pivot :: eq ++ qs' gtd
end.

Lemma QSDom_all :
  forall (A : VerifiedQSArgs) (l : list A), QSDom A l.
Proof.
  intro A.
  apply well_founded_induction_type with (R := ltof _ (@length A)).
    apply well_founded_ltof.
    intros l IH. destruct (short l) as [[h t] |] eqn: Hshort.
      Focus 2. constructor. assumption.
      destruct (choosePivot h t) as [pivot rest] eqn: Hpivot;
      destruct (partition pivot rest) as [[lt eq] gt] eqn: Hpartition.
      econstructor 2; try eassumption.
        apply IH; red. apply le_lt_trans with (length rest).
          apply (partition_len_lt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
        apply IH; red. apply le_lt_trans with (length rest).
          apply (partition_len_gt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
Defined.

Definition qs (A : VerifiedQSArgs) (l : list A) : list A :=
  qs' (QSDom_all A l).

Lemma len_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (filter p l) <= length l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (p h).
      cbn. apply le_n_S. assumption.
      apply le_S. assumption.
Defined.

#[refine]
Instance QSArgs_nat : VerifiedQSArgs :=
{
    T := nat;
    short l :=
      match l with
          | [] => None
          | h :: t => Some (h, t)
      end;
    adhoc _ := [];
    choosePivot h t := (h, t);
    partition p l :=
      (filter (fun x => leb x p) l,
       [],
       filter (fun x => negb (leb x p)) l)
}.
Proof.
  destruct l; inversion 1; cbn. apply le_refl.
  inversion 1. reflexivity.
  inversion 1; subst. apply len_filter.
  inversion 1; subst. apply len_filter.
Admitted.

(*
Compute qs QSArgs_nat [4; 3; 2; 1].
*)

Lemma qs'_ind :
  forall (A : VerifiedQSArgs) (P : list A -> list A -> Prop),
    (forall l : list A, short l = None -> P l (adhoc l)) ->
    (
      forall (l : list A) (h : A) (t : list A),
        short l = Some (h, t) ->
      forall (pivot : A) (rest : list A),
        choosePivot h t = (pivot, rest) ->
      forall (lt eq gt : list A) (ltd : QSDom A lt) (gtd : QSDom A gt) ,
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

Lemma qs_ind :
  forall (A : VerifiedQSArgs) (P : list A -> list A -> Prop),
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
    intros. unfold qs in *.
Abort.

Lemma isProp_QSDom :
  forall (A : VerifiedQSArgs) (l : list A) (d1 d2 : QSDom A l),
    d1 = d2.
Proof.
  induction d1; destruct d2.
    f_equal. admit.
    congruence.
    congruence.
    {
      assert (h = h0) by congruence.
      assert (t = t0) by congruence.
      assert (pivot = pivot0) by congruence.
      assert (rest = rest0) by congruence.
      assert (lt = lt0) by congruence.
      assert (eq = eq0) by congruence.
      assert (gt = gt0) by congruence.
      subst. f_equal.
        admit.
        admit.
        admit.
        apply IHd1_1.
        apply IHd1_2.
Admitted.

Lemma qs_ind_bad :
  forall (A : VerifiedQSArgs) (P : list A -> list A -> Prop),
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

Inductive qsG (A : VerifiedQSArgs) : list A -> list A -> Prop :=
    | ShortG :
        forall l : list A, short l = None -> qsG A l (adhoc l)
    | LongG :
        forall {l : list A},
          forall {h : A} {t : list A},
            short l = Some (h, t) ->
          forall (pivot : A) {rest : list A},
            choosePivot h t = (pivot, rest) ->
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          forall lt' gt' : list A,
            qsG A lt lt' -> qsG A gt gt' ->
              qsG A l (lt' ++ pivot :: eq ++ gt').

Lemma qsG_det :
  forall (A : VerifiedQSArgs) (l r1 r2 : list A),
    qsG A l r1 -> qsG A l r2 -> r1 = r2.
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
        apply IHqsG1. assumption.
        apply IHqsG2. assumption.
    }
Qed.

Lemma qsG_correct :
  forall (A : VerifiedQSArgs) (l : list A),
    qsG A l (qs A l).
Proof.
  intros. unfold qs.
  generalize (QSDom_all A l).
  induction q; cbn.
    constructor. assumption.
    econstructor; eassumption.
Qed.

Lemma qsG_complete :
  forall (A : VerifiedQSArgs) (l r : list A),
    qsG A l r -> r = qs A l.
Proof.
  intros.
  eapply qsG_det.
    eassumption.
    apply qsG_correct.
Qed.

Lemma qs_ind :
  forall (A : VerifiedQSArgs) (P : list A -> list A -> Prop),
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
  apply qsG_ind.
    assumption.
    intros. apply qsG_complete in H4. apply qsG_complete in H6.
      subst. eapply H0; eassumption.
    apply qsG_correct.
Qed.

Require Import Recdef.

Function qsf
  (A : VerifiedQSArgs) (l : list A) {measure length l} : list A :=
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

(*
Compute qsf QSArgs_nat [4; 3; 2; 1].
*)

Instance Transitive_Permutation :
  forall A : Type, Transitive (@Permutation A).
Admitted.

Theorem Permutation_qsf :
  forall
    (A : VerifiedQSArgs) (l : list A),
      Permutation l (qsf A l).
Proof.
  intros.
  functional induction (qsf A l).
    apply Permutation_adhoc. assumption.
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

Theorem Sorted_qsf :
  forall
    (A : VerifiedQSArgs) (l : list A),
      Sorted A (qsf A l).
Proof.
  intros.
  functional induction (qsf A l).
    apply Sorted_adhoc. assumption.
      apply Sorted_app_all; auto.
        apply Sorted_cons.
          intros. apply in_app_or in H. destruct H.
            erewrite spec_eq; eauto.
            eapply spec_hi; eauto. eapply uqs_In; eauto.
          apply Sorted_app; auto.
            assert (forall x : A, In x eq -> x = pivot).
              eapply spec_eq; eauto.
              clear e1. induction eq; auto. destruct eq; auto. constructor.
                rewrite (H a), (H c); cbn; auto.
                apply IHeq. intro. inv 1; apply H; cbn; auto.
            intros. apply uqs_In in H0.
              erewrite (spec_eq pivot) at 1; eauto.
                eapply spec_hi; eauto.
          intros. apply uqs_In in H. eapply spec_lo; eauto.
Qed.

Theorem uqs_In :
  forall
    (A : LinDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A)
    (l : list A) (x : A),
      In x (uqs adhoc choosePivot partition l) <->
      In x l.
Proof.
  intros.
  split; apply Permutation_in.
    apply Permutation_uqs.
    symmetry. apply Permutation_uqs.
Qed.

