Require Import List.
Import ListNotations.

Require Import ProveTermination.

Module BoveCapretta_original.

Inductive QSDom (A : QSArgs) : list A -> Prop :=
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

Lemma Long_inv_lt :
  forall
    {A : QSArgs} {l : list A} {h : A} {t : list A} (d : QSDom A l),
    short l = Some (h, t) ->
      let '(pivot, rest) := choosePivot h t      in
      let '(lt, _, _)    := partition pivot rest in
        QSDom A lt.
Proof.
  destruct 1; intro.
    congruence.
    rewrite H in H2. inversion H2; subst. rewrite H0, H1.
      exact d1.
Qed.

Lemma Long_inv_lt' :
  forall
    {A : QSArgs} {l : list A} (d : QSDom A l),
      forall {h : A} {t : list A},
        short l = Some (h, t) ->
      forall {pivot : A} {rest : list A},
        choosePivot h t = (pivot, rest) ->
      forall {lt eq gt : list A},
        partition pivot rest = (lt, eq, gt) ->
          QSDom A lt.
Proof.
  destruct 1; intros.
    congruence.
    {
      rewrite H in H2; inversion H2; subst.
      rewrite H0 in H3; inversion H3; subst.
      rewrite H1 in H4; inversion H4; subst.
      exact d1.
    }
Qed.

Lemma Long_inv_lt'' :
  forall
    {A : QSArgs} {l : list A} {h : A} {t : list A} (d : QSDom A l),
      short l = Some (h, t) ->
        QSDom A (
          let '(pivot, rest) := choosePivot h t      in
          let '(lt, _, _)    := partition pivot rest in lt).
Proof.
  destruct 1; intro.
    congruence.
    rewrite H in H2; inversion H2; subst.
      rewrite H0, H1. assumption.
Qed.

Lemma Long_inv_gt :
  forall
    {A : QSArgs} {l : list A} {h : A} {t : list A} (d : QSDom A l),
    short l = Some (h, t) ->
      let '(pivot, rest) := choosePivot h t      in
      let '(_, _, gt)    := partition pivot rest in
        QSDom A gt.
Proof.
  destruct 1; intro.
    congruence.
    rewrite H in H2. inversion H2; subst. rewrite H0, H1.
      exact d2.
Qed.

Fixpoint qs' {A : QSArgs} (l : list A) (d : QSDom A l) : list A.
Proof.
(*
  destruct (short l) as [[h t] _ |] eqn: Hshort.
    2: exact (adhoc l).
    destruct (choosePivot h t) as [pivot rest],
             (partition pivot rest) as [[lt eq] gt].
      Check (Long_inv_lt' d Hshort).
pose (lt' := qs' A lt (Long_inv_lt _)).
*)
refine (
match short l with
    | None => adhoc l
    | Some (h, t) =>
        let '(pivot, rest) := choosePivot h t in
        let '(lt, eq, gt)  := partition pivot rest in
          qs' A lt _ ++
            pivot :: eq ++
          qs' A gt _
end).
(*
  apply Long_inv_lt''.
  eapply Long_inv_lt'; try eassumption.
  pose (Hlt := @Long_inv_lt A l h t d ).
  apply Hlt.
  
  apply Long_inv_lt.
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          QSDom A lt -> QSDom A gt -> QSDom A l.

match d with
    | Short _ _ _ => adhoc l
    | Long _ _ pivot _ eq _ ltd gtd =>
        qs' ltd ++ pivot :: eq ++ qs' gtd
end.
*)
Admitted.

Require Import Wellfounded Arith.

Lemma QSDom_all :
  forall (A : QSArgs) (l : list A), QSDom A l.
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
          admit.
          admit.
        apply IH; red. apply le_lt_trans with (length rest).
          admit.
          admit.
Abort.

Lemma QSDom_all :
  forall (A : QSArgs) (l : list A), QSDom A l.
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

Definition qs (A : QSArgs) (l : list A) : list A :=
  qs' l (QSDom_all A l).

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

End BoveCapretta_original.