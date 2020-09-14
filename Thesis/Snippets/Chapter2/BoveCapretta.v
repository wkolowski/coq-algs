Require Export ProveTermination.

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
Defined.

Lemma Long_inv_gt :
  forall
    {A : QSArgs} {l : list A} (d : QSDom A l),
      forall {h : A} {t : list A},
        short l = Some (h, t) ->
      forall {pivot : A} {rest : list A},
        choosePivot h t = (pivot, rest) ->
      forall {lt eq gt : list A},
        partition pivot rest = (lt, eq, gt) ->
          QSDom A gt.
Proof.
  destruct 1; intros.
    congruence.
    {
      rewrite H in H2; inversion H2; subst.
      rewrite H0 in H3; inversion H3; subst.
      rewrite H1 in H4; inversion H4; subst.
      exact d2.
    }
Defined.

Fixpoint qs'
  (A : QSArgs) (l : list A)
  (d : QSDom A l) {struct d}
  : list A :=
match
  short l as x return short l = x -> _
with
| None => fun _ => adhoc l
| Some (h, t) => fun _ =>
    match
      choosePivot h t as y return choosePivot h t = y -> _
    with
    | (pivot, rest) => fun _ =>
        match
          partition pivot rest as z return partition pivot rest = z -> _
        with
        | (lt, eq, gt) => fun _ =>
            qs' A lt ltac:(eapply Long_inv_lt; eassumption)
            ++ pivot :: eq ++
            qs' A gt ltac:(eapply Long_inv_gt; eassumption)
        end eq_refl
    end eq_refl
end eq_refl.

Lemma QSDom_all :
  forall (A : TerminatingQSArgs) (l : list A), QSDom A l.
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

Definition qs (A : TerminatingQSArgs) (l : list A) : list A :=
  qs' A l (QSDom_all A l).

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
Instance TQSA_default
  (A : Type) (p : A -> A -> bool) : TerminatingQSArgs :=
{
    args :=
    {|
        T := A;
        short l :=
          match l with
              | [] => None
              | h :: t => Some (h, t)
          end;
        adhoc _ := [];
        choosePivot h t := (h, t);
        partition pivot rest :=
          (filter (fun x => p x pivot) rest,
           [],
           filter (fun x => negb (p x pivot)) rest);
    |}
}.
Proof.
  all: cbn.
    destruct l; inversion 1; cbn. apply le_refl.
    inversion 1. reflexivity.
    inversion 1; subst. apply len_filter.
    inversion 1; subst. apply len_filter.
Defined.

Compute qs (TQSA_default nat leb) [4; 3; 2; 1].