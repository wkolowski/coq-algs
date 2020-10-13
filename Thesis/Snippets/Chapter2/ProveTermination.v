Require Export AbstractTheAlgorithm.

Class TerminatingQSArgs : Type :=
{
    args :> QSArgs;

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
}.

Coercion args : TerminatingQSArgs >-> QSArgs.

Inductive QSDom (A : QSArgs) : list A -> Type :=
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
  {A : QSArgs} {l : list A} (d : QSDom A l) : list A :=
match d with
    | Short _ _ _ => adhoc l
    | Long _ _ pivot _ eq _ ltd gtd =>
        qs' ltd ++ pivot :: eq ++ qs' gtd
end.

Lemma QSDom_all :
  forall (A : QSArgs) (l : list A), QSDom A l.
Proof.
  intro A.
  apply well_founded_induction_type with (R := ltof _ (@length A)).
    apply well_founded_ltof.
    intros l IH. destruct (short l) as [[h t] |] eqn: Hshort.
      2: constructor; assumption.
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
  forall (A : TerminatingQSArgs) (l : list A), QSDom A l.
Proof.
  intro A.
  apply well_founded_induction_type with (R := ltof _ (@length A)).
    apply well_founded_ltof.
    intros l IH. destruct (short l) as [[h t] |] eqn: Hshort.
      2: constructor; assumption.
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
Instance TQSA_nat : TerminatingQSArgs :=
{
    args := QSA_nat;
}.
Proof.
  all: cbn.
    destruct l; inversion 1; cbn. apply le_refl.
    inversion 1; subst. reflexivity.
    inversion 1; subst. apply len_filter.
    inversion 1; subst. apply len_filter.
Defined.

Compute qs TQSA_nat [4; 3; 2; 1].
(* ===> = [1; 2; 3; 4]
        : list TQSA_nat *)

(** * 2.3.4 User experience: provide a default implementation *)

Instance QSA_default
  (A : Type) (p : A -> A -> bool) : QSArgs :=
{
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
       filter (fun x => negb (p x pivot)) rest)
}.

#[refine]
Instance TQSA_default
  (A : Type) (p : A -> A -> bool) : TerminatingQSArgs :=
{
    args := QSA_default A p;
}.
Proof.
  all: cbn.
    destruct l; inversion 1; cbn. apply le_refl.
    inversion 1; subst. reflexivity.
    inversion 1; subst. apply len_filter.
    inversion 1; subst. apply len_filter.
Defined.

Compute
  qs
    (TQSA_default _ (fun l1 l2 => leb (length l1) (length l2)))
    [[1; 2; 3]; [2; 2]; []; [4; 4; 4; 42]].
(* ===> = [[]; [2; 2]; [1; 2; 3]; [4; 4; 4; 42]] *)

(** * A slight variation on a theme *)

Module Variation.

Unset Guard Checking.
Fixpoint QSDom_all
  (A : QSArgs) (l : list A) {struct l} : QSDom A l.
Proof.
  destruct (short l) as [[h t] |] eqn: Hshort.
    Focus 2. constructor. assumption.
    destruct (choosePivot h t) as [pivot rest] eqn: Hpivot,
             (partition pivot rest) as [[lt eq] gt] eqn: Hpartition.
      econstructor 2; try eassumption.
        apply QSDom_all.
        apply QSDom_all.
Defined.
Set Guard Checking.

Definition qs
  (A : QSArgs) (l : list A) : list A :=
    qs' (QSDom_all A l).

Compute qs TQSA_nat [4; 2; 3; 5; 1; 1; 0; 12345].

End Variation.