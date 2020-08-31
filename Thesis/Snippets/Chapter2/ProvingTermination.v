Require Import List Arith.
Import ListNotations.

Class QSArgs : Type :=
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
}.

Coercion T : QSArgs >-> Sortclass.

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

Arguments Short {A l}.

Fixpoint qs {A : QSArgs} {l : list A} (d : QSDom A l) : list A :=
match d with
    | Short _ => adhoc l
    | Long _ _ pivot _ eq _ ltd gtd => qs ltd ++ pivot :: eq ++ qs gtd
end.

Definition QSDom_all :
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
        apply IH. red. eapply le_lt_trans.
          apply (partition_len_lt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
        apply IH. red. eapply le_lt_trans.
          apply (partition_len_gt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
Defined.

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
Instance QSArgs_nat : QSArgs :=
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
Defined.

Compute qs (QSDom_all QSArgs_nat [4; 3; 2; 1]).