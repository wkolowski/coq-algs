Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export ListLemmas.
Require Export Sorting.Sort.

(*Require Import InsertionSort.*)

Set Implicit Arguments.

Local Hint Unfold lt : core.
Local Hint Resolve le_n_S filter_length : core.

(** Time to generalize [ghqs]:
    - Rather that [n], the length of the desired "small list",
      we will just give some function that determines if the
      input list is small enough (and if not, if returns an
      element of the list and the rest of the list)
*)

Class Small (A : Ord) : Type :=
{
    small : list A -> list A + A * list A;
    small_inl :
      forall l l' : list A,
        small l = inl l' -> l = l';
    small_inr :
      forall (h : A) (t l : list A),
         small l = inr (h, t) -> Permutation l (h :: t)
}.

Coercion small : Small >-> Funclass.

Class AdHocSort {A : Ord} (small : Small A) : Type :=
{
    adhoc : list A -> list A;
    Sorted_adhoc :
      forall l l' : list A,
        small l = inl l' -> Sorted trich_le (adhoc l');
    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm l' (adhoc l');
}.

Coercion adhoc : AdHocSort >-> Funclass.

Class Pivot (A : Ord) : Type :=
{
    pivot : A -> list A -> A * list A;
    pivot_spec :
      forall (h h' : A) (t t' : list A),
        pivot h t = (h', t') -> Permutation (h :: t) (h' :: t')
}.

Coercion pivot : Pivot >-> Funclass.

Class Partition (A : Ord) : Type :=
{
    partition : A -> list A -> list A * list A * list A;
    spec_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x lo -> x ≤ pivot;
    spec_eq :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x eq -> x = pivot;
    spec_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x hi -> pivot ≤ x /\ pivot <> x;
    len_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length lo <= length l;
    len_eq :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length eq <= length l;
    len_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length hi <= length l;
    partition_perm :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          perm l (lo ++ eq ++ hi);
}.

Lemma Permutation_partition :
  forall (A : Ord) (p : Partition A) (pivot : A) (l lo eq hi : list A),
    partition pivot l = (lo, eq, hi) -> Permutation (lo ++ eq ++ hi) l.
Proof.
  intros. apply perm_Permutation. symmetry.
  eapply partition_perm. eassumption.
Qed.

Coercion partition : Partition >-> Funclass.

Function uqs
  (A : Ord)
  (small : Small A)
  (adhoc : AdHocSort small)
  (choosePivot : Pivot A)
  (partition : Partition A)
  (l : list A)
  {measure length l} : list A :=
match small l with
    | inl l' => adhoc l'
    | inr (h, t) =>
        let
          '(pivot, rest) := choosePivot h t
        in
        let
          '(lo, eq, hi) := partition pivot rest
        in
          uqs adhoc choosePivot partition lo ++
          pivot :: eq ++
          uqs adhoc choosePivot partition hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply pivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; lia.
Defined.

(** Ordinary quicksort using [uqs] *)

#[refine]
Instance Small_head (A : Ord) : Small A :=
{
    small :=
      fun l : list A =>
      match l with
          | [] => inl []
          | h :: t => inr (h, t)
      end;
}.
Proof.
  all: destruct l; cbn; inv 1.
Defined.

#[refine]
Instance AdHocSort_id (A : Ord) : AdHocSort (Small_head A) :=
{
    adhoc := id;
}.
Proof.
  all: destruct l; inv 1; constructor.
Defined.

#[refine]
Instance Pivot_head (A : Ord) : Pivot A :=
{
    pivot :=
      fun (h : A) (t : list A) => (h, t)
}.
Proof. inv 1. Defined.

#[refine]
Instance Partition_filter (A : Ord) : Partition A :=
{
    partition x l :=
      (filter (fun y => y ≤? x) l, [],
       filter (fun y => negb (y ≤? x)) l)
}.
Proof.
  all: intros; inv H.
    rewrite filter_In in H0. firstorder trich.
    inv H0.
    rewrite filter_In in H0. destruct H0. split; try inv 1; trich.
    cbn. lia.
    cbn. unfold perm. intros. rewrite count_app. apply count_filter.
Defined.

Definition qs A :=
  uqs (AdHocSort_id A) (Pivot_head A) (Partition_filter A).

#[refine]
Instance Partition_bifilter (A : Ord) : Partition A :=
{
    partition x l :=
      let '(lo, hi) := bifilter (fun y => y ≤? x) l in (lo, [], hi)
}.
Proof.
  all: intros; rewrite bifilter_spec in H; inv H.
    apply filter_In in H0. firstorder trich.
    inv H0.
    apply filter_In in H0. destruct H0. trich. inv H0.
    cbn. split; try inv 1; trich.
    cbn. lia.
    cbn. unfold perm. intros. rewrite count_app. apply count_filter.
Defined.

Definition qs2 A :=
  uqs (AdHocSort_id A) (Pivot_head A) (Partition_bifilter A).

#[refine]
Instance Small_length (A : Ord) (n : nat) : Small A :=
{
    small l :=
    match l with
        | [] => inl []
        | h :: t =>
            if Nat.leb (length l) n then inl l else inr (h, t)
    end
}.
Proof.
  destruct l; inv 1. destruct n.
    inv H1.
    destruct (Nat.leb (length l) n); inv H1.
  destruct l; inv 1. destruct n.
    inv H1.
    destruct (Nat.leb (length l) n); inv H1.
Defined.

#[refine]
Instance AdHocSort_Sort
  {A : Ord} (small : Small A) (sort : Sort trich_le) : AdHocSort small :=
{
    adhoc := sort
}.
Proof.
  intros. apply Sorted_sort.
  intros. apply sort_perm.
Defined.

Definition hqs
  (n : nat) (A : Ord) (sort : Sort trich_le) (l : list A) : list A :=
    uqs (AdHocSort_Sort (Small_length A n) sort)
        (Pivot_head A) (Partition_bifilter A) l.