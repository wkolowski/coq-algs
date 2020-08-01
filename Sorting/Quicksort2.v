Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export ListLemmas.
Require Export Sorting.Sort.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

Local Hint Extern 0 (length _ < length _) =>
match goal with
    | H : bifilter _ _ = _ |- _ => rewrite bifilter_spec in H; inversion H;
        apply filter_lengthOrder
end.

Class QSArgs (A : Type) : Type :=
{
    small : list A -> list A + A * list A;
    small_inr :
      forall (h : A) (t l : list A),
         small l = inr (h, t) -> Permutation l (h :: t);
    adhoc : list A -> list A;
    choosePivot : A -> list A -> A * list A;
    choosePivot_spec :
      forall (h h' : A) (t t' : list A),
        choosePivot h t = (h', t') -> Permutation (h :: t) (h' :: t');
    partition : A -> list A -> list A * list A * list A;
    len_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length lo <= length l;
    len_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length hi <= length l;
}.

Function uqs
  (A : Type)
  (args : QSArgs A)
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
          uqs args lo ++ pivot :: eq ++ uqs args hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply choosePivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; omega. Show Proof.
Defined.

Class VerifiedQSArgs (A : Type) : Type :=
{
    args :> QSArgs A;
    rel : A -> A -> Prop;
    Sorted_adhoc :
      forall l1 l2 : list A,
        small l1 = inl l2 -> Sorted rel (adhoc l2);
(*    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm l' (adhoc l');*)
}.

Arguments rel {A} _.

Coercion args : VerifiedQSArgs >-> QSArgs.

Theorem Sorted_uqs :
  forall
    {A : Type} (vqsa : VerifiedQSArgs A) (l : list A),
      @Sorted A (rel vqsa) (uqs vqsa l).
Proof.
  intros.
  functional induction (uqs vqsa l).
    apply (Sorted_adhoc l). assumption.
    (*apply small_inr in e. apply pivot_spec in e0.*)
    apply Sorted_app_all; try assumption.
      apply Sorted_cons.
        intros. apply in_app_or in H. destruct H.
          admit. (*erewrite spec_eq; eauto.*)
          admit. (*eapply spec_hi; eauto. eapply uqs_In; eauto.*)
        apply Sorted_app; auto.
          assert (forall x : A, In x eq -> x = pivot).
            admit. (*eapply spec_eq; eauto.*)
            clear e1. induction eq; auto. destruct eq; auto. constructor.
              rewrite (H a), (H a0); cbn; auto. admit.
              apply IHeq. intro. inv 1; apply H; cbn; auto.
          intros. apply uqs_In in H0.
            erewrite (spec_eq pivot) at 1; eauto.
              eapply spec_hi; eauto.
        intros. apply uqs_In in H. eapply spec_lo; eauto.
Qed.


(** Ordinary quicksort using [uqs] *)

(*

#[refine]
Instance Small_head (A : LinDec) : Small A :=
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
Instance AdHocSort_id (A : LinDec) : AdHocSort (Small_head A) :=
{
    adhoc := id;
}.
Proof.
  all: destruct l; inv 1; constructor.
Defined.

#[refine]
Instance Pivot_head (A : LinDec) : Pivot A :=
{
    pivot :=
      fun (h : A) (t : list A) => (h, t)
}.
Proof. inv 1. Defined.

#[refine]
Instance Partition_filter (A : LinDec) : Partition A :=
{
    partition x l :=
      (filter (fun y => y <=? x) l, [],
       filter (fun y => negb (y <=? x)) l)
}.
Proof.
  all: intros; inv H.
    rewrite filter_In in H0. firstorder dec.
    rewrite filter_In in H0. dec.
      destruct H0. inv H0.
      destruct H0. apply LinDec_not_leq_lt in n. firstorder.
    cbn. omega.
    cbn. unfold perm. intros. rewrite count_app. apply count_filter.
Defined.

Definition qs A :=
  uqs (AdHocSort_id A) (Pivot_head A) (Partition_filter A).

#[refine]
Instance Partition_bifilter (A : LinDec) : Partition A :=
{
    partition x l :=
      let '(lo, hi) := bifilter (fun y => y <=? x) l in (lo, [], hi)
}.
Proof.
  all: intros; rewrite bifilter_spec in H; inv H.
    apply filter_In in H0. firstorder dec.
    apply filter_In in H0. dec.
      destruct H0. inv H0.
      destruct H0. apply LinDec_not_leq_lt in n. firstorder.
    cbn. omega.
    cbn. unfold perm. intros. rewrite count_app. apply count_filter.
Defined.

Definition qs2 A :=
  uqs (AdHocSort_id A) (Pivot_head A) (Partition_bifilter A).

#[refine]
Instance Small_length (A : LinDec) (n : nat) : Small A :=
{
    small l :=
    match l with
        | [] => inl []
        | h :: t =>
            if @leqb natle (length l) n then inl l else inr (h, t)
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
  {A : LinDec} (small : Small A) (sort : Sort A) : AdHocSort small :=
{
    adhoc := sort
}.
Proof.
  intros. apply Sorted_sort.
  intros. apply sort_perm.
Defined.

Definition hqs
  (n : nat) (A : LinDec) (sort : Sort A) (l : list A) : list A :=
    uqs (AdHocSort_Sort (Small_length A n) sort)
        (Pivot_head A) (Partition_bifilter A) l.

*)