Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import InsertionSort.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

(* TODO: remove *)
(*Function qs (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => qs A (filter (fun x : A => leqb x h) t) ++
           h :: qs A (filter (fun x : A => negb (leqb x h)) t)
end.
Proof. all: simpl; auto. Defined.*)

Local Hint Extern 0 (length _ < length _) =>
match goal with
    | H : bifilter _ _ = _ |- _ => rewrite bifilter_spec in H; inversion H;
        apply filter_lengthOrder
end.

(* TODO: remove *)
(*Function qs2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t =>
        let (lo, hi) := bifilter (fun x : A => x <=? h) t in
        qs2 A lo ++ h :: qs2 A hi
end.
Proof. all: auto. Defined.*)

(* TODO: remove *)
Function hqs (n : nat) (A : LinDec) (sort : list A -> list A) (l : list A)
  {measure length l} : list A :=
  if @leqb natle (length l) n
  then sort l
  else match l with
      | [] => []
      | h :: t =>
          let (lo, hi) := bifilter (fun x : A => x <=? h) t in
              hqs n A sort lo ++ h :: hqs n A sort hi
  end.
Proof. all: auto. Defined.

(** Time to generalize [ghqs]:
    - Rather that [n], the length of the desired "small list",
      we will just give some function that determines if the
      input list is small enough (and if not, if returns an
      element of the list and the rest of the list)
    - [sort] remains there
    - [pivot] will be a procedure for choosing the pivot (it
      needs a default element as an argument)
    - [partition] stays there]
*)

Class Small (A : LinDec) : Type :=
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

Class Pivot (A : LinDec) : Type :=
{
    pivot : A -> list A -> A * list A;
    pivot_spec :
      forall (h h' : A) (t t' : list A),
        pivot h t = (h', t') -> Permutation (h :: t) (h' :: t')
}.

Coercion pivot : Pivot >-> Funclass.

Class AdHocSort {A : LinDec} (small : Small A) : Type :=
{
    adhoc :> list A -> list A;
    adhoc_sorted :
      forall l l' : list A,
        small l = inl l' -> sorted A (adhoc l');
    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm A l' (adhoc l');
}.

Coercion adhoc : AdHocSort >-> Funclass.

Function ultimate_qs
  (A : LinDec)
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
          ultimate_qs adhoc choosePivot partition lo ++
          pivot :: eq ++
          ultimate_qs adhoc choosePivot partition hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply pivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; omega.
Defined.

(** Ordinary quicksort using [ultimate_qs] *)

Instance head_Small (A : LinDec) : Small A :=
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

Instance head_Pivot (A : LinDec) : Pivot A :=
{
    pivot :=
      fun (h : A) (t : list A) => (h, t)
}.
Proof. inv 1. Defined.

Instance bifilter_Partition (A : LinDec) : Partition A :=
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

Instance id_AdHocSort (A : LinDec) : AdHocSort (head_Small A) :=
{
    adhoc := id;
}.
Proof.
  all: destruct l; inv 1; constructor.
Defined.

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
  ultimate_qs (id_AdHocSort A) (head_Pivot A) (Partition_filter A).

Definition qs2 A :=
  ultimate_qs (id_AdHocSort A) (head_Pivot A) (bifilter_Partition A).

Compute qs2 natle [4; 3; 2; 1].

(** Like [ultimate_qs], but additionally has knowledge about the
    recursion's depth. *)

(*Function ultimate_qs
  (A : LinDec)
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
          ultimate_qs adhoc choosePivot partition lo ++
          pivot :: eq ++
          ultimate_qs adhoc choosePivot partition hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply pivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; omega.
Defined.*)
