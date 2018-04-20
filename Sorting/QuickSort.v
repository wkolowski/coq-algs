Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import InsertionSort.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

Function qs (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => qs A (filter (fun x : A => leqb x h) t) ++
           h :: qs A (filter (fun x : A => negb (leqb x h)) t)
end.
Proof. all: simpl; auto. Defined.

Local Hint Extern 0 (length _ < length _) =>
match goal with
    | H : bifilter _ _ = _ |- _ => rewrite bifilter_spec in H; inversion H;
        apply filter_lengthOrder
end.

Function qs2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t =>
        let (lo, hi) := bifilter (fun x : A => x <=? h) t in
        qs2 A lo ++ h :: qs2 A hi
end.
Proof. all: auto. Defined.

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

Function ghqs
  (n : nat) (A : LinDec)
  (sort : Sort) (*list A -> list A)*) (partition : Partition A)
  (l : list A) {measure length l} : list A :=
    if @leqb natle (length l) (S n)
    then sort A l
    else match l with
        | [] => []
        | h :: t =>
            let '(lo, eq, hi) := partition h t in
              ghqs n sort partition lo ++
              h :: eq ++
              ghqs n sort partition hi
    end.
Proof.
  intros. apply len_hi in teq1. cbn. omega.
  intros. apply len_lo in teq1. cbn. omega.
Defined.

Arguments ghqs _ _ _ _ _ : clear implicits.

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

Function ultimate_qs
  (A : LinDec)
  (small : Small A)
  (sort : Sort)
  (choosePivot : Pivot A)
  (partition : Partition A)
  (l : list A)
  {measure length l} : list A :=
match small l with
    | inl l' => sort A l'
    | inr (h, t) =>
        let
          '(pivot, rest) := choosePivot h t
        in
        let
          '(lo, eq, hi) := partition pivot rest
        in
        ultimate_qs small sort choosePivot partition lo ++
        pivot :: eq ++
        ultimate_qs small sort choosePivot partition hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply pivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; omega.
Defined.