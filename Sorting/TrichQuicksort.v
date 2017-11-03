Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import TrichDec.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

Function htqs (n : nat) (A : TrichDec) (sort : list A -> list A) (l : list A)
  {measure length l} : list A :=
if @trichb_ltb natlt (length l) (S n)
then sort l
else match l with
    | [] => []
    | h :: t =>
        let '(lo, eq, hi) := trifilter' h t in
          htqs n A sort lo ++ h :: eq ++ htqs n A sort hi
end.
Proof.
  intros. rewrite trifilter'_spec in teq1. inversion teq1; subst; cbn.
    pose (filter_length (fun x => h <? x) t). omega.
  intros. rewrite trifilter'_spec in teq1. inversion teq1; subst; cbn.
    pose (filter_length (fun x => x <? h) t). omega.
Defined.

Definition tqs (A : TrichDec) (l : list A) : list A :=
  htqs 0 A (fun l => l) l.

Function htqs2
  (n : nat) (A : TrichDec)
  (sort : list A -> list A) (partition : Partition A)
  (l : list A) {measure length l} : list A :=
    if @trichb_ltb natlt (length l) (S n)
    then sort l
    else match l with
        | [] => []
        | h :: t =>
            let '(lo, eq, hi) := partition h t in
              htqs2 n A sort partition lo ++
              h :: eq ++
              htqs2 n A sort partition hi
    end.
Proof.
  intros. apply spec_hi in teq1. cbn. omega.
  intros. apply spec_lo in teq1. cbn. omega.
Defined.

Instance Trifilter (A : TrichDec) : Partition A :=
{
    partition := trifilter'
}.
Proof.
  intros. rewrite trifilter'_spec in H. inversion H; subst; cbn.
    apply filter_length.
  intros. rewrite trifilter'_spec in H. inversion H; subst; cbn.
    apply filter_length.
Defined.

Definition wut (A : TrichDec) (l : list A) : list A :=
  htqs2 0 A (fun l => l) (Trifilter A) l.

Time Compute wut natlt (cycle 30 testl).
Time Compute tqs natlt (cycle 3000 testl).
Time Compute tqs natlt (cycle 1500 [1]).