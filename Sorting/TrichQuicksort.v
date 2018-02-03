Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export TrichDec.

Set Implicit Arguments.

Local Hint Unfold lt.
Local Hint Resolve le_n_S filter_length.

Function htqs (n : nat) (A : TrichDec) (sort : list A -> list A) (l : list A)
  {measure length l} : list A :=
if @TrichDec_ltb natlt (length l) (S n)
then sort l
else match l with
    | [] => []
    | h :: t =>
        let '(lo, eq, hi) := trifilter h t in
          htqs n A sort lo ++ h :: eq ++ htqs n A sort hi
end.
Proof.
  intros. rewrite trifilter_spec in teq1. inversion teq1; subst; cbn.
    pose (filter_length (fun x => h <? x) t). omega.
  intros. rewrite trifilter_spec in teq1. inversion teq1; subst; cbn.
    pose (filter_length (fun x => x <? h) t). omega.
Defined.

Definition tqs (A : TrichDec) (l : list A) : list A :=
  htqs 0 A (fun l => l) l.

Function htqs2
  (n : nat) (A : TrichDec)
  (sort : list A -> list A) (partition : Partition A)
  (l : list A) {measure length l} : list A :=
    if @TrichDec_ltb natlt (length l) (S n)
    then sort l
    else match l with
        | [] => []
        | h :: t =>
            let '(lo, eq, hi) := partition h t in
              htqs2 n sort partition lo ++
              h :: eq ++
              htqs2 n sort partition hi
    end.
Proof.
  intros. apply len_hi in teq1. cbn. unfold lt. apply le_n_S. assumption.
  intros. apply len_lo in teq1. cbn. unfold lt. apply le_n_S. assumption.
Defined.

Arguments htqs2 _ _ _ _ : clear implicits.

Instance Trifilter (A : TrichDec) : Partition A :=
{
    partition := trifilter
}.
Proof.
  all: intros.
    functional induction trifilter pivot l; inv H; trich.
      inv H0. 1-3: eapply IHp; eauto.
    functional induction trifilter pivot l; inv H; trich.
      inv H0. eapply IHp; eauto.
    functional induction trifilter pivot l; inv H; trich.
      1-2: eapply IHp; eauto.
      inv H0.
        split; intro; trich.
        eapply IHp; eauto.
    1-3: rewrite trifilter_spec in H; inv H.
    unfold perm. intro.
      functional induction trifilter pivot l; cbn; inv H; trich;
      specialize (IHp _ _ _ e0); rewrite IHp, !count_app; cbn;
      rewrite ?count_app; trich.
Defined.

Definition wut (A : TrichDec) (l : list A) : list A :=
  htqs2 0 A (fun l => l) (Trifilter A) l.

(*Time Compute wut natlt (cycle 30 testl).
Time Compute tqs natlt (cycle 3000 testl).
Time Compute tqs natlt (cycle 1500 [1]).*)