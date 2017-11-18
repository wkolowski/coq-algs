Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.
Require Import Omega.
Require Import Recdef.

Definition divF (f : nat -> forall k : nat, 0 < k -> nat)
  (n k : nat) (H : 0 < k) : nat :=
match le_lt_dec k n with
    | left _ => S (f (n - k) k H)
    | right _ => 0
end.

Arguments iter [A] _ _.

Theorem divF_terminates :
  forall (n k : nat) (H : 0 < k),
    {v : nat | exists p : nat, forall n_iter : nat, p < n_iter ->
      forall f : forall n k : nat, 0 < k -> nat,
         iter n_iter divF f n k H = v}.
Proof.
  intros. generalize dependent n.
  apply well_founded_induction_type with lt.
    apply lt_wf.
    intros. case_eq (le_lt_dec k x); intro.
      Focus 2. exists 0. exists 0. intros. destruct n_iter; cbn.
        omega.
        unfold divF. rewrite H1. trivial.
      destruct (H0 (x - k)) as [v Hv].
        omega.
        exists (S v). destruct Hv as [p Hp]. exists (S p). intros.
          destruct (n_iter); cbn.
            omega.
            unfold divF. rewrite H1. f_equal. apply Hp. omega.
Defined.

Definition div (n k : nat) (H : 0 < k) : nat :=
  proj1_sig (divF_terminates n k H).

Require Import RCCBase.

Theorem div_fix : div = divF div.
Proof.
  ext n; ext k; ext H.
  unfold div at 1. destruct (divF_terminates n k H). cbn.
  destruct e as [p Hp]. assert (p < S p) by omega.
  rewrite <- (Hp _ H0 div). cbn. clear Hp. gen H; gen k; gen n.
  induction p as [| p'].
    trivial.
    f_equal.
Restart.
  ext n. gen n. apply (@well_founded_induction _ _ lt_wf).
  intros n IH. ext k; ext H. unfold divF.
  case_eq (le_lt_dec k n); intros.
    Focus 2. unfold div. destruct (divF_terminates _ _ _). cbn.
      destruct e as [p Hp]. erewrite <- (Hp (S p)).
        cbn. unfold divF. rewrite H0. trivial.
        omega.
    assert (n - k < n) by omega. specialize (IH _ H1).
      assert (div (n - k) k H = divF div (n - k) k H). congruence. clear IH.
      unfold divF in H2. case_eq (le_lt_dec k (n - k)); intros.
        unfold div in *.
        destruct (divF_terminates (n - k) k H),
                 (divF_terminates n k H).
Abort.

Lemma div_equation :
  forall (n k : nat) (H : 0 < k),
    div n k H =
    if le_lt_dec k n then S (div (n - k) k H) else 0.
Proof.
  intros. generalize dependent n.
  apply (@well_founded_induction_type _ _ lt_wf); intros. unfold div.
  destruct (divF_terminates x k H), (divF_terminates (x -k) k H); cbn.
  destruct e as [p Hp], e0 as [p' Hp'].
  case_eq (le_lt_dec k x); intros.
    Focus 2. erewrite <- (Hp (S p)).
      cbn. unfold divF. rewrite H1. trivial.
      omega.
    erewrite <- (Hp (S p)), <- (Hp' (S p')). case_eq (le_lt_dec k (x - k)); intros.
      cbn. unfold divF. rewrite ?H1, ?H2. fold divF.
      assert (x - k < x) by omega. specialize (H0 _ H3).
      rewrite H2 in H0. unfold div in H0.
        
Restart.
  intros. unfold div.
  destruct (divF_terminates n k H),
           (divF_terminates (n - k) k H); intros. cbn.
  destruct e as [p Hp], e0 as [p' Hp'].
  case_eq (le_lt_dec k n); intros; cbn.
    Focus 2. erewrite <- (Hp (S p)).
      cbn. unfold divF. rewrite H0. trivial.
      omega.
    case_eq (le_lt_dec p p'); intros.
      assert (p < S (p + p')) by omega.
        erewrite <- (Hp (S p')), <- (Hp' p'). cbn. unfold divF.
        rewrite H0. fold divF. reflexivity.
Restart.
  intros. unfold div at 1. destruct (divF_terminates n k H). cbn.
  case_eq (le_lt_dec k n); intros.
    destruct e as [p Hp]. erewrite <- (Hp (S p)). cbn. unfold divF.
      rewrite H0. fold divF. unfold div.
      destruct (divF_terminates (n - k) k H). cbn. destruct e as [p' Hp'].
        rewrite Hp'. all: auto. 
Abort.

Inductive divR' : nat -> nat -> nat -> Prop :=
    | div_base :
        forall (n k : nat), 0 < k -> n < k -> divR' n k 0
    | div_rec :
        forall (n k r : nat), 0 < k -> k <= n ->
          divR' (n - k) k r -> divR' n k (S r).

Hint Constructors divR'.

Lemma divR'_correct :
  forall (n k r : nat) (H : 0 < k),
    div n k H = r -> divR' n k r.
Proof.
  apply (@well_founded_induction nat lt lt_wf
    (fun n : nat => forall (k r : nat) (H : 0 < k ),
      div n k H = r -> divR' n k r)).
  intros. rewrite div_equation' in H1. destruct (le_lt_dec k x); subst.
    Focus 2. constructor; auto.
    constructor; auto. apply H with H0; omega.
Qed.

Lemma divR'_complete :
  forall (n k r : nat) (H : 0 < k),
    divR' n k r -> div n k H = r.
Proof.
  induction 1.
    apply div_lt_n_k. assumption.
    rewrite <- IHdivR' with H. rewrite div_le_k_n; auto.
Qed.

Theorem div_ind :
  forall P : nat -> nat -> nat -> Prop,
    (forall n k : nat, 0 < k -> n < k -> P n k 0) ->
    (forall (n k : nat) (H : 0 < k), k <= n ->
      P (n - k) k (div (n - k) k H) -> P n k (S (div (n - k) k H))) ->
        forall (n k : nat) (H : 0 < k), P n k (div n k H).
Proof.
  intros. apply divR'_ind; intros.
    apply H; auto.
    eapply (divR'_complete _ _ _ H2) in H4. subst. apply H0; assumption.
    apply divR'_correct with H1. reflexivity.
Qed.