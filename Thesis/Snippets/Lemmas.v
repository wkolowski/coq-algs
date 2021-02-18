Require Export List Setoid Arith Specification.

Lemma Permutation_refl :
  forall {A : Type} {l : list A},
    Permutation l l.
Proof.
  unfold Permutation.
  reflexivity.
Qed.

Lemma Permutation_symm :
  forall {A : Type} (l1 l2 : list A),
    Permutation l1 l2 -> Permutation l2 l1.
Proof.
  unfold Permutation. congruence.
Qed.

Lemma Permutation_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Permutation l1 l2 ->
    Permutation l2 l3 ->
      Permutation l1 l3.
Proof.
  unfold Permutation.
  congruence.
Qed.

Instance Equivalence_Permutation
  (A : Type) : Equivalence (@Permutation A).
Proof.
  split; red; unfold Permutation; congruence.
Defined.

Lemma Permutation_cons :
  forall {A : Type} {h : A} {t1 t2 : list A},
    Permutation t1 t2 ->
      Permutation (h :: t1) (h :: t2).
Proof.
  unfold Permutation.
  cbn. congruence.
Qed.

Lemma Permutation_swap :
  forall {A : Type} {x y : A} {l : list A},
    Permutation (y :: x :: l) (x :: y :: l).
Proof.
  unfold Permutation.
  cbn; intros.
  destruct (p x), (p y); reflexivity.
Qed.

Lemma count_app :
  forall {A : Type} (p : A -> bool) (l1 l2 : list A),
    count p (l1 ++ l2) = count p l1 + count p l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite IHt1, Nat.add_assoc. reflexivity.
Qed.

Lemma Permutation_app :
  forall {A : Type} {l1 l2 l1' l2' : list A},
    Permutation l1 l1' ->
    Permutation l2 l2' ->
      Permutation (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold Permutation.
  intros.
  rewrite !count_app, H, H0.
  reflexivity.
Qed.

Lemma Permutation_app_symm :
  forall {A : Type} (l1 l2 : list A),
    Permutation (l1 ++ l2) (l2 ++ l1).
Proof.
  unfold Permutation.
  intros. rewrite !count_app. apply Nat.add_comm.
Qed.

Lemma count_length :
  forall {A : Type} (p : A -> bool) (l : list A),
    count p l <= length l.
Proof.
  induction l as [| h t]; cbn.
    constructor.
    destruct (p h).
      apply le_n_S. assumption.
      constructor. assumption.
Qed.

Require Import Lia.

Lemma Forall_count :
  forall {A : Type} {p : A -> bool} {l : list A},
    Forall (fun x => p x = true) l <-> count p l = length l.
Proof.
  induction l as [| h t]; cbn.
    split; constructor.
    split.
      inversion 1. rewrite H2. cbn. f_equal. rewrite <- IHt. assumption.
      constructor.
        destruct (p h) eqn: Hph.
          reflexivity.
          cbn in H. pose (count_length p t). lia.
        destruct (p h) eqn: Hph.
          inversion H. rewrite IHt. assumption.
          cbn in H. pose (count_length p t). lia.
Qed.

Lemma count_true :
  forall {A : Type} (l : list A),
    count (fun _ => true) l = length l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.

Lemma Permutation_Forall :
  forall {A : Type} {p : A -> bool} {l1 l2 : list A},
    Permutation l1 l2 ->
      Forall (fun x => p x = true) l1 -> Forall (fun x => p x = true) l2.
Proof.
  unfold Permutation.
  intros A p l1 l2 HP HF.
  rewrite Forall_count.
  rewrite Forall_count in HF.
  rewrite <- HP, HF.
  specialize (HP (fun _ => true)).
  rewrite 2!count_true in HP.
  assumption.
Qed.