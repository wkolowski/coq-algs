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

Lemma Permutation_Forall :
  forall {A : Type} {P : A -> Prop} {l1 l2 : list A},
    Permutation l1 l2 ->
      Forall P l1 -> Forall P l2.
Proof.
  intros until 2. revert l2 H.
  induction H0; intros.
    destruct l2.
      constructor.
      unfold Permutation in H. specialize (H (fun _ => true)).
        inversion H.
    destruct l2 as [| h2 t2].
      unfold Permutation in H1. specialize (H1 (fun _ => true)).
        inversion H1.
      apply IHForall; clear IHForall. unfold Permutation in *.
        intro p. cbn in *. specialize (H1 p). destruct (p h2).
Admitted.