Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Sort.

Set Implicit Arguments.

Fixpoint ins (A : LinDec) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if x <=? h then x :: h :: t else h :: (ins A x t)
end.

Definition insertionSort (A : LinDec) (l : list A)
    : list A := fold_right (ins A) [] l.

Eval compute in insertionSort natle testl.

Lemma perm_ins: forall (A : LinDec) (x : A) (l : list A),
    perm A (x :: l) (ins A x l).
Proof.
  unfold perm; intros. induction l.
    reflexivity.
    unfold ins; destruct (leqb x a); fold ins.
      reflexivity.
      rewrite (perm_swap A x a l l (perm_refl A l)).
        cbn. rewrite <- IHl. reflexivity.
Qed.

Lemma ins_sorted : forall (A : LinDec) (x : A) (l : list A),
    sorted A l -> sorted A (ins A x l).
Proof.
  induction l as [| h t]; intros; cbn.
    constructor.
    destruct (leqb_spec x h).
      auto.
      induction t as [| h' t']; cbn in *.
        repeat constructor.
          destruct (leq_total h x); auto.
        destruct (leqb_spec x h'); intros.
          constructor.
            destruct (leq_total x h); auto.
            constructor. eauto. eapply sorted_tail. eauto.
            constructor.
              inversion H. auto.
              apply IHt; auto. eapply sorted_tail; eauto.
Restart.
  induction l as [| h t]; intros; cbn.
    constructor.
    dec. induction t as [| h' t']; cbn in *; dec.
Qed.

Instance Sort_insertionSort : Sort :=
{
    sort := insertionSort
}.
Proof.
  induction l as [| h t]; simpl; auto.
    apply ins_sorted. assumption.
  induction l as [| h t]; simpl; auto.
    apply perm_trans with (h :: insertionSort A t); auto. apply perm_ins.
Defined.

Eval cbv in sort testl.