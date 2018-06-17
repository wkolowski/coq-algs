Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.

Set Implicit Arguments.

Fixpoint ins (A : LinDec) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if x <=? h then x :: h :: t else h :: (ins A x t)
end.

Definition insertionSort (A : LinDec) (l : list A)
  : list A := fold_right (ins A) [] l.

Lemma perm_ins :
  forall (A : LinDec) (x : A) (l : list A),
    perm A (x :: l) (ins A x l).
Proof.
  unfold perm; intros. induction l.
    reflexivity.
    unfold ins; destruct (leqb x a); fold ins.
      reflexivity.
      rewrite (perm_swap A x a l l (perm_refl A l)).
        cbn. rewrite <- IHl. reflexivity.
Qed.

Lemma sorted_ins :
  forall (A : LinDec) (x : A) (l : list A),
    sorted A l -> sorted A (ins A x l).
Proof.
  induction l as [| h t]; intros; cbn.
    constructor.
    dec. induction t as [| h' t']; cbn in *; dec.
Qed.

Instance Sort_insertionSort (A : LinDec) : Sort A :=
{
    sort := insertionSort A
}.
Proof.
  induction l as [| h t]; cbn; auto.
    apply sorted_ins. assumption.
  induction l as [| h t]; simpl; auto.
    apply perm_trans with (h :: insertionSort A t); auto. apply perm_ins.
Defined.

(** Better insertion sort. *)

Fixpoint ins'
  {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if cmp x h then x :: h :: t else h :: (ins' cmp x t)
end.

Definition insertionSort'
  {A : Type} (cmp : A -> A -> bool) (l : list A) : list A :=
    fold_right (ins' cmp) [] l.

Coercion leqb : LinDec >-> Funclass.

Lemma perm_ins' :
  forall (A : LinDec) (x : A) (l : list A),
    perm A (x :: l) (ins' A x l).
Proof.
  unfold perm. induction l; cbn; intros.
    reflexivity.
    unfold ins'; destruct (leqb x a); fold (@ins' A).
      reflexivity.
      dec; rewrite <- IHl; cbn; dec.
Qed.

Lemma sorted_ins' :
  forall (A : LinDec) (x : A) (l : list A),
    sorted A l -> sorted A (ins' A x l).
Proof.
  induction l as [| h t]; cbn; intros.
    constructor.
    dec. induction t as [| h' t']; cbn in *; dec.
Qed.

Instance Sort_insertionSort' (A : LinDec) : Sort A :=
{
    sort := insertionSort' A
}.
Proof.
  induction l as [| h t]; cbn; auto.
    apply sorted_ins'. assumption.
  induction l as [| h t]; simpl; auto.
    apply perm_trans with (h :: insertionSort' A t), perm_ins'; auto.
Defined.