Require Import Sort.

(* Insertion sort *)
Fixpoint fold {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
match l with
    | [] => b
    | h :: t => f h (fold f b t)
end.

Fixpoint ins (A : LinDec) (a : A) (l : list A) : list A :=
match l with
    | [] => [a]
    | h :: t => if leqb a h then a :: h :: t else h :: (ins A a t)
end.

Definition insertionSort (A : LinDec) (l : list A)
    : list A := fold (ins A) [] l.

Eval compute in insertionSort natle testl.

Lemma perm_ins: forall (A : LinDec) (x : A) (l : list A),
    perm A (x :: l) (ins A x l).
Proof.
  unfold perm; intros. induction l.
    reflexivity.
    unfold ins; destruct (leqb x a); fold ins.
      reflexivity.
      rewrite (perm_swap A x a l l (perm_refl A l)).
        simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma ins_sorted : forall (A : LinDec) (x : A) (l : list A),
    sorted A l -> sorted A (ins A x l).
Proof.
  induction l as [| h t]; intros; simpl.
    constructor.
    unfold leqb. destruct (leq_dec x h).
      eauto with sort.
      induction t as [| h' t']; simpl in *.
        repeat constructor.
          destruct (leq_total h x); eauto. contradiction.
        unfold leqb in *. destruct (leq_dec x h'); intros.
          constructor.
            destruct (leq_total x h); auto. contradiction.
            constructor. eauto. eapply sorted_inv. eauto.
            constructor.
              inversion H. auto.
              apply IHt; auto. eapply sorted_inv; eauto.
Qed.

Definition sort : forall (A : LinDec) (l : list A),
    {l' : list A | perm A l l' /\ sorted A l'}.
Proof.
  induction l as [| h t].
    exists nil. auto with sort.
    destruct IHt as [l' [Hperm Hsorted]]. exists (ins A h l'). split.
      apply perm_trans with (h :: l').
        auto with sort.
        apply perm_ins.
      apply ins_sorted; assumption.
Defined.

Definition sort' (A : LinDec) (l : list A) : list A :=
    proj1_sig (sort A l).

Definition sort'_inv (A : LinDec) (l : list A) : list A :=
    proj1_sig (sort (DualLinDec A) l).

(* Tried to prove that quicksort gives a permutation, but failed. *)
(*Lemma nb_occ_app : forall (A : LinDec) (l1 l2 : list A) (x : A),
    nb_occ A x (l1 ++ l2) = nb_occ A x (l2 ++ l1).
Proof.
  induction l1 as [| h t]; induction l2 as [| h' t']; simpl;
  intros; repeat rewrite app_nil_r; auto. simpl in *.
  case_eq (LinDec_eq x h); case_eq (LinDec_eq x h'); intros.
  f_equal. assert (h = h'). unfold LinDec_eq in H. 
    

Lemma perm_app : forall (A : LinDec) (l1 l2 : list A),
    perm A (l1 ++ l2) (l2 ++ l1).
Proof.
  induction l1 as [| h t].
    simpl. intro. rewrite app_nil_r. apply perm_refl.
    simpl. induction l2 as [| h' t'].
      simpl. rewrite app_nil_r. apply perm_refl.
      simpl. SearchAbout perm. Print perm.

Lemma perm_lemma : forall (A : LinDec) (h : A) (t l1 l2 : list A),
    perm A t (l1 ++ l2) -> perm A (h :: t) (l1 ++ h :: l2).
Proof.
  intros.

Program Fixpoint qs' (A : LinDec) (l : list A) {measure (length l)}
    : {l' : list A | perm A l l'} :=
match l with
    | nil => nil
    | h :: t => qs' A (filter (fun x : A => leqb x h) t) ++ [h]
             ++ qs' A (filter (fun x : A => negb (leqb x h)) t)
end.
Next Obligation. constructor. Qed.
Next Obligation. simpl. unfold lt. auto. Qed.
Next Obligation. simpl. unfold lt. auto. Qed.
Next Obligation. *)


Print testl.
Eval cbv in min natle_min (remove eq_nat_dec 0 testl).


Print testl.

Time Eval cbv in sort' natle testl. (* Insertion sort *)
Time Eval cbv in selectionSort natle_min testl.
Time Eval cbv in qs natle testl.
Time Eval cbv in mergeSort natle testl.

Time Eval cbv in sort'_inv natle testl.

Time Eval cbv in sort' nat_evenle testl.
Time Eval cbv in sort'_inv nat_evenle testl.

Fixpoint to0 (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: to0 n'
end.

Eval cbv in to0 5.

Fixpoint length_less {A : Type} (n : nat) (l : list A) : bool :=
match n, l with
    | _, [] => true
    | 0, _ => false
    | S n', h :: t => length_less n' t
end.

Program Fixpoint ms2 (A : LinDec) (l : list A)  {measure (length l)} : list A :=
(*if le_dec (length l) 6*)
if length_less 6 l
then sort' A l
else
      let n := div2 (length l) in
      let l1 := take n l in
      let l2 := drop n l in
      merge A (ms2 A l1) (ms2 A l2).
(*Next Obligation.
  apply take_length2. apply lt_div2. destruct l; simpl in *;
  try (contradiction H0; auto; fail); try omega. Qed.
Next Obligation.
  apply drop_length2; auto.
    destruct l; simpl in *. omega.
      destruct l; simpl in *; omega.
    intro. subst. simpl in H. omega.
Defined.*)
Next Obligation. admit. Defined.
Next Obligation. admit. Defined.

Fixpoint repeat {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ repeat n' l
end.

Definition testl2 := repeat 50 testl.

(*Time Eval cbv in selectionSort natle_min (to0 15).*)
(*Time Eval cbv in qs natle (to0 32).
Time Eval cbv in sort' natle (to0 16).
Time Eval cbv in mergeSort natle (to0 32).
Time Eval cbv in ms2 natle (to0 100).

Time Eval cbv in qs natle testl2.
Time Eval cbv in mergeSort natle testl2.
Time Eval cbv in ms2 natle testl2.*)



(*Theorem selectionSort_perm : forall (A : LinDecMin) (l : list A),
    perm A l (selectionSort A l).
Proof.
  intros. destruct l.
    compute. intros _. auto.
    compute.*)

Class DenseOrd : Type :=
{
    lin' :> Lin;
    dense : lin' -> lin' -> lin';
    is_dense : forall x y : lin', leq x (dense x y) /\ leq (dense x y) y
}.