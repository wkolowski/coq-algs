Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

From CoqAlgs Require Export Sorting.Sort.
From CoqAlgs Require Export ListLemmas.

(* From CoqAlgs Require Import InsertionSort. *)

Set Implicit Arguments.

Function merge (A : Ord) (l : list A * list A)
  {measure lenSum l} : list A :=
  let (l1, l2) := l in
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h :: t, h' :: t' =>
        if h ≤? h'
        then h :: merge A (t, l2)
        else h' :: merge A (l1, t')
end.
Proof.
  intros. unfold lenSum. simpl. lia.
  intros. unfold lenSum. simpl. lia.
Defined.

Theorem Sorted_merge :
  forall (A : Ord) (l : list A * list A),
    Sorted trich_le (fst l) -> Sorted trich_le (snd l) -> Sorted trich_le (merge A l).
Proof.
  intros.
  functional induction merge A l; cbn in *.
    assumption.
    assumption.
    1-2: rewrite merge_equation in *.
      inv H.
        constructor; trich.
        trich; constructor; trich.
      inv H0.
        constructor; trich.
        trich; constructor; trich.
Qed.

Theorem merge_perm :
  forall (A : Ord) (l : list A * list A),
    perm (fst l ++ snd l) (merge A l).
Proof.
  intros. functional induction merge A l; simpl; auto; try clear y.
    rewrite app_nil_r. auto.
    eapply Perm.perm_trans.
      rewrite app_comm_cons. apply perm_app_comm.
      simpl. apply perm_cons. simpl in IHl0. rewrite <- IHl0.
        apply perm_app_comm.
Qed.

Theorem Permutation_merge :
  forall (A : Ord) (l : list A * list A),
    Permutation (fst l ++ snd l) (merge A l).
Proof.
  intros. functional induction merge A l; cbn in *.
    reflexivity.
    rewrite app_nil_r. auto.
    constructor. assumption.
    rewrite Permutation_app_comm. cbn. rewrite Permutation.perm_swap.
      constructor. rewrite Permutation_app_comm. assumption.
Qed.

Theorem merge_pres_perm :
  forall (A : Ord) (l1 l1' l2 l2' : list A),
    perm l1 l1' -> perm l2 l2' ->
      perm (merge A (l1, l2)) (merge A (l1', l2')).
Proof.
  intros. rewrite <- !merge_perm. cbn. apply perm_app; assumption.
Qed.

Theorem Permutation_merge' :
  forall (A : Ord) (l1 l1' l2 l2' : list A),
    Permutation l1 l1' -> Permutation l2 l2' ->
      Permutation (merge A (l1, l2)) (merge A (l1', l2')).
Proof.
  intros. rewrite <- !Permutation_merge. cbn. 
  apply Permutation_app; assumption.
Qed.

Class Split (A : Ord) : Type :=
{
    split' : list A -> list A * list A;
    split'_spec1 :
      forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> Nat.lt (length l1) (length l);
    split'_spec2 :
      forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> Nat.lt (length l2) (length l);
    perm_split_app :
      forall (l : list A),
        perm l (fst (split' l) ++ snd (split' l))
}.

Lemma Permutation_app_split :
  forall (A : Ord) (s : Split A) (l : list A),
    Permutation (fst (split' l) ++ snd (split' l)) l.
Proof.
  intros. apply perm_Permutation. rewrite <- perm_split_app. reflexivity.
Qed.

Coercion split' : Split >-> Funclass.

Function ghms (n : nat) (A : Ord)
  (sort : list A -> list A) (split : Split A)
  (l : list A) {measure length l} : list A :=
    if Nat.leb (length l) (S n)
    then sort l
    else let (l1, l2) := split l in
      merge A (@ghms n A sort split l1, @ghms n A sort split l2).
Proof.
  intros. apply split'_spec2 with l1; auto.
    apply leb_complete_conv in teq. lia.
  intros. apply split'_spec1 with l2; auto.
    apply leb_complete_conv in teq. lia.
Defined.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_lt_S :
  forall n : nat, Nat.lt (div2 n) (S n).
Proof.
  intros. functional induction div2 n; lia.
Qed.

#[refine]
#[export]
Instance HalfSplit (A : Ord) : Split A :=
{
    split' l :=
      let n := div2 (length l) in
      let l1 := take n l in
      let l2 := drop n l in (l1, l2)
}.
Proof.
  intros. destruct l as [| x [| y t]]; cbn in *.
    lia.
    lia.
    inversion H; subst; cbn. apply lt_n_S. apply take_length_lt. cbn.
      apply div2_lt_S.
  intros. inversion H; subst. apply drop_length_lt. cbn.
    destruct l as [| x [| y t]]; cbn in *; lia.
    destruct l as [| x [| y t]]; cbn in *; inversion 1. lia.
  intros. cbn. rewrite take_drop. reflexivity.
Defined.

Fixpoint interleave {A : Type} (l1 l2 : list A) : list A :=
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: interleave t1 t2
end.

Theorem ms_split_interleave :
  forall (A : Type) (l : list A),
    interleave (fst (ms_split l)) (snd (ms_split l)) = l.
Proof.
  induction l as [| | h h' t] using list_ind2; cbn; auto.
    destruct (ms_split t). cbn in *. rewrite IHt. auto.
Qed.

Lemma count_interleave :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    count p (interleave l1 l2) = count p l1 + count p l2.
Proof.
  induction l1 as [| h1 t1]; cbn; auto.
    destruct l2 as [| h2 t2]; cbn.
      apply plus_n_O.
      rewrite IHt1. destruct (p h1), (p h2); lia.
Qed.

Lemma perm_interleave :
  forall (A : Ord) (l1 l1' l2 l2' : list A),
    perm l1 l1' -> perm l2 l2' ->
      perm (interleave l1 l2) (interleave l1' l2').
Proof.
  unfold perm. intros. rewrite !count_interleave. auto.
Qed.

Lemma merge_perm_interleave :
  forall (A : Ord) (l : list A * list A),
    perm (merge A l) (interleave (fst l) (snd l)).
Proof.
  unfold perm; intros. rewrite count_interleave.
  rewrite <- merge_perm. rewrite count_app. auto.
Qed.

#[refine]
#[export]
Instance MsSplit (A : Ord) : Split A :=
{
    split' := ms_split;
}.
Proof.
  intros. destruct l as [| x [| y t]]; cbn in *.
    lia.
    lia.
    eapply ms_split_len1. eauto.
  intros. destruct l as [| x [| y t]]; cbn in *.
    lia.
    lia.
    eapply ms_split_len2. eauto.
  intros. rewrite <- ms_split_interleave at 1.
    rewrite <- merge_perm_interleave. rewrite merge_perm. reflexivity.
Defined.

Definition ms (A : Ord) :=
  @ghms 0 A (fun l => l) (MsSplit A).

Definition ms2 (A : Ord) :=
  @ghms 0 A (fun l => l) (HalfSplit A).

(** Time for ultimate mergesort! *)

Function ums
  (A : Ord)
  (depth : nat) (maxdepth : nat)
  (sort : list A -> list A)
  (split : Split A)
  (l : list A)
  {measure length l} : list A :=
    if Nat.leb maxdepth depth
    then sort l
    else if Nat.leb (length l) 2
    then sort l
    else let (l1, l2) := split l in
      merge A (@ums A (1 + depth) maxdepth sort split l1,
               @ums A (1 + depth) maxdepth sort split l2).
Proof.
  intros. apply split'_spec2 with l1; auto.
    apply leb_complete_conv in teq0. lia.
  intros. apply split'_spec1 with l2; auto.
    apply leb_complete_conv in teq0. lia.
Defined.

(** Time for ultimatier mergesort. *)

Class Small (A : Ord) : Type :=
{
    small : nat -> list A -> bool;
    small_spec :
      forall (n : nat) (l : list A),
        small n l = false -> 2 <= length l;
(*    small_inr :
      forall (n : nat) (h : A) (t l : list A),
         small n l = inr (h, t) -> Permutation l (h :: t)*)
}.

Coercion small : Small >-> Funclass.

Function ums'
  (A : Ord)
  (recdepth : nat)
  (s : Small A)
  (sort : list A -> list A)
  (split : Split A)
  (l : list A)
  {measure length l} : list A :=
    if small recdepth l
    then sort l
    else
      let
        (l1, l2) := split l
      in
        merge A (ums' (1 + recdepth) s sort split l1,
                 ums' (1 + recdepth) s sort split l2).
Proof.
  intros. apply split'_spec2 with l1.
    assumption.
    eapply small_spec. eassumption.
  intros. apply split'_spec1 with l2.
    assumption.
    eapply small_spec. eassumption.
Defined.

Definition ums_wut A := @ums' A 0.

#[refine]
#[export]
Instance Small_recdepth (A : Ord) (max : nat) : Small A :=
{
    small recdepth l :=
      match l with
          | [] | [_] => true
          | _ => Nat.leb max recdepth
      end
}.
Proof.
  destruct l as [| x [| y t]]; cbn.
    1-2: inv 1.
    intros. apply leb_complete_conv in H. lia.
Defined.

Function trollms
  (A : Ord)
  (fuel : nat)
  (sort : list A -> list A)
  (split : Split A)
  (l : list A)
  : list A :=
match fuel with
    | 0 => sort l
    | S fuel' =>
        let
          (l1, l2) := split l
        in
          merge A (trollms fuel' sort split l1,
                   trollms fuel' sort split l2)
end.