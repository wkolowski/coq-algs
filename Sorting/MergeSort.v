Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

Require Export Sorting.Sort.
Require Export ListLemmas.

(*Require Import InsertionSort.*)

Set Implicit Arguments.

Function merge (A : LinDec) (l : list A * list A)
  {measure lenSum l} : list A :=
  let (l1, l2) := l in
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h :: t, h' :: t' =>
        if h <=? h'
        then h :: merge A (t, l2)
        else h' :: merge A (l1, t')
end.
Proof.
  intros. unfold lenSum. simpl. omega.
  intros. unfold lenSum. simpl. omega.
Defined.

Theorem merge_sorted :
  forall (A : LinDec) (l : list A * list A),
    sorted A (fst l) -> sorted A (snd l) -> sorted A (merge A l).
Proof.
  intros. functional induction merge A l; simpl in *; auto;
  rewrite merge_equation in *.
    destruct t; simpl in *; dec.
    destruct t'; simpl in *; dec.
Qed.

Theorem merge_perm :
  forall (A : LinDec) (l : list A * list A),
    perm A (fst l ++ snd l) (merge A l).
Proof.
  intros. functional induction merge A l; simpl; auto; try clear y.
    rewrite app_nil_r. auto.
    eapply perm_trans.
      rewrite app_comm_cons. apply perm_app_comm.
      simpl. apply perm_cons. simpl in IHl0. rewrite <- IHl0.
        apply perm_app_comm.
Qed.

Theorem merge_pres_perm :
  forall (A : LinDec) (l1 l1' l2 l2' : list A),
    perm A l1 l1' -> perm A l2 l2' ->
      perm A (merge A (l1, l2)) (merge A (l1', l2')).
Proof.
  intros. rewrite <- !merge_perm. cbn. apply perm_app; assumption.
Qed.

Class Split (A : LinDec) : Type :=
{
    split' : list A -> list A * list A;
    split'_spec1 :
      forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> length l1 < length l;
    split'_spec2 :
      forall l l1 l2 : list A,
        split' l = (l1, l2) -> 2 <= length l -> length l2 < length l;
    perm_split_app :
      forall (l : list A),
        perm A l (fst (split' l) ++ snd (split' l))
}.

Coercion split' : Split >-> Funclass.

Function ghms (n : nat) (A : LinDec)
  (sort : list A -> list A) (split : Split A)
  (l : list A) {measure length l} : list A :=
    if @leqb natle (length l) (S n)
    then sort l
    else let (l1, l2) := split l in
      merge A (@ghms n A sort split l1, @ghms n A sort split l2).
Proof.
  intros. apply split'_spec2 with l1; dec.
    dec. cbn in *. omega.
  intros. apply split'_spec1 with l2; dec.
    dec. cbn in *. omega.
Defined.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_lt_S :
  forall n : nat, div2 n < S n.
Proof.
  intros. functional induction @div2 n; omega.
Qed.

Instance HalfSplit (A : LinDec) : Split A :=
{
    split' l :=
      let n := div2 (length l) in
      let l1 := take n l in
      let l2 := drop n l in (l1, l2)
}.
Proof.
  intros. destruct l as [| x [| y t]]; cbn in *.
    omega.
    omega.
    inversion H; subst; cbn. apply lt_n_S. apply take_length_lt. cbn.
      apply div2_lt_S.
  intros. inversion H; subst. apply drop_length_lt. cbn.
    destruct l as [| x [| y t]]; cbn in *; omega.
    destruct l as [| x [| y t]]; cbn in *; inversion 1. omega.
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
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    count A x (interleave l1 l2) = count A x l1 + count A x l2.
Proof.
  induction l1 as [| h1 t1]; cbn; auto.
    destruct l2 as [| h2 t2]; cbn.
      apply plus_n_O.
      dec; rewrite IHt1; omega.
Qed.

Lemma perm_interleave :
  forall (A : LinDec) (l1 l1' l2 l2' : list A),
    perm A l1 l1' -> perm A l2 l2' ->
      perm A (interleave l1 l2) (interleave l1' l2').
Proof.
  unfold perm. intros. rewrite !count_interleave. auto.
Qed.

Lemma merge_perm_interleave :
  forall (A : LinDec) (l : list A * list A),
    perm A (merge A l) (interleave (fst l) (snd l)).
Proof.
  unfold perm; intros. rewrite count_interleave.
  rewrite <- merge_perm. rewrite count_app. auto.
Qed.

Instance MsSplit (A : LinDec) : Split A :=
{
    split' := ms_split;
}.
Proof.
  intros. destruct l as [| x [| y t]]; cbn in *.
    omega.
    omega.
    eapply ms_split_len1. eauto.
  intros. destruct l as [| x [| y t]]; cbn in *.
    omega.
    omega.
    eapply ms_split_len2. eauto.
  intros. rewrite <- ms_split_interleave at 1.
    rewrite <- merge_perm_interleave. rewrite merge_perm. reflexivity.
Defined.

Definition ms (A : LinDec) :=
  @ghms 0 A (fun l => l) (MsSplit A).

Definition ms2 (A : LinDec) :=
  @ghms 0 A (fun l => l) (HalfSplit A).

(** Time for ultimate mergesort! *)

Function ums
  (A : LinDec)
  (depth : nat) (maxdepth : nat)
  (sort : list A -> list A)
  (split : Split A)
  (l : list A)
  {measure length l} : list A :=
    if @leqb natle maxdepth depth
    then sort l
    else if @leqb natle (length l) 2
    then sort l
    else let (l1, l2) := split l in
      merge A (@ums A (1 + depth) maxdepth sort split l1,
               @ums A (1 + depth) maxdepth sort split l2).
Proof.
  intros. apply split'_spec2 with l1; dec.
    cbn in *. omega.
  intros. apply split'_spec1 with l2; dec.
    cbn in *. omega.
Defined.

(** Time for ultimatier mergesort. *)

Class Small (A : LinDec) : Type :=
{
    small :> nat -> list A -> bool;
    small_spec :
      forall (n : nat) (l : list A),
        small n l = false -> 2 <= length l;
(*    small_inr :
      forall (n : nat) (h : A) (t l : list A),
         small n l = inr (h, t) -> Permutation l (h :: t)*)
}.

Coercion small : Small >-> Funclass.

Function ums'
  (A : LinDec)
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

Instance Small_recdepth (A : LinDec) (max : nat) : Small A :=
{
    small recdepth l :=
      match l with
          | [] | [_] => true
          | _ => @leqb natle max recdepth
      end
}.
Proof.
  destruct l as [| x [| y t]]; cbn.
    1-2: inv 1.
    dec.
Defined.

Function trollms
  (A : LinDec)
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