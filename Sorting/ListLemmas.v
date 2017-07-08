Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Sort.

(* General lemmas *)
Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
    length l1 < length l2.

Theorem lengthOrder_wf : forall (A : Type),
    well_founded (@lengthOrder A).
Proof.
  unfold lengthOrder. intro.
  apply (@well_founded_lt_compat _ (@length A)). trivial.
Defined.

(* Selection sort lemmas *)
Fixpoint remove_once {A : LinDec} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if x =? h then t else h :: remove_once x t
end.

Lemma remove_once_In_eq : forall (A : LinDec) (x : A) (l : list A),
    In x l -> S (length (remove_once x l)) = length l.
Proof.
  induction l as [| h t]; destruct 1; dec.
Defined.

Lemma remove_once_le : forall (A : LinDec) (x : A) (l : list A),
    length (remove_once x l) <= length l.
Proof.
  induction l as [| h t]; dec.
Defined.

Lemma remove_once_In_lt : forall (A : LinDec) (x : A) (l : list A),
    In x l -> length (remove_once x l) < length l.
Proof.
  induction l as [| h t]; destruct 1; dec.
    apply lt_n_S. auto.
Defined.

Lemma remove_once_min_lengthOrder :
  forall (A : LinDec) (h : A) (t : list A),
    lengthOrder (remove_once (min_dflt A h t) (h :: t)) (h :: t).
Proof.
  red; intros. apply remove_once_In_lt. apply min_In.
Defined.

Lemma remove_once_cons:
  forall (A : LinDec) (h : A) (t : list A), min_dflt A h t <> h ->
    lengthOrder (h :: remove_once (min_dflt A h t) t) (h :: t).
Proof.
  intros. replace (h :: remove_once (min_dflt A h t) t) with
    (remove_once (min_dflt A h t) (h :: t)).
    apply remove_once_min_lengthOrder.
    simpl. dec. rewrite e in H. contradiction.
Qed.

Lemma min_split :
  forall (A : LinDec) (h : A) (t : list A),
    exists l1 l2 : list A, h :: t = l1 ++ min_dflt A h t :: l2 /\
      l1 ++ l2 = remove_once (min_dflt A h t) (h :: t).
Proof.
  induction t as [| h' t']; intros.
    exists [], []. simpl. dec.
    simpl. dec; subst; simpl.
      exists [h], t'. simpl. auto.
      rewrite e. exists [], (h' :: t'). simpl. auto.
      exists [h], t'. simpl. auto.
      exists [h], t'. simpl. auto.
      destruct IHt' as [l1 [l2 [H H']]]. destruct l1.
        inversion H. rewrite <- H1 in n. contradiction.
        exists (h :: h' :: l1), l2. simpl. split.
          do 2 f_equal. inversion H. rewrite <- H2. assumption.
          do 2 f_equal. simpl in H'.
            destruct (LinDec_eqb_spec A (min_dflt A h t') h).
              rewrite e in n. contradiction.
              inversion H'. reflexivity.
Qed.

Lemma perm_min_front :
  forall (A : LinDec) (h : A) (t : list A),
    let m := min_dflt A h t in
      perm A (m :: remove_once m (h :: t)) (h :: t).
Proof.
  intros. destruct (min_split A h t) as [l1 [l2 [H H']]]. fold m in H, H'.
  rewrite H at 2. rewrite <- H'. apply perm_symm. apply perm_front.
Qed.

Lemma remove_once_In_conv :
  forall (A : LinDec) (x h : A) (t : list A),
    In x (remove_once (min_dflt A h t) (h :: t)) ->
      In x (h :: t).
Proof.
  induction t as [| h' t'].
    simpl. dec.
    simpl in *. dec; inversion H; subst; auto.
      contradiction.
      inversion H; inversion H0; subst; auto.
        edestruct IHt'; simpl; auto.
Qed.

Lemma remove_once_In :
  forall (A : LinDec) (x h : A) (t : list A),
    In x t -> min_dflt A h t <> x -> In x (remove_once (min_dflt A h t) t).
Proof.
  induction t as [| h' t']; inversion 1; subst; intros.
    simpl in *. dec. rewrite e in H0. contradiction.
    simpl. dec. right. apply IHt'.
      assumption.
      simpl in *. destruct (leqb_spec h' (min_dflt A h t')).
        contradiction.
        assumption.
Qed.

(* Quicksort lemmas *)
Lemma filter_length :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); simpl; omega.
Qed.

Lemma filter_lengthOrder :
  forall {A : Type} (p : A -> bool) (h : A) (t : list A),
    lengthOrder (filter p t) (h :: t).
Proof.
  intros. unfold lengthOrder, lt. simpl. apply le_n_S.
  apply filter_length.
Qed.

Lemma filter_In_app :
  forall (A : LinDec) (p : A -> bool) (x : A) (l : list A),
    In x (filter p l ++ filter (fun x => negb (p x)) l) -> In x l.
Proof.
  induction l as [| h t]; simpl.
    auto.
    destruct (p h); simpl.
      destruct 1; auto.
      intro. apply in_app_or in H. destruct H.
        right. apply IHt. apply in_or_app. auto.
        inversion H.
          subst. auto.
          right. apply IHt. apply in_or_app. auto.
Qed.

(* Mergesort lemmas *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | _, [] => []
    | S n', h :: t => drop n' t
end.

Theorem take_length_le : forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= length l.
Proof.
  induction n as [| n']; destruct l; simpl; intros; auto.
    omega.
    apply le_n_S. apply IHn'.
Qed.

Theorem take_length_lt : forall (A : Type) (n : nat) (l : list A),
    n < length l -> length (take n l) < length l.
Proof.
  induction n as [| n']; simpl; intros; auto.
  destruct l; simpl in *.
    inversion H.
    apply lt_n_S. apply IHn'. omega.
Qed.

Theorem drop_length_le : forall (A : Type) (l : list A) (n : nat),
    length (drop n l) <= length l.
Proof.
  induction l as [| h t]; destruct n; simpl; intros; auto.
Qed.

Theorem drop_length_lt : forall (A : Type) (l : list A) (n : nat),
    0 < n -> l <> [] -> length (drop n l) < length l.
Proof.
  induction l as [| h t]; intros; destruct n; try (inversion H; fail);
  simpl in *.
    contradiction H0. trivial.
    unfold lt. apply le_n_S. apply drop_length_le.
Qed.

Lemma take_In :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    In x (take n l) -> In x l.
Proof.
  induction n as [| n'].
    simpl. inversion 1.
    destruct l as [| h t]; simpl; auto.
      destruct 1; auto.
Qed.

Lemma drop_In :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    In x (drop n l) -> In x l.
Proof.
  induction n as [| n'].
    simpl. auto.
    destruct l as [| h t]; simpl; auto.
Qed.

Lemma take_In_tail :
  forall (A : Type) (n : nat) (x h : A) (t : list A),
    In x (take n t) -> In x (take (S n) (h :: t)).
Proof.
  induction n as [| n']; simpl.
    inversion 2.
    destruct t as [| h' t']; simpl; destruct 1; auto.
Qed.

Lemma drop_In_tail :
  forall (A : Type) (n : nat) (x h : A) (t : list A),
    In x (drop n t) -> In x (drop (S n) (h :: t)).
Proof.
  induction n as [| n']; simpl.
    auto.
    destruct t as [| h' t']; simpl; auto.
Qed.

Fixpoint list_ind2 (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
Proof.
  destruct l as [| h [| h' t]].
    apply Hnil.
    apply Hsingl.
    apply Hcons. apply list_ind2; auto.
Defined.