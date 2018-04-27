Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.

Set Implicit Arguments.

Function min {A : LinDec} (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match min t with
            | None => Some h
            | Some m =>
                Some (if h <=? m then h else m)
        end
end.

Function ss (A : LinDec) (l : list A) {measure length l} : list A :=
match min l with
    | None => []
    | Some m =>
        m :: ss A (remove_once m l)
end.
Proof.
  intros. functional induction @min A l; inv teq; cbn; dec.
  apply lt_n_S. apply IHo. assumption.
Defined.

Lemma min_present :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m -> exists l1 l2 : list A,
      l = l1 ++ m :: l2.
Proof.
  intros. functional induction min l; inv H.
    exists [], t. cbn. reflexivity.
    exists [], t. cbn. reflexivity.
    destruct (IHo _ e0) as (l1 & l2 & Heq). subst.
      exists (h :: l1), l2. cbn. reflexivity.
Qed.

Lemma remove_once_middle :
  forall (A : LinDec) (m : A) (l1 l2 : list A),
    perm A (l1 ++ l2) (remove_once m (l1 ++ m :: l2)).
Proof.
  induction l1 as [| h t]; cbn; intros; dec.
Qed.

Theorem ss_perm :
  forall (A : LinDec) (l : list A), perm A l (ss A l).
Proof.
  intros. functional induction ss A l.
    destruct l; inv e. destruct (min l); inv H0.
    destruct (min_present _ _ e) as (l1 & l2 & Heq). subst.
      eapply perm_trans.
        apply perm_front.
        apply perm_cons. rewrite <- IHl0. apply remove_once_middle.
Qed.

Lemma ss_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (ss A l) <-> In x l.
Proof.
  intros. rewrite !count_In. rewrite <- ss_perm. reflexivity.
Qed.

Lemma min_spec :
  forall (A : LinDec) (x m : A) (l : list A),
    In x l -> min l = Some m -> m ≤ x.
Proof.
  intros. functional induction min l; inv H0.
    inv H. destruct t.
      inv H0.
      cbn in e0. destruct (min t); inv e0.
    inv H. apply leq_trans with m0; dec.
    inv H. dec.
Qed.

Lemma remove_once_min_In :
  forall (A : LinDec) (x m : A) (l : list A),
    In x l -> x <> m -> min l = Some m -> In x (remove_once m l).
Proof.
  intros. functional induction min l; inv H1.
    inv H. destruct t.
      inv H1.
      cbn in e0. destruct (min t); inv e0.
    cbn. dec. inv H.
    cbn. inv H; dec.
Qed.

Lemma remove_once_In :
  forall (A : LinDec) (x m : A) (l : list A),
    In x (remove_once m l) -> In x l.
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    dec. inv H.
Qed.

Theorem ss_sorted :
  forall (A : LinDec) (l : list A), sorted A (ss A l).
Proof.
  intros. functional induction ss A l.
    constructor.
    destruct (ss A (remove_once m l)) eqn: Heq; constructor.
      apply min_spec with l.
        apply remove_once_In with m. rewrite <- ss_In, Heq. left. auto.
        assumption.
      assumption.
Qed.

Instance Sort_ss (A : LinDec) : Sort A :=
{
    sort := @ss A;
    sort_sorted := ss_sorted A;
    sort_perm := ss_perm A
}.