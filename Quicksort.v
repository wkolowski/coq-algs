Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Sort.

Theorem filter_length : forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); simpl; omega.
Qed.

Theorem filter_comm : forall (A : Type) (l : list A) (f g : A -> bool),
    filter f (filter g l) = filter g (filter f l).
Proof.
  induction l as [| h t]; intros.
    simpl. trivial.
    simpl. case_eq (f h); case_eq (g h); intros; simpl.
      rewrite H, H0, IHt. trivial.
      rewrite H, IHt. trivial.
      rewrite H0, IHt. trivial.
      rewrite IHt. trivial.
Qed.

Hint Resolve le_n_S filter_length.

(* Quicksort using Program Fixpoint *)
Program Fixpoint qsPF (A : LinDec) (l : list A) {measure (length l)}
    : list A :=
match l with
    | [] => []
    | h :: t => qsPF A (filter (fun x : A => leqb x h) t) ++ [h]
             ++ qsPF A (filter (fun x : A => negb (leqb x h)) t)
end.
Next Obligation. simpl. unfold lt. auto. Qed.
Next Obligation. simpl. unfold lt. auto. Qed.

Eval compute in qsPF natle testl.

(* Quicksort using Function. *)
Function qsFun (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | h :: t => qsFun A (filter (fun x : A => leqb x h) t) ++
           h :: qsFun A (filter (fun x : A => negb (leqb x h)) t)
end.
Proof.
  intros. unfold lt. simpl. apply le_n_S. apply filter_length.
  intros. unfold lt. simpl. apply le_n_S. apply filter_length.
Defined.

Eval compute in qsFun natle testl.

Lemma sorted_inv2 :
  forall (A : LinDec) (x y : A) (l : list A),
    sorted A (x :: y :: l) -> leq x y.
Proof.
  inversion 1; subst. assumption.
Qed.

Lemma sorted_app_all :
  forall (A : LinDec) (l : list A) (h : A) (t : list A),
    sorted A l -> sorted A (h :: t) -> (forall x : A, In x l -> leq x h) ->
      sorted A (l ++ h :: t).
Proof.
  induction l as [| h t]; simpl; intros.
    assumption.
    destruct t as [| h' t'].
      simpl in *. constructor.
        eapply (H1 h); eauto.
        assumption.
      rewrite <- app_comm_cons. constructor.
        eapply sorted_inv2. eassumption.
        apply IHt.
          apply sorted_inv with h. assumption.
          assumption.
          intros. apply H1. right. assumption.
Qed.

Theorem qsFun_sorted :
  forall (A : LinDec) (l : list A), sorted A (qsFun A l).
Proof.
  intros. functional induction (@qsFun A) l.
    constructor.
    apply sorted_app_all.
      assumption.
      Focus 2. intros.
Abort. (* TODO : *)

(* Quicksort using fuel recursion. *)
Fixpoint qsFuel' (A : LinDec) (fuel : nat) (l : list A) : list A :=
match fuel, l with
    | 0, _ => l
    | _, [] => []
    | _, [x] => [x]
    | S fuel', h :: t =>
        qsFuel' A fuel' (filter (fun x : A => leqb x h) t) ++ h ::
        qsFuel' A fuel' (filter (fun x : A => negb (leqb x h)) t)
end.

Definition qsFuel (A : LinDec) (l : list A) : list A :=
    qsFuel' A (length l) l.

Eval compute in (qsFuel natle testl).

(* Quicksort using well-founded recursion. *)

Lemma filter_lengthOrder :
  forall {A : Type} (p : A -> bool) (h : A) (t : list A),
    lengthOrder (filter p t) (h :: t).
Proof.
  intros. unfold lengthOrder, lt. simpl. apply le_n_S.
  apply filter_length.
Qed.

Definition qsWf (A : LinDec) : list A -> list A.
Proof.
  apply (Fix (@lengthOrder_wf A) _).
  intros l qsWf.
  destruct l as [| h t].
    exact [].
    pose (le := qsWf (filter (fun x : A => leqb x h) t)
        (filter_lengthOrder (fun x => leqb x h) h t)).
    pose (gt := qsWf (filter (fun x : A => negb (leqb x h)) t)
        (filter_lengthOrder (fun x : A => negb (leqb x h)) h t)).
    exact (le ++ h :: gt).
Defined.

Eval compute in qsWf natle testl.

(* Quicksort using wel-founded recursion and refine. *)

Definition qsWfRef (A : LinDec) : list A -> list A.
refine (Fix (@lengthOrder_wf A) _ (fun (l : list A) =>
match l with
    | [] => fun _ => []
    | h :: t => fun qs =>
        qs (filter (fun x : A => leqb x h) t) _ ++ h ::
        qs (filter (fun x : A => negb (leqb x h)) t) _
end)).
Proof.
  apply filter_lengthOrder.
  apply filter_lengthOrder.
Defined.

Eval compute in qsWfRef natle testl.

(* Quicksort using Bove-Capretta *)

Require Import Coq.Init.Wf.

Inductive qsDom {A : LinDec} : list A -> Type :=
    | qsDom0 : qsDom nil
    | qsDom1 : forall (h : A) (t : list A),
        qsDom (filter (fun x : A => leqb x h) t) ->
        qsDom (filter (fun x : A => negb (leqb x h)) t) ->
        qsDom (h :: t).

Fixpoint qsBC' (A : LinDec) (l : list A) (dom : qsDom l) : list A :=
match dom with
    | qsDom0 => nil
    | qsDom1 h t dom1 dom2 =>
        qsBC' A (filter (fun x : A => leqb x h) t) dom1 ++ h ::
        qsBC' A (filter (fun x : A => negb (leqb x h)) t) dom2
end.

Theorem all_qsDom : forall (A : LinDec) (l : list A), qsDom l.
Proof.
  intro. apply well_founded_induction_type with lengthOrder.
    apply lengthOrder_wf.
    intros. destruct x as [| h t]; constructor; apply X.
      simpl. unfold lt. apply le_n_S. apply filter_length.
      simpl. unfold lt. apply le_n_S. apply filter_length.
Defined.

Definition qsBC (A : LinDec) (l : list A) : list A :=
    qsBC' A l (all_qsDom A l).

Eval compute in qsBC natle testl.

(* nb_occ lemmas *)

Lemma nb_occ_reverse :
  forall (A : LinDec) (l : list A) (x : A),
    nb_occ A x (rev l) = nb_occ A x l.
Proof.
  induction l as [| h t].
    simpl; intros; reflexivity.
    intros. SearchAbout rev_append. rewrite rev_alt. simpl.
Abort.

(* Tried to prove that quicksort gives a permutation, but failed. *)
Lemma nb_occ_app : forall (A : LinDec) (x : A) (l1 l2 l3 : list A),
    l3 = l1 ++ l2 -> nb_occ A x (l1 ++ l2) = nb_occ A x (l2 ++ l1).
Proof.
  induction l1 as [| h1 t1].
    simpl; intros. rewrite app_nil_r. reflexivity.
    intros. rewrite <- app_comm_cons at 1.
      replace (l2 ++ h1 :: t1) with ((l2 ++ [h1]) ++ t1). (*
        rewrite <- IHt1. simpl. destruct (LinDec_eq x h1).*)
Restart. Check well_founded_induction.
  intros A x l1 l2.
  apply (@well_founded_induction (list A) _ (lengthOrder_wf A)
    (fun l3 => l3 = l1 ++ l2 -> nb_occ A x (l1 ++ l2) = nb_occ A x (l2 ++ l1))).
  intros; subst.
Abort.

Lemma perm_app : forall (A : LinDec) (l1 l2 : list A),
    perm A (l1 ++ l2) (l2 ++ l1).
Proof.
  induction l1 as [| h t].
    simpl. intro. rewrite app_nil_r. apply perm_refl.
    simpl. induction l2 as [| h' t'].
      simpl. rewrite app_nil_r. apply perm_refl.
      simpl.
Abort.