Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sort.
Require Export ListLemmas.

Set Implicit Arguments.

(* Selection sort using program fixpoint *)
Program Fixpoint ssPF (A : LinDec) (l : list A)
    {measure (length l)} : list A :=
match l with
    | [] => []
    | h :: t => let m := min_dflt A h t in
        m :: ssPF A (remove_once m l)
end.
Next Obligation. apply remove_once_min_lengthOrder. Qed.

Eval compute in ssPF natle testl.

(* Selection sort using Function. *)
Function ssFun (A : LinDec) (l : list A)
    {wf (@lengthOrder A) l} : list A :=
match l with
    | [] => []
    | h :: t => let m := min_dflt A h t in m :: ssFun A (remove_once m l)
end.
Proof.
  intros. apply remove_once_min_lengthOrder.
  intro. apply lengthOrder_wf.
Defined.

Eval compute in ssFun natle testl.

(* Selection sort using fuel recursion. *)
Fixpoint ssFuelOpt {A : LinDec} (n : nat) (l : list A)
    : option (list A) :=
match n with
    | 0 => None
    | S n' =>
        match l with
            | [] => Some []
            | h :: t => let m := min_dflt A h t in
                match ssFuelOpt n' (remove_once m l) with
                    | None => None
                    | Some l' => Some (m :: l')
                end
            end
end.

Eval compute in ssFuelOpt 15 testl.

Lemma ssFuelOpt_eq : forall (A : LinDec) (n : nat) (h : A) (t : list A),
  ssFuelOpt (S n) (h :: t) =
    match ssFuelOpt n (remove_once (min_dflt A h t) (h :: t)) with
        | None => None
        | Some l => Some (min_dflt A h t :: l)
    end.
Proof.
  intros. reflexivity.
Qed.

Theorem ssFuelOpt_extract : forall (A : LinDec) (l : list A),
    {l' : list A | ssFuelOpt (S (length l)) l = Some l'}.
Proof.
  intro. apply (Fix (@lengthOrder_wf A)). intros l H.
  destruct l as [| h t]; intros.
    simpl. exists []. trivial.
    pose (m := min_dflt A h t). pose (r := remove_once m (h :: t)).
      destruct (H r).
        unfold r. apply remove_once_min_lengthOrder.
 	      exists (min_dflt A h t :: x). rewrite ssFuelOpt_eq. fold m. fold r.
          replace (length (h :: t)) with (S (length r)).
            rewrite e. reflexivity.
            unfold r. apply remove_once_In_eq.
              apply min_In.
Defined.

Theorem ssFuelOpt_None : forall (A : LinDec) (l : list A),
    ssFuelOpt (S (length l)) l <> None.
Proof.
  unfold not; intros.
  pose (H' := ssFuelOpt_extract A l).
  destruct H'. rewrite e in H. inversion H.
Defined.

Definition ssFuelOpt' {A : LinDec} (l : list A) : list A :=
    proj1_sig (ssFuelOpt_extract A l).

Eval compute in ssFuelOpt' testl.

Definition ssFuelOpt'' {A : LinDec} (l : list A) : list A.
Proof.
  case_eq (ssFuelOpt (S (length l)) l); intros.
    exact l0.
    apply ssFuelOpt_None in H. destruct H.
Defined.

Eval compute in ssFuelOpt'' testl.

(* Selection sort using fuel recursion without options. *)
Fixpoint ssFuel {A : LinDec} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => let m := min_dflt A h t in
        m :: ssFuel n' (remove_once m l)
end.

Eval compute in ssFuel 100 testl.

(* Selection sort using well-founded recursion *)
Definition ssWf {A : LinDec} : list A -> list A.
Proof.
  apply (Fix (@lengthOrder_wf A)). intros l ss.
  destruct l as [| h t].
    exact [].
    pose (m := min_dflt A h t). pose (r := remove_once m (h :: t)).
      pose (p := remove_once_min_lengthOrder A h t).
      exact (m :: ss r p).
Defined.

Eval compute in ssWf testl.

(* Selection sort using well-founded recursion and refine. *)
Definition ssWfRef {A : LinDec} : list A -> list A.
refine (Fix (@lengthOrder_wf A) _ (fun (l : list A) =>
match l with
    | [] => fun _ => []
    | h :: t => fun ss => let m := min_dflt A h t in
        m :: ss (remove_once m (h :: t)) _
end)).
Proof. apply remove_once_min_lengthOrder. Defined.

Eval compute in ssWfRef testl.

(* Selection sort using Bove-Capretta *)
Inductive ssDom {A : LinDec} : list A -> Type :=
    | ssDomNil : ssDom []
    | ssDomRec : forall (h : A) (t : list A),
        ssDom (remove_once (min_dflt A h t) (h :: t)) -> ssDom (h :: t).

Fixpoint ssBC' {A : LinDec} {l : list A} (p : ssDom l)
    : list A :=
match p with
    | ssDomNil => []
    | ssDomRec h t p => min_dflt A h t :: ssBC' p
end.

Theorem ssDom_all : forall (A : LinDec) (l : list A), ssDom l.
Proof.
  intro. apply well_founded_induction_type with lengthOrder.
    apply lengthOrder_wf.
    intros l ss. destruct l as [| h t]; constructor.
      apply ss. apply remove_once_min_lengthOrder.
Defined.

Definition ssBC {A : LinDec} (l : list A) : list A :=
    ssBC' (ssDom_all A l).

Eval compute in ssBC testl.