Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Definition minmax {A : LinDec} (x y : A) : A * A :=
  if x <=? y then (x, y) else (y, x).

Definition min {A : LinDec} (x y : A) : A :=
  if x <=? y then x else y.

Definition max {A : LinDec} (x y : A) : A :=
  if y <=? x then x else y.

Function sendDown {A : LinDec} (x : A) (t : BTree A) : A * BTree A :=
match t with
    | empty => (x, empty)
    | node v l r =>
        let
          '(m, M) := minmax x v
        in
          match l, r with
              | empty, empty => (m, (node M l r))
              | empty, _ =>
                  let '(m', r') := sendDown M r in
                    (min m m', node (max m m') l r')
              | _, empty =>
                  let '(m', l') := sendDown M l in
                    (min m m', node (max m m') l' r)
              | node vl _ _, node vr _ _ =>
                  if vl <=? vr
                  then
                    let '(m', l') := sendDown M l in
                      (min m m', node (max m m') l' r)
                  else
                    let '(m', r') := sendDown M r in
                      (min m m', node (max m m') l r')
          end
end.

Compute @sendDown natle
  2 (node 4 (node 10 empty empty) (node 8 empty empty)).

Lemma sendDown_elem :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      x = m \/ elem x t'.
Proof.
  intros. functional induction @sendDown A x t; inv H; dec;
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | IH : forall _ _, _ -> _, H : sendDown _ _ = _ |- _ =>
          destruct (IH _ _ H); clear IH; subst
  end;
  unfold min, max, minmax in *; dec; inv e0.
Qed.

Lemma sendDown_elem' :
  forall (A : LinDec) (x m y : A) (t t' : BTree A),
    sendDown x t = (m, t') -> elem y t -> y = m \/ elem y t'.
Proof.
Admitted.

Lemma sendDown_elem'' :
  forall (A : LinDec) (x m y : A) (t t' : BTree A),
    sendDown x t = (m, t') -> elem y t ->
      (x = m /\ t = t') \/
      (y = m \/ elem x t').
Proof.
Admitted.

(*Lemma isHeap_sendDown :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    isHeap t -> sendDown x t = (m, t') ->
      isHeap t' /\ forall a : A, elem a t' -> m ≤ a.
Proof.
  intros. functional induction @sendDown A x t; inv H0.
    split; [constructor | inv 1].
    split.
      repeat constructor; inv 1.
      inv 1; try inv H2. unfold minmax in e0; dec. inv e0.
    destruct _x.
      contradiction.
      inv H. destruct (IHp _ _ H6 e3); clear IHp y. split.
        repeat constructor.
          inv 1.
          intros. unfold max, minmax in *. dec; inv e0.
Admitted.
*)

Function makeHeap {A : LinDec} (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        match makeHeap l, makeHeap r with
            | empty, empty => node v empty empty
            | empty, r' =>
                let '(m, r'') := sendDown v r' in node m empty r''
            | l', empty =>
                let '(m, l'') := sendDown v l' in node m l'' empty
            | node vl _ _ as l', node vr _ _ as r' =>
                if vl <=? vr
                then let '(m, l'') := sendDown v l' in node m l'' r'
                else let '(m, r'') := sendDown v r' in node m l' r''
        end
end.

Ltac dec' := cbn;
repeat match goal with
    | |- context [?x =? ?y] =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | |- context [?x <=? ?y] =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
    | H : context [?x =? ?y] |- _ =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | H : context [?x <=? ?y] |- _ =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
end; cbn;
repeat match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
    | H : True |- _ => clear H
    | H : ?x = ?x |- _ => clear H
end; try congruence.

Inductive ih {A : LinDec} : BTree A -> Prop :=
    | ih_empty : ih empty
    | ih_singl : forall v : A, ih (node v empty empty)
    | ih_l :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> ih (node x l r) -> ih (node v (node x l r) empty)
    | ih_r :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> ih (node x l r) -> ih (node v empty (node x l r))
    | ih_lr :
        forall (v lv rv : A) (ll lr rl rr : BTree A),
          v ≤ lv -> ih (node lv ll lr) ->
          v ≤ rv -> ih (node rv rl rr) ->
            ih (node v (node lv ll lr) (node rv rl rr)).

Lemma minmax_leq :
  forall (A : LinDec) (x y m M : A),
    minmax x y = (m, M) -> m ≤ M.
Proof.
  unfold minmax. intros. dec. inv H.
Qed.

Lemma leq_min_max :
  forall (A : LinDec) (x y : A),
    min x y ≤ max x y.
Proof.
  unfold min, max. intros. dec.
Qed.

Lemma sendDown_ih :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      t = empty /\ t' = empty \/
      exists (v : A) (l r : BTree A),
        t' = node v l r /\ ih t' /\ m ≤ v.
Proof.
  intros. functional induction @sendDown A x t; inv H; right.
    exists M, empty, empty. repeat split.
      constructor.
      eapply minmax_leq. eauto.
    do 3 eexists. repeat split.
      2: apply leq_min_max.
      decompose [and or ex] (IHp _ _ e3); clear IHp; subst.
        contradiction.
        constructor.
Admitted.
(*
        contradiction.
        constructor.
          apply minmax_leq in e0. unfold max; dec. inv e0.
      eauto.
      apply leq_min_max.
    do 3 eexists. split.
      eauto.
      apply leq_min_max.
    do 3 eexists. split.
      eauto.
      apply leq_min_max.
    do 3 eexists. split.
      eauto.
      apply leq_min_max.
Qed.*)

Lemma ih_sendDown_arg :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> ih t ->
      forall a : A, elem a t -> m ≤ a.
Proof.
  intros. functional induction @sendDown A x t.
Abort.

Lemma ih_sendDown_res :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> ih t ->
      forall a : A, elem a t' -> m ≤ a.
Proof.
Admitted.

Lemma makeHeap_ih :
  forall (A : LinDec) (t : BTree A),
    ih (makeHeap t).
Proof.
  intros. functional induction @makeHeap A t;
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x eqn: Hx
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | H : elem _ empty |- _ => inv H
      | H : makeHeap _ = _ |- _ => rewrite ?H in *; clear H
      | H : ih empty |- _ => clear H
  end;
  try match goal with
      | H : sendDown _ _ = _ |- _ =>
          let H' := fresh "H" in 
          assert (H' := sendDown_ih _ _ _ _ _ H);
          decompose [and or ex] H'; clear H'; subst
  end;
  constructor; try assumption; try congruence.
    eapply leq_trans with vl.
      eapply ih_sendDown_arg; eauto.
      dec'.
    eapply leq_trans with vr.
      eapply ih_sendDown_arg; eauto.
      dec.
Qed.

Print Assumptions makeHeap_ih.