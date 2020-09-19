Require Export ProveTermination Recdef.

Extraction Language Haskell.
Extraction QSDom.
(* ===>
  data QSDom =
   | Short (List T)
   | Long (List T) T (List T) T (List T) (List T)
          (List T) (List T) QSDom QSDom
*)

Extraction QSDom_all.
(* ===>
  qSDom_all :: TerminatingQSArgs -> (List T) -> QSDom
  qSDom_all a =
    well_founded_induction_type (\l iH ->
      let {o = short (args a) l} in
      case o of {
       Some p ->
        case p of {
         Pair h t ->
          let {p0 = choosePivot (args a) h t} in
          case p0 of {
           Pair pivot rest ->
            let {p1 = partition (args a) pivot rest} in
            case p1 of {
             Pair p2 x ->
              case p2 of {
               Pair lt eq -> Long l h t pivot rest eq lt x
                (iH lt __) (iH x __)}}}};
       None -> Short l})
*)

Extraction qs'.
(* ===>
  qs' :: QSArgs -> (List T) -> QSDom -> List T
  qs' a l d =
    case d of {
     Short _ -> adhoc a l;
     Long _ _ _ pivot _ eq lt gt ltd gtd ->
      app (qs' a lt ltd) (Cons pivot (app eq (qs' a gt gtd)))}
*)

Inductive QSDom (A : QSArgs) : list A -> Prop :=
    | Short :
        forall l : list A, short l = None -> QSDom A l
    | Long :
        forall {l : list A},
          forall {h : A} {t : list A},
            short l = Some (h, t) ->
          forall (pivot : A) {rest : list A},
            choosePivot h t = (pivot, rest) ->
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          QSDom A lt -> QSDom A gt -> QSDom A l.

Lemma Long_inv_lt :
  forall
    {A : QSArgs} {l : list A} (d : QSDom A l),
      forall {h : A} {t : list A},
        short l = Some (h, t) ->
      forall {pivot : A} {rest : list A},
        choosePivot h t = (pivot, rest) ->
      forall {lt eq gt : list A},
        partition pivot rest = (lt, eq, gt) ->
          QSDom A lt.
Proof.
  destruct 1; intros.
    congruence.
    {
      rewrite H in H2; inversion H2; subst.
      rewrite H0 in H3; inversion H3; subst.
      rewrite H1 in H4; inversion H4; subst.
      exact d1.
    }
Defined.

Lemma Long_inv_gt :
  forall
    {A : QSArgs} {l : list A} (d : QSDom A l),
      forall {h : A} {t : list A},
        short l = Some (h, t) ->
      forall {pivot : A} {rest : list A},
        choosePivot h t = (pivot, rest) ->
      forall {lt eq gt : list A},
        partition pivot rest = (lt, eq, gt) ->
          QSDom A gt.
Proof.
  destruct 1; intros.
    congruence.
    {
      rewrite H in H2; inversion H2; subst.
      rewrite H0 in H3; inversion H3; subst.
      rewrite H1 in H4; inversion H4; subst.
      exact d2.
    }
Defined.

Fixpoint qs'
  (A : QSArgs) (l : list A) (d : QSDom A l) {struct d} : list A :=
match
  short l as x return short l = x -> list A
with
| None => fun _ => adhoc l
| Some (h, t) => fun eq1 =>
    match
      choosePivot h t as y
    return
      choosePivot h t = y -> list A
    with
    | (pivot, rest) => fun eq2 =>
        match
          partition pivot rest as z
        return
          partition pivot rest = z -> list A
        with
        | (lt, eq, gt) => fun eq3 =>
            qs' A lt (Long_inv_lt d eq1 eq2 eq3)
            ++ pivot :: eq ++
            qs' A gt (Long_inv_gt d eq1 eq2 eq3)
        end eq_refl
    end eq_refl
end eq_refl.

Lemma QSDom_all :
  forall (A : TerminatingQSArgs) (l : list A), QSDom A l.
Proof.
  intro A.
  apply well_founded_induction_type with (R := ltof _ (@length A)).
    apply well_founded_ltof.
    intros l IH. destruct (short l) as [[h t] |] eqn: Hshort.
      Focus 2. constructor. assumption.
      destruct (choosePivot h t) as [pivot rest] eqn: Hpivot;
      destruct (partition pivot rest) as [[lt eq] gt] eqn: Hpartition.
      econstructor 2; try eassumption.
        apply IH; red. apply le_lt_trans with (length rest).
          apply (partition_len_lt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
        apply IH; red. apply le_lt_trans with (length rest).
          apply (partition_len_gt Hpartition).
          rewrite (choosePivot_len Hpivot). apply (short_len Hshort).
Defined.

Lemma len_filter :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (filter p l) <= length l.
Proof.
  induction l as [| h t]; cbn.
    trivial.
    destruct (p h).
      cbn. apply le_n_S. assumption.
      apply le_S. assumption.
Defined.

#[refine]
Instance TQSA_default
  (A : Type) (p : A -> A -> bool) : TerminatingQSArgs :=
{
    args :=
    {|
        T := A;
        short l :=
          match l with
              | [] => None
              | h :: t => Some (h, t)
          end;
        adhoc _ := [];
        choosePivot h t := (h, t);
        partition pivot rest :=
          (filter (fun x => p x pivot) rest,
           [],
           filter (fun x => negb (p x pivot)) rest);
    |}
}.
Proof.
  all: cbn.
    destruct l; inversion 1; cbn. apply le_refl.
    inversion 1. reflexivity.
    inversion 1; subst. apply len_filter.
    inversion 1; subst. apply len_filter.
Defined.

Definition qs (A : TerminatingQSArgs) (l : list A) : list A :=
  qs' A l (QSDom_all A l).

Compute qs (TQSA_default nat leb) [4; 3; 2; 1].
(* ===> = [1; 2; 3; 4] *)

Extraction qs'.
(* ===>
  qs' :: QSArgs -> (List T) -> List T
  qs' a l =
    case short a l of {
     Some p ->
      case p of {
       Pair h t ->
        case choosePivot a h t of {
         Pair pivot rest ->
          case partition a pivot rest of {
           Pair p0 gt ->
            case p0 of {
             Pair lt eq ->
              app (qs' a lt) (Cons pivot (app eq (qs' a gt)))}}}};
     None -> adhoc a l}
*)