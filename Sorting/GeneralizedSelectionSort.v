Require Import List.
Import ListNotations.

Require Export Sorting.Sort.

Set Implicit Arguments.

Class ssArgs : Type :=
{
    A : Type;
    S : Type;

    fromList : list A -> S;

    extractMin : S -> option (A * S);

    size : S -> nat;

    size_extractMin :
      forall (a : A) (s s' : S),
        extractMin s = Some (a, s') -> size s' < size s;

    R : A -> A -> Prop;

    extractMin_spec :
      forall (x y : A) (s1 s2 s3 : S),
        extractMin s1 = Some (x, s2) -> extractMin s2 = Some (y, s3) -> R x y;

    countS : (A -> bool) -> S -> nat;

    countS_fromList :
      forall (p : A -> bool) (l : list A),
        countS p (fromList l) = count p l;

    countS_extractMin_None :
      forall (p : A -> bool) (s : S),
        extractMin s = None -> countS p s = 0;

    countS_extractMin_Some :
      forall (p : A -> bool) (a : A) (s s' : S),
        extractMin s = Some (a, s') ->
          countS p s = if p a then 1 + countS p s' else countS p s';
}.

Function toList (args : ssArgs) (s : S) {measure size s} : list A :=
match extractMin s with
    | None => []
    | Some (h, s') => h :: toList args s'
end.
Proof.
  intros. eapply size_extractMin. eassumption.
Defined.

Definition ss (args : ssArgs) (l : list A) : list A := toList args (fromList l).

Lemma Sorted_ss :
  forall (args : ssArgs) (l : list A),
    Sorted R (ss args l).
Proof.
  unfold ss. intros. generalize (fromList l). clear l; intros.
  functional induction toList args s.
    constructor.
    rewrite toList_equation in *. destruct (extractMin s') as [[h' s''] |] eqn: Heq.
      constructor.
        eapply extractMin_spec; eassumption.
        assumption.
      constructor.
Qed.

Lemma count_toList :
  forall (args : ssArgs) (s : S) (p : A -> bool),
    count p (toList args s) = countS p s.
Proof.
  intros. functional induction toList args s; cbn.
    rewrite countS_extractMin_None; trivial.
    erewrite countS_extractMin_Some, IHl.
      reflexivity.
      assumption.
Qed.

Lemma perm_ss :
  forall (args : ssArgs) (l : list A),
    perm (ss args l) l.
Proof.
  unfold ss, perm. intros.
  rewrite count_toList, countS_fromList.
  reflexivity.
Qed.