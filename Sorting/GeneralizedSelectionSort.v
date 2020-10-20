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

(*     Sorted_extractMin :
      forall (a : A) (s s' : S),
        extractMin s = Some (a, s') -> 
 *)
    countS : (A -> bool) -> S -> nat;

    countS_fromList :
      forall (p : A -> bool) (l : list A),
        countS p (fromList l) = count p l;
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
  unfold ss. intros. generalize (fromList l). intros.
  functional induction toList args s.
    constructor.
Abort.

Lemma perm_ss :
  forall (args : ssArgs) (l : list A),
    perm (ss args l) l.
Proof.
  unfold perm, ss. intros.
  generalize (fromList l). intros. revert l.
  functional induction (toList args s); cbn; intros.
    admit.
    destruct (p h) eqn: Hph.
      rewrite (IHl (h :: l)). cbn. rewrite Hph.
    rewrite IHl.  
  rewrite <- countS_toList, <- countS_fromList.
  reflexivity.
Qed.