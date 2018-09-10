Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Require Import LinDec.

Module Type PartialFinMap.

Parameter Map : LinDec -> Type -> Type.

Parameter empty :
  forall {K : LinDec} {V : Type}, Map K V.

Parameter insert :
  forall {K : LinDec} {V : Type}, K -> V -> Map K V -> Map K V.

Parameter remove :
  forall {K : LinDec} {V : Type}, K -> Map K V -> Map K V.

Parameter get :
  forall {K : LinDec} {V : Type}, K -> Map K V -> option V.

(** Properties of [get]. *)

Parameter get_insert :
  forall (K : LinDec) (V : Type) (k : K) (v : V) (m : Map K V),
    get k (insert k v m) = Some v.

Parameter get_insert' :
  forall (K : LinDec) (V : Type) (k k' : K) (v : V) (m : Map K V),
    get k (insert k' v m) =
    if k =? k' then Some v else get k m.

Parameter get_remove :
  forall (K : LinDec) (V : Type) (k : K) (v : V) (m : Map K V),
    get k (remove k m) = None.

Parameter get_remove' :
  forall (K : LinDec) (V : Type) (k k' : K) (v : V) (m : Map K V),
    get k (remove k' m) =
    if k =? k' then None else get k m.

(** Definition of equivalent partial maps. *)

Definition equiv {K : LinDec} {V : Type} (m1 m2 : Map K V) : Prop :=
  forall k : K, get k m1 = get k m2.

Infix "~~" := equiv (at level 50).

Parameter remove_insert_equiv :
  forall (K : LinDec) (V : Type) (k : K) (v : V) (m : Map K V),
    remove k (insert k v m) ~~ m.

Parameter insert_insert_equiv :
  forall (K : LinDec) (V : Type) (k : K) (v1 v2 : V) (m : Map K V),
    insert k v2 (insert k v1 m) ~~ insert k v2 m.

End PartialFinMap.