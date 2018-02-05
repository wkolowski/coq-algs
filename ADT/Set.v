Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Require Import LinDec.

(* TODO *) Module Type SET.

Parameter S : LinDec -> Type.

Parameter empty :
  forall {A : LinDec}, S A.

Parameter isEmpty :
  forall {A : LinDec}, S A -> bool.

Parameter put :
  forall {A : LinDec}, A -> S A -> S A.

Parameter del :
  forall {A : LinDec}, A -> S A -> S A.

Parameter has :
  forall {A : LinDec}, A -> S A -> bool.

End SET.