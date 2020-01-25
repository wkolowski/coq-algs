

Require Export Formula.
(* Require Import Formula2. TODO *)

Variables A B C D E F G P Q R S : Prop.

(* [False] and [True]. *)
Goal False.
Proof.
  try solveGoal.
Abort.

Goal True.
Proof. solveGoal. Qed.

(* Negation. *)
Goal ~ True.
Proof. try solveGoal. Abort.

Goal ~ False.
Proof. solveGoal. Qed.

(* Conjunctions, disjunctions and implications of [True]s and [False]s. *)
Goal True /\ True.
Proof. solveGoal. Qed.

Goal True /\ False.
Proof. try solveGoal. Abort.

Goal False \/ True.
Proof. solveGoal. Qed.

Goal False \/ P.
Proof. try solveGoal. Abort.

Goal True -> True.
Proof. solveGoal. Qed.

Goal False -> False.
Proof. solveGoal. Qed.

(* More complex stuff. *)
Goal P \/ True.
Proof. solveGoal. Qed.

Goal True -> P.
Proof. try solveGoal. Abort.

Goal False -> P.
Proof. solveGoal. Qed.

Goal P -> P.
Proof. solveGoal. Qed.

Goal P -> P \/ Q.
Proof. solveGoal. Abort.

Goal P \/ Q -> Q \/ P.
Proof. solveGoal. Qed.

Goal P -> ~~P.
Proof. try solveGoal. Abort.

Goal P <-> P.
Proof. solveGoal. Qed.

(* Wzięte z R1.v *)

(* Przemienność *)
Theorem and_comm : P /\ Q -> Q /\ P.
Proof. solveGoal. Qed.

Theorem or_comm : P \/ Q -> Q \/ P.
Proof. solveGoal. Qed.

Theorem and_assoc : P /\ (Q /\ R) <-> (P /\ Q) /\ R.
Proof. try solveGoal. Abort.

Theorem or_assoc : P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof. solveGoal. Qed.

(* Rozdzielność *)
Ltac gen x := generalize dependent x.

Theorem and_dist_or : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
(*  repeat (split; solveGoal); gen H; gen H0; solveGoal.*)
Abort.

Theorem or_dist_and : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. try solveGoal. Abort.

Theorem imp_dist_imp : (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
Proof. try solveGoal. Abort.

(* Kuryfikacja *)
Theorem curry : (P /\ Q -> R) -> (P -> Q -> R).
Proof. try solveGoal. Abort.

Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).
Proof. try solveGoal. Abort.

(* De Morgan *)
Theorem deMorgan_1 : ~(P \/ Q) <-> ~P /\ ~Q.
Proof. try solveGoal. Abort.

Theorem deMorgan_2 : ~P \/ ~Q -> ~(P /\ Q).
Proof. try solveGoal. Abort.

(* Niesprzeczność i zasada wyłączonego środka *)
Theorem noncontradiction' : ~(P /\ ~P).
Proof. try solveGoal. Abort.

Theorem noncontradiction_v2 : ~(P <-> ~P).
Proof. try solveGoal. Abort.

Theorem em_irrefutable : ~~(P \/ ~P).
Proof. try solveGoal. Abort.

(* Elementy neutralne i anihilujące *)
Theorem and_false_annihilation : P /\ False <-> False.
Proof. solveGoal. Qed.

Theorem or_false_neutral : P \/ False <-> P.
Proof. solveGoal. Qed.

Theorem and_true_neutral : P /\ True <-> P.
Proof. solveGoal. Qed.

Theorem or_true_annihilation : P \/ True <-> True.
Proof. solveGoal. Qed.

(* Różne *)
Theorem or_imp_and : (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
Proof. try solveGoal. Abort.

Theorem and_not_imp : P /\ ~Q -> ~(P -> Q).
Proof. try solveGoal. Abort.

Theorem or_not_imp : ~P \/ Q -> (P -> Q).
Proof. try solveGoal. Abort.

Theorem contraposition : (P -> Q) -> (~Q -> ~P).
Proof. try solveGoal. Abort.

Theorem absurd : ~P -> P -> Q.
Proof. try solveGoal. Abort.

Theorem impl_and : (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof. try solveGoal. Abort.