Require Import LambdaQsTypes.

Inductive Econ : Set :=
(* Expressions, e *)
| qsLET : Econ
| qsLAM : Econ
| qsAP  : Econ
| qsCMD : Econ
| qsLOC : nat -> Econ
(* Commands, m *)
| qsRET    : Econ
| qsBND    : Econ
| qsDCL    : Econ
| qsGATEAP : nat -> Econ
| qsCTRLAP : nat -> nat -> Econ
(* Intrinsics, U *)
| qsI : Econ
| qsX : Econ
| qsY : Econ
| qsZ : Econ
| qsH : Econ
| qsS : Econ
| qsT : Econ
.
