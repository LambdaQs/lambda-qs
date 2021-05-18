Require Export Hybrid.
Require Import LambdaQsTypes.

Inductive Econ : Set :=
  qLET : Econ
| qLAM : Econ
| qAP  : Econ
| qCMD : Econ
| qLOC : Econ
| Qvar : nat -> Econ
.
