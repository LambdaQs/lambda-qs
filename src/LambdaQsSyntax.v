From HybridSys Require Export Hybrid.
Require Import LambdaQsTypes.

Inductive Econ : Set :=
  (* Expressions, e *)
    qsLET : Econ
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

Definition qexp : Set := expr Econ.

(* Pure expressions **********************************************************)

Definition Var : var -> qexp := VAR Econ.
(* let(e1; x.e2) *)
Definition Let (e1:qexp) (f:qexp -> qexp) : qexp :=
  APP (CON qsLET) (APP e1 (lambda (fun x => f x))).
(* lam{T}(x.e) *)
Definition Lam (f:qexp -> qexp) : qexp := APP (CON qsLAM) (lambda f).
(* ap(e1; e2) *)
Definition Ap (e1 e2:qexp) : qexp := APP (APP (CON qsAP) e1) e2.

(* cmd(m) *)
Definition Cmd (m:qexp) : qexp := APP (CON qsCMD) m.

(* qloc[q] *)
Definition QLoc (q:nat) : qexp := (CON (qsLOC q)).

(* Effectful commands ********************************************************)

(* ret(e) *)
Definition Ret (e:qexp) : qexp := APP (CON qsRET) e.

(* Definition Bnd : bnd -> qexp := BND Econ. *)
(* bnd(e; x.m) *)
Definition Bnd (e:qexp) (f:qexp->qexp) : qexp :=
  APP (CON qsBND) (APP e (lambda (fun x => f x))).

(* dcl(q.m) *)
Definition Dcl (f:qexp->qexp) : qexp := APP (CON qsDCL) (lambda f).

(* TODO: ensure validity of U *)
(* gateap[q](U) *)
Definition GateAp (q:nat) (u:qexp) : qexp := APP (CON (qsGATEAP q)) u.

(* ctrlap[q1, q2](U) *)
Definition CtrlAp (q1 q2:nat) (u:qexp) : qexp := APP (CON (qsCTRLAP q1 q2)) u.
