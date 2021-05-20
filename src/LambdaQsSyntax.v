Require Export Hybrid.
Require Import LambdaQsTypes.

Inductive Econ : Set :=
    qsLET : Econ
  | qsLAM : Econ
  | qsAP  : Econ
  | qsCMD : Econ
  | qsLOC : nat -> Econ
.

Inductive Ccon : Set :=
    qsRET    : Ccon
  | qsBND    : Ccon
  | qsDCL    : Ccon
  | qsGATEAP : Ccon
  | qsCTRLAP : Ccon
.

Definition qexp : Set := expr Econ.
Definition qcmd : Set := expr Ccon.

(* Pure expressions **********************************************************)

Definition Var : var -> qexp := VAR Econ.
Definition Bnd : bnd -> qexp := BND Econ.
(* let(e1; x.e2) *)
Definition Let (e1:qexp) (f:qexp -> qexp) : qexp :=
  APP (CON qsLET) (APP e1 (lambda (fun x => f x))).
(* lam{T}(x.e) *)
Definition Lam (f:qexp -> qexp) : qexp := APP (CON qsLAM) (lambda f).
(* ap(e1; e2) *)
Definition Ap (e1 e2:qexp) : qexp := APP (APP (CON qsAP) e1) e2.

(* cmd(m) *)
(* Definition Cmd (m:qcmd) : qexp := APP (CON qsCMD) m. *)
(* TODO: The term "m" has type "qcmd" while it is expected to have type "expr Econ". *)

(* qloc[q] *)
Definition QLoc (q:nat) : qexp := (CON (qsLOC q)).

(* Effectful commands ********************************************************)

(* ret(e) *)
(* Definition Ret (e:qexp) : qcmd := APP (CON qsRET) e. *)
(* The term "e" has type "qexp" while it is expected to have type "expr Ccon". *)
