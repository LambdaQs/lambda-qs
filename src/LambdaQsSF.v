(* Lambda-Q# formalization based on Software Foundations' STLC

   The plan here is to copy over the contents of PLF/MoreStlc.v and
   modify them as necessary to match the syntax of lambda-Q#. Hopefully
   the existing automation will transfer easily to our use case. -KH *)

Set Warnings "-notation-overridden,-parsing".

(* Imports needed for reproducing MoreStlc.v (not currently used) *)
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(** Types **)

Definition κ := nat. (* lifetime *)
Definition var := nat. (* term variable - could use SF's id type or strings instead *)
Definition avar := nat. (* assignable  - not necessary to separate var/avar/qvar *)
Definition qvar := nat. (* qubit *)

Inductive τ : Type :=
  | ty_num  : τ
  | ty_array : τ (* store the len? *)
  | ty_qbit : τ
  | ty_qref : κ -> τ
  | ty_arrow : τ -> τ -> τ
  | ty_cmd : τ -> τ
  (* TODO: extend prod and sum to support multiple args.
     e.g. using a τ list or nat->τ function *)
  | ty_prod : τ -> τ -> τ
  | ty_sum : τ -> τ -> τ.

(** Intrinsic Gates **)

Inductive U : Type := I | X | Y | Z | H | S | T.
(* Since these gate are "opaque" anyways, we could just make U the string type.
   Then we wouldn't have to worry abou including enough gates. *)

(** Expressions & Commands **)

Inductive exp : Type :=
  | evar : var -> exp
  | num : nat -> exp (* nat or int? *)
  | letexp : var -> exp -> exp -> exp
  | lam : var -> τ -> exp -> exp
  | ap : exp -> exp -> exp
  | arrlit : τ -> exp -> exp -> exp
  | arrget : exp -> exp -> exp
  | cmdexp : cmd -> exp
  | qloc : qvar -> exp
  | pair : exp -> exp -> exp
  | fst : exp -> exp
  | snd : exp -> exp
  | inl : τ -> exp -> exp
  | inr : τ -> exp -> exp
  | caseexp : exp -> var -> exp -> var -> exp -> exp

with cmd : Type :=
  | ret : exp -> cmd
  | bnd : var -> exp -> cmd -> cmd
  | mut : avar -> exp -> cmd -> cmd
  | get : avar -> cmd
  | set : avar -> exp -> cmd
  | dcl : qvar -> cmd -> cmd
  | gateapr : exp -> U -> cmd (* probably better to allow a list of qvar args *)
  | ctrlapr : exp -> exp -> U -> cmd
  | gateap : qvar -> U -> cmd
  | ctrlap : qvar -> qvar -> U -> cmd.

(** Typing rules **)

(** Substitution **)

(** Reduction rules **)

(** Properties of typing **)

(* e.g., progress, preservation ... *)
