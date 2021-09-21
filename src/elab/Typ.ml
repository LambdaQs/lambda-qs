open AbsLambdaQs

(*
  This module is based on the SimPL type checker
  https://cs3110.github.io/textbook/chapters/interp/typecheck.html
 *)

(** The error message produced if a variable is unbound. *)
let unbound_var_err = "Unbound variable"

let plus_err = "Operator and operand type mismatch"

let type_err = "Types do not match"

(** A [Context] is a mapping from variable names to
    types, aka a symbol table, aka a typing environment. *)
module type Context = sig

  (** [t] is the type of a context. *)
  type t

  (** [empty] is the empty context. *)
  val empty : t

  (** [lookup ctx x] gets the binding of [x] in [ctx].
      Raises: [Failure unbound_var_err] if [x] is
      not bound in [ctx]. *)
  val lookup : t -> var -> typ

  (** [extend ctx x ty] is [ctx] extended with a binding
      of [x] to [ty]. *)
  val extend : t -> var -> typ -> t
end

(** The [Context] module implements the [Context] signature
    with an association list. *)
module Context : Context = struct
  type t = (var * typ) list

  let empty = []

  let lookup ctx x =
    try List.assoc x ctx
    with Not_found -> failwith unbound_var_err

  let extend ctx x ty =
    (x, ty) :: ctx
end

open Context

(** [typeof ctx e] is the type of [e] in context [ctx].
    Raises: [Failure] if [e] is not well typed in [ctx]. *)
let rec typeof ctx = function
  | ENat  _           -> TNat
  | ETriv             -> TUnit
  | EQloc _           -> TQbit
  | ECmd  _           -> TCmd
  | EVar  x           -> lookup ctx x
  | EVarT (x, t)      -> if (lookup ctx x = t) then t
                         else failwith type_err
  | EPlus (e1, e2)    -> typeof_plus ctx e1 e2
  | ELet  (x, e1, e2) -> typeof_let  ctx x e1 e2
  | ELam  (x, t, e)   -> typeof_lam  ctx x t e
  | EAp   (e1, e2)    -> typeof_ap   ctx e1 e2

and typeof_plus ctx e1 e2 =
  let t1, t2 = typeof ctx e1, typeof ctx e2 in
  match t1, t2 with
  | TNat, TNat -> TNat
  | _ -> failwith plus_err

and typeof_let ctx x e1 e2 =
  let t1 = typeof ctx e1 in
  let ctx' = extend ctx x t1 in
  typeof ctx' e2

and typeof_lam ctx x t1 e =
  let ctx' = extend ctx x t1 in
  let t2 = typeof ctx' e in
  TParr (t1, t2)

and typeof_ap ctx e1 e2 =
  match typeof ctx e1 with
  | TParr (t1, t2) -> if (typeof ctx e2 = t1)
                      then t2 else failwith type_err
  | _ -> failwith type_err

(** [typecheck e] checks whether [e] is well typed in
    the empty context. Raises: [Failure] if not. *)
let typecheck e =
  ignore (typeof empty e)
