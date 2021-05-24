(* Typ, τ *)
Inductive tp : Type :=
| num : tp
| str : tp
.

(*
  Generic hypothetical judgment of the form
    Χ | Γ ⊢ e : τ
  where Χ is a finite set of variables and
  Γ is the typing context.
*)
