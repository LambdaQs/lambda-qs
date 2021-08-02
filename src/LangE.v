Require Import Metalib.Metatheory.
Require Import LangE_ott.
Require Import LangE_inf.

(*
  Lemma 4.1 (Unicity of Typing). For every typing context Γ and expression e,
  there exists at most one τ such that Γ ⊢ e : τ.
*)
Lemma unicity :
  forall (G:ctx) (e:exp) (T T':typ),
   typing G e T ->
   typing G e T' ->
   T = T'.
Proof.
  intros.
  induction H; inversion H0; eauto.
  (* case let/definition *)
  subst.
Abort.

(*
  Lemma 4.2 (Inversion for Typing). Suppose that Γ ⊢ e : τ. If e = plus(e1; e2),
  then τ = num, Γ ⊢ e1 : num, and Γ ⊢ e2 : num, and similarly for the other
  constructs of the language.
*)
Lemma inversion :
  forall G e T e1 e2,
  typing G e T ->
  e = e_addition e1 e2 ->
  T = Ty_numbers -> typing G e1 Ty_numbers -> typing G e2 Ty_numbers.
Proof.
  intros.
  generalize dependent G.
  intros.
   induction H.
  -

  Abort.
