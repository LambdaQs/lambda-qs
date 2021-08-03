Require Import Metalib.Metatheory.
Require Import LangE_ott.
Import StlcNotations.
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
  generalize dependent T'.
  induction H; intros T' J; inversion J; eauto; subst.
  (* case let/definition *)
  specialize (IHtyping T').
  (* pick fresh x for (L \u L0). *)
  (* eapply H1; eauto. *)
  pick fresh x for L.
  specialize (H0 x).
  specialize (H1 x).
  (* specialize (H7 x). *)
  pose proof (H0 Fr).
  pose proof (H1 Fr).
  specialize (H3 T').
  (* rewrite IHtyping in H2. *)
  eapply H1; eauto.
  rewrite (subst_exp_intro x); eauto.
Abort.

(*
  Lemma 4.2 (Inversion for Typing). Suppose that Γ ⊢ e : τ. If e = plus(e1; e2),
  then τ = num, Γ ⊢ e1 : num, and Γ ⊢ e2 : num, and similarly for the other
  constructs of the language.
*)
Lemma inversion :
  forall G e T e1 e2,
  typing G e T ->
  e = plus e1 e2 ->
  T = Ty_num -> typing G e1 Ty_num -> typing G e2 Ty_num.
Proof.
  intros.
  generalize dependent G.
  intros.
   induction H.
  -

  Abort.
