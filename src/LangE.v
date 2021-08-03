Require Import Metalib.Metatheory.
Require Import LangE_ott.
Import StlcNotations.
Require Import LangE_inf.

(*
  Lemma 4.3 (Weakening). If Γ ⊢ e′: τ′, then Γ, x : τ ⊢ e′: τ′
  for any x `notin`dom(Γ) and any type τ.
*)
Lemma weakening :
  forall G e' T' x T,
    typing G e' T' ->
    x `notin` dom G ->
    typing (x ~ T ++ G) e' T'.
Proof.
  intros G e' T' x T H X.
  (* generalize dependent G. *)
  induction H; auto.
  (* - apply binds_weaken. *)
Abort.


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
  (* generalize dependent T'. *)
  induction H;
  (* intros T' J; *)
  inversion H0; eauto; subst.
  pick fresh x.
  eapply H2; eauto.
  rewrite (subst_exp_intro x); eauto.
  rewrite subst_exp_open_exp_wrt_exp; auto.

  specialize (H1 x).
  (* pose (B := H1 Fr). *)
  (* case let/definition *)
  (* pose proof (H1 Fr). *)

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
