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
  apply IHtyping in H5. subst.
  pick fresh x.
  eapply H1; eauto.
Qed.

(*
  Lemma 4.2 (Inversion for Typing). Suppose that Γ ⊢ e : τ. If e = plus(e1; e2),
  then τ = num, Γ ⊢ e1 : num, and Γ ⊢ e2 : num, and similarly for the other
  constructs of the language.

  NOTE: only for `plus` here.
*)
(* TODO: is the statement correct? *)
Lemma inversion :
  forall G e T e1 e2,
  typing G e T ->
  e = plus e1 e2 ->
  T = Ty_num -> typing G e1 Ty_num -> typing G e2 Ty_num.
Proof.
  intros G e T e1 e2 H P.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; inversion P.
  subst e3 e0; auto.
Qed.

(*
  Lemma 4.3 (Weakening). If Γ ⊢ e′: τ′, then Γ, x : τ ⊢ e′: τ′
  for any x `notin` dom(Γ) and any type τ.
*)
Lemma weakening :
  forall G e' T' x T,
    typing G e' T' ->
    x `notin` dom G ->
    typing (x ~ T ++ G) e' T'.
Proof.
  intros G e' T' x T H Fx.
  (* generalize dependent T'. *)
  induction H; auto.
  (* var_f case *)
  (* - apply (typing_var_f x0). *)
  (* - apply binds_weaken. *)
Abort.