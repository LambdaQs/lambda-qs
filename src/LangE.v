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
  induction H; intros T' J; inversion J; subst; eauto.
  2: {
    apply IHtyping in H5. subst.
    pick fresh x.
    eapply H1; eauto.
   }
  -
Abort.

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
  forall (E F G : ctx) e' T',
    typing (G ++ E) e' T' ->
    uniq (G ++ F ++ E) ->
    typing (G ++ F ++ E) e' T'.
Proof.
  intros E F G e' T' H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst; eauto.
  (* letdef case  *)
  - apply (T_41h (dom (G0 ++ F ++ E) \u L) _ _ _ _ T1); eauto.
    intros.
    rewrite_env (([(x, T1)] ++ G0) ++ F ++ E).
    apply H1; auto.
      simpl_env. apply uniq_push; auto.
Qed.
