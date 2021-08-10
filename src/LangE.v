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
  - apply binds_unique with (E := G) (x := x); auto.
  - apply IHtyping in H5. subst.
    pick fresh x.
    eapply H1; eauto.
Qed.

(*
  Lemma 4.2 (Inversion for Typing). Suppose that Γ ⊢ e : τ. If e = plus(e1; e2),
  then τ = num, Γ ⊢ e1 : num, and Γ ⊢ e2 : num, and similarly for the other
  constructs of the language.

  NOTE: only for `plus` here.
*)
Lemma inversion_plus :
  forall G e T e1 e2,
    typing G e T ->
    e = plus e1 e2 ->
    T = Ty_num -> typing G e1 Ty_num -> typing G e2 Ty_num.
Proof.
  intros G e T e1 e2 H P.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; inversion P.
  subst; auto.
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

(* the following three lemmas used in substitution lemma below
   are taken from Stlc tutorial. *)
Lemma subst_neq_var : forall (x y : var) u,
  y <> x -> [x ~> u](var_f y) = var_f y.
Proof.
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x).
  (* - Case "left". *)
  - destruct Neq. auto.
  (* - Case "right". *)
  - auto.
Qed.

Lemma subst_var : forall (x y : var) u e,
  y <> x ->
  lc_exp u ->
  ([x ~> u] e) ^ y = [x ~> u] (e ^ y).
Proof.
  intros x y u e Neq H.
  rewrite subst_exp_open_exp_wrt_exp with (e2 := var_f y); auto.
  rewrite subst_neq_var; auto.
Qed.

Lemma typing_to_lc_exp : forall E e T,
  typing E e T -> lc_exp e.
Proof.
  intros E e T H. induction H; eauto.
Qed.

(*
  Lemma 4.4 (Substitution). If Γ, x : τ ⊢ e′ : τ′ and Γ ⊢ e : τ,
  then Γ ⊢ [e/x]e′ : τ′.
*)
Lemma substitution :
  forall G E x T T' e e',
    typing (G ++ x ~ T ++ E) e' T' ->
    typing E e T ->
    typing (G ++ E) ([x ~> e] e') T'.
Proof.
  intros G E x T T' e e' He' He.
  remember (G ++ x ~ T ++ E) as E'.
  generalize dependent G.
  induction He'; intros G0 Eq; subst; simpl; auto.
  - (* var case *)
    destruct (x0 == x); subst.
    + (* case x0 = x *)
      assert (T0 = T); subst.
      * eapply binds_mid_eq.
        apply H0.
        auto.
      * apply weakening with (G := nil).
          apply He.
          simpl_env. eapply uniq_remove_mid. apply H.
    + (* case x0 != x *)
      eapply T_41a.
        * eapply uniq_remove_mid. apply H.
        * eapply binds_remove_mid.
            apply H0.
            auto.
  - (* letdef case *)
    apply (T_41h ({{x}} \u L) _ _ _ _ T1).
      + apply IHHe'; auto.
      + intros z Frz.
        rewrite subst_var; auto.
        * rewrite_env ((z ~ T1 ++ G0) ++ E).
          apply H0; eauto.
        * apply (typing_to_lc_exp E e T); auto.
Qed.

(*
  Lemma 4.5 (Decomposition). If Γ ⊢ [e/x]e′ : τ′,
  then for every type τ such that Γ ⊢ e : τ,
  we have Γ, x : τ ⊢ e′ : τ′.

  Note: converse of substitution
*)
Lemma decomposition :
  forall E e e' x T T',
    typing E ([x ~> e] e') T' ->
    typing E e T ->
    typing (x ~ T ++ E) e' T'.
Proof.
  intros E e e' x T T' Hs He.
  induction Hs; auto.
  Abort.

(* Theorem 6.2 (Preservation). If e : τ and e |--> e′, then e′ : τ. *)
Theorem preservation :
  forall e e' T,
    typing nil e T ->
    trans e e' ->
    typing nil e' T.
Proof.
  intros.
  induction H; inversion H0; subst; auto.
  -
Abort.

(*
  Theorem 6.4 (Progress). If e : τ, then either e val,
  or there exists e′ such that e |--> e′.
*)
Theorem progress :
  forall e T,
    typing nil e T ->
    is_value e \/ (exists e', trans e e').
Proof.
Abort.
