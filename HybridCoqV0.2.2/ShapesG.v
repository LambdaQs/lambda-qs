(****************************************************************

   File: ShapesG.v
   Author: Amy Felty

   original: January 2010
   updated: March 2014
   Mar 2021: Current Coq Version: V8.13.1

   Generalized context version (G version) of
   proofs of properties about equality and shapes.

  ***************************************************************)

From HybridSys Require Export Shapes.

(****************************************************************
  1. If equal T E then shape T E.
  ****************************************************************)

Section eqsh.

(************)
(* Contexts *)
(************)

Inductive avG : list atm -> Prop :=
| nil_av: avG nil
| cons_av: forall (Phi:list atm) (x y:uexp), proper x -> proper y ->
    avG Phi -> avG (eq_a x y::varE y::varT x::Phi).

Hint Resolve nil_av cons_av : hybrid.

Lemma memb_av : forall (Phi:list atm) (x y:uexp),
  avG Phi -> In (eq_a x y) Phi ->
  (In (varT x) Phi /\ In (varE y) Phi).
Proof.
intros Phi x y; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | [h2 | h2]]].
- injection h2; intros; subst; simpl; auto.
- discriminate h2.
- discriminate h2.
- simpl; tauto.
Qed.

Lemma shape_strengthen_weaken :
  forall (i:nat) (T E:uexp) (Phi Psi:list atm),
  (forall (T:uexp), In (varT T) Phi <->  In (varT T) Psi) ->
  (forall (E:uexp), In (varE E) Phi <->  In (varE E) Psi) ->
  (forall (T E:uexp), In (shape T E) Phi <-> In (shape T E) Psi) ->
  seq_ i Phi (atom_ (shape T E)) ->
  seq_ i Psi (atom_ (shape T E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T E:uexp) (Phi Psi:list atm),
     (forall (T:uexp), In (varT T) Phi <->  In (varT T) Psi) ->
     (forall (E:uexp), In (varE E) Phi <->  In (varE E) Psi) ->
     (forall (T E:uexp), In (shape T E) Phi <-> In (shape T E) Psi) ->
     seq_ i Phi (atom_ (shape T E)) ->
     seq_ i Psi (atom_ (shape T E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T E Phi Psi h1 h2 h3' h4.
inversion h4; subst; clear h4.
- inversion H0; subst; clear H0.
  (* varT/varE case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (varT T)) (atom_ (varE E)));
      eauto with hybrid.
    apply s_and; auto.
    * inversion H4; subst; clear H4.
      -- inversion H0; subst; clear H0.
      -- destruct (h1 T) as [h3 h4].
         specialize (h3 H2).
         generalize h3; clear h3; case Psi; try (simpl; tauto).
         intros a l h3; apply s_init; auto.
    * inversion H5; subst; clear H5.
      -- inversion H0; subst; clear H0.
      -- destruct (h2 E) as [h3 h4].
         specialize (h3 H2).
         generalize h3; clear h3; case Psi; try (simpl; tauto).
         intros a l h3; apply s_init; auto.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp =>
                  (All (fun y:uexp =>
                          (Imp (varT x) (Imp (varE y) (atom_ (shape (T0 x) (E0 y)))))))));
      eauto with hybrid.
    apply s_all; auto.
    intros x h3.
    generalize (H4 x h3); clear H4; intro h4.
    inversion h4; subst; clear h4.
    apply s_all; auto.
    intros y h4.
    generalize (H3 y h4); clear H3; intro h5.
    inversion h5; subst; clear h5.
    inversion H3; subst; clear H3.
    apply s_imp; auto.
    apply s_imp; auto.
    apply h with (varE y::varT x::Phi); auto; try lia.
    (* proof of extended context inv *)
    * intros T; generalize (h1 T); simpl; tauto.
    * intros E; generalize (h2 E); simpl; tauto.
    * intros T E; generalize (h3' T E); simpl; tauto.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=h2) (4:=h3') (5:=H4).
    specialize h' with (1:=hi) (2:=h1) (3:=h2) (4:=h3') (5:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (shape T1 E1)) (atom_ (shape T2 E2)));
      auto with hybrid.
    apply s_and; auto.
(* context case *)
- destruct (h3' T E) as [h4 h5].
  generalize (h4 H2).
  case Psi.
  + simpl; tauto.
  + intros a Phi h6.
    apply s_init; auto with hybrid.
Qed.

Lemma d_str_av2v_shape :
  forall (i:nat) (T E x y:uexp) (Gamma:list atm),
  seq_ i (eq_a x y::varE y::varT x::Gamma) (atom_ (shape T E)) ->
  seq_ i (varE y::varT x::Gamma) (atom_ (shape T E)).
Proof.
intros i T T' x y Gamma h.
apply shape_strengthen_weaken with (eq_a x y::varE y::varT x::Gamma); auto.
- clear h T T' i.
  intros T; simpl; split.
  + intros [h1 | [h1 | [h1 | h1]]]; try discriminate h1; auto.
  + intros [h1 | [h1 | h1]]; try discriminate h1; auto.
- clear h T T' i.
  intros E; simpl; split.
  + intros [h1 | [h1 | [h1 | h1]]]; try discriminate h1; auto.
  + intros [h1 | [h1 | h1]]; try discriminate h1; auto.
- clear h T T' i.
  intros T E; simpl; split.
  + intros [h1 | [h1 | [h1 | h1]]]; try discriminate h1; auto.
  + intros [h1 | [h1 | h1]]; try discriminate h1; auto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma eq_shape :
  forall (i:nat) (T E:uexp) (Phi:list atm), avG Phi ->
  seq_ i Phi (atom_ (eq_a T E)) ->
  seq_ (2*i+2) Phi (atom_ (shape T E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T E:uexp) (Phi:list atm), avG Phi ->
     seq_ i Phi (atom_ (eq_a T E)) ->
     seq_ (2*i+2) Phi (atom_ (shape T E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T E Phi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + generalize (eq_lam_inv i0 Phi T0 E0 H3); clear H3; intros [j [h1 h2]];
      subst.
    replace (2*(j+3+1)+2) with (2*j+1+1+1+1+1+1+1+1+1+1); try lia.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp =>
                  (All (fun y:uexp =>
                          (Imp (varT x) (Imp (varE y) (atom_ (shape (T0 x) (E0 y)))))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    apply s_all; auto.
    intros y h3.
    apply s_imp; auto.
    apply s_imp; auto.
    apply seq_mono with (2*j+2); auto; try lia.
    apply d_str_av2v_shape; auto.
    apply h; eauto with hybrid; try lia.
    apply seq_thin_exch with (eq_a x y::Phi); auto.
    * intro a; simpl; tauto.
    * apply h2; auto.
  (* app case *)
  + inversion H3; subst; clear H3.
    replace (2*(i+1+1)+2) with (2*i+1+1+1+1+1+1); try lia.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (shape T1 E1)) (atom_ (shape T2 E2)));
      auto with hybrid.
    apply s_and; auto.
    * apply seq_mono with (2*i+2); auto; try lia.
      apply h; try lia; auto.
    * apply seq_mono with (2*i+2); auto; try lia.
      apply h; try lia; auto.
(* context case *)
- inversion cInv; subst.
  specialize memb_av with (1:=cInv) (2:=H2); intros [h1 h2]; clear H2.
  replace (2*i+2) with (2*i+1+1); try lia.
  unfold seq_,atom_; apply s_bc with (Conj (atom_ (varT T)) (atom_ (varE E)));
    auto with hybrid.
  apply s_and; auto.
  * apply s_init; auto with hybrid.
  * apply s_init; auto with hybrid.
Qed.

Lemma eq_shape_cor : forall (T E:uexp),
 seq0 (atom_ (eq_a T E)) -> seq0 (atom_ (shape T E)).
Proof.
intros T E [i h1].
generalize nil_av; intro h2.
specialize eq_shape with (1:=h2) (2:=h1); intro h.
exists (2*i+2); auto.
Qed.

End eqsh.
