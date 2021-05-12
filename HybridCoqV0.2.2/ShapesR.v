(****************************************************************

   File: ShapesR.v
   Author: Amy Felty

   original: January 2010
   updated: March 2014
   Mar 2021: Current Coq Version: V8.13.1

   Context relation version (R version) of
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

Inductive avR : list atm -> list atm -> Prop :=
| nil_av: avR nil nil
| cons_av: forall (Phi Psi:list atm) (x y:uexp), proper x -> proper y ->
    avR Phi Psi -> avR (eq_a x y::Phi) (varE y::varT x::Psi).

Hint Resolve nil_av cons_av : hybrid.

Lemma memb_av : forall (Phi Psi:list atm) (x y:uexp),
  avR Phi Psi -> In (eq_a x y) Phi ->
  (In (varT x) Psi /\ In (varE y) Psi).
Proof.
intros Phi Psi x y; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma eq_shape :
  forall (i:nat) (T E:uexp) (Phi Psi:list atm), avR Phi Psi ->
  seq_ i Phi (atom_ (eq_a T E)) ->
  seq_ (2*i+2) Psi (atom_ (shape T E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T E:uexp) (Phi Psi:list atm), avR Phi Psi ->
     seq_ i Phi (atom_ (eq_a T E)) ->
     seq_ (2*i+2) Psi (atom_ (shape T E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T E Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + generalize (eq_lam_inv i0 Phi T0 E0 H3); clear H3; intros [j [h1 h2]];
      subst.
    replace (2*(j+3+1)+2) with (2*j+1+1+1+1+1+1+1+1+1+1); try lia.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (All (fun y:uexp =>
            (Imp (varT x) (Imp (varE y) (atom_ (shape (T0 x) (E0 y)))))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    apply s_all; auto.
    intros y h3.
    apply s_imp; auto.
    apply s_imp; auto.
    apply seq_mono with (2*j+2); auto; try lia.
    apply h with (eq_a x y::Phi); eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    replace (2*(i+1+1)+2) with (2*i+1+1+1+1+1+1); try lia.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (shape T1 E1)) (atom_ (shape T2 E2)));
      auto with hybrid.
    apply s_and; auto.
    * apply seq_mono with (2*i+2); auto; try lia.
      apply h with Phi; try lia; auto.
    * apply seq_mono with (2*i+2); auto; try lia.
      apply h with Phi; try lia; auto.
(* context case *)
- inversion cInv; subst.
  specialize memb_av with (1:=cInv) (2:=H2); intros [h1 h2]; clear H2.
  replace (2*i+2) with (2*i+1+1); try lia.
  unfold seq_,atom_; apply s_bc with (Conj (atom_ (varT T)) (atom_ (varE E)));
    auto with hybrid.
  apply s_and; auto.
  + apply s_init; auto with hybrid.
  + apply s_init; auto with hybrid.
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

#[global] Hint Resolve nil_av cons_av : hybrid.

(****************************************************************
 2. Theorem: if shape T E and varTOcc T N then varTOcc E N.
    or equivalently
    Theorem: if shape T E then all N. varTOcc T N implies varTOcc E N.
  ****************************************************************)

Section bndEq.

(************)
(* Contexts *)
(************)

Inductive vR : list atm -> list atm -> list atm -> Prop :=
| nil_v: vR nil nil nil
| cons_v: forall (Phi Psi Psi':list atm) (n:nat) (x:uexp), proper x ->
    vR Phi Psi Psi' ->
    vR (varE x::varT (Var n)::Phi) (varT (Var n)::Psi) (varE x::Psi').

Hint Resolve nil_v cons_v : hybrid.

Lemma memb_v1 : forall (Phi Psi Psi':list atm), vR Phi Psi Psi' ->
  forall (a:atm), In a Phi ->
  (exists n:nat, a=(varT (Var n))) \/ (exists E:uexp, a=(varE E)).
Proof.
intros Phi Psi Psi'; induction 1; auto.
- simpl; intros a h; elim h.
- intros a h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
  + right; exists x; auto.
  + left; exists n; auto.
  + auto.
Qed.

Lemma memb_v2 : forall (Phi Psi Psi':list atm), vR Phi Psi Psi' ->
  forall (a:atm), In a Psi -> exists n:nat, a=(varT (Var n)).
Proof.
intros Phi Psi Psi'; induction 1.
- simpl; intros a h; elim h.
- intros a h2; simpl in h2; destruct h2 as [h2 | h2].
  + exists n; auto.
  + auto.
Qed.

Lemma memb_v3 : forall (Phi Psi Psi':list atm), vR Phi Psi Psi' ->
  forall (x:uexp), In (varE x) Phi -> In (varE x) Psi'.
Proof.
intros Phi Psi Psi'; induction 1; auto.
intros y h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- injection h2; intros; subst; simpl; auto.
- discriminate h2.
- simpl; auto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma bndEq :
  forall (i N:nat) (T E:uexp) (Phi Psi Psi':list atm),
  vR Phi Psi Psi' ->
  seq_ i Phi (atom_ (shape T E)) -> 
  seq_ i Psi (atom_ (varTOcc T N)) ->
  seq_ i Psi' (atom_ (varEOcc E N)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (N:nat) (T E:uexp) (Phi Psi Psi':list atm),
     vR Phi Psi Psi' ->
     seq_ i Phi (atom_ (shape T E)) -> 
     seq_ i Psi (atom_ (varTOcc T N)) ->
     seq_ i Psi' (atom_ (varEOcc E N)))).
intro H'.
apply H'; clear H' i; auto.
intros i h N T E Phi Psi Psi' cInv h1 h2.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* varT/varE case *)
  + inversion H3; subst; clear H3.
    specialize memb_v1 with (1:=cInv); intro cInv1.
    specialize memb_v2 with (1:=cInv); intro cInv2.
    specialize memb_v3 with (1:=cInv); intro cInv3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      -- inversion H4; subst; clear H4.
         ++ inversion H1; subst; clear H1.
         ++ specialize cInv1 with (1:=H6).
            elim cInv1; clear cInv1; intros [x h1]; discriminate h1.
      -- inversion H4; subst; clear H4.
         ++ inversion H1; subst; clear H1.
         ++ specialize cInv1 with (1:=H6).
            elim cInv1; clear cInv1; intros [x h1]; discriminate h1.
      -- unfold seq_,atom_; apply s_bc with (atom_ (varE E)); auto with hybrid.
         inversion H5; subst; clear H5.
         ++ inversion H1; subst; clear H1.
         ++ specialize cInv3 with (1:=H6).
            generalize cInv3; case Psi'.
            ** simpl; tauto.
            ** intros a Phi h1.
               apply s_init; auto with hybrid.
    * specialize cInv2 with (1:=H2); elim cInv2.
      intros x h1; discriminate h1.
  (* lam case *)
  + specialize shape_lam_inv with (1:=H3); intros [j [h1 h3]]; subst; clear H3.
    replace (j+4+1) with (j+1+1+1+1+1); try lia.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (varE x) (atom_ (varEOcc (E0 x) N)))));
      auto with hybrid.
    apply s_all.
    intros x h1.
    apply s_imp.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      -- inversion H4; subst; clear H4.
         specialize H8 with (1:=(proper_Var 0)).
         inversion H8; subst; clear H8.
         specialize h3 with (1:=(proper_Var 0)) (2:=h1).
         assert (i=j+1+1); try lia; subst; clear H.
         assert (h2: seq_ (j+1+1) (varE x :: varT (Var 0) :: Phi)
                          (atom_ (shape (T0 (Var 0)) (E0 x)))).
         { apply seq_mono with j; try lia; auto. }
         apply h with (T (Var 0)) (varE x :: varT (Var 0) :: Phi) (varT (Var 0) :: Psi);
           auto; try lia.
         ++ eauto with hybrid.
         ++ specialize abstr_lbind_simp with (1:=H7) (2:=H2) (3:=H0); intro h4.
            rewrite -> h4; auto with hybrid.
      -- inversion H4; subst; clear H4.
         ++ inversion H1; subst; clear H1.
         ++ specialize memb_v2 with (1:=cInv); intro cInv2.
            specialize cInv2 with (1:=H6); elim cInv2.
            intros y h2; discriminate h2.
    * specialize memb_v2 with (1:=cInv); intro cInv2.
      specialize cInv2 with (1:=H3); elim cInv2.
      intros y h2; discriminate h2.
  (* app/apply case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      -- inversion H3; subst; clear H3.
         assert (i=i1); try lia; subst; clear H.
         unfold seq_,atom_;
           apply s_bc with (Conj (atom_ (varEOcc E1 N1)) (atom_ (varEOcc E2 N2)));
           auto with hybrid.
         apply s_and; auto.
         ++ apply h with T1 Phi Psi; auto; try lia.
         ++ apply h with T2 Phi Psi; auto; try lia.
      -- inversion H3; subst; clear H3.
         ++ inversion H1; subst; clear H1.
         ++ specialize memb_v2 with (1:=cInv); intro cInv2.
            specialize cInv2 with (1:=H6); elim cInv2.
            intros x h1; discriminate h1.
    * specialize memb_v2 with (1:=cInv); intro cInv2.
      specialize cInv2 with (1:=H2); elim cInv2.
      intros x h1; discriminate h1.
(* context case *)
- specialize memb_v1 with (1:=cInv); intro cInv1.
  specialize cInv1 with (1:=H2); elim cInv1; intros [x h1]; discriminate h1.
Qed.

End bndEq.
