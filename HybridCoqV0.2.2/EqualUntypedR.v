(****************************************************************

   File: EqualUntypedR.v
   Author: Amy Felty

   original: January 2014
   Apr 2021: Current Coq Version: V8.13.1

   Context relation version (R version) of:
   1. Admissibility of reflexivity for algorithmic equality
   2. Admissibility of symmetry, transitivity for algorithmic equality
   3. Correctness of algorithmic equality with respect to declaritive
      equality.
   4. Adequacy

  ***************************************************************)

From HybridSys Require Export sl.

#[global] Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
#[global] Hint Resolve proper_APP abstr_proper : hybrid.
#[global] Hint Unfold proper: hybrid.

Section encoding.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set := cAPP: Econ | cLAM: Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition app : uexp -> uexp -> uexp :=
  fun M:uexp => fun N:uexp => (APP (APP (CON cAPP) M) N).
Definition lam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON cLAM) (lambda M)).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

Lemma proper_lam : forall (e:uexp->uexp), abstr e -> proper (lam e).
Proof.
unfold lam; auto with hybrid.
Qed.

Lemma proper_app : forall e1 e2:uexp,
  proper e1 -> proper e2 -> proper (app e1 e2).
Proof.
unfold app; auto with hybrid.
Qed.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Inductive atm : Set :=
   term : uexp -> atm
 | deq : uexp -> uexp -> atm
 | aeq : uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  (* well-formedness of terms (app and lam) *)
  | tm_a : forall M N:uexp,
      prog (term (app M N))
        (Conj (atom_ (term M)) (atom_ (term N)))
  | tm_l : forall M:uexp->uexp, abstr M ->
      prog (term (lam M))
        (All (fun x:uexp =>
          (Imp (term x) (atom_ (term (M x))))))
  (* declarative equality *)
  | de_l :forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (deq (lam M) (lam N))
        (All (fun x:uexp =>
          (Imp (term x)
            (Imp (deq x x) (atom_ (deq (M x) (N x)))))))
  | de_a : forall M1 M2 N1 N2:uexp,
      prog (deq (app M1 M2) (app N1 N2))
        (Conj (atom_ (deq M1 N1)) (atom_ (deq M2 N2)))
  | de_r : forall M:uexp, 
      prog (deq M M) (atom_ (term M))
  | de_s : forall M1 M2:uexp, 
      prog (deq M2 M1) (atom_ (deq M1 M2))
  | de_t : forall M1 M2 M3:uexp,
      prog (deq M1 M3) (Conj (atom_ (deq M1 M2)) (atom_ (deq M2 M3)))
  (* algorithmic equality *)
  | ae_l :forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (aeq (lam M) (lam N))
        (All (fun x:uexp =>
          (Imp (aeq x x) (atom_ (aeq (M x) (N x))))))
  | ae_a : forall M1 M2 N1 N2:uexp,
      prog (aeq (app M1 M2) (app N1 N2))
        (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2))).

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

End encoding.

#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tm_a tm_l de_l de_a de_r de_s de_t ae_l ae_a : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Admissibility of Reflexivity
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_refl.

(* Context Relation for Admissibility of Reflexivity and aeq Adequacy *)
Inductive xaR : list atm -> list atm -> Prop :=
| nil_xa : xaR nil nil
| cons_xa : forall (Phi_x Phi_a:list atm) (x:uexp), proper x ->
    xaR Phi_x Phi_a -> xaR (term x::Phi_x) (aeq x x::Phi_a).

(* Context Membership *)
Lemma memb_refl_iff : forall (Phi_x Phi_a:list atm) (T:uexp),
xaR Phi_x Phi_a -> (In (term T) Phi_x <-> In (aeq T T) Phi_a).
Proof.
intros Phi_a Phi_x T; induction 1; try (simpl; tauto).
split.
- intro h2; simpl in h2; destruct h2 as [h2 | h2].
  + injection h2; intros; subst; simpl; auto.
  + simpl; tauto.
- intro h2; simpl in h2; destruct h2 as [h2 | h2].
  + injection h2; intros; subst; simpl; auto.
  + simpl; tauto.
Qed.

(* Membership corollary *)
Lemma memb_refl : forall (Phi_x Phi_a:list atm) (T:uexp),
xaR Phi_x Phi_a -> In (term T) Phi_x -> In (aeq T T) Phi_a.
Proof.
intros Phi_x Phi_a T h1 h2.
generalize (memb_refl_iff Phi_x Phi_a T h1); intros [h3 h4].
auto.
Qed.

End ctx_refl.

#[global] Hint Resolve nil_xa cons_xa memb_refl : hybrid.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section refl.

Lemma aeq_refl :
  forall (i:nat) (T:uexp) (Phi_x Phi_a:list atm),
  xaR Phi_x Phi_a ->
  seq_ i Phi_x (atom_ (term T)) ->
  seq_ i Phi_a (atom_ (aeq T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi_x Phi_a:list atm),
     xaR Phi_x Phi_a ->
     seq_ i Phi_x (atom_ (term T)) ->
     seq_ i Phi_a (atom_ (aeq T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi_x Phi_a cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (aeq M M)) (atom_ (aeq N N)));
      auto with hybrid.
    apply s_and; auto.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M x) (M x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    generalize (H4 x h1); intro h2.
    inversion h2; subst; clear h2.
    apply s_imp; auto.
    apply h with (term x::Phi_x); eauto with hybrid; try lia.
(* context case *)
- inversion cInv; subst.
  apply s_init; eauto with hybrid.
Qed.

(* Empty context corollary *)
Lemma aeq_refl_cor :
  forall (T:uexp), seq0 (atom_ (term T)) -> seq0 (atom_ (aeq T T)).
Proof.
intros T [n h].
generalize nil_xa; intro h1.
specialize aeq_refl with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End refl.

(****************************************************************
 2. Admissibility of Symmetry and Transivity
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_symm_tr.

(* Context Relation for Symmetry and Transitivity *)
Inductive aG : list atm -> Prop :=
| nil_a : aG nil
| cons_a : forall (Phi_a:list atm) (x:uexp), proper x ->
    aG Phi_a -> aG (aeq x x::Phi_a).

(* Membership Lemma: used in symmetry and transitivity proofs *)
Lemma memb_symm_tr: forall (Phi_a:list atm) (T T':uexp),
  aG Phi_a -> In (aeq T T') Phi_a -> T=T'.
Proof.
intros Phi_a T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2]; auto.
injection h2; intros; subst; simpl; auto.
Qed.

End ctx_symm_tr.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

#[global] Hint Resolve nil_a cons_a : hybrid.

Section symm_tr.

Lemma aeq_symm :
  forall (i:nat) (T T':uexp) (Phi_a:list atm),
  aG Phi_a ->
  seq_ i Phi_a (atom_ (aeq T T')) ->
  seq_ i Phi_a (atom_ (aeq T' T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi_a:list atm),
     aG Phi_a ->
     seq_ i Phi_a (atom_ (aeq T T')) ->
     seq_ i Phi_a (atom_ (aeq T' T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi_a cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (N x) (M x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h2.
    specialize H4 with (1:=h2).
    inversion H4; subst; clear H4.
    apply s_imp; auto.
    apply h; eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (aeq N1 M1)) (atom_ (aeq N2 M2)));
      auto with hybrid.
    apply s_and; auto.
    * apply h; try lia; auto.
    * apply h; try lia; auto.
(* context case *)
- inversion cInv; subst.
  specialize memb_symm_tr with (1:=cInv) (2:=H2); intro; subst; auto.
  apply s_init; eauto with hybrid.
Qed.

Lemma aeq_symm_cor : forall (T T':uexp),
 seq0 (atom_ (aeq T T')) -> seq0 (atom_ (aeq T' T)).
Proof.
intros T T' [i h1].
generalize nil_a; intro h3.
exists i; apply aeq_symm; auto.
Qed.

Lemma aeq_trans :
  forall (i:nat) (T R U:uexp) (Phi_a:list atm),
  aG Phi_a ->
  seq_ i Phi_a (atom_ (aeq T R)) ->
  seq_ i Phi_a (atom_ (aeq R U)) ->
  seq_ i Phi_a (atom_ (aeq T U)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T R U:uexp) (Phi_a:list atm),
     aG Phi_a ->
     seq_ i Phi_a (atom_ (aeq T R)) ->
     seq_ i Phi_a (atom_ (aeq R U)) ->
     seq_ i Phi_a (atom_ (aeq T U)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T R U Phi_a cInv h1 h2.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      specialize abstr_lbind_simp with (1:=H7) (2:=H5) (3:=H0); intro h1.
      rewrite H.
      unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M x) (N0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h2.
      inversion H6; subst; clear H6.
      specialize H10 with (1:=h2).
      unfold ext_eq in h1; rewrite -> h1 in H10; auto; clear H0 H7 h1 M0.
      assert (hi:i1=i); try lia; subst; clear H.
      specialize H4 with (1:=h2).
      inversion H10; subst; clear H10.
      inversion H4; subst; clear H4.
      apply s_imp; auto.
      assert (hi:i0=i); try lia; subst; clear H.
      apply h with (N x); eauto with hybrid; try lia.
    (* lam case: context subcase *)
    * specialize memb_symm_tr with (1:=cInv) (2:=H3); intro; subst.
      unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M x) (N x))))));
        auto with hybrid.
      apply s_all; auto.
  (* app case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      inversion H3; subst; clear H3.
      assert (hi:i1=i); try lia; subst; clear H.
      unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (aeq M1 N0)) (atom_ (aeq M2 N3)));
        auto with hybrid.
      apply s_and; auto.
      -- apply h with N1; try lia; auto.
      -- apply h with N2; try lia; auto.
    (* app case: context subcase *)
    * specialize memb_symm_tr with (1:=cInv) (2:=H2); intro; subst.
      unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- inversion cInv; subst.
  specialize memb_symm_tr with (1:=cInv) (2:=H2); intro; subst; auto.
Qed.

Lemma aeq_trans_cor : forall (T R U:uexp),
 seq0 (atom_ (aeq T R)) -> seq0 (atom_ (aeq R U)) ->
 seq0 (atom_ (aeq T U)).
Proof.
intros T R U [i h1] [j h2].
generalize nil_a; intro h3.
exists (i+j); apply aeq_trans with R; auto.
- apply seq_mono_cor with i; auto; try lia.
- apply seq_mono_cor with j; auto; try lia.
Qed.

End symm_tr.

(****************************************************************
 3. Correctness
  ****************************************************************)

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section de_inv.

Lemma de_l_inv :
forall (i:nat) (Psi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Psi (Imp (term x) (Imp (deq x x)
                   (atom_ (deq (T x) (T' x)))))) ->
exists j:nat, (i=j+2 /\ 
 forall x : uexp,
       proper x ->
       seq_ j ((deq x x)::(term x)::Psi) (atom_ (deq (T x) (T' x)))).
Proof.
induction i; auto.
- intros Psi T T' H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- generalize i; clear i IHi.
  induction i; auto.
  + intros Psi T T' H.
    generalize (H (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    inversion H4; clear H4; subst.
    replace (i0+1+1) with (S (S i0)) in H0; try lia.
  + intros Psi T T' H.
    exists i; split; try lia.
    intros x H0.
    generalize (H x H0); intro H1.
    inversion H1; clear H1; subst.
    inversion H5; clear H5; subst.
    assert (i1 = i); try lia.
    subst; auto.
Qed.

End de_inv.

(************)
(* Contexts *)
(************)

Section ctx_ceq.

(* Context Relation for Completeness (also used in adequacy) *)
Inductive adR : list atm -> list atm -> Prop :=
| nil_ad : adR nil nil
| cons_ad : forall (Phi_a Phi_xd:list atm) (x:uexp), proper x ->
    adR Phi_a Phi_xd ->
    adR (aeq x x::Phi_a) (deq x x::term x::Phi_xd).

(* Membership Lemma *)
Lemma memb_ceq : forall (Phi_a Phi_xd:list atm) (T T':uexp),
  adR Phi_a Phi_xd ->
  In (deq T T') Phi_xd -> In (aeq T T') Phi_a.
Proof.
intros Phi_a Phi_xd T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- injection h2; intros; subst; subst; simpl; auto.
- discriminate h2.
- simpl; right; auto with hybrid.
Qed.

Fixpoint rm_xd2x (l:list atm) {struct l} : list atm
  := match l with
       nil => nil
     | (deq x y::term z::l') => (term z::rm_xd2x l')
     | _ => nil
     end.

Hint Resolve nil_ad cons_ad : hybrid.

Lemma term_strengthen_weaken :
  forall (i:nat) (M:uexp) (Phi1 Phi2:list atm),
  (forall (M:uexp), In (term M) Phi1 ->  In (term M) Phi2) ->
  seq_ i Phi1 (atom_ (term M)) ->
  seq_ i Phi2 (atom_ (term M)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (M:uexp) (Phi1 Phi2:list atm),
     (forall (M:uexp), In (term M) Phi1 ->  In (term M) Phi2) ->
     seq_ i Phi1 (atom_ (term M)) ->
     seq_ i Phi2 (atom_ (term M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M Phi1 Phi2 h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H4).
    specialize h' with (1:=hi) (2:=h1) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (term M0)) (atom_ (term N)));
      auto with hybrid.
    apply s_and; auto.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (Imp (term x) (atom_ (term (M0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h5.
    generalize (H4 x h5); intro h6.
    inversion h6; subst; clear h6 H4.
    apply s_imp; auto.
    apply h with (term x::Phi1); auto; try lia.
    (* proof of extended context inv *)
    intro T; generalize (h1 T); simpl; tauto.
(* context case *)
- specialize h1 with (M:=M).
  generalize (h1 H2); clear h1 H2.
  case Phi2.
  + simpl; tauto.
  + intros a Phi1 h1.
    apply s_init; auto with hybrid.
Qed.

(* relation strengthening *)
Lemma adR2xaR_strengthen : forall (Phi_a Phi_xd:list atm),
  adR Phi_a Phi_xd -> xaR (rm_xd2x Phi_xd) Phi_a.
Proof.
intros Phi_a Phi_xd; induction 1; simpl; eauto with hybrid.
Qed.

Lemma c_str_xd2x_aux : forall (Phi_a Phi_xd:list atm) (M:uexp),
  adR Phi_a Phi_xd ->
  In (term M) Phi_xd ->
  In (term M) (rm_xd2x Phi_xd).
Proof.
intros Phi_a Phi_xd M; induction 1.
- simpl; tauto.
- simpl; intros [h1 | [h1 | h1]]; try tauto.
  discriminate h1.
Qed.

Hint Resolve c_str_xd2x_aux : hybrid.

Lemma c_str_xd2x :
  forall (i:nat) (Phi_a Phi_xd:list atm) (M:uexp),
  adR Phi_a Phi_xd ->
  seq_ i Phi_xd (atom_ (term M)) ->
  seq_ i (rm_xd2x Phi_xd) (atom_ (term M)).
Proof.
intros i Phi_xa Phi_xd M h1 h2.
apply term_strengthen_weaken with Phi_xd; eauto with hybrid.
Qed.

Lemma adRaG : forall (Phi_a Phi_xd:list atm),
  adR Phi_a Phi_xd -> aG Phi_a.
Proof.
intros Phi_a Phi_xd; induction 1; eauto with hybrid.
Qed.

End ctx_ceq.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section ceq.

Hint Resolve adR2xaR_strengthen c_str_xd2x : hybrid.

Lemma refl_promote :
  forall (i:nat) (T:uexp) (Phi_a Phi_xd:list atm),
  adR Phi_a Phi_xd ->
  seq_ i Phi_xd (atom_ (term T)) ->
  seq_ i Phi_a (atom_ (aeq T T)).
Proof.
intros i T Phi_a Phi_xd h h2.
apply aeq_refl with (rm_xd2x Phi_xd); eauto with hybrid.
  (* eauto applies adR2xaR_strengthen to first subgoal *)
  (* eauto applies c_str_xd2x with Phi_a to second subgoal *)
Qed.

Hint Resolve adRaG : hybrid.

Lemma symm_promote :
  forall (i:nat) (T T':uexp) (Phi_a Phi_xd:list atm),
  adR Phi_a Phi_xd ->
  seq_ i Phi_a (atom_ (aeq T T')) ->
  seq_ i Phi_a (atom_ (aeq T' T)).
Proof.
intros i T T' Phi_a Phi_xd h h2.
apply aeq_symm; eauto with hybrid.
Qed.

Lemma trans_promote :
  forall (i:nat) (T R U:uexp) (Phi_a Phi_xd :list atm),
  adR Phi_a Phi_xd ->
  seq_ i Phi_a (atom_ (aeq T R)) ->
  seq_ i Phi_a (atom_ (aeq R U)) ->
  seq_ i Phi_a (atom_ (aeq T U)).
Proof.
intros i T R U Phi_a Phi_xd h h2 h3.
apply aeq_trans with R; eauto with hybrid.
Qed.

Hint Resolve nil_ad cons_ad memb_ceq: hybrid.

Lemma eq_ceq :
  forall (i:nat) (M N:uexp) (Phi_a Phi_xd:list atm),
  adR Phi_a Phi_xd ->
  seq_ i Phi_xd (atom_ (deq M N)) ->
  seq_ i Phi_a (atom_ (aeq M N)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (M N:uexp) (Phi_a Phi_xd:list atm),
     adR Phi_a Phi_xd ->
     seq_ i Phi_xd (atom_ (deq M N)) ->
     seq_ i Phi_a (atom_ (aeq M N)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M N Phi_a Phi_xd cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (de_l_inv i Phi_xd M0 N0 H4); clear H4; intros [j [h1 h2]];
      subst.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M0 x) (N0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    apply seq_mono with (j+1); try lia.
    apply s_imp; auto.
    apply h with (deq x x::term x::Phi_xd);
      eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2)));
      auto with hybrid.
    apply s_and; auto.
    * apply h with Phi_xd; try lia; auto.
    * apply h with Phi_xd; try lia; auto.
  (* refl case *)
  + apply refl_promote with Phi_xd; auto.
    apply seq_mono with i0; auto; try lia.
  (* symm case *)
  + apply symm_promote with Phi_xd; auto.
    apply seq_mono with i0; try lia.
    apply h with Phi_xd; try lia; auto.
  (* trans case *)
  + inversion H3; subst; clear H3.
    apply trans_promote with M2 Phi_xd; auto.
    * apply seq_mono with i; try lia.
      apply h with Phi_xd; auto; try lia.
    * apply seq_mono with i; try lia.
      apply h with Phi_xd; auto; try lia.
(* context case *)
- inversion cInv; subst.
  apply s_init; eauto with hybrid.
Qed.

Lemma eq_ceq_cor : forall (T R:uexp),
 seq0 (atom_ (deq T R)) -> seq0 (atom_ (aeq T R)).
Proof.
intros T R [i h1].
generalize nil_ad; intro h3.
exists i; apply eq_ceq with nil; auto.
Qed.

End ceq.

(****************************************************************
 4. Adequacy
  ****************************************************************)

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section ae_inv.

Lemma ae_l_inv :
forall (i:nat) (Phi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (aeq x x) (atom_ (aeq (T x) (T' x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (aeq x x::Phi) (atom_ (aeq (T x) (T' x)))).
Proof.
induction i; auto.
- intros Phi T T' H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros Phi T T' H.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

End ae_inv.

(*********************)
(* "proper" Adequacy *)
(*********************)

Section proper_adeq.

Lemma term_proper : forall T:uexp,
  seq0 (atom_ (term T)) -> (proper T).
Proof.
intros T [n h1].
generalize T h1; clear h1 T.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T : uexp, seq_ n nil (atom_ (term T)) -> proper T)).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 T h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* app case *)
- inversion H3; clear H3; subst.
  apply proper_app; auto.
  + apply h1 with i0; auto; try lia.
  + apply h1 with i0; auto; try lia.
(* lam case *)
- inversion H3; clear H3; subst.
  apply proper_lam; auto.
Qed.

Lemma deq_proper : forall T T':uexp,
  seq0 (atom_ (deq T T')) -> (proper T /\ proper T').
Proof.
intros T T' [n h1].
generalize T T' h1; clear h1 T T'.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T T' : uexp, seq_ n nil (atom_ (deq T T')) ->
        (proper T /\ proper T'))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 T T' h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* lam case *)
- split; apply proper_lam; auto.
(* app case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split; apply proper_app; auto.
(* refl case *)
- split; apply term_proper; unfold seq0,seq'_,seq'; auto.
  + exists i; auto.
  + exists i; auto.
(* symm case *)
- assert (h4:i<i+1); try lia.
  specialize h1 with (1:=h4) (2:=H3); elim h1; clear h1; intros h1 h5; auto.
(* trans case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split; auto.
Qed.

Lemma aeq_proper : forall T T':uexp,
  seq0 (atom_ (aeq T T')) -> (proper T /\ proper T').
Proof.
intros T T' [n h1].
generalize T T' h1; clear h1 T T'.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T T' : uexp, seq_ n nil (atom_ (aeq T T')) ->
        (proper T /\ proper T'))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 T T' h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* lam case *)
- split; apply proper_lam; auto.
(* app case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split; apply proper_app; auto.
Qed.

End proper_adeq.

(************)
(* Contexts *)
(************)

Section ctx_aeq_adeq.

(* Membership lemma used in adequacy of aeq *)
Lemma memb_aeq_adeq1 : forall (Phi_x Phi_a:list atm) (T T':uexp),
  xaR Phi_x Phi_a -> In (aeq T T') Phi_a -> In (term T) Phi_x.
Proof.
intros Phi_x Phi_a T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; subst; simpl; auto.
- simpl; right; auto with hybrid.
Qed.

(* Membership lemma used in adequacy of aeq *)
Lemma memb_aeq_adeq2 : forall (Phi_x Phi_a:list atm) (T T':uexp),
  xaR Phi_x Phi_a -> In (aeq T T') Phi_a -> In (term T') Phi_x.
Proof.
intros Phi_x Phi_a T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; subst; simpl; auto.
- simpl; right; auto with hybrid.
Qed.

End ctx_aeq_adeq.

(****************)
(* aeq Adequacy *)
(****************)

#[global] Hint Resolve memb_aeq_adeq1 memb_aeq_adeq2 : hybrid.

Section aeq_adeq.

Lemma aeq_term :
  forall (i:nat) (T T':uexp) (Phi_x Phi_a:list atm),
  xaR Phi_x Phi_a ->
  seq_ i Phi_a (atom_ (aeq T T')) ->
  seq_ i Phi_x (atom_ (term T)) /\ seq_ i Phi_x (atom_ (term T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi_x Phi_a:list atm),
     xaR Phi_x Phi_a ->
     seq_ i Phi_a (atom_ (aeq T T')) ->
     seq_ i Phi_x (atom_ (term T)) /\ seq_ i Phi_x (atom_ (term T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi_x Phi_a cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (ae_l_inv i Phi_a M N H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (term x:: Phi_x) (atom_ (term (M x))) /\
         seq_ j (term x:: Phi_x) (atom_ (term (N x))))).
    { intros x h1.
      apply h with (aeq x x::Phi_a);
        eauto with hybrid; try lia. }
    split.
    * unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (term x) (atom_ (term (M x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
    * unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (term x) (atom_ (term (N x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
    split.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term M1)) (atom_ (term M2)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term N1)) (atom_ (term N2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- inversion cInv; subst.
split; apply s_init; eauto with hybrid.
Qed.

Lemma aeq_term_cor : forall T T':uexp, seq0 (atom_ (aeq T T')) ->
  (seq0 (atom_ (term T)) /\ seq0 (atom_ (term T'))).
Proof.
intros T T' [n h].
generalize nil_xa; intro h1.
specialize aeq_term with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End aeq_adeq.

(************)
(* Contexts *)
(************)

Section ctx_deq_adeq.

Inductive xdR : list atm -> list atm -> Prop :=
| nil_xd : xdR nil nil
| cons_xd : forall (Phi_x Phi_xd:list atm) (x:uexp), proper x ->
    xdR Phi_x Phi_xd ->
    xdR (term x::Phi_x) (deq x x::term x::Phi_xd).

Lemma memb_deq_adeq1 : forall (Phi_x Phi_xd:list atm) (T T':uexp),
  xdR Phi_x Phi_xd -> In (deq T T') Phi_xd -> In (term T) Phi_x.
Proof.
intros Phi_x Phi_xd T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- injection h2; intros; subst; subst; simpl; auto.
- discriminate h2.
- simpl; right; auto with hybrid.
Qed.

Lemma memb_deq_adeq2 : forall (Phi_x Phi_xd:list atm) (T T':uexp),
  xdR Phi_x Phi_xd -> In (deq T T') Phi_xd -> In (term T') Phi_x.
Proof.
intros Phi_x Phi_xd T T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- injection h2; intros; subst; subst; simpl; auto.
- discriminate h2.
- simpl; right; auto with hybrid.
Qed.

Lemma memb_deq_adeq3 : forall (Phi_x Phi_xd:list atm) (T:uexp),
  xdR Phi_x Phi_xd -> In (term T) Phi_xd -> In (term T) Phi_x.
Proof.
intros Phi_x Phi_xd T; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- discriminate h2.
- injection h2; intros; subst; simpl; auto.
- simpl; right; auto with hybrid.
Qed.

Hint Resolve memb_deq_adeq3 : hybrid.

Lemma c_str_xd2x_term : forall (i:nat) (M:uexp) (Phi_x Phi_xd:list atm),
  xdR Phi_x Phi_xd ->
  seq_ i Phi_xd (atom_ (term M)) ->
  seq_ i Phi_x (atom_ (term M)).
Proof.
intros i M Phi_x Phi_xd h; apply term_strengthen_weaken.
intros; eauto with hybrid. (* eauto applies memb_deq_adeq3 *)
Qed.

End ctx_deq_adeq.

(****************)
(* deq Adequacy *)
(****************)

Section deq_adeq.

Hint Resolve nil_xd cons_xd : hybrid.
Hint Resolve memb_deq_adeq1 memb_deq_adeq2 : hybrid.

Lemma deq_term :
  forall (i:nat) (T T':uexp) (Phi_x Phi_xd:list atm),
  xdR Phi_x Phi_xd ->
  seq_ i Phi_xd (atom_ (deq T T')) ->
  seq_ i Phi_x (atom_ (term T)) /\ seq_ i Phi_x (atom_ (term T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi_x Phi_xd:list atm),
     xdR Phi_x Phi_xd ->
     seq_ i Phi_xd (atom_ (deq T T')) ->
     seq_ i Phi_x (atom_ (term T)) /\ seq_ i Phi_x (atom_ (term T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi_x Phi_xd cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (de_l_inv i Phi_xd M N H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (term x:: Phi_x) (atom_ (term (M x))) /\
         seq_ j (term x:: Phi_x) (atom_ (term (N x))))).
    { intros x h1.
      apply h with (deq x x::term x::Phi_xd);
        eauto with hybrid; try lia. }
    replace (j+2) with (j+1+1); try lia.
    split.
    * unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (term x) (atom_ (term (M x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); intros [h6 h7].
      apply seq_mono with j; auto; try lia.
    * unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (term x) (atom_ (term (N x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); intros [h6 h7].
      apply seq_mono with j; auto; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
    split.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term M1)) (atom_ (term M2)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term N1)) (atom_ (term N2)));
        auto with hybrid.
      apply s_and; auto.
  (* refl case *)
  + split; apply seq_mono with i0; try lia;
      apply c_str_xd2x_term with Phi_xd; auto.
  (* symm case *)
  + assert (hi:i0<i0+1); try lia.
    specialize h with (1:=hi) (2:=cInv) (3:=H3); destruct h as [h1 h2].
    split; apply seq_mono with i0; auto; try lia.
  (* trans case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4); destruct h as [h2 h3].
    specialize h' with (1:=hi) (2:=cInv) (3:=H5); destruct h' as [h4 h5].
    split; apply seq_mono with i; auto; try lia.
(* context case *)
- inversion cInv; subst.
  split; apply s_init; eauto with hybrid.
  (* eauto applies memb_deq_adeq1 and memb_deq_adeq2 *)
Qed.

Lemma deq_term_cor : forall T T':uexp, seq0 (atom_ (deq T T')) ->
  (seq0 (atom_ (term T)) /\ seq0 (atom_ (term T'))).
Proof.
intros T T' [n h].
generalize nil_xd; intro h1.
specialize deq_term with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End deq_adeq.
