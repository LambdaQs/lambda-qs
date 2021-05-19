(****************************************************************
   File: EqualPolyR.v
   Author: Amy Felty

   original: January 2014
   Apr 2021: Current Coq Version: V8.13.1

   Context relation version (R version) of:

   1. Admissibility of reflexivity of algorithmic equality for the
      polymorphically typed lambda calculus (types)
   2. Admissibility of reflexivity of algorithmic equality for the
      polymorphically typed lambda calculus (terms)
   3. Adequacy
   4. An alternative way to prove promotion (from part 2 above)

  ***************************************************************)

From HybridSys Require Export sl.

#[global] Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
#[global] Hint Resolve proper_APP abstr_proper : hybrid.
#[global] Hint Unfold proper: hybrid.

Section encoding.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set :=
 Carr: Econ | Call: Econ | Capp: Econ | Clam: Econ |
 Ctapp: Econ | Ctlam: Econ.

Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition app : uexp -> uexp -> uexp :=
  fun M1:uexp => fun M2:uexp => (APP (APP (CON Capp) M1) M2).
Definition lam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON Clam) (lambda M)).
Definition tapp : uexp -> uexp -> uexp :=
  fun M:uexp => fun A:uexp => (APP (APP (CON Ctapp) M) A).
Definition tlam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON Ctlam) (lambda M)).
Definition arr : uexp -> uexp -> uexp :=
  fun A1:uexp => fun A2:uexp => (APP (APP (CON Carr) A1) A2).
Definition all : (uexp -> uexp) -> uexp :=
  fun A:uexp->uexp => (APP (CON Call) (lambda A)).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Inductive atm : Set :=
 | tp : uexp -> atm
 | term : uexp -> atm
 | atp : uexp -> uexp -> atm
 | aeq : uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  (* well-formedness of types (arr and all) *)
  | tp_ar : forall A1 A2:uexp,
      prog (tp (arr A1 A2))
        (Conj (atom_ (tp A1)) (atom_ (tp A2)))
  | tp_al : forall A:uexp->uexp, abstr A ->
      prog (tp (all A))
        (All (fun a:uexp =>
          (Imp (tp a) (atom_ (tp (A a))))))
  (* well-formedness of terms (app, lam, tapp, tlam) *)
  | tm_a : forall M1 M2:uexp,
      prog (term (app M1 M2))
        (Conj (atom_ (term M1)) (atom_ (term M2)))
  | tm_l : forall M:uexp->uexp, abstr M ->
      prog (term (lam M))
        (All (fun x:uexp =>
          (Imp (term x) (atom_ (term (M x))))))
  | tm_ta : forall M A:uexp,
      prog (term (tapp M A))
        (Conj (atom_ (term M)) (atom_ (tp A)))
  | tm_tl : forall M:uexp->uexp, abstr M ->
      prog (term (tlam M))
        (All (fun a:uexp =>
          (Imp (tp a) (atom_ (term (M a))))))
  (* algorithmic equality for types *)
  | at_a : forall A1 A2 B1 B2:uexp,
      prog (atp (arr A1 A2) (arr B1 B2))
        (Conj (atom_ (atp A1 B1)) (atom_ (atp A2 B2)))
  | at_al : forall A B:uexp->uexp, abstr A -> abstr B ->
      prog (atp (all A) (all B))
        (All (fun a:uexp =>
          (Imp (atp a a) (atom_ (atp (A a) (B a))))))
  (* algorithmic equality for terms *)
  | ae_a : forall M1 M2 N1 N2:uexp,
      prog (aeq (app M1 M2) (app N1 N2))
        (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2)))
  | ae_l : forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (aeq (lam M) (lam N))
        (All (fun x:uexp =>
          (Imp (aeq x x) (atom_ (aeq (M x) (N x))))))
  | ae_ta : forall M N A B:uexp,
      prog (aeq (tapp M A) (tapp N B))
        (Conj (atom_ (aeq M N)) (atom_ (atp A B)))
  | ae_tl : forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (aeq (tlam M) (tlam N))
        (All (fun a:uexp =>
          (Imp (atp a a) (atom_ (aeq (M a) (N a)))))).

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

End encoding.

#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tp_ar tp_al tm_a tm_l tm_ta tm_tl
                       at_a at_al ae_a ae_l ae_ta ae_tl : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Admissibility of Reflexivity for Types
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_tp.

(* Context Relation for reflexivity of types *)
Inductive atpR : list atm -> list atm -> Prop :=
| nil_atp : atpR nil nil
| cons_atp : forall (Phi_alph Phi_atp:list atm) (a:uexp), proper a ->
    atpR Phi_alph Phi_atp -> atpR (tp a::Phi_alph) (atp a a::Phi_atp).

(* Context Membership *)
Lemma memb_refl_tp : forall (Phi_alph Phi_atp:list atm) (T:uexp),
  atpR Phi_alph Phi_atp -> (In (tp T) Phi_alph -> In (atp T T) Phi_atp).
Proof.
intros Phi_alph Phi_atp T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | h].
- injection h; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

End ctx_tp.

#[global] Hint Resolve nil_atp cons_atp memb_refl_tp : hybrid.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section refl_tp.

Lemma atp_refl :
  forall (i:nat) (T:uexp) (Phi_alph Phi_atp:list atm),
  atpR Phi_alph Phi_atp ->
  seq_ i Phi_alph (atom_ (tp T)) ->
  seq_ i Phi_atp (atom_ (atp T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi_alph Phi_atp:list atm),
     atpR Phi_alph Phi_atp ->
     seq_ i Phi_alph (atom_ (tp T)) ->
     seq_ i Phi_atp (atom_ (atp T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi_alph Phi_atp cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* arr case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (atp A1 A1)) (atom_ (atp A2 A2)));
      auto with hybrid.
    apply s_and; auto.
  (* all case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun a:uexp => (Imp (atp a a) (atom_ (atp (A a) (A a))))));
      auto with hybrid.
    apply s_all; auto.
    intros a h1.
    generalize (H4 a h1); intro h2.
    inversion h2; subst; clear h2.
    apply s_imp; auto.
    apply h with (tp a::Phi_alph); eauto with hybrid; try lia.
(* context case *)
- inversion cInv; subst.
  apply s_init; eauto with hybrid.
Qed.

Lemma atp_refl_cor :
  forall (T:uexp), seq0 (atom_ (tp T)) -> seq0 (atom_ (atp T T)).
Proof.
intros T [n h].
generalize nil_atp; intro h1.
specialize atp_refl with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End refl_tp.

(****************************************************************
 2. Admissibility of Reflexivity for Terms
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_term.

(* Context Relation for reflexivity of terms *)
Inductive aeqR : list atm -> list atm -> Prop :=
| nil_aeq : aeqR nil nil
| tcons_aeq : forall (Phi_alphx Phi_aeq:list atm) (a:uexp), proper a ->
    aeqR Phi_alphx Phi_aeq -> aeqR (tp a::Phi_alphx) (atp a a::Phi_aeq)
| acons_aeq : forall (Phi_alphx Phi_aeq:list atm) (x:uexp), proper x ->
    aeqR Phi_alphx Phi_aeq -> aeqR (term x::Phi_alphx) (aeq x x::Phi_aeq).

(* Context Membership *)
Lemma memb_refl_tp_atp : forall (Phi_alphx Phi_aeq:list atm) (T:uexp),
  aeqR Phi_alphx Phi_aeq -> (In (tp T) Phi_alphx -> In (atp T T) Phi_aeq).
Proof.
intros Phi_alphx Phi_aeq T; induction 1; try (simpl; tauto).
- intro h; simpl in h; destruct h as [h | h].
  + injection h; intros; subst; simpl; auto.
  + simpl; tauto.
- intro h; simpl in h; destruct h as [h | h].
  discriminate h.
  simpl; tauto.
Qed.

Lemma memb_refl_term_aeq : forall (Phi_alphx Phi_aeq:list atm) (T:uexp),
  aeqR Phi_alphx Phi_aeq -> (In (term T) Phi_alphx -> In (aeq T T) Phi_aeq).
Proof.
intros Phi_alphx Phi_aeq T; induction 1; try (simpl; tauto).
- intro h; simpl in h; destruct h as [h | h].
  + discriminate h.
  + simpl; tauto.
- intro h; simpl in h; destruct h as [h | h].
  + injection h; intros; subst; simpl; auto.
  + simpl; tauto.
Qed.

Lemma atp_strengthen_weaken :
  forall (i:nat) (T T':uexp) (Phi Psi:list atm),
  (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
  seq_ i Phi (atom_ (atp T T')) ->
  seq_ i Psi (atom_ (atp T T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi Psi:list atm),
     (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
     seq_ i Phi (atom_ (atp T T')) ->
     seq_ i Psi (atom_ (atp T T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi Psi h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* arr case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H4).
    specialize h' with (1:=hi) (2:=h1) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (atp A1 B1)) (atom_ (atp A2 B2)));
      auto with hybrid.
    apply s_and; auto.
  (* all case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun a:uexp => (Imp (atp a a) (atom_ (atp (A a) (B a))))));
      auto with hybrid.
    apply s_all; auto.
    intros a h5.
    generalize (H4 a h5); intro h6.
    inversion h6; subst; clear h6 H4.
    apply s_imp; auto.
    apply h with (atp a a::Phi); auto; try lia.
    (* proof of extended context inv *)
    intros T T'; generalize (h1 T T'); simpl; tauto.
(* context case *)
- destruct (h1 T T') as [h2 h3].
  generalize (h2 H2); clear h1 h2 h3 H2.
  case Psi.
  + simpl; tauto.
  + intros a Phi h1.
    apply s_init; auto with hybrid.
Qed.

Lemma tp_strengthen_weaken :
  forall (i:nat) (T:uexp) (Phi Psi:list atm),
  (forall (T:uexp), In (tp T) Phi <->  In (tp T) Psi) ->
  seq_ i Phi (atom_ (tp T)) ->
  seq_ i Psi (atom_ (tp T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi Psi:list atm),
     (forall (T:uexp), In (tp T) Phi <->  In (tp T) Psi) ->
     seq_ i Phi (atom_ (tp T)) ->
     seq_ i Psi (atom_ (tp T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi Psi h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* arr case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H4).
    specialize h' with (1:=hi) (2:=h1) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (tp A1)) (atom_ (tp A2)));
      auto with hybrid.
    apply s_and; auto.
  (* all case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun a:uexp => (Imp (tp a) (atom_ (tp (A a))))));
      auto with hybrid.
    apply s_all; auto.
    intros a h5.
    generalize (H4 a h5); intro h6.
    inversion h6; subst; clear h6 H4.
    apply s_imp; auto.
    apply h with (tp a::Phi); auto; try lia.
    (* proof of extended context inv *)
    intro T; generalize (h1 T); simpl; tauto.
(* context case *)
- destruct (h1 T) as [h2 h3].
  generalize (h2 H2); clear h1 h2 h3 H2.
  case Psi.
  + simpl; tauto.
  + intros a Phi h1.
    apply s_init; auto with hybrid.
Qed.

End ctx_term.

(*************)
(* Promotion *)
(*************)

Section promote.

Fixpoint rm_alphx2alph (l:list atm) {struct l} : list atm
  := match l with
     | (tp a::l') => (tp a::rm_alphx2alph l')
     | (term x::l') => (rm_alphx2alph l')
     | _ => nil
     end.

Fixpoint rm_aeq2atp (l:list atm) {struct l} : list atm
  := match l with
     | (atp a b::l') => (atp a b::rm_aeq2atp l')
     | (aeq x y::l') => (rm_aeq2atp l')
     | _ => nil
     end.

(* We could merge the above 2 definitions into a single definition. *)

Hint Resolve nil_atp cons_atp : hybrid.
Hint Resolve nil_aeq tcons_aeq acons_aeq : hybrid.

(* Relation Strengthening *)
Lemma aeqR2atpR_strengthen : forall (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  atpR (rm_alphx2alph Phi_alphx) (rm_aeq2atp Phi_aeq).
Proof.
intros Phi_alphx Phi_aeq; induction 1; simpl; eauto with hybrid.
Qed.

Lemma rm_alphx2alph_lem_tp :
  forall (A:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  (In (tp A) Phi_alphx <-> In (tp A) (rm_alphx2alph Phi_alphx)).
Proof.
intros A Phi_alphx Phi_aeq; induction 1.
- simpl; tauto.
- split.
  + simpl; tauto.
  + simpl; intros [h1 | h1]; try tauto.
- split.
  + simpl; intros [h1 | h1]; try tauto.
    discriminate h1.
  + simpl; tauto.
Qed.

Hint Resolve rm_alphx2alph_lem_tp : hybrid.

Lemma c_str_alphx2alph_tp :
  forall (i:nat) (T:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_alphx (atom_ (tp T)) ->
  seq_ i (rm_alphx2alph Phi_alphx) (atom_ (tp T)).
Proof.
intros i T Phi_alphx Phi_aeq h1 h2.
apply tp_strengthen_weaken with Phi_alphx;
  eauto with hybrid.
Qed.

Lemma rm_aeq2atp_lem_atp :
  forall (A B:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  (In (atp A B) (rm_aeq2atp Phi_aeq) <-> In (atp A B) Phi_aeq).
Proof.
intros A B Phi_alphx Phi_aeq; induction 1.
- simpl; tauto.
- split.
  + simpl; tauto.
  + simpl; intros [h1 | h1]; try tauto.
- split.
  + simpl; tauto.
  + simpl; intros [h1 | h1]; try tauto.
    discriminate h1.
Qed.

Hint Resolve rm_aeq2atp_lem_atp : hybrid.

Lemma c_wk_aeq2atp_atp :
  forall (i:nat) (T T':uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i (rm_aeq2atp Phi_aeq) (atom_ (atp T T')) ->
  seq_ i Phi_aeq (atom_ (atp T T')).
Proof.
intros i T T' Phi_alphx Phi_aeq h1 h2.
apply atp_strengthen_weaken with (rm_aeq2atp Phi_aeq);
  eauto with hybrid.
Qed.

Hint Resolve c_wk_aeq2atp_atp c_str_alphx2alph_tp aeqR2atpR_strengthen : hybrid.
Hint Resolve atp_refl : hybrid.

(* Promotion Lemma for Reflexivity of Types *)
Lemma atp_refl_promote :
  forall (i:nat) (A:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_alphx (atom_ (tp A)) ->
  seq_ i Phi_aeq (atom_ (atp A A)).
Proof.
intros i A Phi_alphx Phi_aeq h h2; eauto with hybrid.
(* apply c_wk_aeq2atp_atp with Phi_alphx; auto.
   apply atp_refl with (rm_alphx2alph Phi_alphx); auto.
   apply aeqR2atpR_strengthen; auto.
   apply c_str_alphx2alph_tp with Phi_aeq; auto. *)
Qed.

End promote.

#[global] Hint Resolve nil_aeq tcons_aeq acons_aeq : hybrid.
#[global] Hint Resolve memb_refl_tp_atp memb_refl_term_aeq : hybrid.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section refl_term.

Lemma aeq_refl :
  forall (i:nat) (T:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_alphx (atom_ (term T)) ->
  seq_ i Phi_aeq (atom_ (aeq T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi_alphx Phi_aeq:list atm),
     aeqR Phi_alphx Phi_aeq ->
     seq_ i Phi_alphx (atom_ (term T)) ->
     seq_ i Phi_aeq (atom_ (aeq T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi_alphx Phi_aeq cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (aeq M1 M1)) (atom_ (aeq M2 M2)));
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
    apply h with (term x::Phi_alphx); eauto with hybrid; try lia.
  (* tapp case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (aeq M M)) (atom_ (atp A A)));
      auto with hybrid.
    apply s_and; auto.
    apply atp_refl_promote with Phi_alphx; auto.
  (* tlam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun a:uexp => (Imp (atp a a) (atom_ (aeq (M a) (M a))))));
      auto with hybrid.
    apply s_all; auto.
    intros a h1.
    generalize (H4 a h1); intro h2.
    inversion h2; subst; clear h2.
    apply s_imp; auto.
    apply h with (tp a::Phi_alphx); eauto with hybrid; try lia.
(* context case *)
- inversion cInv; subst.
  + apply s_init; eauto with hybrid.
  + apply s_init; eauto with hybrid.
Qed.

Lemma aeq_refl_cor :
  forall (T:uexp), seq0 (atom_ (term T)) -> seq0 (atom_ (aeq T T)).
Proof.
intros T [n h].
generalize nil_aeq; intro h1.
specialize aeq_refl with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End refl_term.

(****************************************************************
 3. Adequacy
  ****************************************************************)

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section atp_inv.

Lemma at_al_inv :
forall (i:nat) (Phi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (atp x x) (atom_ (atp (T x) (T' x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (atp x x::Phi) (atom_ (atp (T x) (T' x)))).
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

End atp_inv.

(************)
(* Contexts *)
(************)

Section ctx_atp_adeq.

(* Membership lemma used in adequacy of atp *)
Lemma memb_atp_adeq1 : forall (Phi_alph Phi_atp:list atm) (T T':uexp),
  atpR Phi_alph Phi_atp -> In (atp T T') Phi_atp -> In (tp T) Phi_alph.
Proof.
intros Phi_alph Phi_atp T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | h].
- injection h; intros; subst; subst; simpl; auto.
- simpl; tauto.
Qed.

Lemma memb_atp_adeq2 : forall (Phi_alph Phi_atp:list atm) (T T':uexp),
  atpR Phi_alph Phi_atp -> In (atp T T') Phi_atp -> In (tp T') Phi_alph.
Proof.
intros Phi_alph Phi_atp T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | h].
- injection h; intros; subst; subst; simpl; auto.
- simpl; tauto.
Qed.

End ctx_atp_adeq.

#[global] Hint Resolve nil_atp cons_atp memb_atp_adeq1 memb_atp_adeq2 : hybrid.

(****************)
(* atp Adequacy *)
(****************)

Section atp_adeq.

Lemma atp_tp :
  forall (i:nat) (T T':uexp) (Phi_alph Phi_atp:list atm),
  atpR Phi_alph Phi_atp ->
  seq_ i Phi_atp (atom_ (atp T T')) ->
  seq_ i Phi_alph (atom_ (tp T)) /\ seq_ i Phi_alph (atom_ (tp T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi_alph Phi_atp:list atm),
     atpR Phi_alph Phi_atp ->
     seq_ i Phi_atp (atom_ (atp T T')) ->
     seq_ i Phi_alph (atom_ (tp T)) /\ seq_ i Phi_alph (atom_ (tp T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi_alph Phi_atp cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* arr case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
    split.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (tp A1)) (atom_ (tp A2)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (tp B1)) (atom_ (tp B2)));
        auto with hybrid.
      apply s_and; auto.
  (* all case *)
  + inversion H3; subst; clear H3.
    generalize (at_al_inv i Phi_atp A B H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (tp x:: Phi_alph) (atom_ (tp (A x))) /\
         seq_ j (tp x:: Phi_alph) (atom_ (tp (B x))))).
    { intros x h1.
      apply h with (atp x x::Phi_atp); eauto with hybrid; try lia. }
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (tp x) (atom_ (tp (A x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (tp x) (atom_ (tp (B x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
(* context case *)
- inversion cInv; subst.
  split; apply s_init; eauto with hybrid.
Qed.

Lemma atp_tp1 :
  forall (i:nat) (T T':uexp) (Phi_alph Phi_atp:list atm),
  atpR Phi_alph Phi_atp ->
  seq_ i Phi_atp (atom_ (atp T T')) ->
  seq_ i Phi_alph (atom_ (tp T)).
Proof.
apply atp_tp.
Qed.

Lemma atp_tp2 :
  forall (i:nat) (T T':uexp) (Phi_alph Phi_atp:list atm),
  atpR Phi_alph Phi_atp ->
  seq_ i Phi_atp (atom_ (atp T T')) ->
  seq_ i Phi_alph (atom_ (tp T')).
Proof.
apply atp_tp.
Qed.

Lemma atp_tp_cor : forall T T':uexp, seq0 (atom_ (atp T T')) ->
  (seq0 (atom_ (tp T)) /\ seq0 (atom_ (tp T'))).
Proof.
intros T T' [n h].
generalize nil_atp; intro h1.
specialize atp_tp with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End atp_adeq.

(*************)
(* Promotion *)
(*************)

Section promote_atp_adeq.

Lemma c_str_alphx2alph_atp :
  forall (i:nat) (T T':uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_aeq (atom_ (atp T T')) ->
  seq_ i (rm_aeq2atp Phi_aeq) (atom_ (atp T T')).
Proof.
intros i T T' Phi_alphx Phi_aeq h1 h2.
apply atp_strengthen_weaken with Phi_aeq; eauto with hybrid.
intros T0 T'0; rewrite <- rm_aeq2atp_lem_atp; eauto with hybrid; tauto.
  (* "Hint Resolve rm_aeq2atp_lem_atp" would work except that <-> is
     in the wrong direction *)
Qed.

Lemma c_wk_alphx2alph_lem_tp :
  forall (i:nat) (T:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i (rm_alphx2alph Phi_alphx) (atom_ (tp T)) ->
  seq_ i Phi_alphx (atom_ (tp T)).
Proof.
intros i T Phi_alphx Phi_aeq h1 h2.
apply tp_strengthen_weaken with (rm_alphx2alph Phi_alphx);
  eauto with hybrid.
intro T'; rewrite <- rm_alphx2alph_lem_tp; eauto with hybrid; tauto.
  (* "Hint Resolve rm_alphx2alph_lem_tp" would work except that <-> is
     in the wrong direction *)
Qed.

Hint Resolve aeqR2atpR_strengthen : hybrid.

(* Promotion Lemma for Adequacy of atp *)
Lemma atp_tp_promote :
  forall (i:nat) (T T':uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_aeq (atom_ (atp T T')) ->
  seq_ i Phi_alphx (atom_ (tp T)) /\ seq_ i Phi_alphx (atom_ (tp T')).
Proof.
intros i T T' Phi_alphx Phi_aeq h h2.
split; apply c_wk_alphx2alph_lem_tp with Phi_aeq; eauto with hybrid.
- apply atp_tp1 with T' (rm_aeq2atp Phi_aeq); eauto with hybrid.
  apply c_str_alphx2alph_atp with Phi_alphx; auto.
- apply atp_tp2 with T (rm_aeq2atp Phi_aeq); eauto with hybrid.
  apply c_str_alphx2alph_atp with Phi_alphx; auto.
Qed.

End promote_atp_adeq.

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section aeq_inv.

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

Lemma ae_tl_inv :
forall (i:nat) (Phi:list atm) (M N:uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (atp x x) (atom_ (aeq (M x) (N x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (atp x x::Phi) (atom_ (aeq (M x) (N x)))).
Proof.
induction i; auto.
- intros Phi M N H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros Phi M N H.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

End aeq_inv.

(************)
(* Contexts *)
(************)

Section ctx_aeq_adeq.

(* Membership lemmas used in adequacy of aeq *)
Lemma memb_aeq_adeq1 : forall (Phi_alphx Phi_aeq:list atm) (T T':uexp),
  aeqR Phi_alphx Phi_aeq -> In (aeq T T') Phi_aeq -> In (term T) Phi_alphx.
Proof.
intros Phi_alphx Phi_aeq T; induction 1; try (simpl; tauto).
- intro h; simpl in h; destruct h as [h | h].
  + discriminate.
  + simpl; tauto.
- intro h; simpl in h; destruct h as [h | h].
  + injection h; intros; subst; subst; simpl; auto.
  + simpl; tauto.
Qed.

Lemma memb_aeq_adeq2 : forall (Phi_alphx Phi_aeq:list atm) (T T':uexp),
  aeqR Phi_alphx Phi_aeq -> In (aeq T T') Phi_aeq -> In (term T') Phi_alphx.
Proof.
intros Phi_alphx Phi_aeq T; induction 1; try (simpl; tauto).
- intro h; simpl in h; destruct h as [h | h].
  + discriminate.
  + simpl; tauto.
- intro h; simpl in h; destruct h as [h | h].
  + injection h; intros; subst; subst; simpl; auto.
  + simpl; tauto.
Qed.

End ctx_aeq_adeq.

#[global] Hint Resolve nil_aeq tcons_aeq acons_aeq memb_aeq_adeq1 memb_aeq_adeq2 : hybrid.

(****************)
(* aeq Adequacy *)
(****************)

Section aeq_adeq.

Lemma aeq_term :
  forall (i:nat) (T T':uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_aeq (atom_ (aeq T T')) ->
  seq_ i Phi_alphx (atom_ (term T)) /\ seq_ i Phi_alphx (atom_ (term T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi_alphx Phi_aeq:list atm),
     aeqR Phi_alphx Phi_aeq ->
     seq_ i Phi_aeq (atom_ (aeq T T')) ->
     seq_ i Phi_alphx (atom_ (term T)) /\ seq_ i Phi_alphx (atom_ (term T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi_alphx Phi_aeq cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
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
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (ae_l_inv i Phi_aeq M N H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (term x:: Phi_alphx) (atom_ (term (M x))) /\
         seq_ j (term x:: Phi_alphx) (atom_ (term (N x))))).
    { intros x h1.
      apply h with (aeq x x::Phi_aeq); eauto with hybrid; try lia. }
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (term x) (atom_ (term (M x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (term x) (atom_ (term (N x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
  (* tapp case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    elim h; intros h2 h3; clear h.
    specialize atp_tp_promote with (1:=cInv) (2:= H5); intros [h4 h5].
    split.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term M)) (atom_ (tp A)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (term N)) (atom_ (tp B)));
        auto with hybrid.
      apply s_and; auto.
  (* tlam case *)
  + inversion H3; subst; clear H3.
    generalize (ae_tl_inv i Phi_aeq M N H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (tp x:: Phi_alphx) (atom_ (term (M x))) /\
         seq_ j (tp x:: Phi_alphx) (atom_ (term (N x))))).
    { intros x h1.
      apply h with (atp x x::Phi_aeq); eauto with hybrid; try lia. }
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (tp x) (atom_ (term (M x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (tp x) (atom_ (term (N x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
(* context case *)
- inversion cInv; subst.
  + split; apply s_init; eauto with hybrid.
    (* applied memb_aeq_adeq1 and memb_aeq_adeq2 *)
  + split; apply s_init; eauto with hybrid.
    (* applied memb_aeq_adeq1 and memb_aeq_adeq2 *)
Qed.

Lemma aeq_term_cor : forall T T':uexp, seq0 (atom_ (aeq T T')) ->
  (seq0 (atom_ (term T)) /\ seq0 (atom_ (term T'))).
Proof.
intros T T' [n h].
generalize nil_aeq; intro h1.
specialize aeq_term with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End aeq_adeq.

(****************************************************************
 4. An Alternative Way to Prove Promotion
  ****************************************************************)

Section alt_promote.

(************)
(* Contexts *)
(************)

Inductive alphxR : list atm -> list atm -> Prop :=
| nil_alphx : alphxR nil nil
| tcons_alphx : forall (Phi_alph Phi_alphx:list atm) (x:uexp), proper x ->
    alphxR Phi_alph Phi_alphx -> alphxR Phi_alph (term x::Phi_alphx)
| acons_alphx : forall (Phi_alph Phi_alphx:list atm) (a:uexp), proper a ->
    alphxR Phi_alph Phi_alphx -> alphxR (tp a::Phi_alph) (tp a::Phi_alphx).

Inductive aeqatpR : list atm -> list atm -> Prop :=
| nil_aeqatp : aeqatpR nil nil
| tcons_aeqatp : forall (Phi_aeq Phi_atp:list atm) (x:uexp), proper x ->
    aeqatpR Phi_aeq Phi_atp -> aeqatpR (aeq x x::Phi_aeq) Phi_atp
| acons_aeqatp : forall (Phi_aeq Phi_atp:list atm) (a:uexp), proper a ->
    aeqatpR Phi_aeq Phi_atp -> aeqatpR (atp a a::Phi_aeq) (atp a a::Phi_atp).

Hint Resolve nil_alphx tcons_alphx acons_alphx : hybrid.
Hint Resolve nil_aeqatp tcons_aeqatp acons_aeqatp : hybrid.

Lemma aeqatpR_atp : forall (Phi_atp Phi_aeq:list atm) (T T':uexp),
  aeqatpR Phi_aeq Phi_atp -> (In (atp T T') Phi_atp <-> In (atp T T') Phi_aeq).
Proof.
intros Phi_atp Phi_aeq T T'; induction 1; try (simpl; tauto).
destruct IHaeqatpR as [h1 h2]; split.
- simpl; tauto.
- intro h; simpl in h; destruct h as [h | h].
  * discriminate h.
  * simpl; tauto.
Qed.

Hint Resolve aeqatpR_atp : hybrid.

Lemma c_wk_aeq2atp_atp_alt :
  forall (i:nat) (T T':uexp) (Phi_atp Phi_aeq:list atm),
  aeqatpR Phi_aeq Phi_atp ->
  seq_ i Phi_atp (atom_ (atp T T')) ->
  seq_ i Phi_aeq (atom_ (atp T T')).
Proof.
intros i T T' Phi_atp Phi_aeq h1 h2.
apply atp_strengthen_weaken with Phi_atp;
  eauto with hybrid.
Qed.

Lemma alphxR_tp : forall (Phi_alph Phi_alphx:list atm) (T:uexp),
  alphxR Phi_alph Phi_alphx -> (In (tp T) Phi_alphx <-> In (tp T) Phi_alph).
Proof.
intros Phi_alph Phi_alphx T; induction 1; try (simpl; tauto).
destruct IHalphxR as [h1 h2]; split.
- intro h; simpl in h; destruct h as [h | h].
  * discriminate h.
  * simpl; tauto.
- simpl; tauto.
Qed.

Hint Resolve alphxR_tp : hybrid.

Lemma c_str_alphx2alph_tp_alt :
  forall (i:nat) (T:uexp) (Phi_alphx Phi_alph:list atm),
  alphxR Phi_alph Phi_alphx ->
  seq_ i Phi_alphx (atom_ (tp T)) ->
  seq_ i Phi_alph (atom_ (tp T)).
Proof.
intros i T Phi_alphx Phi_alph h1 h2.
apply tp_strengthen_weaken with Phi_alphx; eauto with hybrid.
Qed.

(**************************)
(* Relation Strengthening *)
(**************************)

Lemma aeqR2atpR_strengthen_alt1 :
  forall (Phi_alphx Phi_aeq Phi_alph Phi_atp:list atm),
  aeqR Phi_alphx Phi_aeq ->
  alphxR Phi_alph Phi_alphx ->
  aeqatpR Phi_aeq Phi_atp ->
  atpR Phi_alph Phi_atp.
Proof.
intros Phi_alphx Phi_aeq Phi_alph Phi_atp h.
generalize Phi_alph; generalize Phi_atp; clear Phi_alph Phi_atp.
induction h;
  intros Phi_atp Phi_alph; inversion_clear 1; inversion_clear 1; auto.
- apply nil_atp.
- apply cons_atp; auto.
Qed.

Lemma aeqR2atpR_strengthen_alt2 :
  forall (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  exists (Phi_alph:list atm), exists (Phi_atp:list atm),
  alphxR Phi_alph Phi_alphx ->
  aeqatpR Phi_aeq Phi_atp ->
  atpR Phi_alph Phi_atp.
Proof.
intros Phi_alphx Phi_aeq; induction 1.
- exists nil; exists nil; auto.
  intros; apply nil_atp.
- destruct IHaeqR as [Phi_alph [Phi_atp h]].
  exists (tp a::Phi_alph); exists (atp a a::Phi_atp).
  inversion_clear 1; inversion_clear 1; auto.
  apply cons_atp; auto.
- destruct IHaeqR as [Phi_alph [Phi_atp h]].
  exists Phi_alph; exists Phi_atp.
  inversion_clear 1; inversion_clear 1; auto.
Qed.

Lemma aeqR2atpR_strengthen_alt3 :
  forall (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  exists (Phi_alph:list atm), exists (Phi_atp:list atm),
  (alphxR Phi_alph Phi_alphx /\
   aeqatpR Phi_aeq Phi_atp /\ atpR Phi_alph Phi_atp).
Proof.
intros Phi_alphx Phi_aeq; induction 1.
- exists nil; exists nil; auto.
  repeat split.
  + apply nil_alphx.
  + apply nil_aeqatp.
  + apply nil_atp.
- destruct IHaeqR as [Phi_alph [Phi_atp [h1 [h2 h3]]]].
  exists (tp a::Phi_alph); exists (atp a a::Phi_atp).
  repeat split.
  + apply acons_alphx; auto.
  + apply acons_aeqatp; auto.
  + apply cons_atp; auto.
- destruct IHaeqR as [Phi_alph [Phi_atp [h1 [h2 h3]]]].
  exists Phi_alph; exists Phi_atp.
  repeat split.
  + apply tcons_alphx; auto.
  + apply tcons_aeqatp; auto.
  + auto.
Qed.

(* Promotion Lemma for Reflexivity of Types *)
Lemma atp_refl_promote_alt :
  forall (i:nat) (A:uexp) (Phi_alphx Phi_aeq:list atm),
  aeqR Phi_alphx Phi_aeq ->
  seq_ i Phi_alphx (atom_ (tp A)) ->
  seq_ i Phi_aeq (atom_ (atp A A)).
Proof.
intros i A Phi_alphx Phi_aeq h h2.
specialize aeqR2atpR_strengthen_alt3 with (1:=h).
intros [Phi_alph [Phi_atp [h3 [h4 h5]]]].
apply c_wk_aeq2atp_atp_alt with Phi_atp; auto.
apply atp_refl with Phi_alph; auto.
apply c_str_alphx2alph_tp_alt with Phi_alphx; auto.
Qed.

End alt_promote.
