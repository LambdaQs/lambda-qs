(****************************************************************

   File: EqualUntypedR_ITP10.v
   Author: Amy Felty

   original: January 2010
   Apr 2021: Current Coq Version: V8.13.1

   Example from:
   Amy Felty and Brigitte Pientka, Reasoning with Higher-Order
   Abstract Syntax and Contexts: A Comparison, In International
   Conference on Interactive Theorem Proving (ITP), 2010.

   We formalized the proof of Theorem 1 in Section 2.1 using context
   relations.  The formal proof is described in Section 4.

   Contents:
   1. Admissibility of reflexivity for algorithmic equality
   2. Admissibility of transitivity for algorithmic equality
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
   is_tm : uexp -> atm
 | equal_d : uexp -> uexp -> atm
 | eq_a : uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  (* well-formedness of terms (app and lam) *)
  | tm_app : forall T1 T2:uexp,
      prog (is_tm (app T1 T2))
        (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)))
  | tm_lam : forall T:uexp->uexp, abstr T ->
      prog (is_tm (lam T))
        (All (fun x:uexp =>
          (Imp (is_tm x) (atom_ (is_tm (T x))))))
  (* declarative equality *)
  | e_l :forall T T':uexp->uexp, abstr T -> abstr T' ->
      prog (equal_d (lam T) (lam T'))
        (All (fun x:uexp =>
          (Imp (is_tm x)
            (Imp (equal_d x x) (atom_ (equal_d (T x) (T' x)))))))
  | e_a : forall T1 T2 E1 E2:uexp,
      prog (equal_d (app T1 T2) (app E1 E2))
        (Conj (atom_ (equal_d T1 E1)) (atom_ (equal_d T2 E2)))
  | e_r : forall T:uexp, 
      prog (equal_d T T) (atom_ (is_tm T))
  | e_t : forall T T' S:uexp,
      prog (equal_d T S) (Conj (atom_ (equal_d T T')) (atom_ (equal_d T' S)))
  (* algorithmic equality *)
  | eq_lam :forall T T':uexp->uexp, abstr T -> abstr T' ->
      prog (eq_a (lam T) (lam T'))
        (All (fun x:uexp =>
          (Imp (eq_a x x) (atom_ (eq_a (T x) (T' x))))))
  | eq_app : forall T1 T2 E1 E2:uexp,
      prog (eq_a (app T1 T2) (app E1 E2))
        (Conj (atom_ (eq_a T1 E1)) (atom_ (eq_a T2 E2))).

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

End encoding.

#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tm_app tm_lam e_l e_a e_r e_t eq_lam eq_app : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Admissibility of Reflexivity
  ****************************************************************)

Section ref.

(************)
(* Contexts *)
(************)

Definition ref_inv : list atm -> list atm -> Prop :=
  fun Phi:list atm => fun Psi:list atm =>
  (forall (T:uexp), In (is_tm T) Phi -> In (eq_a T T) Psi).

Lemma ref_extended_cInv1 : forall (Phi Psi:list atm) (x:uexp),
  ref_inv Phi Psi -> ref_inv (is_tm x::Phi) (eq_a x x::Psi).
Proof.
unfold ref_inv; intros Phi Psi x cInv T h1.
simpl in h1; elim h1; clear h1; intro h1.
- injection h1; clear h1; intros; subst; subst.
  simpl; tauto.
- specialize cInv with (1:=h1).
  simpl; tauto.
Qed.

Lemma ref_extended_cInv2 : forall (Phi Psi:list atm) (x:uexp),
  ref_inv Phi Psi ->
  ref_inv (equal_d x x::is_tm x::Phi) (eq_a x x::Psi).
Proof.
unfold ref_inv; intros Phi Psi x cInv T h1.
simpl in h1; elim h1; clear h1; intro h1.
- discriminate h1.
- elim h1; clear h1; intro h1.
  + injection h1; clear h1; intros; subst; subst.
    simpl; tauto.
  + specialize cInv with (1:=h1).
    simpl; tauto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma eq_ref :
  forall (i:nat) (T:uexp) (Phi Psi:list atm), ref_inv Phi Psi ->
  seq_ i Phi (atom_ (is_tm T)) ->
  seq_ i Psi (atom_ (eq_a T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi Psi:list atm),
     ref_inv Phi Psi ->
     seq_ i Phi (atom_ (is_tm T)) ->
     seq_ i Psi (atom_ (eq_a T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (eq_a T1 T1)) (atom_ (eq_a T2 T2)));
      auto with hybrid.
    apply s_and; auto.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (eq_a x x) (atom_ (eq_a (T0 x) (T0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    generalize (H4 x h1); intro h2.
    inversion h2; subst; clear h2.
    apply s_imp; auto.
    apply h with (is_tm x::Phi); auto; try lia.
    apply ref_extended_cInv1; auto.
(* context case *)
- unfold ref_inv in cInv.
  specialize cInv with (1:=H2); clear H2.
  generalize cInv; case Psi.
  + simpl; tauto.
  + intros a Phi h1.
    apply s_init; auto with hybrid.
Qed.

Lemma eq_ref_cor :
  forall (T:uexp), seq0 (atom_ (is_tm T)) -> seq0 (atom_ (eq_a T T)).
Proof.
intros T [n h].
assert (cInv:ref_inv nil nil).
{ unfold ref_inv; simpl; tauto. }
specialize eq_ref with (1:=cInv) (2:=h); intro h2.
exists n; auto.
Qed.

End ref.

(****************************************************************
 2. Admissibility of Transivity
  ****************************************************************)

Section tr.

(************)
(* Contexts *)
(************)

Definition tr_inv : list atm -> Prop :=
  fun Psi:list atm =>
   (forall (T T':uexp), In (eq_a T T') Psi -> T=T').

Lemma tr_extended_cInv : forall (Psi:list atm) (x:uexp),
  tr_inv Psi -> tr_inv (eq_a x x::Psi).
Proof.
unfold tr_inv; intros Psi x cInv T T' h1.
simpl in h1; elim h1; clear h1; intro h1.
- injection h1; clear h1; intros; subst; subst; auto.
- specialize cInv with (1:=h1); auto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma eq_tr :
  forall (i:nat) (T R U:uexp) (Psi:list atm), tr_inv Psi ->
  seq_ i Psi (atom_ (eq_a T R)) ->
  seq_ i Psi (atom_ (eq_a R U)) ->
  seq_ i Psi (atom_ (eq_a T U)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T R U:uexp) (Psi:list atm), tr_inv Psi ->
     seq_ i Psi (atom_ (eq_a T R)) ->
     seq_ i Psi (atom_ (eq_a R U)) ->
     seq_ i Psi (atom_ (eq_a T U)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T R U Psi cInv h1 h2.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      specialize abstr_lbind_simp with (1:=H7) (2:=H5) (3:=H0); intro h1.
      rewrite H.
      unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (eq_a x x) (atom_ (eq_a (T0 x) (T'0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h2.
      inversion H6; subst; clear H6.
      specialize H10 with (1:=h2).
      unfold ext_eq in h1; rewrite -> h1 in H10; auto; clear H0 H7 h1 T.
      assert (hi:i1=i); try lia; subst; clear H.
      specialize H4 with (1:=h2).
      inversion H10; subst; clear H10.
      inversion H4; subst; clear H4.
      apply s_imp; auto.
      assert (hi:i0=i); try lia; subst; clear H.
      apply h with (T' x); auto; try lia.
      apply tr_extended_cInv; auto.
    (* lam case: context subcase *)
    * unfold tr_inv in cInv.
      specialize cInv with (1:=H3); subst.
      unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (eq_a x x) (atom_ (eq_a (T0 x) (T' x))))));
        auto with hybrid.
      apply s_all; auto.
  (* app case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H1; subst; clear H1.
      inversion H3; subst; clear H3.
      assert (hi:i1=i); try lia; subst; clear H.
      unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (eq_a T1 E0)) (atom_ (eq_a T2 E3)));
        auto with hybrid.
      apply s_and; auto.
      -- apply h with E1; try lia; auto.
      -- apply h with E2; try lia; auto.
    (* app case: context subcase *)
    * unfold tr_inv in cInv.
      specialize cInv with (1:=H2); subst.
      unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (eq_a T1 E1)) (atom_ (eq_a T2 E2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- unfold tr_inv in cInv.
  specialize cInv with (1:=H2); clear H2; subst; auto.
Qed.

Lemma eq_tr_cor : forall (T R U:uexp),
 seq0 (atom_ (eq_a T R)) -> seq0 (atom_ (eq_a R U)) ->
 seq0 (atom_ (eq_a T U)).
Proof.
intros T R U [i h1] [j h2].
assert (cInv:tr_inv nil).
- unfold tr_inv; simpl; tauto.
- exists (i+j); apply eq_tr with R; auto.
  * apply seq_mono_cor with i; auto; try lia.
  * apply seq_mono_cor with j; auto; try lia.
Qed.

End tr.

(****************************************************************
 3. Correctness
  ****************************************************************)

Section ceq.

(************)
(* Contexts *)
(************)

Definition ceq_inv : list atm -> list atm -> Prop :=
  fun Phi:list atm => fun Psi:list atm =>
   ((forall (T T':uexp), In (equal_d T T') Phi -> In (eq_a T T') Psi) /\
    ref_inv Phi Psi /\
    tr_inv Psi).

Lemma ceq_extended_cInv : forall (Phi Psi:list atm) (x:uexp),
  ceq_inv Phi Psi ->
  ceq_inv (equal_d x x::is_tm x::Phi) (eq_a x x::Psi).
Proof.
unfold ceq_inv; intros Phi Psi x [cInv1 [cInv2 cInv3]].
repeat split.
- intros T T' h1.
  simpl in h1; elim h1; clear h1; intro h1.
  + injection h1; clear h1; intros; subst; subst; simpl; tauto.
  + elim h1; clear h1; intro h1.
    * discriminate h1.
    * specialize cInv1 with (1:=h1); simpl; tauto.
- apply ref_extended_cInv2; auto.
- apply tr_extended_cInv; auto.
Qed.

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Lemma equal_lam_inv :
forall (i:nat) (Phi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (is_tm x) (Imp (equal_d x x)
                   (atom_ (equal_d (T x) (T' x)))))) ->
exists j:nat, (i=j+2 /\ 
 forall x : uexp,
       proper x ->
       seq_ j ((equal_d x x)::(is_tm x)::Phi) (atom_ (equal_d (T x) (T' x)))).
Proof.
induction i; auto.
- intros Phi T T' H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- generalize i; clear i IHi.
  induction i; auto.
  + intros Phi T T' H.
    generalize (H (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    inversion H4; clear H4; subst.
    replace (i0+1+1) with (S (S i0)) in H0; try lia.
  + intros Phi T T' H.
    exists i; split; try lia.
    intros x H0.
    generalize (H x H0); intro H1.
    inversion H1; clear H1; subst.
    inversion H5; clear H5; subst.
    assert (i1 = i); try lia.
    subst; auto.
Qed.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Lemma eq_ceq :
  forall (i:nat) (T R:uexp) (Phi Psi:list atm), ceq_inv Phi Psi ->
  seq_ i Phi (atom_ (equal_d T R)) ->
  seq_ i Psi (atom_ (eq_a T R)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T R:uexp) (Phi Psi:list atm), ceq_inv Phi Psi ->
     seq_ i Phi (atom_ (equal_d T R)) ->
     seq_ i Psi (atom_ (eq_a T R)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T R Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (equal_lam_inv i Phi T0 T' H4); clear H4; intros [j [h1 h2]];
      subst.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (eq_a x x) (atom_ (eq_a (T0 x) (T' x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h1.
    apply seq_mono with (j+1); try lia.
    apply s_imp; auto.
    apply h with (equal_d x x::is_tm x::Phi); auto; try lia.
    apply ceq_extended_cInv; auto.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (eq_a T1 E1)) (atom_ (eq_a T2 E2)));
      auto with hybrid.
    apply s_and; auto.
    * apply h with Phi; try lia; auto.
    * apply h with Phi; try lia; auto.
  (* refl case *)
  + apply seq_mono with i0; auto; try lia.
    apply eq_ref with Phi; auto.
    unfold ceq_inv in cInv; tauto.
  (* trans case *)
  + inversion H3; subst; clear H3.
    apply eq_tr with T'; auto.
    * unfold ceq_inv in cInv; tauto.
    * apply seq_mono with i; auto; try lia.
      apply h with Phi; auto; try lia.
    * apply seq_mono with i; auto; try lia.
      apply h with Phi; auto; try lia.
(* context case *)
- elim cInv; clear cInv; intros cInv1 [cInv2 cInv3].
  specialize cInv1 with (1:=H2); clear H2.
  generalize cInv1; case Psi.
  + simpl; tauto.
  + intros a Phi h1.
    apply s_init; auto with hybrid.
Qed.

Lemma eq_ceq_cor : forall (T R:uexp),
 seq0 (atom_ (equal_d T R)) -> seq0 (atom_ (eq_a T R)).
Proof.
intros T R [i h1].
assert (cInv:ceq_inv nil nil).
- unfold ceq_inv; unfold tr_inv,ref_inv; simpl; tauto.
- exists i; apply eq_ceq with nil; auto.
Qed.

End ceq.

(****************************************************************
 4. Adequacy
  ****************************************************************)

(*********************)
(* "proper" Adequacy *)
(*********************)

Section proper_adeq.

Lemma is_tm_proper : forall T:uexp,
  seq0 (atom_ (is_tm T)) -> (proper T).
Proof.
intros T [n h1].
generalize T h1; clear h1 T.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T : uexp, seq_ n nil (atom_ (is_tm T)) -> proper T)).
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

Lemma equal_proper : forall T T':uexp,
  seq0 (atom_ (equal_d T T')) -> (proper T /\ proper T').
Proof.
intros T T' [n h1].
generalize T T' h1; clear h1 T T'.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T T' : uexp, seq_ n nil (atom_ (equal_d T T')) ->
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
- split; apply is_tm_proper; unfold seq0,seq'_,seq'; auto.
  + exists i; auto.
  + exists i; auto.
(* trans case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split; auto.
Qed.

Lemma eq_proper : forall T T':uexp,
  seq0 (atom_ (eq_a T T')) -> (proper T /\ proper T').
Proof.
intros T T' [n h1].
generalize T T' h1; clear h1 T T'.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T T' : uexp, seq_ n nil (atom_ (eq_a T T')) ->
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

Section equal_adeq.

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Lemma eq_lam_inv :
forall (i:nat) (Psi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Psi (Imp (eq_a x x) (atom_ (eq_a (T x) (T' x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (eq_a x x::Psi) (atom_ (eq_a (T x) (T' x)))).
Proof.
induction i; auto.
- intros Psi T T' H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros Psi T T' H.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

(************)
(* Contexts *)
(************)

Definition equal_context_inv : list atm -> list atm -> Prop :=
  fun Phi:list atm => fun Psi:list atm =>
  ((forall (T T':uexp), (In (equal_d T T') Phi) ->
    (In (is_tm T) Psi /\ In (is_tm T') Psi)) /\
   (forall (T:uexp), In (is_tm T ) Phi ->  In (is_tm T) Psi)).

Lemma equal_extended_cInv :
  forall (Phi Psi:list atm) (x:uexp), equal_context_inv Phi Psi ->
   equal_context_inv (equal_d x x::is_tm x::Phi) (is_tm x::Psi).
Proof.
unfold equal_context_inv; intros Phi Psi x [cInv1 cInv2]; split.
- intros T T' h5; simpl in h5; elim h5; clear h5; [intro h5 | intros [h5 | h5]].
  + injection h5; clear h5; intros; subst; subst.
    simpl; tauto.
  + discriminate h5.
  + specialize cInv1 with (1:=h5).
    elim cInv1; simpl; tauto.
- simpl.
  intros T [h3 | [h3 | h3]].
  + discriminate h3.
  + injection h3; subst; tauto.
  + specialize cInv2 with (1:=h3); tauto.
Qed.

Lemma is_tm_related_contexts :
  forall (i:nat) (T:uexp) (Phi Psi:list atm),
  (forall (T:uexp), In (is_tm T) Phi ->  In (is_tm T) Psi) ->
  seq_ i Phi (atom_ (is_tm T)) ->
  seq_ i Psi (atom_ (is_tm T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi Psi:list atm),
     (forall (T:uexp), In (is_tm T ) Phi ->  In (is_tm T) Psi) ->
     seq_ i Phi (atom_ (is_tm T)) ->
     seq_ i Psi (atom_ (is_tm T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi Psi h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* app case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H4).
    specialize h' with (1:=hi) (2:=h1) (3:=H5).
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)));
      auto with hybrid.
    apply s_and; auto.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h5.
    generalize (H4 x h5); intro h6.
    inversion h6; subst; clear h6 H4.
    apply s_imp; auto.
    apply h with (is_tm x::Phi); auto; try lia.
    (* proof of extended context inv *)
    intro T; generalize (h1 T); simpl; tauto.
(* context case *)
- generalize (h1 T H2); clear h1 H2.
case Psi.
  + simpl; tauto.
  + intros a Phi h1.
    apply s_init; auto with hybrid.
Qed.

(********************)
(* equal_d Adequacy *)
(********************)

Lemma equal_is_tm :
  forall (i:nat) (T T':uexp) (Phi Psi:list atm),
  equal_context_inv Phi Psi ->
  seq_ i Phi (atom_ (equal_d T T')) ->
  seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi (atom_ (is_tm T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi Psi:list atm),
     equal_context_inv Phi Psi ->
     seq_ i Phi (atom_ (equal_d T T')) ->
     seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi (atom_ (is_tm T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (equal_lam_inv i Phi T0 T'0 H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (is_tm x:: Psi) (atom_ (is_tm (T0 x))) /\
         seq_ j (is_tm x:: Psi) (atom_ (is_tm (T'0 x))))).
    { intros x h1.
      apply h with (equal_d x x::is_tm x::Phi); auto; try lia.
      apply equal_extended_cInv; auto. }
    replace (j+2) with (j+1+1); try lia.
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); intros [h6 h7].
      apply seq_mono with j; auto; try lia.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T'0 x))))));
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
        apply s_bc with (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (is_tm E1)) (atom_ (is_tm E2)));
        auto with hybrid.
      apply s_and; auto.
  (* refl case *)
  + elim cInv; intros cInv1 cInv2.
    specialize is_tm_related_contexts with (1:=cInv2) (2:=H3); intro h1.
    split; apply seq_mono with i0; auto; try lia.
  (* trans case *)
  + inversion H3; subst; clear H3.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=cInv) (3:=H4).
    specialize h' with (1:=hi) (2:=cInv) (3:=H5).
    elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
    split; apply seq_mono with i; auto; try lia.
(* context case *)
- elim cInv; intros cInv1 cInv2.
  specialize cInv1 with (1:=H2); clear H2.
  elim cInv1; clear cInv2; case Psi.
  simpl; tauto.
  intros a Phi h1 h2.
  split; apply s_init; auto with hybrid.
Qed.

Lemma equal_is_tm_cor : forall T T':uexp, seq0 (atom_ (equal_d T T')) ->
  (seq0 (atom_ (is_tm T)) /\ seq0 (atom_ (is_tm T'))).
Proof.
intros T T' [n h].
assert (cInv:equal_context_inv nil nil).
{ unfold equal_context_inv; simpl; tauto. }
specialize equal_is_tm with (1:=cInv) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End equal_adeq.

Section eq_adeq.

(************)
(* Contexts *)
(************)

Definition eq_context_inv : list atm -> list atm -> Prop :=
  fun Phi:list atm => fun Psi:list atm =>
  (forall (T T':uexp), (In (eq_a T T') Phi) ->
    (In (is_tm T) Psi /\ In (is_tm T') Psi)).

Lemma eq_extended_cInv :
  forall (Phi Psi:list atm) (x:uexp), eq_context_inv Phi Psi ->
   eq_context_inv (eq_a x x::Phi) (is_tm x::Psi).
Proof.
unfold eq_context_inv; intros Phi Psi x cInv T T' h1.
simpl in h1; elim h1; clear h1; intro h1.
- injection h1; clear h1; intros; subst; subst.
  simpl; tauto.
- specialize cInv with (1:=h1).
  elim cInv; simpl; tauto.
Qed.

(*****************)
(* eq_a Adequacy *)
(*****************)

Lemma eq_is_tm :
  forall (i:nat) (T T':uexp) (Phi Psi:list atm),
  eq_context_inv Phi Psi ->
  seq_ i Phi (atom_ (eq_a T T')) ->
  seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi (atom_ (is_tm T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi Psi:list atm),
     eq_context_inv Phi Psi ->
     seq_ i Phi (atom_ (eq_a T T')) ->
     seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi (atom_ (is_tm T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    generalize (eq_lam_inv i Phi T0 T'0 H4); clear H4; intros [j [h1 h2]];
      subst.
    assert (h':forall x:uexp, proper x -> 
        (seq_ j (is_tm x:: Psi) (atom_ (is_tm (T0 x))) /\
         seq_ j (is_tm x:: Psi) (atom_ (is_tm (T'0 x))))).
    { intros x h1.
      apply h with (eq_a x x::Phi); auto; try lia.
      apply eq_extended_cInv; auto. }
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      generalize (h' x h5); tauto.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T'0 x))))));
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
        apply s_bc with (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)));
        auto with hybrid.
      apply s_and; auto.
    * unfold seq_,atom_;
        apply s_bc with (Conj (atom_ (is_tm E1)) (atom_ (is_tm E2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- unfold eq_context_inv in cInv.
  specialize cInv with (1:=H2); clear H2.
  elim cInv; clear cInv; case Psi.
  + simpl; tauto.
  + intros a Phi h1 h2.
    split; apply s_init; auto with hybrid.
Qed.

Lemma eq_is_tm_cor : forall T T':uexp, seq0 (atom_ (eq_a T T')) ->
  (seq0 (atom_ (is_tm T)) /\ seq0 (atom_ (is_tm T'))).
Proof.
intros T T' [n h].
assert (cInv:eq_context_inv nil nil).
unfold eq_context_inv; simpl; tauto.
specialize eq_is_tm with (1:=cInv) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End eq_adeq.
