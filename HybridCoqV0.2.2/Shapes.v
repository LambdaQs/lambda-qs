(****************************************************************
   File: Shapes.v
   Author: Amy Felty

   original: January 2010
   updated: March 2014
   Mar 2021: Current Coq Version: V8.13.1

   Definition of lambda terms, predicates, and judgments plus
   proofs of internal adequacy for all judgments

  ***************************************************************)

From HybridSys Require Export sl.

#[global] Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
#[global] Hint Resolve proper_APP abstr_proper : hybrid.
#[global] Hint Unfold proper: hybrid.

Section encoding.

Hint Rewrite ext_eq_eta : hybrid.

(****************************************************************
   Constants for Two Kinds of Terms
  ****************************************************************)

Inductive Econ: Set := cAPP: Econ | cLAM: Econ | cAPPLY : Econ | cFUN : Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition app : uexp -> uexp -> uexp :=
  fun e1:uexp => fun e2:uexp => (APP (APP (CON cAPP) e1) e2).
Definition lam : (uexp -> uexp) -> uexp :=
  fun e:uexp->uexp => (APP (CON cLAM) (lambda e)).
Definition apply : uexp -> uexp -> uexp :=
  fun e1:uexp => fun e2:uexp => (APP (APP (CON cAPPLY) e1) e2).
Definition fn : (uexp -> uexp) -> uexp :=
  fun e:uexp->uexp => (APP (CON cFUN) (lambda e)).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

Lemma proper_lam : forall (e:uexp->uexp),
  abstr e -> proper (lam e).
Proof.
unfold lam; auto with hybrid.
Qed.

Lemma proper_app : forall e1 e2:uexp,
  proper e1 -> proper e2 -> proper (app e1 e2).
Proof.
unfold app; auto with hybrid.
Qed.

Lemma proper_fn : forall (e:uexp->uexp),
  abstr e -> proper (fn e).
Proof.
unfold fn; auto with hybrid.
Qed.

Lemma proper_apply : forall e1 e2:uexp,
  proper e1 -> proper e2 -> proper (apply e1 e2).
Proof.
unfold apply; auto with hybrid.
Qed.

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Inductive atm : Set :=
   is_tm : uexp -> atm
 | is_exp : uexp -> atm
 | eq_a : uexp -> uexp -> atm
 | shape : uexp -> uexp -> atm
 | varT : uexp -> atm
 | varE : uexp -> atm
 | varTOcc : uexp -> nat -> atm
 | varEOcc : uexp -> nat -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold oo_ atom_ T_: hybrid.

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
  (* well-formedness of expressions (apply and fn) *)
  | exp_apply : forall E1 E2:uexp,
      prog (is_exp (apply E1 E2))
        (Conj (atom_ (is_exp E1)) (atom_ (is_exp E2)))
  | exp_fn : forall E:uexp->uexp, abstr E ->
      prog (is_exp (fn E))
        (All (fun x:uexp =>
          (Imp (is_exp x) (atom_ (is_exp (E x))))))
  (* algorithmic equality between terms and expressions *)
  | eq_lam : forall T E:uexp->uexp, abstr T -> abstr E ->
      prog (eq_a (lam T) (fn E))
        (All (fun x:uexp =>
          (All (fun y:uexp =>
            (Imp (eq_a x y) (atom_ (eq_a (T x) (E y))))))))
  | eq_app : forall T1 T2 E1 E2:uexp,
      prog (eq_a (app T1 T2) (apply E1 E2))
        (Conj (atom_ (eq_a T1 E1)) (atom_ (eq_a T2 E2)))
  (* same shape for terms and expressions *)
  | sh_v : forall T E:uexp, 
      prog (shape T E)
      (Conj (atom_ (varT T)) (atom_ (varE E)))
  | sh_lam : forall T E:uexp->uexp, abstr T -> abstr E ->
      prog (shape (lam T) (fn E))
        (All (fun x:uexp =>
          (All (fun y:uexp =>
            (Imp (varT x) (Imp (varE y) (atom_ (shape (T x) (E y)))))))))
  | sh_app : forall T1 T2 E1 E2:uexp,
      prog (shape (app T1 T2) (apply E1 E2))
        (Conj (atom_ (shape T1 E1)) (atom_ (shape T2 E2)))
  (* counting variables in terms *)
  | v_lm : forall T:uexp->uexp, forall N:nat, abstr T ->
      prog (varTOcc (lam T) N)
        (All (fun x:uexp => (Imp (varT x) (atom_ (varTOcc (T x) N)))))
  | v_app : forall T1 T2:uexp, forall N1 N2:nat,
      prog (varTOcc (app T1 T2) (N1+N2))
        (Conj (atom_ (varTOcc T1 N1)) (atom_ (varTOcc T2 N2)))
  | v_varT : forall T:uexp,
      prog (varTOcc T 1) (atom_ (varT T))
  (* counting variables in expressions *)
  | v_fn : forall E:uexp->uexp, forall N:nat, abstr E ->
      prog (varEOcc (fn E) N)
        (All (fun x:uexp => (Imp (varE x) (atom_ (varEOcc (E x) N)))))
  | v_apply : forall E1 E2:uexp, forall N1 N2:nat,
      prog (varEOcc (apply E1 E2) (N1+N2))
        (Conj (atom_ (varEOcc E1 N1)) (atom_ (varEOcc E2 N2)))
  | v_varE : forall E:uexp,
      prog (varEOcc E 1) (atom_ (varE E)).

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := sl.seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

End encoding.

#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.
#[global] Hint Unfold proper: hybrid.
#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tm_app tm_lam exp_apply exp_fn
               eq_lam eq_app sh_v sh_lam sh_app
               v_lm v_app v_varT v_fn v_apply v_varE : hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.
#[global] Hint Resolve proper_Var : hybrid.

(****************************************************************
   Specialized Inversion Properties of prog
  ****************************************************************)

Section prog_inv.

Hint Rewrite ext_eq_eta : hybrid.

Lemma eq_lam_inv :
forall (i:nat) (Psi:list atm) (T E:uexp->uexp),
seq_ i Psi (All (fun x:uexp => All (fun y:uexp =>
                Imp (eq_a x y) (atom_ (eq_a (T x) (E y)))))) ->
exists j:nat, (i=j+3 /\ 
 forall (x y:uexp),
       proper x -> proper y ->
       seq_ j (eq_a x y::Psi) (atom_ (eq_a (T x) (E y)))).
Proof.
intro i; case i.
- intros Psi T E H.
  inversion H; clear H; subst.
  replace (i0+1) with (S i0) in H0; try lia.
- clear i; intro i; case i.
  + intros Psi T E H.
    inversion H; clear H; subst.
    generalize (H3 (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    replace (i1+1+1) with (S (S i1)) in H0; try lia.
  + clear i; intro i; case i.
    * intros Psi T E H.
      inversion H; clear H; subst.
      generalize (H3 (Var 0) (proper_Var 0)); clear H3; intro H1.
      inversion H1; clear H1; subst.
      generalize (H4 (Var 0) (proper_Var 0)); clear H4; intro H1.
      inversion H1; clear H1; subst.
      replace (i0+1+1+1) with (S (S (S i0))) in H0; try lia.
    * intros n Psi T E h.
      exists n; split; try lia.
      intros x y H0 H1.
      inversion h; clear h; subst.
      generalize (H4 x H0); clear H4; intro H4.
      inversion H4; clear H4; subst.
      generalize (H6 y H1); clear H6; intro H6.
      inversion H6; clear H6; subst.
      assert (i0 = n); try lia.
      subst; auto.
Qed.

Lemma shape_lam_inv :
forall (i:nat) (Psi:list atm) (T E:uexp->uexp),
seq_ i Psi (All (fun x:uexp => All (fun y:uexp =>
           Imp (varT x) (Imp (varE y) (atom_ (shape (T x) (E y))))))) ->
exists j:nat, (i=j+4 /\ 
 forall (x y:uexp),
       proper x -> proper y ->
       seq_ j (varE y::varT x::Psi) (atom_ (shape (T x) (E y)))).
Proof.
intro i; case i.
- intros Psi T E H.
  inversion H; clear H; subst.
  replace (i0+1) with (S i0) in H0; try lia.
- clear i; intro i; case i.
  + intros Psi T E H.
    inversion H; clear H; subst.
    generalize (H3 (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    replace (i1+1+1) with (S (S i1)) in H0; try lia.
  + clear i; intro i; case i.
    * intros Psi T E H.
      inversion H; clear H; subst.
      generalize (H3 (Var 0) (proper_Var 0)); clear H3; intro H1.
      inversion H1; clear H1; subst.
      generalize (H4 (Var 0) (proper_Var 0)); clear H4; intro H1.
      inversion H1; clear H1; subst.
      replace (i0+1+1+1) with (S (S (S i0))) in H0; try lia.
    * clear i; intro i; case i.
      -- intros Psi T E H.
         inversion H; clear H; subst.
         generalize (H3 (Var 0) (proper_Var 0)); clear H3; intro H1.
         inversion H1; clear H1; subst.
         generalize (H4 (Var 0) (proper_Var 0)); clear H4; intro H1.
         inversion H1; clear H1; subst.
         inversion H4; clear H4; subst.
         replace (i1+1+1+1+1) with (S (S (S (S i1)))) in H0; try lia.
      -- intros n Psi T E h.
         exists n; split; try lia.
         intros x y H0 H1.
         inversion h; clear h; subst.
         generalize (H4 x H0); clear H4; intro H4.
         inversion H4; clear H4; subst.
         generalize (H6 y H1); clear H6; intro H6.
         inversion H6; clear H6; subst.
         inversion H5; clear H5; subst.
         assert (i1 = n); try lia.
         subst; auto.
Qed.

Lemma varTOcc_lam_inv :
forall (i N:nat) (Psi:list atm) (T:uexp->uexp),
seq_ i Psi (All (fun x:uexp => Imp (varT x) (atom_ (varTOcc (T x) N)))) ->
exists j:nat, (i=j+2 /\ 
 forall (x:uexp), proper x ->
       seq_ j (varT x::Psi) (atom_ (varTOcc (T x) N))).
Proof.
intro i; case i.
- intros N Psi T H.
  inversion H; clear H; subst.
  replace (i0+1) with (S i0) in H0; try lia.
- clear i; intro i; case i.
  + intros N Psi T H.
    inversion H; clear H; subst.
    generalize (H3 (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    replace (i1+1+1) with (S (S i1)) in H0; try lia.
  + intros n N Psi T h.
    exists n; split; try lia.
    intros x H0.
    inversion h; clear h; subst.
    generalize (H3 x H0); clear H3; intro H4.
    inversion H4; clear H4; subst.
    assert (i1 = n); try lia.
    subst; auto.
Qed.

End prog_inv.

(****************************************************************
   Adequacy
  ****************************************************************)

Section proper_adeq.

Hint Rewrite ext_eq_eta : hybrid.

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

Lemma is_exp_proper : forall E:uexp,
  seq0 (atom_ (is_exp E)) -> (proper E).
Proof.
intros E [n h1].
generalize E h1; clear h1 E.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall E : uexp, seq_ n nil (atom_ (is_exp E)) -> proper E)).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 E h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* apply case *)
- inversion H3; clear H3; subst.
  apply proper_apply; auto.
  apply h1 with i0; auto; try lia.
  apply h1 with i0; auto; try lia.
(* fn case *)
- inversion H3; clear H3; subst.
  apply proper_fn; auto.
Qed.

Lemma eq_proper : forall T E:uexp,
  seq0 (atom_ (eq_a T E)) -> (proper T /\ proper E).
Proof.
intros T E [n h1].
generalize T E h1; clear h1 T E.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T E : uexp, seq_ n nil (atom_ (eq_a T E)) ->
        (proper T /\ proper E))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 T E h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* fn case *)
- split.
  + apply proper_lam; auto.
  + apply proper_fn; auto.
(* apply case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split.
  + apply proper_app; auto.
  + apply proper_apply; auto.
Qed.

Lemma shape_proper : forall T E:uexp,
  seq0 (atom_ (shape T E)) -> (proper T /\ proper E).
Proof.
intros T E [n h1].
generalize T E h1; clear h1 T E.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall T E : uexp, seq_ n nil (atom_ (shape T E)) ->
        (proper T /\ proper E))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 T E h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* var case *)
- inversion H3; subst; clear H3.
  inversion H4; subst; clear H4.
  inversion H0; subst; clear H0.
(* fn case *)
- split.
  + apply proper_lam; auto.
  + apply proper_fn; auto.
(* apply case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i0<i0+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4); elim h2; clear h2; intros h2 h5.
  specialize h3 with (1:=h4) (2:=H5); elim h3; clear h3; intros h3 h6.
  split.
  + apply proper_app; auto.
  + apply proper_apply; auto.
Qed.

Lemma varTOcc_proper : forall T:uexp, forall n:nat,
  seq0 (atom_ (varTOcc T n)) -> proper T.
Proof.
intros T n [i h1].
generalize T n h1; clear h1 T n.
generalize
 (lt_wf_ind i
    (fun i:nat =>
       forall T:uexp, forall n:nat, seq_ i nil (atom_ (varTOcc T n)) ->
        proper T)).
intro h'.
apply h'; clear h'; auto.
clear i.
intros i h1 T n h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* lam case *)
- apply proper_lam; auto.
(* apply case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i<i+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4).
  specialize h3 with (1:=h4) (2:=H5).
  apply proper_app; auto.
(* var case *)
- inversion H3; clear H3; subst.
  inversion H0; clear H0; subst.
Qed.

Lemma varEOcc_proper : forall E:uexp, forall n:nat,
  seq0 (atom_ (varEOcc E n)) -> proper E.
Proof.
intros E n [i h1].
generalize E n h1; clear h1 E n.
generalize
 (lt_wf_ind i
    (fun i:nat =>
       forall E:uexp, forall n:nat, seq_ i nil (atom_ (varEOcc E n)) ->
        proper E)).
intro h'.
apply h'; clear h'; auto.
clear i.
intros i h1 E n h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* lam case *)
- apply proper_fn; auto.
(* apply case *)
- inversion H3; clear H3; subst.
  generalize h1; generalize h1; intros h2 h3.
  assert (h4:i<i+1+1); try lia.
  specialize h2 with (1:=h4) (2:=H4).
  specialize h3 with (1:=h4) (2:=H5).
  apply proper_apply; auto.
(* var case *)
- inversion H3; clear H3; subst.
  inversion H0; clear H0; subst.
Qed.

End proper_adeq.

Section eq_adeq.

Hint Rewrite ext_eq_eta : hybrid.

Inductive ateR: list atm -> list atm -> list atm -> Prop :=
| nil_ate: ateR nil nil nil
| cons_ate: forall (Phi Psi Psi':list atm) (x y:uexp), proper x -> proper y ->
    ateR Phi Psi Psi' ->
    ateR (eq_a x y::Phi) (is_tm x::Psi) (is_exp y::Psi').

Hint Resolve nil_ate cons_ate : hybrid.

Lemma memb_ate : forall (Phi Psi Psi':list atm) (x y:uexp),
  ateR Phi Psi Psi' -> In (eq_a x y) Phi ->
  (In (is_tm x) Psi /\ In (is_exp y) Psi').
Proof.
intros Phi Psi Psi' x y; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

Lemma eq_adeq :
  forall (i:nat) (T E:uexp) (Phi Psi Psi':list atm),
  ateR Phi Psi Psi' ->
  seq_ i Phi (atom_ (eq_a T E)) ->
  seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi' (atom_ (is_exp E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T E:uexp) (Phi Psi Psi':list atm),
     ateR Phi Psi Psi' ->
     seq_ i Phi (atom_ (eq_a T E)) ->
     seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi' (atom_ (is_exp E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T E Phi Psi Psi' cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + generalize (eq_lam_inv i0 Phi T0 E0 H3); clear H3; intros [j [h1 h2]];
      subst.
    assert (h':forall (x y:uexp), proper x -> proper y ->
        (seq_ j (is_tm x:: Psi) (atom_ (is_tm (T0 x))) /\
         seq_ j (is_exp y:: Psi') (atom_ (is_exp (E0 y))))).
    { intros x y h1 h3.
      apply h with (eq_a x y::Phi); auto; try lia; eauto with hybrid. }
    replace (j+3) with (j+1+1+1); try lia.
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply seq_mono with j; try lia.
      generalize (h' x (Var 0) h5 (proper_Var 0)); tauto.
    * unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (is_exp x) (atom_ (is_exp (E0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply seq_mono with j; try lia.
      generalize (h' (Var 0) x (proper_Var 0) h5); tauto.
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
        apply s_bc with (Conj (atom_ (is_exp E1)) (atom_ (is_exp E2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- specialize memb_ate with (1:=cInv) (2:=H2); intros [h1 h2]; clear H2.
  split.
  + inversion cInv; subst.
    apply s_init; auto with hybrid.
  + inversion cInv; subst.
    apply s_init; auto with hybrid.
Qed.

Lemma eq_adeq_cor : forall T E:uexp, seq0 (atom_ (eq_a T E)) ->
  (seq0 (atom_ (is_tm T)) /\ seq0 (atom_ (is_exp E))).
Proof.
intros T E [i h1].
generalize nil_ate; intro h2.
specialize eq_adeq with (1:=h2) (2:=h1); intro h.
split; exists i; tauto.
Qed.

End eq_adeq.

Section shape_adeq.

Hint Rewrite ext_eq_eta : hybrid.

Inductive steR: list atm -> list atm -> list atm -> Prop :=
| nil_ste: steR nil nil nil
| cons_ste: forall (Phi Psi Psi':list atm) (x y:uexp), proper x -> proper y ->
    steR Phi Psi Psi' ->
    steR (varE y::varT x::Phi) (is_tm x::Psi) (is_exp y::Psi').

Hint Resolve nil_ste cons_ste : hybrid.

Lemma memb_ste1: forall (Phi Psi Psi':list atm) (x y:uexp),
  steR Phi Psi Psi' -> ~(In (shape x y) Phi).
Proof.
intros Phi Psi Psi' x y; induction 1; eauto with hybrid.
simpl; intros [h1 | [h1 | h1]]; try discriminate h1; try tauto.
Qed.

Lemma memb_ste2 : forall (Phi Psi Psi':list atm) (x:uexp),
  steR Phi Psi Psi' -> In (varT x) Phi -> In (is_tm x) Psi.
Proof.
intros Phi Psi Psi' x; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- discriminate h2.
- injection h2; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

Lemma memb_ste3 : forall (Phi Psi Psi':list atm) (x:uexp),
  steR Phi Psi Psi' -> In (varE x) Phi -> In (is_exp x) Psi'.
Proof.
intros Phi Psi Psi' x; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | [h2 | h2]].
- injection h2; intros; subst; simpl; auto.
- discriminate h2.
- simpl; tauto.
Qed.

Lemma shape_adeq :
  forall (i:nat) (T E:uexp) (Phi Psi Psi':list atm),
  steR Phi Psi Psi' ->
  seq_ i Phi (atom_ (shape T E)) ->
  seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi' (atom_ (is_exp E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T E:uexp) (Phi Psi Psi':list atm),
     steR Phi Psi Psi' ->
     seq_ i Phi (atom_ (shape T E)) ->
     seq_ i Psi (atom_ (is_tm T)) /\ seq_ i Psi' (atom_ (is_exp E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T E Phi Psi Psi' cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* var case *)
  + inversion H3; subst; clear H3.
    inversion H4; subst; clear H4.
    * inversion H0; subst; clear H0.
    * specialize memb_ste2 with (1:=cInv) (2:=H2); case Psi.
      -- simpl; tauto.
      -- intros a Phi h1.
         split.
         ++ apply s_init; auto with hybrid.
         ++ inversion H5; subst; clear H5.
            ** inversion H0; subst; clear H0.
            ** specialize memb_ste3 with (1:=cInv) (2:=H1); case Psi'.
               --- simpl; tauto.
               --- intros a' Phi' h1'.
                   apply s_init; auto with hybrid.
  (* lam case *)
  + generalize (shape_lam_inv i0 Phi T0 E0 H3); clear H3; intros [j [h1 h2]];
      subst.
    assert (h':forall (x y:uexp), proper x -> proper y ->
        (seq_ j (is_tm x:: Psi) (atom_ (is_tm (T0 x))) /\
         seq_ j (is_exp y:: Psi') (atom_ (is_exp (E0 y))))).
    { intros x y h1 h3.
      apply h with (varE y::varT x::Phi); eauto with hybrid; try lia. }
    replace (j+4+1) with (j+1+1+1+1+1); try lia.
    split.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply seq_mono with j; try lia.
      generalize (h' x (Var 0) h5 (proper_Var 0)); tauto.
    * unfold seq_,atom_;
        apply s_bc with (All (fun x:uexp => (Imp (is_exp x) (atom_ (is_exp (E0 x))))));
        auto with hybrid.
      apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply seq_mono with j; try lia.
      generalize (h' (Var 0) x (proper_Var 0) h5); tauto.
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
        apply s_bc with (Conj (atom_ (is_exp E1)) (atom_ (is_exp E2)));
        auto with hybrid.
      apply s_and; auto.
(* context case *)
- specialize memb_ste1 with (x:=T) (y:=E) (1:=cInv); intro; tauto.
Qed.

Lemma shape_adeq_cor : forall T E:uexp, seq0 (atom_ (shape T E)) ->
  (seq0 (atom_ (is_tm T)) /\ seq0 (atom_ (is_exp E))).
Proof.
intros T E [n h1].
generalize nil_ste; intro h2.
specialize shape_adeq with (1:=h2) (2:=h1); intro h.
split; exists n; tauto.
Qed.

End shape_adeq.

Section varTOcc_adeq.

Hint Rewrite ext_eq_eta : hybrid.

Inductive vtR: list atm -> list atm -> Prop :=
| nil_vt: vtR nil nil
| cons_vt: forall (Phi Psi:list atm) (x:uexp), proper x ->
    vtR Phi Psi -> vtR (varT x::Phi) (is_tm x::Psi).

Hint Resolve nil_vt cons_vt : hybrid.

Lemma memb_vt1: forall (Phi Psi:list atm) (x:uexp) (n:nat),
  vtR Phi Psi -> ~(In (varTOcc x n) Phi).
Proof.
intros Phi Psi x n; induction 1; eauto with hybrid.
simpl; intros [h1 | h1]; try discriminate h1; try tauto.
Qed.

Lemma memb_vt2 : forall (Phi Psi:list atm) (x:uexp),
  vtR Phi Psi -> In (varT x) Phi -> In (is_tm x) Psi.
Proof.
intros Phi Psi x; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

Lemma varTOcc_adeq :
  forall (i n:nat) (T:uexp) (Phi Psi:list atm),
  vtR Phi Psi ->
  seq_ i Phi (atom_ (varTOcc T n)) -> seq_ i Psi (atom_ (is_tm T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (n:nat) (T:uexp) (Phi Psi:list atm),
     vtR Phi Psi ->
     seq_ i Phi (atom_ (varTOcc T n)) -> seq_ i Psi (atom_ (is_tm T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h n T Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h5.
    specialize (H2 x h5).
    inversion H2; subst; clear H2.
    apply s_imp; auto.
    apply h with n (varT x::Phi); eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)));
      auto with hybrid.
    apply s_and; auto.
    * apply h with N1 Phi; auto; try lia.
    * apply h with N2 Phi; auto; try lia.
  (* var case *)
  + inversion H3; subst; clear H3.
    inversion H0; subst; clear H0.
    specialize memb_vt2 with (1:=cInv) (2:=H2); case Psi.
    * simpl; tauto.
    * intros a Phi h1.
      apply s_init; auto with hybrid.
(* context case *)
- specialize memb_vt1 with (x:=T) (n:=n) (1:=cInv); intro; tauto.
Qed.

Lemma varTOcc_adeq_cor : forall (T:uexp) (n:nat),
  seq0 (atom_ (varTOcc T n)) -> seq0 (atom_ (is_tm T)).
Proof.
intros T n [i h].
generalize nil_vt; intro h2.
specialize varTOcc_adeq with (1:=h2) (2:=h); intro; exists i; auto.
Qed.

End varTOcc_adeq.

Section varEOcc_adeq.

Hint Rewrite ext_eq_eta : hybrid.

Inductive veR: list atm -> list atm -> Prop :=
| nil_ve: veR nil nil
| cons_ve: forall (Phi Psi:list atm) (x:uexp), proper x ->
    veR Phi Psi -> veR (varE x::Phi) (is_exp x::Psi).

Hint Resolve nil_ve cons_ve : hybrid.

Lemma memb_ve1: forall (Phi Psi:list atm) (x:uexp) (n:nat),
  veR Phi Psi -> ~(In (varEOcc x n) Phi).
Proof.
intros Phi Psi x n; induction 1; eauto with hybrid.
simpl; intros [h1 | h1]; try discriminate h1; try tauto.
Qed.

Lemma memb_ve2 : forall (Phi Psi:list atm) (x:uexp),
  veR Phi Psi -> In (varE x) Phi -> In (is_exp x) Psi.
Proof.
intros Phi Psi x; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
injection h2; intros; subst; simpl; auto.
simpl; tauto.
Qed.

Lemma varEOcc_adeq :
  forall (i n:nat) (E:uexp) (Phi Psi:list atm),
  veR Phi Psi ->
  seq_ i Phi (atom_ (varEOcc E n)) -> seq_ i Psi (atom_ (is_exp E)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (n:nat) (E:uexp) (Phi Psi:list atm),
     veR Phi Psi ->
     seq_ i Phi (atom_ (varEOcc E n)) -> seq_ i Psi (atom_ (is_exp E)))).
intro H'.
apply H'; clear H' i; auto.
intros i h n E Phi Psi cInv h1.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* fn case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (is_exp x) (atom_ (is_exp (E0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h5.
    specialize (H2 x h5).
    inversion H2; subst; clear H2.
    apply s_imp; auto.
    apply h with n (varE x::Phi); eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (is_exp E1)) (atom_ (is_exp E2)));
      auto with hybrid.
    apply s_and; auto.
    * apply h with N1 Phi; auto; try lia.
    * apply h with N2 Phi; auto; try lia.
  (* var case *)
  + inversion H3; subst; clear H3.
    * inversion H0; subst; clear H0.
    * specialize memb_ve2 with (1:=cInv) (2:=H2); case Psi.
      -- simpl; tauto.
      -- intros a Phi h1.
         apply s_init; auto with hybrid.
(* context case *)
- specialize memb_ve1 with (x:=E) (n:=n) (1:=cInv); intro; tauto.
Qed.

Lemma varEOcc_adeq_cor : forall (E:uexp) (n:nat),
  seq0 (atom_ (varEOcc E n)) -> seq0 (atom_ (is_exp E)).
Proof.
intros T n [i h].
generalize nil_ve; intro h2.
specialize varEOcc_adeq with (1:=h2) (2:=h); intro; exists i; auto.
Qed.

End varEOcc_adeq.
