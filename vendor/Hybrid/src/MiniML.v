(****************************************************************
   File: MiniML.v                                                 
   Author: Amy Felty

   original: July 2007
   updated: March 2014
   Feb 2021: Current Coq Version: V8.13.1
                                                                 
   Example from:
   [1] Amy Felty and Alberto Momigliano, Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax, In Journal
   of Automated Reasoning, 48(1):43-105, 2012.

  ***************************************************************)

From HybridSys Require Export Hybrid.

Section miniml.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set := cABS: Econ | cAPP: Econ | cFIX : Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition App : uexp -> uexp -> uexp :=
  fun e1:uexp => fun e2:uexp => (APP (APP (CON cAPP) e1) e2).
Definition Fun : (uexp -> uexp) -> uexp :=
  fun f:uexp->uexp => (APP (CON cABS) (lambda f)).
Definition Fix : (uexp -> uexp) -> uexp :=
  fun f:uexp->uexp => (APP (CON cFIX) (lambda f)).


(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

Lemma proper_App: forall (E1 E2:uexp),
  proper E1 -> proper E2 -> proper (App E1 E2).
Proof.
unfold App; auto with hybrid.
Qed.

Lemma proper_App_l : forall (E1 E2:uexp),
  proper (App E1 E2) -> proper E1.
Proof.
unfold App; intros E1 E2 h.
inversion h; subst; clear h; auto.
inversion H2; subst; auto.
Qed.

Lemma proper_App_r : forall (E1 E2:uexp),
  proper (App E1 E2) -> proper E2.
Proof.
unfold App; intros E1 E2 h.
inversion h; subst; clear h; auto.
Qed.

Lemma proper_Fun: forall (E:uexp -> uexp),
  abstr E -> proper (Fun (fun x => E x)).
Proof.
unfold Fun; auto with hybrid.
Qed.

Lemma proper_Fix:
  forall (E:uexp -> uexp), abstr E -> proper (Fix (fun x => E x)).
Proof.
unfold Fix; auto with hybrid.
Qed.

Lemma abstr_proper_Fix:
  forall E:uexp->uexp, (abstr E) -> (proper (Fix E)).
Proof.
unfold Fix; auto with hybrid.
Qed.

(* MC-Theorem 9 in [1] *)
Lemma FA_clash : forall (e:uexp->uexp) (e1 e2:uexp), (Fun e)<>(App e1 e2).
Proof.
intros e e1 e2 H.
inversion H.
Qed.

Lemma Fun_inj: forall E E':uexp->uexp,
  (abstr E) -> (abstr E') -> (Fun E)=(Fun E')->(ext_eq E E').
Proof.
unfold Fun; intros E E' H H0 H1.
inversion H1.
apply abstr_lbind_simp with 0; auto.
Qed.

Lemma Fix_inj: forall E E':uexp->uexp,
  (abstr E) -> (abstr E') -> (Fix E)=(Fix E')->(ext_eq E E').
Proof.
unfold Fix; intros E E' H H0 H1.
inversion H1.
apply abstr_lbind_simp with 0; auto.
Qed.

Lemma clash_App_Fun : forall (e:uexp->uexp) (e1 e2:uexp) (P:Prop),
  (Fun e)=(App e1 e2) -> P.
Proof.
intros e e1 e2 P H.
generalize (FA_clash e e1 e2); intro H0; elim H0; auto.
Qed.

(****************************************************************
   The isterm1 predicate for internal adequacy.  See page 60 of [1]
  ****************************************************************)

Inductive isterm1 : list uexp -> uexp -> Prop :=
| term1_var : forall (G:list uexp) (x:uexp), In x G -> isterm1 G x
| term1_app : forall (G:list uexp) (M N:uexp),
              isterm1 G M -> isterm1 G N -> isterm1 G (App M N)
| term1_lam : forall (G:list uexp) (E:uexp -> uexp), abstr E ->
              (forall x:uexp, proper x -> isterm1 (x::G) (E x)) ->
              isterm1 G (Fun (fun x => (E x)))
| term1_fix : forall (G:list uexp) (E:uexp -> uexp), abstr E ->
              (forall x:uexp, proper x -> isterm1 (x::G) (E x)) ->
              isterm1 G (Fix (fun x => (E x))).

(****************************************************************
   Types
  ****************************************************************)

Inductive tp: Set :=
   gnd : tp
 | arrow : tp -> tp -> tp.

End miniml.
