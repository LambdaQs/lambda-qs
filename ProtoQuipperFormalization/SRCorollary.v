(****************************************************************
   File: SRCorollary.v
   Authors: Mohamend Yousri Mahmoud and Amy Felty
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Subject Reduction (Type Soundness) for Proto-Quipper
   for closed terms (no free term variables, only free
   quantum variables)
   ***************************************************************)
Require Import SubjectReduction.
Require Import ProgLemmas3.
Require Import ProgLemmas2.
Require Import ProgLemmas1.
Require Import PQAdequacy.
Require Import ProtoQuipperProg.
Require Import LSL.
Require Import ProtoQuipperSyntax.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Definition seq_ := SubjectReduction.seq_.
Definition prog := SubjectReduction.prog.

Hint Constructors validT Subtyping.

Theorem subject_reduction': forall i, forall IL C C' a a' LL1 LL2 A,
      (forall V, In V (get_boxed a) -> 
                 ~ (exists n, V = (Var n) \/ V = (CON (Qvar n))))-> 
      NoDup (FQUC a') -> NoDup(FQU a')->  
      (forall t, In t IL ->
                 (exists n, t = is_qexp (Var n) \/ t = is_qexp (CON (Qvar n)) \/
                            exists T, t = typeof (Var n) T)) ->
      (forall q, In q (FQ a') -> In (typeof q qubit) LL2)->
      Subtypecontext IL LL1 IL LL1 ->
      Subtypecontext IL LL2 IL LL2 ->
      common_ll a a' LL1 LL2 ->
      seq_ i IL [] (atom_ (reduct C a C' a')) ->
      exists j, seq_ j IL LL1  (atom_ (typeof a A)) ->
                exists k, seq_ k IL LL2 (atom_ (typeof a' A)).
Proof.
  intros i IL C C' a a' LL1 LL2 A H H0 H1 H2 H3 H4 H5 H6 H7.
  generalize (subject_reduction i IL C C' a a' H H0 H1 H2 H7).
  intros [j H8].
  exists j; intros H9.
  specialize (H8 LL1 LL2 A H4 H5 H6 H3 H9).
  assumption.
Qed.  

Inductive qvar_ctx_rel : qexp -> qexp -> list atm ->list atm -> list atm -> Prop :=
| qcr_nil: forall a a', qvar_ctx_rel a a' [] [] []
| qcr_is_qexp: forall a a' a'' il ll1 ll2,
    qvar_ctx_rel a a' il ll1 ll2 -> qvar_ctx_rel a a' (is_qexp a''::il) ll1 ll2
| qcr_is_typeof1: forall q a a' il ll1 ll2,
    In q (FQ a) -> ~(In q (FQ a')) -> ~(In (typeof q qubit) ll1) ->
    qvar_ctx_rel a a' il ll1 ll2 ->
    qvar_ctx_rel a a' (is_qexp q::il) (typeof q qubit::ll1) ll2
| qcr_is_typeof2: forall q a a' il ll1 ll2,
    ~(In q (FQ a)) -> In q (FQ a') -> ~(In (typeof q qubit) ll2) ->
    qvar_ctx_rel a a' il ll1 ll2 ->
    qvar_ctx_rel a a' (is_qexp q::il) ll1 (typeof q qubit::ll2)
| qcr_is_typeof_both: forall q a a' il ll1 ll2,
    In q (FQ a) -> In q (FQ a') ->
    ~(In (typeof q qubit) ll1) -> ~(In (typeof q qubit) ll2) ->
    qvar_ctx_rel a a' il ll1 ll2 ->
    qvar_ctx_rel a a' (is_qexp q::il) (typeof q qubit::ll1) (typeof q qubit::ll2).

Definition qvar_context_constraints (a a':qexp) (IL LL1 LL2:list atm) : Prop :=
  (forall t, In t IL -> exists i, t = is_qexp (CON (Qvar i))) /\
  (forall q, In q (FQ a') -> In (typeof q qubit) LL2) /\
  qvar_ctx_rel a a' IL LL1 LL2.

Lemma ctx_constraints_weaken_qvar : forall a a' IL LL1 LL2,
    qvar_context_constraints a a' IL LL1 LL2 ->
    forall t : atm, In t IL ->
                    exists i0 : var,
                      t = is_qexp (Var i0) \/ t = is_qexp (CON (Qvar i0)) \/
                      (exists T : qtp, t = typeof (Var i0) T).
Proof.
  unfold qvar_context_constraints.
  intros a a' IL LL1 LL2 [H [H1 H2]] t H3.
  specialize H with (1:=H3).
  destruct H as [i H]; subst. exists i; tauto.
Qed.

Lemma ctx_constraints_weaken_Subtypecontext1 : forall a a' IL LL1 LL2,
    qvar_context_constraints a a' IL LL1 LL2 -> Subtypecontext IL LL1 IL LL1.
Proof.
  unfold qvar_context_constraints.
  intros a a' IL LL1 LL2 [H [H0 H1]].
  clear H H0. induction H1; auto.
  - constructor.
  - constructor; auto.
  - apply subcnxt_llg; auto.
  - constructor; auto.
  - apply subcnxt_llg; auto.
Qed.
  
Lemma ctx_constraints_weaken_Subtypecontext2 : forall a a' IL LL1 LL2,
    qvar_context_constraints a a' IL LL1 LL2 -> Subtypecontext IL LL2 IL LL2.
Proof.
  unfold qvar_context_constraints.
  intros a a' IL LL1 LL2 [H [H0 H1]].
  clear H H0. induction H1; auto.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - apply subcnxt_llg; auto.
  - apply subcnxt_llg; auto.
Qed.
  
Lemma ctx_constraints_weaken_common_ll : forall a a' IL LL1 LL2,
    qvar_context_constraints a a' IL LL1 LL2 -> common_ll a a' LL1 LL2.
Proof.
  unfold qvar_context_constraints.
  intros a a' IL LL1 LL2 [H [H0 H1]].
  clear H H0. induction H1; auto.
Qed.

Hint Resolve ctx_constraints_weaken_Subtypecontext1 ctx_constraints_weaken_Subtypecontext2
     ctx_constraints_weaken_common_ll.
  
Corollary subject_reduction_cor: forall i, forall IL C C' a a' LL1 LL2 A,
      (forall V, In V (get_boxed a)  -> 
                 ~(exists i, V = (Var i) \/ V = (CON (Qvar i)))) -> 
      NoDup (FQUC a') -> NoDup(FQU a') ->  
      qvar_context_constraints a a' IL LL1 LL2 ->
      seq_ i IL [] (atom_ (reduct C a C' a')) ->
      exists j, seq_ j IL LL1 (atom_ (typeof a A)) ->
      exists k, seq_ k IL LL2 (atom_ (typeof a' A)).
Proof.
  intros i IL C C' a a' LL1 LL2 A H H0 H1 H2 H3.
  generalize H2; intros [H4 [H5 H6]].
  generalize (subject_reduction' i IL C C' a a' LL1 LL2 A H H0 H1
                                (ctx_constraints_weaken_qvar a a' IL LL1 LL2 H2)
                                H5
                                (ctx_constraints_weaken_Subtypecontext1 a a' IL LL1 LL2 H2)
                                (ctx_constraints_weaken_Subtypecontext2 a a' IL LL1 LL2 H2)
                                (ctx_constraints_weaken_common_ll a a' IL LL1 LL2 H2)
                                H3); auto.
Qed.
