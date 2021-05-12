(****************************************************************
   File: SR_MiniML_meval.v
   Author: Amy Felty

   original: July 2007
   updated: February 2015
   Feb 2021: Current Coq Version: V8.13.1
                                                                 
   Subject Reduction for Call-by-Value Mini-ML using Hybrid
   Version with evaluation judgment defined as an inductive definition
   (meval).

   Example from:
   [1] Amy Felty and Alberto Momigliano, Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax, In Journal
   of Automated Reasoning, 48(1):43-105, 2012.

  ***************************************************************)

From HybridSys Require Export sl.
From HybridSys Require Export MiniML.

(****************************************************************
 ****************************************************************
   Evaluation judgment defined as an inductive definition (meval),
   and associated properties as described in Section 3.3 of [1].
  ****************************************************************
  ****************************************************************)

(****************************************************************
   Evaluation
  ****************************************************************)

Section meval.

Inductive meval: uexp -> uexp -> Prop :=
  meval_App: forall E1':uexp -> uexp, forall E1 E2 V V2:uexp,
               abstr E1' ->
               meval E1 (Fun (fun x => E1' x)) ->
               meval E2 V2 -> meval (E1' V2) V ->
               meval (App E1 E2) V
| meval_Fun: forall E:uexp -> uexp, abstr E -> 
               isterm1 nil (Fun (fun x => E x)) ->
               meval (Fun (fun x => E x)) (Fun (fun x => E x))
| meval_Fix: forall E:uexp -> uexp, forall V:uexp,
               abstr E ->
               isterm1 nil (Fix (fun x => E x)) ->
               meval (E (Fix (fun x => E x))) V ->
               meval (Fix (fun x => E x)) V.

End meval.

(****************************************************************
   Adequacy: proper conditions
  ****************************************************************)

Section m_proper_adeq.

Lemma meval_proper_l : forall E V:uexp, meval E V -> proper E.
Proof.
intros E V; induction 1.
- apply proper_App; auto.
- apply proper_Fun; auto.
- apply proper_Fix; auto.
Qed.

Lemma meval_proper_r : forall E V:uexp, meval E V -> proper V.
intros E V; induction 1; auto.
apply proper_Fun; auto.
Qed.

(* MC-Lemma 14 (1) from [1] *)
Lemma meval_proper : forall E V:uexp,
  meval E V -> (proper E /\ proper V).
Proof.
intros E V h1; split.
- apply meval_proper_l with V; auto.
- apply meval_proper_r with E; auto.
Qed.

Hint Resolve term1_var term1_app term1_lam term1_fix : hybrid.

(* MC-Lemma 14 (2) from [1] *)
Lemma meval_isterm_ctx : forall (M N:uexp),
  meval M N -> (isterm1 nil M /\ isterm1 nil N).
Proof.
intros M N; induction 1; try tauto.
split; try tauto.
apply term1_app; tauto.
Qed.

(* MC-Lemma 13 from [1] *)
Lemma eval_unique:
  forall E F:uexp, (meval E F) -> forall G:uexp, (meval E G) -> F=G.
Proof.
intros E F; induction 1.
(* App case *)
- intros G H2'.
  inversion H2'; subst.
  generalize (IHmeval1 (Fun (fun x : uexp => E1'0 x)) H6); intro H9'.
  specialize abstr_eta with (1:=H); intro H10'.
  specialize abstr_eta with (1:=H5); intro H11'.
  generalize (Fun_inj (fun x => E1' x) (fun x => E1'0 x) H10' H11' H9');
    intro H12'.
  unfold ext_eq in H12'.
  generalize (IHmeval2 V1 H7); intro H7'; subst.
  rewrite <- H12' in H9.
  + apply IHmeval3; auto.
  + apply meval_proper_r with E2; auto.
(* Fun case *)
- intros G h0.
inversion h0; auto.
unfold Fun,lambda.
rewrite H1; auto.
(* Fix case *)
- intros G H1'.
  inversion H1'; auto.
  specialize abstr_eta with (1:=H); intro H6'.
  specialize abstr_eta with (1:=H3); intro H7'.
  generalize (abstr_lbind_simp H7' H6' H2); intro H8.
  unfold ext_eq in H8.
  apply IHmeval; auto.
  rewrite <- H8; auto.
  + unfold Fix,lambda.
    unfold Fix,lambda in H0.
    rewrite <- H2; auto.
  + apply proper_Fix; auto.
Qed.

End m_proper_adeq.

(****************************************************************
 ****************************************************************
   The two-level encoding of isterm, eval, and hastype judgments
   as in Figure 6 in [1].
  ****************************************************************
  ****************************************************************)

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Section encoding.

Inductive atm : Set :=
   typeof : uexp -> tp -> atm
 | isterm : uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  | tabs :
      forall (T1 T2: tp) (E : uexp -> uexp),
      abstr E ->
      prog (typeof (Fun (fun x => E x)) (arrow T1 T2))
        (All (fun x : uexp => Imp (typeof x T1) (atom_ (typeof (E x) T2))))
  | tap :
      forall E1 E2: uexp, forall T T' : tp,
      prog (typeof (App E1 E2) T)
        (Conj (atom_ (typeof E1 (arrow T' T))) (atom_ (typeof E2 T')))
  | tfix :
      forall (T: tp) (E : uexp -> uexp),
      abstr E ->
      prog (typeof (Fix (fun x => E x)) T)
        (All (fun x : uexp => Imp (typeof x T) (atom_ (typeof (E x) T))))
  | exp_app : forall M N:uexp,
      prog (isterm (App M N))
        (Conj (atom_ (isterm M)) (atom_ (isterm N)))
  | exp_lam : forall (E:uexp -> uexp),
      abstr E ->
      prog (isterm (Fun (fun x => (E x))))
        (All (fun x:uexp => (Imp (isterm x) (atom_ (isterm (E x))))))
  | exp_fix : forall (E:uexp -> uexp),
      abstr E ->
      prog (isterm (Fix (fun x => (E x))))
        (All (fun x:uexp => (Imp (isterm x) (atom_ (isterm (E x)))))).
          
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
#[global] Hint Resolve tabs tap tfix exp_app exp_lam exp_fix : hybrid.

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section prog_inv.

Lemma typeof_abs_inv :
forall (i:nat) (l:list atm) (T T':tp) (E:uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i l (Imp (typeof x T) (atom_ (typeof (E x) T')))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j ((typeof x T)::l) (atom_ (typeof (E x) T'))).
Proof.
induction i; auto.
- intros l T T' E H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros l T T' E H.
  clear IHi.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

End prog_inv.

(****************************************************************
 ****************************************************************
   Version of subject reduction with eval judgments defined as an
   inductive type (meval) as described in Section 4.4 of [1].
  ****************************************************************
  ****************************************************************)

Section meta_sr.

(* MC-Theorem 26 from [1] *)
Theorem meta_subject_reduction :
 forall e v : uexp, (meval e v) ->
 forall t : tp, seq0 (atom_ (typeof e t)) -> seq0 (atom_ (typeof v t)).
intros e v; induction 1.
(* App case *)
- intros t H3.
  unfold seq0 in H3; elim H3; clear H3; intros j H3.
  inversion H3; clear H3; subst.
  inversion H5; clear H5; subst.
  inversion H8; clear H8; subst.
  assert (seq0 (atom_ (typeof E1 (arrow T' t)))).
  + unfold seq0,seq_; exists i0; auto.
  + assert (seq0 (atom_ (typeof E2 T'))).
    { unfold seq0,seq_; exists i0; auto. }
    clear H7 H9.
    generalize (IHmeval2 T' H4); intro H4'.
    generalize (IHmeval1 (arrow T' t) H3); intro H8.
    unfold seq0 in H8; elim H8; clear H8; intros j H8.
    inversion H8; clear H8; subst.
    inversion H6; clear H6; subst.
    inversion H10; clear H10; subst.
    generalize (typeof_abs_inv i1 nil T' t E H9); intro H10.
    elim H10; clear H10; intros j [Heq H10].
    subst.
    clear H9.
    generalize (H10 V2 (meval_proper_r E2 V2 H1)); clear H10; intro H10.
    generalize (abstr_eta H); intro H15'.
    generalize (abstr_eta H11); intro H5'.
    generalize (abstr_lbind_simp H5' H15' H5); intro H12.
    unfold ext_eq in H12.
    rewrite H12 in H10; auto.
    * clear H12 H5' H5 H11 E.
      apply IHmeval3; auto.
      unfold seq0, seq_.
      apply seq_cut with (typeof V2 T'); auto.
      unfold seq'.
      exists j; auto.
    * apply meval_proper_r with E2; auto.
(* Fun case *)
- auto.
(* Fix case *)
- intros t h1.
  elim h1; intros j H1'.
  inversion H1'; clear H1'; subst.
  inversion H3; clear H3; subst.
  inversion H6; clear H6; subst.
  generalize (typeof_abs_inv i0 nil t t E0 H8); clear H8; intro H9.
  elim H9; clear H9; intros j [Heq H9]; subst.
  generalize (H9 (Fix (fun x : uexp => E x))); clear H9; intro H9.
  generalize (abstr_eta H); intro H5'.
  generalize (abstr_eta H7); intro H8'.
  generalize (abstr_lbind_simp H8' H5' H2); intro H1'.
  unfold ext_eq in H1'.
  rewrite -> H1' in H9.
  + clear H1' H8' H2 H7 E0.
    generalize (abstr_proper_Fix (fun x => E x) H5'); intro H0'.
    generalize (H9 H0'); clear H9; intro H9.
    apply IHmeval; auto.
    unfold seq0, seq_.
    apply seq_cut with (typeof (Fix (fun x : uexp => E x)) t); auto.
    unfold seq'.
    exists j; auto.
  + apply proper_Fix; auto.
Qed.

End meta_sr.
