(****************************************************************
   File: SR_MiniML_eval.v
   Author: Amy Felty

   original: July 2007
   updated: February 2015
   Feb 2021: Current Coq Version: V8.13.1
                                                                 
   Subject Reduction for Call-by-Value Mini-ML using Hybrid

   Example from:
   [1] Amy Felty and Alberto Momigliano, Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax, In Journal
   of Automated Reasoning, 48(1):43-105, 2012.

  ***************************************************************)

From HybridSys Require Export sl.
From HybridSys Require Export MiniML.

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
 | eval : uexp -> uexp -> atm
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
  | eap : forall E1':uexp -> uexp, forall E1 E2 V V2:uexp,
      abstr E1' ->
      prog (eval (App E1 E2) V)
        (Conj (atom_ (eval E1 (Fun (fun x => E1' x))))
         (Conj (atom_ (eval E2 V2))
          (atom_ (eval (E1' V2) V))))
  | eabs : forall E:uexp -> uexp, (abstr E) -> 
      prog (eval (Fun (fun x => E x)) (Fun (fun x => E x)))
        (atom_ (isterm (Fun (fun x => E x))))
  | efix : forall E:uexp -> uexp, forall V:uexp,
      abstr E ->
      prog (eval (Fix (fun x => E x)) V)
        (Conj (atom_ (eval (E (Fix (fun x => E x))) V))
         (atom_ (isterm (Fix (fun x => E x)))))
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
#[global] Hint Resolve tabs tap tfix eap eabs efix exp_app exp_lam exp_fix : hybrid.

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
   Version of internal adequacy and subject reduction with eval
   judgments defined using the specification logic as described in
   Section 4.2 of [1]
  ****************************************************************
  ****************************************************************)

(****************************************************************
   Adequacy: proper conditions
  ****************************************************************)

Section proper_adeq.

Lemma eval_proper_l : forall E V:uexp,
  seq0 (atom_ (eval E V)) -> (proper E).
Proof.
intros E V [n h1].
generalize E V h1; clear h1 E V.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall E V : uexp, seq_ n nil (atom_ (eval E V)) -> proper E)).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 E V h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
- inversion H3; clear H3; subst.
  inversion H6; clear H6; subst.
  assert (i<i+1+1+1); try lia.
  assert (i+1<i+1+1+1); try lia.
  generalize (h1 i H E2 V2 H3); intro h2.
  generalize (h1 (i+1) H0 E1 (Fun (fun x : uexp => E1' x)) H5); intro h3.
  apply proper_App; auto.
- apply proper_Fun; auto.
- apply proper_Fix; auto.
Qed.

Lemma eval_proper_r : forall E V:uexp,
  seq0 (atom_ (eval E V)) -> (proper V).
intros E V [n h1].
generalize E V h1; clear h1 E V.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall E V : uexp, seq_ n nil (atom_ (eval E V)) -> proper V)).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 E V h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
- inversion H3; clear H3; subst.
  inversion H6; clear H6; subst.
  apply h1 with i (E1' V2); auto; lia.
- apply proper_Fun; auto.
- inversion H3; clear H3; subst.
  apply h1 with i0 (E0 (Fix (fun x : uexp => E0 x))); auto; lia.
Qed.

(* MC-Lemma 20 (1) from [1] *)
Lemma eval_proper : forall E V:uexp,
  seq0 (atom_ (eval E V)) -> (proper E) /\ (proper V).
Proof.
intros E V h1; split.
- apply eval_proper_l with V; auto.
- apply eval_proper_r with E; auto.
Qed.

(* MC-Lemma 20 (3) from [1] *)
Lemma hastype_proper : forall (E:uexp) (T:tp),
  seq0 (atom_ (typeof E T)) -> (proper E).
Proof.
intros E T [n h1].
generalize E T h1; clear h1 E T.
generalize
 (lt_wf_ind n
    (fun n:nat =>
     forall (E : uexp) (T : tp), seq_ n nil (atom_ (typeof E T)) -> proper E)).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 E T h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
- apply proper_Fun; auto.
- inversion H3; clear H3; subst.
  apply proper_App; auto.
  + apply h1 with i0 (arrow T' T); auto; try lia.
  + apply h1 with i0 T'; auto; try lia.
- apply proper_Fix; auto.
Qed.

End proper_adeq.

(****************************************************************
   Internal Adequacy of Judgments
  ****************************************************************)

Section adeq.

Inductive txR: list atm -> list atm -> Prop :=
| nil_tx: txR nil nil
| cons_tx: forall (Phi Psi:list atm) (x:uexp) (T:tp), proper x ->
    txR Phi Psi ->
    txR (typeof x T::Phi) (isterm x::Psi).

Hint Resolve nil_tx cons_tx : hybrid.

Lemma memb_tx : forall (Phi Psi:list atm) (x:uexp) (T:tp),
  txR Phi Psi -> In (typeof x T) Phi -> In (isterm x) Psi.
Proof.
intros Phi Psi x; induction 1; eauto with hybrid.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; simpl; auto.
- simpl; tauto.
Qed.

Lemma hastype_isterm_ctx :
  forall (i:nat) (M:uexp) (T:tp) (l l':list atm),
  txR l l' ->
  seq_ i l (atom_ (typeof M T)) ->
  seq_ i l' (atom_ (isterm M)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (M : uexp) (T : tp) (l l' : list atm),
     txR l l' ->
     seq_ i l (atom_ (typeof M T)) -> seq_ i l' (atom_ (isterm M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M T l l' h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* Fun case *)
  + inversion H3; subst; clear H3.
    generalize (typeof_abs_inv i l T1 T2 E H2); clear H2; intros [j [h3 h4]];
      subst.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (Imp (isterm x) (atom_ (isterm (E x)))))).
    * apply exp_lam; auto.
    * apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply h with T2 (typeof x T1::l); eauto with hybrid.
      lia.
  (* App case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_; apply s_bc with (Conj (atom_ (isterm E1)) (atom_ (isterm E2))).
    * apply exp_app.
    * apply s_and; auto.
      apply h with (arrow T' T) l; auto.
      lia.
      apply h with T' l; auto.
      lia.
  (* Fix case *)
  + inversion H3; subst; clear H3.
    generalize (typeof_abs_inv i l T T E H2); clear H2; intros [j [h3 h4]];
      subst.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (Imp (isterm x) (atom_ (isterm (E x)))))).
    * apply exp_fix; auto.
    * apply s_all; auto.
      intros x h5.
      apply s_imp; auto.
      apply h with T (typeof x T::l); eauto with hybrid.
      lia.
(* context case *)
- specialize memb_tx with (1:=h1) (2:=H2).
  case l'.
  + simpl; tauto.
  + intros a l'' h2; unfold seq_,atom_; apply s_init; auto.
Qed.

(* MC-Lemma 20 (4) from [1] *)
Lemma hastype_isterm : forall (M:uexp) (T:tp),
  seq0 (atom_ (typeof M T)) ->
  seq0 (atom_ (isterm M)).
Proof.
intros M T [i h].
generalize nil_tx; intro h1.
generalize (hastype_isterm_ctx i M T nil nil); intro h2.
exists i; tauto.
Qed.

Lemma eval_isterm_ctx : forall (i:nat) (M N:uexp),
  seq_ i nil (atom_ (eval M N)) ->
  (seq_ i nil (atom_ (isterm M)) /\ seq_ i nil (atom_ (isterm N))).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall M N : uexp,
     seq_ i nil (atom_ (eval M N)) ->
     seq_ i nil (atom_ (isterm M)) /\ seq_ i nil (atom_ (isterm N)))).
intro H'; apply H'; clear H' i; auto.
intros i h M N h3.
inversion h3; subst; clear h3.
inversion H0; subst; clear H0.
- inversion H3; subst; clear H3.
  inversion H6; subst; clear H6.
  (* App case *)
  + assert (ha1: (i0<i0+1+1+1)); try lia.
    assert (ha2: (i0+1<i0+1+1+1)); try lia.
    generalize h; intro h'.
    specialize h' with (1:=ha1) (2:=H3).
    elim h'; clear h'; intros h1 h2.
    generalize h; intro h'.
    specialize h' with (1:=ha1) (2:=H7).
    elim h'; clear h'; intros h3 h4.
    generalize h; intro h'.
    specialize h' with (1:=ha2) (2:=H5).
    elim h'; clear h'; intros h5 h6.
    split.
    * unfold seq_,atom_;
        apply s_bc with
            (Conj (atom_ (isterm E1)) (atom_ (isterm E2))).
      -- apply exp_app.
      -- apply s_and; auto.
         apply seq_mono with i0; auto; try lia.
    * unfold seq_,atom_; apply seq_mono with i0; auto; try lia.
(* Fun case *)
- unfold seq_,atom_; split; apply seq_mono with i0; auto; try lia.
(* Fix case *)
- inversion H3; subst; clear H3.
  split.
  + unfold seq_,atom_; apply seq_mono with i; auto; try lia.
  + assert (ha:(i<i+1+1)); try lia.
    specialize h with (1:=ha) (2:=H5).
    elim h; intros h1 h2.
    unfold seq_,atom_; apply seq_mono with i; auto; try lia.
Qed.

(* MC-Lemma 20 (2) from [1] *)
Lemma eval_isterm : forall (M N:uexp),
  seq0 (atom_ (eval M N)) ->
  (seq0 (atom_ (isterm M)) /\ seq0 (atom_ (isterm N))).
Proof.
intros M N [i h].
specialize eval_isterm_ctx with (1:=h); intros [h1 h2].
split; exists i; auto.
Qed.

End adeq.

(****************************************************************
   Subject Reduction (Type Soundness)
  ****************************************************************)

Section sr.

(* MC-Theorem 24 from [1] *)
Theorem OL_subject_reduction :
 forall e v : uexp, seq0 (atom_ (eval e v)) ->
 forall t : tp, seq0 (atom_ (typeof e t)) -> seq0 (atom_ (typeof v t)).
intros e v H t H0.
unfold seq0 in H; elim H; clear H; intros n H.
generalize
 (lt_wf_ind n
    (fun j:nat =>
       forall e v:uexp, seq_ j nil (atom_ (eval e v)) ->
       forall t:tp, seq0 (atom_ (typeof e t)) ->
       seq0 (atom_ (typeof v t)))).
intro H'.
apply H' with e; clear H'; auto.
clear H n H0 e v t.
intros n H e v H0 t H1.
inversion H0; clear H0; subst.
inversion H3; clear H3; subst.
(* App case *)
- inversion H6; clear H6; subst.
  inversion H8; clear H8; subst.
  unfold seq0 in H1; elim H1; clear H1; intros j H1.
  inversion H1; clear H1; subst.
  inversion H2; clear H2; subst.
  inversion H8; clear H8; subst.
  assert (seq0 (atom_ (typeof E1 (arrow T' t)))).
  { unfold seq0,seq_; exists i1; auto. }
  assert (seq0 (atom_ (typeof E2 T'))).
  { unfold seq0,seq_; exists i1; auto. }
  clear H4 H10.
  assert (i < i+1+1+1); try lia.
  assert (i+1 < i+1+1+1); try lia.
  generalize (H i H2 E2 V2 H6 T' H1); intro H4.
  generalize (H (i+1) H3 E1 (Fun (fun x => E1' x)) H7 (arrow T' t) H0);
    intro H8.
  unfold seq0 in H8.
  elim H8; clear H8; intros j H8.
  inversion H8; clear H8; subst.
  inversion H11; clear H11; subst.
  inversion H14; clear H14; subst.
  generalize (typeof_abs_inv i2 nil T' t E H13); intro H10.
  elim H10; clear H10; intros j [Heq H10].
  subst.
  clear H13.
  assert (proper V2).
  { apply eval_proper_r with E2.
    unfold seq0; exists i; auto. }
  generalize (H10 V2 H11); clear H10; intro H10.
  generalize (abstr_eta H15); intro H15'.
  generalize (abstr_eta H5); intro H5'.
  generalize (abstr_lbind_simp H15' H5' H8); intro H12.
  unfold ext_eq in H12.
  rewrite H12 in H10; auto; clear H12 H15' H8 H15 E.
  apply H with i (E1' V2); auto; try lia.
  unfold seq0, seq_.
  apply seq_cut with (typeof V2 T'); auto.
  unfold seq'.
  exists j; auto.
(* Fun case *)
- exact H1.
(* Fix case *)
- elim H1; intros j H1'.
  inversion H1'; clear H1'; subst.
  inversion H2; clear H2; subst.
  inversion H7; clear H7; subst.
  generalize (typeof_abs_inv i1 nil t t E0 H9); clear H9; intro H9.
  elim H9; clear H9; intros j [Heq H9]; subst.
  generalize (H9 (Fix (fun x : uexp => E x))); clear H9; intro H9.
  generalize (abstr_eta H5); intro H5'.
  generalize (abstr_eta H8); intro H8'.
  generalize (abstr_lbind_simp H8' H5' H0); intro H1'.
  unfold ext_eq in H1'.
  rewrite -> H1' in H9; auto.
  + clear H1' H8' H0 H8 E0.
    generalize (abstr_proper_Fix (fun x => E x) H5'); intro H0.
    generalize (H9 H0); clear H9; intro H9.
    inversion H6; subst; clear H6.
    apply H with i0 (E (Fix (fun x : uexp => E x))); auto; try lia.
    unfold seq0, seq_.
    apply seq_cut with (typeof (Fix (fun x : uexp => E x)) t); auto.
    unfold seq'.
    exists j; auto.
  + apply proper_Fix; auto.
Qed.

End sr.

(****************************************************************
 ****************************************************************
   Equivalence of eval and meval
  ****************************************************************
  ****************************************************************)

Section equiv.

(****************************************************************
   Evaluation
  ****************************************************************)

Inductive meval: uexp -> uexp -> Prop :=
  eval_App: forall E1':uexp -> uexp, forall E1 E2 V V2:uexp,
               abstr E1' ->
               meval E1 (Fun (fun x => E1' x)) ->
               meval E2 V2 -> meval (E1' V2) V ->
               meval (App E1 E2) V
| eval_Fun: forall E:uexp -> uexp, abstr E -> 
               seq0 (atom_ (isterm (Fun (fun x => E x)))) ->
               meval (Fun (fun x => E x)) (Fun (fun x => E x))
| eval_Fix: forall E:uexp -> uexp, forall V:uexp,
               abstr E ->
               seq0 (atom_ (isterm (Fix (fun x => E x)))) ->
               meval (E (Fix (fun x => E x))) V ->
               meval (Fix (fun x => E x)) V.

(* MC-Theorem 25 from [1] *)
Theorem eval_equiv_meval : forall e v:uexp,
 (meval e v) <-> seq0 (atom_ (eval e v)).
Proof.
intros e v; split.
(* -> *)
- induction 1; auto with hybrid.
  (* App case *)
  + destruct IHmeval1 as [i1 h1].
    destruct IHmeval2 as [i2 h2].
    destruct IHmeval3 as [i3 h3].
    exists (i1+i2+i3+1+1+1+1).
    unfold seq_,atom_;
      apply s_bc with
          (Conj (atom_ (eval E1 (Fun (fun x => E1' x))))
                (Conj (atom_ (eval E2 V2))
                      (atom_ (eval (E1' V2) V)))); eauto with hybrid.
    apply s_and.
    * apply seq_mono with i1; try lia; auto.
    * apply s_and.
      -- apply seq_mono with i2; try lia; auto.
      -- apply seq_mono with i3; try lia; auto.
  (* Fun case *)
  + destruct H0 as [i h].
    exists (i+1).
    unfold seq_,atom_; apply s_bc with (atom_ (isterm (Fun (fun x => E x))));
      eauto with hybrid.
  (* Fix case *)
  + destruct H0 as [i1 h1].
    destruct IHmeval as [i2 h2].
    exists (i1+i2+1+1+1).
    unfold seq_,atom_;
      apply s_bc with
          (Conj (atom_ (eval (E (Fix (fun x => E x))) V))
                (atom_ (isterm (Fix (fun x => E x))))); eauto with hybrid.
    apply s_and; auto.
    * apply seq_mono with i2; try lia; auto.
    * apply seq_mono with i1; try lia; auto.
(* <- *)
- intro h.
  unfold seq0 in h; elim h; clear h; intros n h.
  generalize
    (lt_wf_ind n
               (fun j:nat =>
                  forall e v:uexp,
                    seq_ j nil (atom_ (eval e v)) -> meval e v)).
  intro H'.
  apply H'; clear H'; auto.
  clear h n e v.
  intros n H e v H0.
  inversion H0; subst; clear H0.
  inversion H2; subst; clear H2.
  (* App case *)
  + inversion H5; subst; clear H5.
    inversion H7; subst; clear H7.
    apply eval_App with E1' V2; auto.
    * apply H with (i+1); auto; try lia.
    * apply H with i; auto; try lia.
    * apply H with i; auto; try lia.
  (* Fun case *)
  + apply eval_Fun; auto.
    exists i; auto.
  (* Fix case *)
  + inversion H5; subst; clear H5.
    apply eval_Fix; auto.
    * exists i0; auto.
    * apply H with i0; auto; try lia.
Qed.

End equiv.
