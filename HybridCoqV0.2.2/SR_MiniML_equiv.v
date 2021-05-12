(****************************************************************
   File: SR_MiniML_equi.v
   Author: Amy Felty

   original: March 2014
   Feb 2021: Current Coq Version: V8.13.1
                                                                 
   Subject Reduction for Call-by-Value Mini-ML using Hybrid
   Example showing why meta-level isterm1 cannot be used for
   equivalence proof of meval and eval
   (the exists/forall quantifier problem).

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

Hint Unfold seq_ seq'_ seq0: hybrid.

End encoding.

#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.
#[global] Hint Unfold proper: hybrid.
#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tabs tap tfix eap eabs efix exp_app exp_lam exp_fix : hybrid.

(****************************************************************
 ****************************************************************
   Version of subject reduction with eval judgments defined as an
   inductive type (meval) as described in Section 4.4 of [1].
  ****************************************************************
  ****************************************************************)

Section meta_sr.

Fixpoint uexp2atm_list (l:list uexp) : list atm :=
  match l with
    | nil => nil
    | (e::l') => (isterm e::(uexp2atm_list l'))
  end.

Lemma memb_isterm: forall (x:uexp) (Gamma: list uexp),
  In x Gamma -> In (isterm x) (uexp2atm_list Gamma).
Proof.
intro x; induction Gamma; simpl; auto.
intros [h | h]; subst; auto.
Qed.

Hint Resolve memb_isterm : hybrid.

Theorem isterm_equiv_isterm1 : forall (E:uexp)(Gamma:list uexp),
 isterm1 Gamma E <->
 exists n:nat, seq_ n (uexp2atm_list Gamma) (atom_ (isterm E)).
intros E Gamma; split.
- induction 1; auto with hybrid.
  (* var case *)
  + generalize H; clear H; case G.
    * simpl; try tauto.
    * intros u l h.
      specialize memb_isterm with (1:=h); intro h'.
      exists 0; unfold seq_,atom_; apply s_init; eauto with hybrid.
  (* App case *)
  + destruct IHisterm1_1 as [i1 h1].
    destruct IHisterm1_2 as [i2 h2].
    exists (i1+i2+1+1+1).
    apply s_bc with (Conj (atom_ (isterm M)) (atom_ (isterm N))); eauto with hybrid.
    apply s_and; auto.
    * apply seq_mono with i1; auto; try lia.
    * apply seq_mono with i2; auto; try lia.
  (* Fun case *)
  (* exists/forall quantification problem *)
  +      
Abort.

(* MC-Theorem 25 from [1] *)
Theorem eval_equiv_meval : forall e v:uexp,
 (meval e v) <-> seq0 (atom_ (eval e v)).
Proof.
intros e v; split.
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
  + exists (0+1).
    unfold seq_,atom_; apply s_bc with (atom_ (isterm (Fun (fun x => E x))));
      eauto with hybrid.
(* need the above failed lemma to continue *)
Abort.
