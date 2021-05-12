(****************************************************************
   File: sl.v                                                 
   Author: Amy Felty

   - original: May 2009
   - Feb 2021: Current Coq Version: V8.13.1
                                                                 
   An intuitionistic sequent calculus used as a specification
   logic, for use in two-level Hybrid.  See:

   Amy Felty and Alberto Momigliano, "Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax."  Journal
   of Automated Reasoning, 48(1):43-105, 2012.
  ***************************************************************)

From HybridSys Require Export Hybrid.

Section sl.

Set Implicit Arguments.

(****************************************************************
   The intuitionistic specification logic.
  ****************************************************************)
Variable atm : Set.
Variable con : Set.

Inductive oo : Set :=
  | atom : atm -> oo
  | T : oo
  | Conj : oo -> oo -> oo
  | Imp : atm -> oo -> oo
  | All : (expr con -> oo) -> oo
  | Some : (expr con -> oo) -> oo.

Variable prog : atm -> oo -> Prop.

Inductive seq : nat -> list atm -> oo -> Prop :=
  | s_bc :
      forall (i : nat) (A : atm) (L : list atm) (b : oo),
      prog A b -> seq i L b -> seq (i+1) L (atom A)
  | s_init :
      forall (i : nat) (A A' : atm) (L : list atm),
      In A (A' :: L) -> seq i (A' :: L) (atom A)
  | s_tt : forall (i : nat) (L : list atm), seq i L T
  | s_and :
      forall (i : nat) (B C : oo) (L : list atm),
      seq i L B -> seq i L C -> seq (i+1) L (Conj B C)
  | s_imp :
      forall (i : nat) (A : atm) (B : oo) (L : list atm),
      seq i (A :: L) B -> seq (i+1) L (Imp A B)
  | s_all :
      forall (i : nat) (B : expr con -> oo) (L : list atm),
      (forall x : expr con, proper x -> seq i L (B x)) -> seq (i+1) L (All B)
  | s_some :
      forall (i : nat) (B : expr con -> oo) (L : list atm) (x : expr con),
      seq i L (B x) -> seq (i+1) L (Some B).

Definition seq' (L : list atm) (B : oo) : Prop := exists i : nat, seq i L B.

(* height weakening *)
Theorem seq_mono :
 forall (j k : nat) (l : list atm) (b : oo), j < k -> seq j l b -> seq k l b.
intro j.
generalize
 (lt_wf_ind j
    (fun j : nat =>
     forall (k : nat) (l : list atm) (b : oo),
     j < k -> seq j l b -> seq k l b)).
intros H k l b H0 H1.
apply H; auto.
clear H1 H0 b l k H j.
intros n H k l b; generalize b l k; clear b l k.
simple induction b.
- intros a l k H0 H1.
  inversion H1.
  + subst.
    specialize lt_non_zero with (1 := H0); intro H7.
    elim H7; clear H7; intros j' H7.
    subst.
    apply s_bc with b0; auto.
    apply H with i; try lia; auto.
  + subst.
    apply s_init; auto.
- intros l k H0 H1.
  apply s_tt; auto.
- intros p H0 p0 H1 l k H2 H3.
  clear H0 H1.
  inversion H3.
  subst.
  specialize lt_non_zero with (1 := H2); intro H0.
  elim H0; clear H0; intros j' H0.
  subst.
  apply s_and; auto.
  + apply H with i; try lia; auto.
  + apply H with i; try lia; auto.
- intros a p H0 l k H1 H2.
  clear H0.
  inversion H2.
  subst.
  specialize lt_non_zero with (1 := H1); intro H0.
  elim H0; clear H0; intros j' H0.
  subst.
  apply s_imp; auto.
  apply H with i; try lia; auto.
- intros p H0 l k H1 H2.
  clear H0.
  inversion H2.
  subst.
  specialize lt_non_zero with (1 := H1); intro H0.
  elim H0; clear H0; intros j' H0.
  subst.
  apply s_all; auto.
  intros x HP.
  apply H with i; try lia; auto.
- intros p H0 l k H1 H2.
  clear H0.
  inversion H2.
  subst.
  specialize lt_non_zero with (1 := H1); intro H0.
  elim H0; clear H0; intros j' H0.
  subst.
  apply s_some with x; auto.
  apply H with i; try lia; auto.
Qed.

Theorem seq_mono_cor :
 forall (j k : nat) (l : list atm) (b : oo),
 j <= k -> seq j l b -> seq k l b.
intros j k l b H H0.
specialize le_lt_or_eq with (1 := H); intro H1.
elim H1; clear H1; intro H1.
- apply seq_mono with j; auto.
- rewrite <- H1; auto.
Qed.

(* context weakening *)
Theorem seq_thin_exch :
 forall (j : nat) (b : oo) (l l' : list atm),
 (forall a : atm, In a l -> In a l') -> seq j l b -> seq j l' b.
intros j b l l' H H0.
generalize H0 l' H; clear H0 H l'.
simple induction 1.
- intros i A L b0 H H1 H2 l' H3.
  apply s_bc with b0; auto.
- intros i A A' L H l' H1.
  generalize (H1 A H).
  clear H1; generalize l'; clear l'.
  induction l'.
  + intro H1; elim H1; auto.
  + apply s_init; auto.
- intros; apply s_tt.
- intros i B C L H H1 H2 H3 l' H4.
  apply s_and; auto.
- intros i A B L H H1 l' H2.
  apply s_imp; auto.
  apply H1; auto.
  intros a H3.
  specialize in_inv with (1 := H3); intro H4.
  elim H4; clear H4; intro H4.
  + rewrite H4.
    apply in_eq; auto.
  + apply in_cons; apply H2; auto.
- intros i B L H H1 l' H2.
  apply s_all; auto.
- intros i B L x H H1 l' H2.
  apply s_some with x; auto.
Qed.

Theorem specialization :
  forall (i:nat) (l:list atm) (b:expr con -> oo),
  seq (i+1) l (All b) -> forall (x:expr con), proper x -> seq i l (b x).
Proof.
intros i l b h0 x h1.
inversion h0; subst.
assert (i=i0); try lia; subst; clear H.
apply H2; auto.
Qed.

(* atomic cut *)
Lemma seq_cut_aux:
  forall (i j:nat)(a:atm)(b:oo)(l:(list atm)),
  (seq i (a::l) b)->(seq j l (atom a))->(seq (i+j) l b).
Proof.
intro i.
generalize (lt_wf_ind
              i
              (fun i:nat =>
              forall (j:nat)(a:atm)(b:oo)(l:(list atm)),
              (seq i (cons a l) b)->(seq j l (atom a))->(seq (plus i j) l b))).
intros H j a b l H0 H1.
apply H with a; auto.
clear H1 H0 l b a j H i.
intros n H j a b.
generalize b j a; clear b j a.
induction b.
- intros j a0 l H0 H1.
  inversion H0; subst.
  + replace (i+1+j) with (i+j+1); try lia.
    apply s_bc with b; auto.
    apply H with a0; auto; lia.
  + simpl in H4.
    elim H4; clear H4; intro H4.
    * subst.
      apply seq_mono_cor with j; auto; try lia.
    * clear H0 H1; generalize l H4; clear l H4.
      induction l; auto.
      ++ simpl; intro H0; elim H0.
      ++ intro H0; apply s_init; auto.
(* T case *)
- intros; apply s_tt; auto.
(* Conj case *)
- intros j a l H2 H3.
  inversion H2; subst.
  replace (i+1+j) with (i+j+1); try lia.
  apply s_and; auto.
  + apply H with a; auto; lia.
  + apply H with a; auto; lia.
(* Imp case *)
- intros j a0 l H1 H2.
  inversion H1; subst.
  replace (i+1+j) with (i+j+1); try lia.
  apply s_imp; auto.
  apply H with a0; auto; try lia.
  + apply seq_thin_exch with (a::a0::l); auto.
    intros a1 H0.
    simpl; simpl in H0.
    tauto.
  + apply seq_thin_exch with l; auto.
    simpl; intros a1 H0; tauto.
(* All case *)
- intros j a l H1 H2.
  inversion H1; subst.
  replace (i+1+j) with (i+j+1); try lia.
  apply s_all; auto.
  intros x H'.
  apply H with a; auto; try lia.
(* Some case *)
- intros j a l H1 H2.
  inversion H1; subst.
  replace (i+1+j) with (i+j+1); try lia.
  apply s_some with x; auto.
  apply H with a; auto; try lia.
Qed.

Theorem seq_cut:
  forall (a:atm)(b:oo)(l:(list atm)),
  (seq' (a::l) b)->(seq' l (atom a))->(seq' l b).
unfold seq'.
intros a b l [i H] [j H0].
exists (i + j).
apply seq_cut_aux with a; auto.
Qed.

Unset Implicit Arguments.

End sl.
