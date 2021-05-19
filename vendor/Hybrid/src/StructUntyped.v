
(****************************************************************
   File: StructUntyped.v
   Author: Amy Felty

   original: January 2010
   updated: March 2014
   Feb 2021: Current Coq Version: V8.13.1

   Structural relationship between lambda-terms, simple example

   Theorem: if (forall N. le N K implies le N L) then  le K L.

   Note: Nested universal quantification and implication.

  ***************************************************************)

From HybridSys Require Export sl.

Section encoding.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set := cAPP: Econ | cLAM: Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition app : uexp -> uexp -> uexp :=
  fun M1:uexp => fun M2:uexp => (APP (APP (CON cAPP) M1) M2).
Definition lam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON cLAM) (lambda M)).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Hint Unfold proper: hybrid.

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

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Inductive atm : Set :=
   is_tm : uexp -> atm
 | lt: uexp -> uexp -> atm
 | le: uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

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
  (* lt *)
  | lt_lam : forall (N:uexp) (M:uexp->uexp), abstr M ->
      prog (lt N (lam M))
        (Conj (All (fun x:uexp => (Imp (is_tm x) (atom_ (le N (M x))))))
              (atom_ (is_tm N)))
  | lt_appl : forall N M1 M2:uexp,
      prog (lt N (app M1 M2))
        (Conj (atom_ (le N M1)) (atom_ (is_tm M2)))
  | lt_appr : forall N M1 M2:uexp,
      prog (lt N (app M1 M2))
        (Conj (atom_ (le N M2)) (atom_ (is_tm M1)))
  (* le *)
  | le_ : forall M N:uexp, 
      prog (le M M) (atom_ (is_tm M))
  | le_lt : forall M N:uexp, 
      prog (le M N) (atom_ (lt M N)).

Hint Resolve tm_app tm_lam lt_lam lt_appl lt_appr le_ le_lt : hybrid.

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := sl.seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

Hint Unfold seq_ seq'_ seq0: hybrid.

End encoding.

#[global] Hint Unfold proper: hybrid.
#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tm_app tm_lam lt_lam lt_appl lt_appr le_ le_lt : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
  Main Theorem: if forall N. le N K implies le N L then  le K L.
  ****************************************************************)

Lemma ref : forall (M:uexp),
  seq0 (atom_ (is_tm M)) -> seq0 (atom_ (le M M)).
Proof.
intros M [n h1].
generalize h1; clear h1; case n.
- intro h; inversion h; subst; clear h.
  replace (i+1) with (S i) in H; try lia; discriminate H.
- clear n; intros n h.
  exists ((S n)+1); unfold seq_,atom_; apply s_bc with (atom_ (is_tm M));
    auto with hybrid.
Qed.

Theorem thm' : forall (K L:uexp),
  seq0 (atom_ (is_tm K)) ->
  (forall (N:uexp), seq0 (atom_ (le N K)) -> seq0 (atom_ (le N L))) ->
  seq0 (atom_ (le K L)).
Proof.
intros K L h1 h2.
specialize ref with (1:=h1); intro h3.
specialize h2 with (1:=h3); auto.
Qed.

Theorem thm : forall (K L:uexp),
  seq0 (atom_ (is_tm K)) ->
  (forall (N:uexp), seq0 (atom_ (le N K)) -> seq0 (atom_ (le N L))) ->
  seq0 (atom_ (le K L)).
Proof.
intros K L [n h1] h2.
inversion h1; subst; clear h1.
inversion H0; subst; clear H0.
- inversion H3; subst; clear H3.
  assert (h1:(seq0 (atom_ (is_tm (app T1 T2))))).
  { exists (i0+1+1); unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (is_tm T1)) (atom_ (is_tm T2)));
      auto with hybrid.
    apply s_and; auto. }
  specialize ref with (1:=h1); intro h3.
  specialize h2 with (1:=h3); auto.
- inversion H3; subst; clear H3.
  assert (h1:(seq0 (atom_ (is_tm (lam T))))).
  { exists (i0+1+1); unfold seq_,atom_;
      apply s_bc with (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (T x))))));
      auto with hybrid.
    apply s_all; auto. }
  specialize ref with (1:=h1); intro h3.
  specialize h2 with (1:=h3); auto.
Qed.

(****************************************************************
   Internal Adequacy
  ****************************************************************)

Section lemmas.

Hint Rewrite ext_eq_eta : hybrid.

Lemma abstr_id : (abstr (fun x:uexp => x)).
Proof.
exists (fun x:uexp => x); split; auto with hybrid.
apply abst_id; auto.
Qed.

Hint Resolve abstr_id : hybrid.

Lemma proper_lam_id : (proper (lam (fun x:uexp => x))).
Proof.
apply proper_lam; auto with hybrid.
Qed.

Hint Resolve proper_lam_id : hybrid.

Lemma is_tm_id : forall (l:list atm),
   seq_ 3 l (atom_ (is_tm (lam (fun x:uexp => x)))).
Proof.
intro l; replace 3 with (0+1+1+1); try lia.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm x)))));
  auto with hybrid.
apply s_all; auto.
intros x h3.
apply s_imp; auto.
apply s_init; auto; simpl; tauto.
Qed.

Lemma lt_lam_inv :
forall (i:nat) (Psi:list atm) (N:uexp) (M:uexp->uexp),
seq_ i Psi (All (fun x:uexp =>
                Imp (is_tm x) (atom_ (le N (M x))))) ->
exists j:nat, (i=j+2 /\ 
 forall (x:uexp),
       proper x ->
       seq_ j (is_tm x::Psi) (atom_ (le N (M x)))).
Proof.
intro i; case i.
- intros Psi N M H.
  inversion H; clear H; subst.
  replace (i0+1) with (S i0) in H0; try lia.
- clear i; intro i; case i.
  + intros Psi N M H.
    inversion H; clear H; subst.
    generalize (H3 (Var 0) (proper_Var 0)); intro H1.
    inversion H1; clear H1; subst.
    replace (i1+1+1) with (S (S i1)) in H0; try lia.
  + intros n Psi N M h.
    exists n; split; try lia.
    intros x H0.
    inversion h; clear h; subst.
    generalize (H3 x H0); clear H3; intro H3.
    inversion H3; clear H3; subst.
    assert (i1 = n); try lia.
    subst; auto.
Qed.

End lemmas.

#[global] Hint Resolve abstr_id : hybrid.
#[global] Hint Resolve proper_lam_id : hybrid.

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

Lemma lt_proper : forall M N:uexp,
  seq0 (atom_ (lt M N)) -> (proper M /\ proper N).
Proof.
intros M N [n h1].
generalize M N h1; clear h1 M N.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall M N : uexp, seq_ n nil (atom_ (lt M N)) ->
        (proper M /\ proper N))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 M N h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* lam case *)
- inversion H3; subst; clear H3.
  inversion H5; subst; clear H5.
  specialize H2 with (1:=proper_lam_id).
  inversion H2; subst; clear H2.
  split.
  + inversion H3; subst; clear H3.
    * inversion H0; subst; clear H0.
      -- apply abstr_proper_e; auto with hybrid.
      -- specialize seq_cut_aux with (1:=H5) (2:=(is_tm_id nil)); intro h4.
         assert (h5:i+3<i+1+1+1+1+1); try lia.
         specialize h1 with (1:=h5) (2:=h4); tauto.
    * simpl in H1; elim H1; clear H1; intro H1; try contradiction.
      discriminate H1.
  + apply proper_lam; auto.
(* app left case *)
- inversion H3; clear H3; subst.
  inversion H4; clear H4; subst.
  inversion H0; clear H0; subst.
  + split.
    * apply is_tm_proper; exists i; auto.
    * apply proper_app; auto.
      -- apply is_tm_proper; exists i; auto.
      -- apply is_tm_proper; exists (i+1); auto.
  + assert (h2:i<i+1+1+1); try lia.
    specialize h1 with (1:=h2) (2:=H3).
    split; try tauto.
    apply proper_app; try tauto.
    apply is_tm_proper; exists (i+1); auto.
(* app right case *)
- inversion H3; clear H3; subst.
  inversion H4; clear H4; subst.
  inversion H0; clear H0; subst.
  + split.
    * apply is_tm_proper; exists i; auto.
    * apply proper_app; auto.
      -- apply is_tm_proper; exists (i+1); auto.
      -- apply is_tm_proper; exists i; auto.
  + assert (h2:i<i+1+1+1); try lia.
    specialize h1 with (1:=h2) (2:=H3).
    split; try tauto.
    apply proper_app; try tauto.
    apply is_tm_proper; exists (i+1); auto.
Qed.

Lemma le_proper : forall M N:uexp,
  seq0 (atom_ (le M N)) -> (proper M /\ proper N).
Proof.
intros M N [n h1].
generalize M N h1; clear h1 M N.
generalize
 (lt_wf_ind n
    (fun n:nat =>
       forall M N : uexp, seq_ n nil (atom_ (le M N)) ->
        (proper M /\ proper N))).
intro h'.
apply h'; clear h'; auto.
clear n.
intros n h1 M N h2.
inversion h2; clear h2; subst.
inversion H0; clear H0; subst.
(* refl case *)
- split; apply is_tm_proper; exists i; auto.
(* lt case *)
- apply lt_proper; auto.
  exists i; auto.
Qed.

End proper_adeq.

Section lt_le_adeq.

Inductive xR: list atm -> Prop :=
| nil_x: xR nil
| cons_x: forall (Phi:list atm) (x:uexp), proper x ->
    xR Phi -> xR (is_tm x::Phi).

Hint Resolve nil_x cons_x : hybrid.

Lemma memb_x1: forall (Phi:list atm) (x y:uexp),
  xR Phi -> ~(In (lt x y) Phi).
Proof.
intros Phi x; induction 1; eauto with hybrid.
simpl; intros [h1 | h1]; try discriminate h1; try tauto.
Qed.

Lemma memb_x2: forall (Phi:list atm) (x y:uexp),
  xR Phi -> ~(In (le x y) Phi).
Proof.
intros Phi x; induction 1; eauto with hybrid.
simpl; intros [h1 | h1]; try discriminate h1; try tauto.
Qed.

Lemma lt_le_adeq :
  forall (i:nat) (M N:uexp) (Phi:list atm),
  xR Phi ->
  (seq_ i Phi (atom_ (lt M N)) \/ seq_ i Phi (atom_ (le M N))) ->
  seq_ i Phi (atom_ (is_tm M)) /\ seq_ i Phi (atom_ (is_tm N)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (M N:uexp) (Phi:list atm),
     xR Phi ->
     (seq_ i Phi (atom_ (lt M N)) \/ seq_ i Phi (atom_ (le M N))) ->
     seq_ i Phi (atom_ (is_tm M)) /\ seq_ i Phi (atom_ (is_tm N)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M N Phi cInv h1.
destruct h1 as [h1 | h1].
(* lt case *)
- inversion h1; subst; clear h1.
  + inversion H0; subst; clear H0.
    (* lt_lam case *)
    * inversion H3; subst; clear H3.
      generalize (lt_lam_inv i Phi M M0 H5); clear H5; intros [j [h1 h2]];
        subst.
      split.
      -- apply seq_mono with (j + 2); try lia; auto.
      -- unfold seq_,atom_;
           apply s_bc with
               (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (M0 x))))));
           auto with hybrid.
         apply s_all; auto.
         intros x h5.
         replace (j+2) with (j+1+1); try lia.
         apply s_imp; auto.
         specialize (h2 x h5).
         assert (hj:j+1<j+2+1+1); try lia.
         assert (h1:seq_ (j+1) (is_tm x :: Phi) (atom_ (lt M (M0 x))) \/
                    seq_ (j+1) (is_tm x :: Phi) (atom_ (le M (M0 x)))).
         { right; apply seq_mono with j; try lia; auto. }
         assert (h3:xR (is_tm x::Phi)); eauto with hybrid.
         specialize h with (1:=hj) (2:=h3) (3:=h1); tauto.
    (* lt_appl case *)
    * inversion H3; subst; clear H3.
      assert (hi:i<i+1+1); try lia.
      generalize h; intro h'.
      assert (h4:seq prog i Phi (atom_ (lt M M1)) \/
                 seq prog i Phi (atom_ (le M M1))); try tauto.
      specialize h' with (1:=hi) (2:=cInv) (3:=h4).
      destruct h' as [h1 h2].
      split.
      -- apply seq_mono with i; try lia; auto.
      -- unfold seq_,atom_;
           apply s_bc with (Conj (atom_ (is_tm M1)) (atom_ (is_tm M2)));
           auto with hybrid.
         apply s_and; auto.
    (* lt_appr case *)
    * inversion H3; subst; clear H3.
      assert (hi:i<i+1+1); try lia.
      generalize h; intro h'.
      assert (h4:seq prog i Phi (atom_ (lt M M2)) \/
                 seq prog i Phi (atom_ (le M M2))); try tauto.
      specialize h' with (1:=hi) (2:=cInv) (3:=h4).
      destruct h' as [h1 h2].
      split.
      -- apply seq_mono with i; try lia; auto.
      -- unfold seq_,atom_;
           apply s_bc with (Conj (atom_ (is_tm M1)) (atom_ (is_tm M2)));
           auto with hybrid.
         apply s_and; auto.
  (* context case *)
  + specialize (memb_x1 (A'::L) M N cInv); tauto.
(* le case *)
- inversion h1; subst; clear h1.
  + inversion H0; subst; clear H0.
    (* le_refl case *)
    * split; apply seq_mono with i0; try lia; auto.
    (* le_lt case *)
    * assert (hi:i0<i0+1); try lia.
      assert (h1:seq prog i0 Phi (atom_ (lt M N)) \/
                 seq prog i0 Phi (atom_ (le M N))); try tauto.
      specialize h with (1:=hi) (2:=cInv) (3:=h1).
      split; apply seq_mono with i0; try lia; tauto.
  (* context case *)
  + specialize (memb_x2 (A'::L) M N cInv); tauto.
Qed.

Lemma lt_adeq_cor : forall M N:uexp, seq0 (atom_ (lt M N)) ->
  (seq0 (atom_ (is_tm M)) /\ seq0 (atom_ (is_tm N))).
Proof.
intros M N [i h1].
generalize nil_x; intro h2.
assert (h3:seq prog i nil (atom_ (lt M N)) \/
           seq prog i nil (atom_ (le M N))); try tauto.
specialize lt_le_adeq with (1:=h2) (2:=h3); intro h.
split; exists i; tauto.
Qed.

Lemma le_adeq_cor : forall M N:uexp, seq0 (atom_ (le M N)) ->
  (seq0 (atom_ (is_tm M)) /\ seq0 (atom_ (is_tm N))).
Proof.
intros M N [i h1].
generalize nil_x; intro h2.
assert (h3:seq prog i nil (atom_ (lt M N)) \/
           seq prog i nil (atom_ (le M N))); try tauto.
specialize lt_le_adeq with (1:=h2) (2:=h3); intro h.
split; exists i; tauto.
Qed.

End lt_le_adeq.
