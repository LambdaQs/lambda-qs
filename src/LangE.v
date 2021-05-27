(* Language E of simple expressions from PFPL Ch-4 *)

From HybridSys Require Export Hybrid.
From HybridSys Require Export sl.
Require Import Strings.String.

Section encoding.

(****************************************************************
   Types
  ****************************************************************)

(* Typ, τ *)
Inductive tp : Type :=
| num : tp
| str : tp
.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

(* Exp, e *)
Inductive Econ : Set :=
| eNUM   : nat -> Econ
| eSTR   : string -> Econ
| ePLUS  : Econ
| eTIMES : Econ
| eCAT   : Econ
| eLEN   : Econ
| eLET   : Econ
.

Definition eexp : Set := expr Econ.

Definition Var : var -> eexp := VAR Econ.
Definition Bnd : bnd -> eexp := (VAR Econ).

Definition Num (n:nat) : eexp := (CON (eNUM n)).
Definition Str (s:string) : eexp := (CON (eSTR s)).
Definition Plus (e1 e2 : eexp) : eexp := APP (APP (CON ePLUS) e1) e2.
Definition Times (e1 e2 : eexp) : eexp := APP (APP (CON eTIMES) e1) e2.
Definition Cat (e1 e2 : eexp) : eexp := APP (APP (CON eCAT) e1) e2.
Definition Len (e:eexp) : eexp := APP (CON eLEN) e.
(* let(e1; x.e2) *)
Definition Let (e1:eexp) (f : eexp -> eexp) : eexp :=
  (APP (APP (CON eLET) e1) (lambda (fun x => f x))).

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

Lemma proper_Let: forall (e1:eexp) (f:eexp -> eexp),
  proper e1 -> abstr f -> proper (Let e1 (fun x => f x)).
Proof.
  unfold Let; auto with hybrid.
Qed.

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.

   atm/atom represents atomic predicates of the object language
  ****************************************************************)
Inductive atm : Set :=
| oft  : eexp -> tp -> atm (* e : τ *)
| term : eexp -> atm (* is_exp *)
.

(* oo is the type of SL (specification logic) propositions *)
Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

(****************************************************************
   Contexts with Unique Variables
  ****************************************************************)

(* newvar for atoms *)
Definition nvA (a:atm) : var :=
  match a with
  | oft  e t => (newvar e)
  | term e   => (newvar e)
  end.

Lemma nvA_oft : forall (e:eexp) (t:tp),
  nvA (oft e t) = (newvar e).
Proof.
  simpl; auto.
Qed.

Lemma nvA_term : forall (e:eexp), nvA (term e) = (newvar e).
Proof.
  simpl; auto.
Qed.

(* newvar wrt a context *)
Fixpoint nvC (l:list atm) {struct l} : var :=
  match l with
  | nil     => 0
  | (a::l') => max (nvA a) (nvC l')
  end.

Lemma nvC_cons: forall (a:atm) (l:list atm),
  nvC (a::l) = max (nvA a) (nvC l).
Proof.
  simpl; auto.
Qed.

Lemma greater_head_nvC : forall (v:var) (t:tp) (l:list atm),
  (nvC (oft (Var v) t::l)) > v.
Proof.
  intros v t l; simpl.
  assert (h:(exists n:nat, (nvC l)=n)).
  { exists (nvC l); auto. }
  elim h; clear h; intros n h; rewrite h; clear h.
  case n; simpl; auto.
  intro n0; rewrite max_SS.
  generalize (max_dec (S v) (S n0)); intros [h | h].
  - rewrite h; lia.
  - generalize (PeanoNat.Nat.max_spec_le (S v) (S n0)).
  rewrite h; lia.
Qed.

Lemma greater_nvC: forall (v:var) (t:tp) (l:list atm),
  (In (oft (Var v) t) l) -> (nvC l > v).
Proof.
  induction l; try contradiction; auto.
  (* cons case *)
  generalize a; clear a; induction a; try contradiction; auto.
  - generalize e; clear e; induction e.
    (* CON case *)
    + intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
        try discriminate h.
      simpl; apply IHl; auto.
    (* VAR case *)
    + intro h; specialize in_inv with (1:=h); clear h; intros [h | h].
      * unfold Var; injection h; intros; subst; clear h.
        apply greater_head_nvC; auto.
      * generalize (IHl h); clear IHl h; intro h.
        rewrite -> nvC_cons.
        rewrite -> nvA_oft.
        unfold newvar.
        generalize (PeanoNat.Nat.max_dec (S v0) (nvC l)); intros [h1 | h1].
        -- generalize (PeanoNat.Nat.max_spec_le (S v0) (nvC l)).
          rewrite h1; lia.
        -- rewrite h1; auto.
    (* BND case *)
    + intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
        try discriminate h.
      simpl; apply IHl; auto.
    (* APP case *)
    + intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
        try discriminate h.
      simpl.
      generalize (IHl h); intro h1.
      generalize (PeanoNat.Nat.max_spec_le (max (newvar e1) (newvar e2)) (nvC l));
        intro h2.
      lia.
    (* ABS case *)
    + intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
        try discriminate h.
      simpl.
      generalize (IHl h); intro h1.
      generalize (PeanoNat.Nat.max_spec_le (newvar e) (nvC l)); intro h2.
      lia.
  (* term case *)
  - simpl; intros [h | h]; try discriminate h.
    generalize (IHl h); intro h1.
    generalize (PeanoNat.Nat.max_spec_le (newvar e) (nvC l)); lia.
Qed.

Lemma fresh_nvC: forall (v:var) (t:tp) (l:list atm),
  (In (oft (Var v) t) l) -> (nvC l <> v).
Proof.
  intros v t l h; generalize (greater_nvC v t l); intro h1.
  generalize (h1 h); intro; lia.
Qed.

(****************************************************************
   Definition of prog
  ****************************************************************)

(* prog is the object level judgment *)
Inductive prog : atm -> oo_ -> Prop :=
(*
  Generic hypothetical judgment of the form
    Χ | Γ ⊢ e : τ
  where Χ is a finite set of variables and Γ is the typing context
  with hypotheses of the form x : τ, where x ∈ Χ.
*)
| of_str : forall (s:string),
    prog (oft (Str s) str) T_
| of_num : forall (n:nat),
    prog (oft (Num n) num) T_
| of_plus : forall (e1 e2: eexp),
    prog (oft (Plus e1 e2) num)
      (Conj (atom_ (oft e1 num)) (atom_ (oft e2 num)))
| of_times : forall (e1 e2: eexp),
    prog (oft (Times e1 e2) num)
      (Conj (atom_ (oft e1 num)) (atom_ (oft e2 num)))
| of_cat : forall (e1 e2: eexp),
    prog (oft (Cat e1 e2) str)
      (Conj (atom_ (oft e1 str)) (atom_ (oft e2 str)))
| of_len : forall (e:eexp),
    prog (oft (Len e) num) (atom_ (oft e str))
| of_let : forall (t1 t2:tp) (e1:eexp) (f:eexp -> eexp),
    abstr f ->
    prog (oft (Let e1 f) t2)
      (Conj (atom_ (oft e1 t1))
        (All (fun x : eexp => Imp (oft x t1) (atom_ (oft (f x) t2)))))

(* Well-formed terms.
   This is not needed in Twelf and Beluga
 *)
| tm_num : forall (n:nat), prog (term (Num n)) T_
| tm_str : forall (s:string), prog (term (Str s)) T_
| tm_plus : forall (e1 e2: eexp),
    prog (term (Plus e1 e2)) (Conj (atom_ (term e1)) (atom_ (term e2)))
| tm_times : forall (e1 e2: eexp),
    prog (term (Times e1 e2))  (Conj (atom_ (term e1)) (atom_ (term e2)))
| tm_cat : forall (e1 e2: eexp),
    prog (term (Cat e1 e2))  (Conj (atom_ (term e1)) (atom_ (term e2)))
| tm_len : forall (e:eexp), prog (term (Len e)) (atom_ (term e))
| tm_let : forall (e1:eexp) (f:eexp->eexp),
    abstr f ->
    prog (term (Let e1 f))
      (All (fun x:eexp => (Imp (term x) (atom_ (term (f x))))))
.

(****************************************************************
   Instantiation of seq
  ****************************************************************)

(* seq is the SL level judgment,
   the nat arg corresponds to height of the (inductive) proof
*)
Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := exists i : nat, seq_ i nil B.

End encoding.

#[global] Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
#[global] Hint Resolve proper_APP abstr_proper : hybrid.
#[global] Hint Unfold proper: hybrid.
#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve of_str of_num of_plus of_times of_cat of_len of_let : hybrid.
#[global] Hint Resolve tm_str tm_num tm_plus tm_times tm_cat tm_len tm_let : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Type Uniqueness
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_uniq.

(* Context Gamma *)
Inductive xtG : list atm -> Prop :=
| nil_t : xtG nil
| cons_t : forall (Phi_t:list atm) (t:tp),
    xtG Phi_t -> xtG (oft (Var (nvC Phi_t)) t::Phi_t).

(* TODO: this seems like a lot of work to introduce a lemma for each term :(

Lemma memb_xtG_NoStr : forall (Phi_t:list atm) (E:eexp->eexp) (T T':tp),
  xtG Phi_t -> ~(In (oft (lam T E) T') Phi_t).
Proof.
intros Phi_t E T T'; induction 1; simpl; try tauto.
intro h; elim IHxtG.
destruct h as [h2 | h2]; try discriminate h2; auto.
Qed.

Lemma memb_xtG_NoApp : forall (Phi_t:list atm) (M N:eexp) (T:tp),
  xtG Phi_t -> ~(In (oft (app M N) T) Phi_t).
Proof.
intros Phi_t M N T; induction 1; simpl; try tauto.
intro h; elim IHxtG.
destruct h as [h2 | h2]; try discriminate h2; auto.
Qed. *)

(* Context invariant (induction hypothesis for type unicity):
  > This invariant expresses that every term occurring in a typing judgment in
  > the context is a variable, and if a variable occurs more than once
  > associated with more than one type, then these types must all be the same.
  > Note that this definition is just a restatement of type unicity specific to
  > variables inside the context.
  See:
    Felty, Momigliano. Reasoning with hypothetical judgments and open terms in
    Hybrid. PPDP 2009.
  and
    H-Lemma 31 (Context Membership) in
    Felty, Momigliano, Pientka. The Next 700 Challenge Problems for Reasoning
    with Higher-Order Abstract Syntax Representations: Part 2–A Survey. JAR 2015
 *)
Lemma memb_uniq : forall (Phi_t:list atm) (e:eexp) (t t':tp),
  xtG Phi_t ->
  In (oft e t) Phi_t -> In (oft e t') Phi_t ->
   (exists v:var, e = Var v) /\ t = t'.
Proof.
  intros Phi_t e t t'; induction 1; try (simpl; tauto).
  simpl; intros h1 h2; destruct h1 as [h1 | h1]; destruct h2 as [h2 | h2].
  - injection h1; injection h2; intros; subst; subst; simpl; split; auto.
    exists (nvC Phi_t); auto.
  - injection h1; intros; subst; subst.
    specialize fresh_nvC with (1:=h2); tauto.
  - injection h2; intros; subst; subst.
    specialize fresh_nvC with (1:=h1); tauto.
  - auto.
Qed.

End ctx_uniq.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

#[global] Hint Resolve nil_t cons_t : hybrid.

Section uniq.

Lemma uniq : forall (i:nat) (Phi_t:list atm) (M:eexp) (A:tp),
  xtG Phi_t ->
  seq_ i Phi_t (atom_ (oft M A)) ->
  forall (k:nat) (B:tp), seq_ k Phi_t (atom_ (oft M B)) -> A = B.
Proof.
  intros i Phi_t M A h1 h2 k B h3.
  generalize
  (lt_wf_ind i
      (fun i:nat =>
      forall (Phi_t:list atm) (M:eexp) (A:tp),
      xtG Phi_t ->
      seq_ i Phi_t (atom_ (oft M A)) ->
      forall (k:nat) (B:tp), seq_ k Phi_t (atom_ (oft M B)) -> A = B)).
  intro H'.
  apply H' with Phi_t M k; clear H'; auto.
  clear h1 h2 h3 i Phi_t M A B k.
  intros i hInd Phi_t M A hCInv h1 k B h2.
  inversion h1; subst.
  - inversion H0; subst; clear H0.
    (* str case *)
    + inversion h2; subst; clear h2.
      * inversion H0. auto.
      * inversion H2. subst. clear H2.
      Admitted.
      (* inversion H0. auto.
    + inversion H3; subst; clear H3.
      inversion h2; subst; clear h2.
      * inversion H0; subst; clear H0.
        auto.
      * inversion H2. subst. clear H2.
        inversion h1. subst. absurd (In (oft (lam A0 (fun x:eexp => M0 x)) B) (A'::L)); eauto with hybrid.
    (* app case *)
    + inversion H3; subst; clear H3.
      inversion h2; subst; clear h2.
      * inversion H0; subst; clear H0.
        inversion H3; subst; clear H3.
        assert (h2: i < i+1+1); try lia.
        generalize (hInd i h2 Phi_t M0 (arr B0 A) hCInv H4 i1 (arr B1 B) H6);
          intro h4.
        inversion h4; auto.
      * absurd (In (oft (app M0 N) B) (A'::L)); eauto with hybrid.
  - (* context case *)
    generalize hCInv; intro h'.
    inversion h'; subst.
    specialize memb_uniq with (1:=hCInv) (2:=H2) (3:=H2);
      intros [[v h3] h4]; clear h4; subst.
    inversion h2; subst; clear h2.
    + inversion H1.
    + specialize memb_uniq with (1:=hCInv) (2:=H2) (3:=H3);
        intros [h3 h4]; subst; auto.
Qed. *)

Lemma uniq_cor: forall (M:eexp) (A B:tp),
  seq0 (atom_ (oft M A)) -> seq0 (atom_ (oft M B)) -> (A=B).
Proof.
  intros M A B h1 h2.
  unfold seq0 in h1; elim h1; clear h1; intros i h1.
  unfold seq0 in h2; elim h2; clear h2; intros k h2.
  apply uniq with i (nil:list atm) M k; eauto with hybrid.
Qed.

End uniq.
