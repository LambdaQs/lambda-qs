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
