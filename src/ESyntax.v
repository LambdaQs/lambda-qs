From HybridSys Require Export Hybrid.
From HybridSys Require Export sl.
Require Import Strings.String.
Require Import ETypes.

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
  APP (CON eLET) (APP e1 (lambda (fun x => f x))).

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
  abstr f -> proper (Let e1 (fun x => f x)).
Proof.
  unfold Let.
  Abort.
   (* auto with hybrid.
Qed. *)

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)
Inductive atm : Set :=
| oft  : eexp -> tp -> atm (* e : τ *)
| term : eexp -> atm (* is_exp *)
.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

Inductive prog : atm -> oo_ -> Prop :=
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
