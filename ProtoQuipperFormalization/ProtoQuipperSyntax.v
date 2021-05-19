(****************************************************************
   File: ProtoQuipperSyntax.v
   Authors: Mohamed Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9

   The synatx of ProtoQuipper, a quantum lambda calculus
   programming language.
  ***************************************************************)

Require Export Hybrid.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import FunInd.
Require Import Lia.
Import ListNotations.


Inductive Econ: Set := qABS: Econ | qAPP: Econ | qPROD : Econ
	|qLET:Econ |sLET:Econ| qCIRC:Econ | qIF:Econ
	|BOX:qtp->Econ|UNBOX:Econ|REV:Econ
        |TRUE:Econ|FALSE:Econ|STAR:Econ|
         Qvar:nat->Econ|Crcons:nat->Econ.

Definition qexp : Set := expr Econ.

(****************************************************************
  Lemmas about contexts of elements of type qexp
  (could be moved to a general library about lists and sets of
   any type)
  ****************************************************************)

Theorem eq_dec: forall x y:qexp, {x=y}+{x<>y}.
Proof.
decide equality; decide equality; decide equality.
Qed.

Theorem set_add_new: forall a x,
    ~In a x -> set_add eq_dec a x = x++[a].
Proof.
  intros. induction x.
  - simpl. auto.
  - apply not_in_cons in H. inversion H.
    apply IHx in H1. simpl.
    case (eq_dec a a0).
    + intros. contradict H0.  auto.
    + rewrite H1. auto.
Qed.

Theorem add_ident: forall x a,
    In a x -> set_add eq_dec a x =  x.
Proof.
  intros.  induction x.
  - inversion H.
  - inversion H.
    + subst.
      unfold set_add. case(eq_dec a a); auto.
      intros. contradict n. auto.
    + apply IHx in H0.
      unfold set_add.
      case (eq_dec a a0); auto.
      intros. unfold set_add in H0.  rewrite H0. auto.
Qed.

Theorem union_empty: forall (x:set qexp),
    NoDup x ->
    set_union eq_dec [] x  = List.rev x.
Proof.
  intros. induction x.
  - simpl.  auto.
  - rewrite NoDup_cons_iff in H.
    inversion H.  simpl. apply IHx in H1.
    rewrite in_rev in H0.
    apply set_add_new in H0.
    rewrite H1,H0. auto.
Qed.

Fixpoint add_list (a:set qexp) (x:set qexp) :set qexp :=
    match a with
    | nil => x
    | a1 :: x1 =>
        match in_dec eq_dec a1 x with
        | left _ => add_list x1 x
        | right _ => add_list x1 x++[a1]
        end
    end.

Functional Scheme add_list_ind := Induction for add_list Sort Prop.

Theorem union_eq: forall x y,
    NoDup y ->
    set_union eq_dec x y = add_list y x.
Proof.
intros. functional induction add_list y x.
- simpl. auto.
- simpl.  assert(_x':=_x).
  apply set_union_intro1 with (Aeq_dec:=eq_dec)
                              (y:=x1) in _x'.
  apply add_ident in _x'.
  rewrite _x'.
  rewrite NoDup_cons_iff in H. inversion H.
  auto.
- simpl. rewrite NoDup_cons_iff in H. inversion H.
  assert(~ set_In a1 (set_union eq_dec x x1)).
  { contradict H0. apply set_union_elim in H0.
    destruct H0; auto.
    assert(_x':=_x). contradict _x'.  auto. }
  apply set_add_new in H2. rewrite H2.
  apply IHs in H1. rewrite H1. auto.
Qed.

Theorem union_same: forall (x y:set qexp),
    NoDup y -> (forall a, In a  y -> In a x) ->
    add_list y x = x.
intros. functional induction add_list y x; auto.
- rewrite NoDup_cons_iff in H. inversion H.
  apply IHs;auto. intros.
  apply H0. apply in_cons. auto.
- assert(In a1 (a1::x1)); try apply in_eq.
  apply H0 in H1. contradict H1. auto.
Qed.

Theorem union_same_alt: forall (x y:set qexp),
    NoDup y -> (forall a, In a  y -> In a x) ->
    set_union eq_dec x y= x.
Proof.
  intros. assert(h:=H). apply union_eq with (x:=x) in H.
  rewrite H. apply union_same;auto.
Qed.

Lemma set_add_iff a b l : In a (set_add eq_dec b l) <-> a = b \/ In a l.
  Proof.
  split. apply set_add_elim. apply set_add_intro.
  Qed.

Lemma set_add_nodup a l : NoDup l -> NoDup (set_add eq_dec  a l).
  Proof.
   induction 1 as [|x l H H' IH]; simpl.
   - constructor; [ tauto | constructor ].
   - destruct (eq_dec  a x) as [<-|Hax]; constructor; trivial.
     rewrite set_add_iff. intuition.
  Qed.

Lemma set_union_nodup l l':
    NoDup l -> NoDup l' ->
    NoDup (set_union eq_dec l l').
Proof.
  induction 2 as [|x' l' ? ? IH]; simpl; trivial.
  now apply set_add_nodup.
Qed.

Theorem nodup_app: forall (l :list qexp),
    NoDup l -> forall l1 a, l = l1++[a] -> NoDup (a::l1).
Proof.
  intros l H. induction H.
  - intros. symmetry in H. apply app_eq_nil in H.
    inversion H. inversion H1.
  - intros. destruct l1.
    + apply NoDup_cons.
      * apply in_nil.
      * apply NoDup_nil.
    + simpl in H1. inversion H1.
      assert(h4:=H4). apply IHNoDup in H4.
      rewrite NoDup_cons_iff in H4. inversion H4.
      repeat apply NoDup_cons; auto.
      * rewrite <- H3. contradict H.
        rewrite h4. inversion H.
        { rewrite H6. apply in_or_app. right. apply in_eq. }
        { contradict H2. auto. }
      * rewrite <- H3.
        contradict H. rewrite h4.
        apply in_or_app. left. auto.
Qed.

Theorem nodup_app2: forall (l :list qexp),
    NoDup l -> forall a, ~ In a l -> NoDup (l++[a]).
Proof.
  intros l H. induction H.
  - intros. simpl. apply NoDup_cons.
    + apply in_nil.
    + apply NoDup_nil.
  - intros. simpl.  apply NoDup_cons.
    + contradict H1. apply in_app_or in H1.
      destruct H1.
      * contradict H. auto.
      * inversion H1.
        { rewrite H2. apply in_eq. }
        { inversion H2. }
    + apply IHNoDup. contradict H1. apply in_cons.
      auto.
Qed.

Theorem nodup_rev: forall (l:list qexp),
    NoDup l -> NoDup (List.rev l).
Proof.
  intros.  induction H.
  - simpl. apply NoDup_nil.
  - simpl.  apply nodup_app2;auto.
    rewrite <- in_rev. auto.
Qed.

Theorem nodup_union: forall s1 s2,
    NoDup s1 -> NoDup s2 -> (forall a, In a s2 -> ~ In a s1) ->
    set_union eq_dec s1 s2 = s1++ (rev s2).
Proof.
  intros. apply union_eq with (x:=s1) in H0.
  rewrite H0. clear H0.  functional induction add_list s2 s1.
  - simpl. rewrite app_nil_r. auto.
  - assert(In a1 (a1::x1));try apply in_eq.
    apply H1 in H0.  contradict H0. auto.
  - simpl. rewrite IHs,app_assoc; auto.
    intros.  apply H1.  apply in_cons. auto.
Qed.

(****************************************************************
  Syntax definitions continued
  ****************************************************************)

Definition Var : var -> qexp := VAR Econ.
Definition Bnd : bnd -> qexp := BND Econ.
Definition App (e1 e2:qexp) : qexp := APP (APP (CON qAPP) e1) e2.
Definition Fun (f:qexp -> qexp) : qexp := APP (CON qABS) (lambda f).
Definition Prod (e1 e2:qexp) : qexp := APP (APP (CON qPROD) e1) e2.
Definition Let (f:qexp -> qexp-> qexp) (e1:qexp) : qexp :=
  APP (CON qLET)  (APP (lambda (fun x=> (lambda (f x)))) e1).
Definition Slet (e1 e2:qexp) : qexp := APP (APP (CON sLET) e1) e2.
Definition If (e1 e2 e3:qexp) : qexp := APP (APP (APP (CON qIF) e1) e2) e3.
Definition Circ (e1:qexp) (i:nat) (e2:qexp) : qexp :=
  APP (APP (APP (CON qCIRC) e1) (CON (Crcons i))) e2.
Definition Box (f:qexp->qexp) (T:qtp) : qexp :=
  APP (CON (BOX T)) (lambda f).
Definition Unbox (e1:qexp) : qexp := APP (CON UNBOX) e1.
Definition Rev (e1:qexp) : qexp := APP (CON REV) e1.

Theorem proper_CON: forall c:Econ, proper (CON c).
Proof.
apply level_CON; try apply proper_CON.
Qed.

Inductive quantum_data :qexp -> Prop :=
vQVAR: forall i,  quantum_data (CON (Qvar i))
|vSTAR:  quantum_data (CON STAR)
|vTENSOr: forall a b,  quantum_data  a ->  quantum_data b ->
   quantum_data (Prod a b).

Theorem quantum_data_proper: forall t,
quantum_data t -> proper t.
Proof.
intros. induction H.
unfold proper;  apply level_CON.
unfold proper;  apply level_CON.
unfold Prod. repeat apply proper_APP;auto.
unfold proper;  apply level_CON.
Qed.

(* No longer needed

Inductive validqexp : qexp -> Prop:=
VVar : forall v, validqexp (Var v)
|VQar: forall i, validqexp (CON (Qvar i))
|VRev: validqexp (CON REV)
|VUnbox: validqexp (CON UNBOX)
|VBox: validqexp (CON BOX)
|VTrue: validqexp (CON TRUE)
|VFalse: validqexp (CON FALSE)
|VStart: validqexp (CON STAR)
|VApp : forall e1 e2, validqexp e1 ->  validqexp e2 ->
   validqexp (App e1 e2)
|VFun: forall f, abstr f -> (forall v, validqexp (f (Var v))) -> validqexp (Fun f)
|VProd: forall e1 e2, validqexp e1 ->  validqexp e2 ->
   validqexp (Prod e1 e2)
|VLet: forall f e, validqexp (lambda (fun x=> (lambda (f x))))
  -> validqexp e -> validqexp (Let f e)
|VSlet: forall e1 e2, validqexp e1 ->  validqexp e2 ->
   validqexp (Slet e1 e2)
|VIf: forall e1 e2 e3, validqexp e1 ->  validqexp e2 -> validqexp e3 ->
   validqexp (If e1 e2 e3)
|VCirc: forall e1 e2 i, validqexp e1 ->  validqexp e2 ->
   validqexp (Circ e1 i e2).

Inductive tvalidqexp : qexp -> Prop:=
tVVar : forall v, tvalidqexp (Var v)
|tVQar: forall i, tvalidqexp (CON (Qvar i))
|tVRev: tvalidqexp (CON REV)
|tVUnbox: tvalidqexp (CON UNBOX)
|tVBox: tvalidqexp (CON BOX)
|tVTrue: tvalidqexp (CON TRUE)
|tVFalse: tvalidqexp (CON FALSE)
|tVStart: tvalidqexp (CON STAR)
|tVApp : forall e1 e2, tvalidqexp e1 ->  tvalidqexp e2 ->
   tvalidqexp (App e1 e2)
|tVFun: forall f, abstr f -> (forall x, proper x -> validqexp x -> tvalidqexp (f x)) -> tvalidqexp (Fun f)
|tVProd: forall e1 e2, tvalidqexp e1 ->  tvalidqexp e2 ->
   tvalidqexp (Prod e1 e2)
|tVLet: forall f e, tvalidqexp (lambda (fun x=> (lambda (f x))))
  -> tvalidqexp e -> tvalidqexp (Let f e)
|tVSlet: forall e1 e2, tvalidqexp e1 ->  tvalidqexp e2 ->
   tvalidqexp (Slet e1 e2)
|tVIf: forall e1 e2 e3, tvalidqexp e1 -> tvalidqexp e2 -> tvalidqexp e3 ->
   tvalidqexp (If e1 e2 e3)
|tVCirc: forall e1 e2 i, tvalidqexp e1 ->  tvalidqexp e2 ->
   tvalidqexp (Circ e1 i e2).*)

Fixpoint FV (e:qexp) :set qexp :=
match e with
VAR _ x => [VAR  Econ x]
|(APP (APP (CON qPROD) e1) e2) => set_union eq_dec (FV e1) (FV e2)
|(APP (APP (CON qAPP) e1) e2)  => set_union eq_dec (FV e1) (FV e2)
|APP (CON qABS) (ABS e)    => FV e
|(APP (APP (APP (CON qIF) e1) e2) e3) => set_union eq_dec (FV e3) (set_union eq_dec (FV e1) (FV e2))
|(APP (APP (CON sLET)  e1) e2) => set_union eq_dec (FV e1) (FV e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) =>
  set_union eq_dec (FV e1) (FV e2)
|(APP (APP (APP (CON qCIRC) e1) (CON (Crcons i))) e2) => FV e2
|_ => []
end.

Fixpoint FQ (e:qexp) :set qexp :=
match e with
CON (Qvar x) => [CON  (Qvar x)]
|(APP (APP (CON qPROD) e1) e2) => set_union eq_dec (FQ e1) (FQ e2)
|(APP (APP (CON qAPP) e1) e2)  => set_union eq_dec (FQ e1) (FQ e2)
|APP (CON qABS) (ABS e)    => FQ e
|(APP (APP (APP (CON qIF) e1) e2) e3) => set_union eq_dec (FQ e3) (set_union eq_dec (FQ e1) (FQ e2))
|(APP (APP (CON sLET)  e1) e2) => set_union eq_dec (FQ e1) (FQ e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) =>
  set_union eq_dec (FQ e1) (FQ e2)
|_ => []
end.

Functional Scheme FQ_ind := Induction for FQ Sort Prop.

(* TODO: change QV to use the following relational version.

Definition QV: nat -> qexp := fun i:nat => (CON (Qvar i)).

Fixpoint FQ (e:qexp) :set qexp :=
  match e with
    (QV i) => [CON  (Qvar x)]
  | (Prod e1 e2) => set_union eq_dec (FQ e1) (FQ e2)
  | (App e1 e2) => set_union eq_dec (FQ e1) (FQ e2)
  | (Fun f) => FQ (f (Var 0))
  | (If e1 e2 e3) => set_union eq_dec (FQ e3) (set_union eq_dec (FQ e1) (FQ e2))
  | (Slet e1 e2) => set_union eq_dec (FQ e1) (FQ e2)
  | (Let f e) =>  set_union eq_dec (FQ (f (Var 0) (Var 0))) (FQ e2)
  | _ => []
end.

Inductive FQ : qexp -> set qexp -> Prop :=
| FQ_QV : forall x, FQ (QV x) [CON  (Qvar x)]
| FQ_Prod : forall (e1 e2:qexp) (vs1 vs2:set qexp),
    FQ e1 vs1 -> FQ e2 vs2 -> FQ (Prod e1 e2) (set_union eq_dec vs1 vs2)
| FQ_App : forall (e1 e2:qexp) (vs1 vs2:set qexp),
    FQ e1 vs1 -> FQ e2 vs2 -> FQ (App e1 e2) (set_union eq_dec vs1 vs2)
| FQ_Fun : forall (f:qexp -> qexp) (vs:set qexp),
    FQ (f (Var 0)) vs -> FQ (Fun f) vs
| FQ_If : forall (e1 e2 e3:qexp) (vs1 vs2 vs3:set qexp),
    FQ e1 vs1 -> FQ e2 vs2 -> FQ e3 vs3 ->
    FQ (If e1 e2 e3) (set_union eq_dec vs3 (set_union eq_dec vs1 vs2))
| FQ_Slet : forall (e1 e2:qexp) (vs1 vs2:set qexp),
    FQ e1 vs1 -> FQ e2 vs2 -> FQ (Slet e1 e2) (set_union eq_dec vs1 vs2)
| FQ_Let : forall (f:qexp -> qexp -> qexp) (e:qexp) (vs1 vs2:set qexp),
    FQ (f (Var 0) (Var 0)) vs1 -> FQ e vs2 ->
    FQ (Let f e) (set_union eq_dec vs1 vs2). *)

Theorem fq_all_qvar: forall a,
  (forall a0, In a0 (FQ a) -> exists x, a0 = CON  (Qvar x)).
Proof.
intros a a0 H.
functional induction FQ a; try inversion H; try inversion H;
  try inversion H0;
  subst; try exists x; auto; apply set_union_elim in H;
  destruct H; try apply IHs in H; try apply IHs0 in H; auto.
apply set_union_elim in H;
  destruct H; try apply IHs0 in H;
    try apply IHs1 in H; auto.
Qed.

Theorem fq_nodup: forall a, NoDup (FQ a).
Proof.
  intros. functional induction FQ a; try apply NoDup_nil;
            try apply set_union_nodup;auto.
  - apply NoDup_cons.
    + apply in_nil.
    + apply NoDup_nil.
  - apply set_union_nodup;auto.
Qed.

Theorem nodup_fq2: forall v, NoDup (FQ v).
  intros. functional induction FQ v; intros;
            simpl;try apply NoDup_nil; try apply set_union_nodup;auto.
 apply  NoDup_cons. auto. apply  NoDup_nil.
 apply set_union_nodup;auto.
Qed.

Inductive is_value :qexp->Prop :=
Varv: forall x, is_value (Var x)
|Qvarv: forall x, is_value (CON (Qvar x))
|Circv: forall a t i, quantum_data t -> quantum_data a -> is_value (Circ t i a)
|Truev: is_value (CON TRUE)
|Falsev: is_value (CON FALSE)
|Starv: is_value (CON STAR)
|Boxv: forall T, valid T -> is_value (CON (BOX T))
|Unboxv: is_value (CON UNBOX)
|Revv: is_value (CON REV)
|Funvv: forall f, abstr f -> is_value (Fun f)
|Prodv: forall v w, is_value v -> is_value w -> is_value (Prod v w)
|Unboxappv: forall v, is_value v -> is_value (App (CON UNBOX) v).

Theorem value_proper: forall v, is_value v -> proper v.
Proof.
intros.  induction H;try apply  proper_CON.
apply proper_VAR.
unfold Circ. repeat apply proper_APP;
try apply  proper_CON;apply quantum_data_proper;auto.
unfold Fun. apply proper_APP;
try apply  proper_CON;apply  abstr_proper;auto.
unfold Prod. repeat apply proper_APP;
try apply  proper_CON;auto.
repeat apply proper_APP;
try apply  proper_CON;auto.
Qed.

Inductive bind :qexp->qexp->Prop :=
|star_bind: bind (CON STAR) (CON STAR)
|qvar_bind: forall i j, bind (CON (Qvar i)) (CON (Qvar j))
|tensor_bind:forall a1 a2 b1 b2, bind a1 b1 ->  bind a2 b2->
bind (Prod a1 a2) (Prod b1 b2).

Theorem quantum_data_bind:forall a b,
bind a b -> quantum_data a /\ quantum_data b.
intros a b H. induction H. split;apply vSTAR.
split;apply vQVAR.
inversion IHbind1. inversion IHbind2.
split; apply vTENSOr;auto.
Qed.

Fixpoint qtyper (v:qexp) :qtp :=
match v with
|CON STAR => one
|CON (Qvar _) => qubit
|(APP (APP (CON qPROD) e1) e2) => tensor (qtyper e1) (qtyper e2)
| _ => one
end.
Functional Scheme qtyper_ind := Induction for qtyper Sort Prop.

Theorem valid_qtyper: forall v, valid (qtyper v).
intros. apply  qtyper_ind; intros;try apply One.
apply Qubit. apply Tensor;auto.
Qed.

Theorem qtyper_bind: forall a b, bind a b ->  qtyper a  = qtyper b.
intros a b H. induction H;simpl;auto.
rewrite IHbind1,IHbind2. auto.
Qed.
(*match u with
CON (Qvar  x) =>
 match v with
 CON (Qvar  y) => [(CON (Qvar  x),CON (Qvar  y))]
 | _ => []
 end
|(APP (APP (CON qPROD) e1) e2) =>
 match v with
 (APP (APP (CON qPROD) e3) e4) =>
    (bind e1 e3) ++ (bind e2 e4)
  | _  => []
  end
| _ => []
end.*)

Fixpoint FQU (e:qexp) :set qexp :=
match e with
CON (Qvar x) => [CON  (Qvar x)]
|(APP (APP (CON qPROD) e1) e2) =>  (FQU e1) ++(FQU e2)
|(APP (APP (CON qAPP) e1) e2)  => (FQU e1) ++(FQU e2)
|APP (CON qABS) (ABS e)    => FQU e
|(APP (APP (APP (CON qIF) e1) e2) e3) => (FQU e1) ++(FQU e2)++(FQU e3)
|(APP (APP (CON sLET)  e1) e2) => (FQU e1) ++(FQU e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) =>
  (FQU e1) ++(FQU e2)
|_ => []
end.
Functional Scheme FQU_ind := Induction for FQU Sort Prop.

Fixpoint find (l:list (qexp*qexp)) (a:qexp) :qexp:=
   match l with
        | nil => a
        | x :: tl => if eq_dec (fst x) a then snd x else find tl a
      end.

Fixpoint binder (bl:list (qexp*qexp)) (a:qexp) :qexp :=
match a with
CON (Qvar  x) =>  find bl (CON (Qvar  x))
| APP e1 e2 => APP (binder bl e1) (binder bl e2)
| ABS e => ABS (binder bl e)
| y => y
end.

Fixpoint newqvar (e:qexp): nat :=
match e with
CON (Qvar x) => x+1
|(APP (APP (CON qPROD) e1) e2) => max (newqvar e1) (newqvar e2)
|(APP (APP (CON qAPP) e1) e2)  => max (newqvar e1) (newqvar e2)
|APP (CON qABS) (ABS e)    => (newqvar e)
|(APP (APP (APP (CON qIF) e1) e2) e3) => max (max (newqvar e1) (newqvar e2)) (newqvar e3)
|(APP (APP (CON sLET)  e1) e2) => max (newqvar e1) (newqvar e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) =>
  max (newqvar e1) (newqvar e2)
|_ => 0
(*match e with
  CON (Qvar x) => x+1
| APP e1 e2 => max (newqvar e1) (newqvar e2)
| ABS e' => newqvar e'
| _ => 0*)
end.

Fixpoint Spec (v:nat) (T:qtp) :qexp :=
match T with
|qubit => CON (Qvar v)
|tensor t1 t2 => Prod (Spec v t1) (Spec (max v (newqvar (Spec v t1))) t2)
| _ => CON STAR
end.

Functional Scheme Spec_ind := Induction for Spec Sort Prop.

Theorem Spec_quantum_data: forall v T, quantum_data (Spec (newqvar v) T).
Proof.
intros. apply Spec_ind; intros;try apply vSTAR.
apply vQVAR.
apply vTENSOr;auto.
Qed.

Theorem nodup_fq: forall v t, NoDup (FQ(Spec v t)).
Proof.
  intros. functional induction Spec v t; intros;
            simpl;try apply NoDup_nil.
  apply NoDup_cons; auto.
  - apply  NoDup_nil.
  - apply set_union_nodup;auto.
 Qed.

Functional Scheme newqvar_ind := Induction for newqvar Sort Prop.

Lemma spec_gt:forall q1 v,
    In (CON (Qvar q1)) (FQ v) -> q1 < newqvar v.
Proof.
  intros.
  functional induction newqvar v;simpl in H ; try inversion H; auto.
  - inversion H0.  lia.
  - contradict H0.
  - rewrite set_union_iff in H. destruct H.
    + destruct (le_ge_dec  (newqvar e9) (newqvar e7)).
      * assert(l':=l). apply max_r in l.  rewrite l.
        apply IHn in H. lia.
      * apply max_l in g. rewrite g. auto.
    + destruct (le_ge_dec  (newqvar e9) (newqvar e7)); auto.
      * assert(l':=l). apply max_r in l.  rewrite l. auto.
      * assert(g':=g).
        apply max_l in g. rewrite g. apply IHn0 in H. lia.
  - rewrite set_union_iff in H. destruct H.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l.
        apply IHn in H. lia.
      * apply max_l in g. rewrite g.
        auto.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)); auto.
      * assert(l':=l). apply max_r in l.  rewrite l.
        auto.
      * assert(g':=g). apply max_l in g. rewrite g. apply IHn0 in H. lia.
  - rewrite set_union_iff in H. destruct H.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l.
        apply IHn in H. lia.
      * apply max_l in g. rewrite g. auto.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l.
        auto.
      * assert(g':=g).
        apply max_l in g. rewrite g. apply IHn0 in H. lia.
  - rewrite set_union_iff in H. destruct H.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l.
        apply IHn in H. lia.
      * apply max_l in g. rewrite g.
        auto.
    + destruct (le_ge_dec  (newqvar e3) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l. auto.
      * assert(g':=g). apply max_l in g. rewrite g. apply IHn0 in H. lia.
  - repeat rewrite set_union_iff in H. destruct H.
    + destruct (le_ge_dec (Nat.max (newqvar e7) (newqvar e3)) (newqvar e2)).
      * assert(l':=l). apply max_r in l.  rewrite l. auto.
      * assert(g':=g). apply max_l in g. rewrite g. apply IHn1 in H. lia.
    + destruct H.
      * destruct (le_ge_dec  (newqvar e7) (newqvar e3)).
        { assert(l':=l).
          apply max_r in l. rewrite l.
          destruct (le_ge_dec (newqvar e3) (newqvar e2)).
          { assert(l0':=l0). apply max_r in l0. rewrite l0.
            apply IHn in H. lia. }
          { apply max_l in g. rewrite g.
            apply IHn in H. lia. }}
        { assert(g':=g).
          apply max_l in g. rewrite g.
          destruct (le_ge_dec (newqvar e7) (newqvar e2)).
          { assert(l':=l).
            apply max_r in l. rewrite l.
            apply IHn in H. lia. }
          { apply max_l in g0. rewrite g0.
            apply IHn in H. lia. }}
      * destruct (le_ge_dec (newqvar e7) (newqvar e3)).
        { assert(l':=l).
          apply max_r in l. rewrite l.
          destruct (le_ge_dec (newqvar e3) (newqvar e2)).
          { assert(l0':=l0). apply max_r in l0. rewrite l0.
            apply IHn0 in H. lia. }
          { apply max_l in g. rewrite g.
            apply IHn0 in H. lia. }}
        { assert(g':=g).
          apply max_l in g. rewrite g.
          destruct (le_ge_dec (newqvar e7) (newqvar e2)).
          { assert(l':=l).
            apply max_r in l. rewrite l.
            apply IHn0 in H. lia. }
          { apply max_l in g0. rewrite g0.
            apply IHn0 in H. lia. }}
Qed.

Theorem spec_gt2: forall q v t,
    In (CON (Qvar q)) (FQ (Spec v t)) -> v <= q.
Proof.
  intros. functional induction Spec v t;simpl in *.
  - destruct H.
    + inversion H.
      lia.
    + contradict H.
  - contradict H.
  - contradict H.
  - rewrite set_union_iff in H. destruct H; auto.
    apply IHq2 in H.
    destruct (le_ge_dec v (newqvar (Spec v t1))).
    + assert(l':=l). apply max_r in l. rewrite l in H. lia.
    + apply max_l in g.  rewrite g in H. auto.
  - contradict H.
  - contradict H.
  - contradict H.
Qed.

Theorem disjoint_fq: forall v t1, forall a,
      In a (FQ v) -> ~ In a (FQ (Spec (newqvar v) t1)).
Proof.
  intros. induction t1;simpl;auto.
  - assert(h:=H). apply fq_all_qvar in H. inversion H.
    subst. apply spec_gt in h.
    apply and_not_or. split;auto.
    destruct (eq_dec (CON (Qvar (newqvar v))) (CON (Qvar x))); auto.
    inversion e. lia.
  - rewrite set_union_iff. apply and_not_or.
    split; auto.
    destruct (In_dec eq_dec a
                     (FQ (Spec (Nat.max (newqvar v)
                                        (newqvar (Spec (newqvar v) t1_1)))
                               t1_2))).
    + assert(i':=i).
      apply fq_all_qvar in i.
      inversion i. subst. apply spec_gt2 in i'.
      apply spec_gt in H.
      destruct (le_ge_dec (newqvar v) (newqvar (Spec (newqvar v) t1_1))).
      * assert(l':=l). apply max_r in l.
        rewrite l in i'. lia.
      * apply max_l in g.  rewrite g in i'.  lia.
    + auto.
Qed.
