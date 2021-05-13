(****************************************************************
   File: ProtoQuipperProg.v
   Authors: Mohamed Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9

   Various lemmas, instantiation of atm with the basic judgments for
   Proto Quipper (which currently include well-formed terms, typing,
   and evaluation), and instantiation of prog with the inference rules
   for these judgments.
   ***************************************************************)

Require Export LSL.
Require Export ProtoQuipperSyntax.
Require Export ProtoQuipperTypes.
Require Export Coq.Lists.List.
Require Export Coq.Lists.ListSet.
Require Import FunInd.
Import ListNotations.

Section Prog.

Set Implicit Arguments.

(****************************************************************
  Some useful tactics
  ****************************************************************)

Ltac apply2 thL h1 h2 :=
  try apply thL in h1; try apply thL in h2.

Ltac destruct_conj :=
  match goal with
    | [ H : ?A/\?B |- _ ] => inversion H;clear H; destruct_conj
    | _ => idtac
  end.

Ltac rexists :=
  match goal with
    | [H:exists _, _ |-_] => inversion H; clear H;rexists
    |_ => idtac end.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

(* The atomic predicates that encode typing, well-formedness, and
   reduction and serve as a parameter to the specification logic *)
Inductive atm : Set :=
| typeof : qexp -> qtp -> atm
| is_qexp : qexp -> atm
| reduct: Econ -> qexp -> Econ -> qexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

(****************************************************************
  Operations and properties about atomic predicates and contexts.
  ****************************************************************)

Definition atmtype (a:atm) :qtp :=
  match a with
      typeof _ t => t
    | _ => one
  end.

Definition atmexp (a:atm) :qexp :=
  match a with
      typeof e _ => e
    | _ => CON STAR
  end.

Inductive vlcontext  :list atm -> Prop :=
  vlc_init: vlcontext []
| vlc_general: forall a t ll, validT(bang t) -> vlcontext ll ->
                              vlcontext (typeof a t::ll).

Inductive vicontext  :list atm -> Prop :=
  vic_init: vicontext []
| vic_general: forall a ll,
                 (exists c, atmtype a = bang c /\  validT (atmtype a)) ->
                 vicontext ll -> vicontext (a::ll).

Theorem In_vic: forall a IL, In a IL -> vicontext IL ->
  (exists c, atmtype a = bang c /\ validT (atmtype a)).
Proof.
intros a IL H H0. induction H0.
- contradiction in_nil with atm a.
- destruct H;auto. subst;auto.
Qed.

Theorem In_vlc: forall a t IL, In (typeof a t) IL -> vlcontext IL ->
  validT (bang t).
Proof.
intros a t IL H H0. induction H0.
- inversion H.
- destruct H;auto. injection H. intros. subst;auto.
Qed.

(* Assigns the type qubit to all quantum variables in the input list,
   returning a context of typed variables *)
Fixpoint toqlist (fq:set qexp) : list atm :=
  match fq with
    | [] => []
    | h::t =>
      match h with
        | CON (Qvar x) => (typeof (CON (Qvar x)) qubit)::toqlist t
        | _ => toqlist t
      end
  end.

(* Forms a context quantum variables for the well-formedness judgment *)
Fixpoint toiqlist (fq:set qexp) : list atm :=
  match fq with
    | [] => []
    | h::t =>
      match h with
        | CON (Qvar x) => (is_qexp (CON (Qvar x)))::toiqlist t
        | _ => toiqlist t
      end
  end.

Functional Scheme toqlist_ind := Induction for toqlist Sort Prop.

Functional Scheme toiqlist_ind := Induction for toiqlist Sort Prop.

(* Maps a set of quantum variables and a formula to an implication
   with the formula on the right, and well-formedness and typing
   assumptions about all of the quantum variables on the left *)
Fixpoint toimp (fq:set qexp) (form:oo_) : oo_ :=
  match fq with
    | [] => form
    | h::t =>
      match h with
        | CON (Qvar x) =>
          Imp (is_qexp (CON (Qvar x)))
              (lImp (typeof (CON (Qvar x)) qubit) (toimp t form))
        | _ => toimp t form
      end
  end.

(* Similar to above, but only well-formedness assumptions included *)
Fixpoint toimpexp (fq:set qexp) (term:oo_) :oo_ :=
  match fq with
    | [] => term
    | h::t =>
      match h with
        | CON (Qvar x) => Imp (is_qexp (CON (Qvar x))) (toimpexp t term)
        | _ => toimp t term
      end
  end.

Theorem toqlist_app: forall l1 l2,
  toqlist (l1++l2)= toqlist l1 ++ toqlist l2.
Proof.
intros l1 l2; functional induction toqlist l1;
try rewrite <- app_comm_cons; simpl; auto.
rewrite <- IHl. auto.
Qed.

Theorem toiqlist_app: forall l1 l2,
  toiqlist (l1++l2)= toiqlist l1 ++ toiqlist l2.
Proof.
intros l1 l2; functional induction toiqlist l1;
try rewrite <- app_comm_cons; simpl; auto.
rewrite <- IHl. auto.
Qed.

Theorem rev_toqlist: forall fq,
  rev (toqlist fq) = toqlist (rev fq).
Proof.
intros fq; functional induction toqlist fq; simpl;
try rewrite toqlist_app; simpl; try rewrite app_nil_r; auto.
rewrite IHl. auto.
Qed.

Theorem rev_toiqlist: forall fq,
  rev (toiqlist fq) = toiqlist (rev fq).
Proof.
intros fq; functional induction toiqlist fq; simpl;
try rewrite toiqlist_app; simpl; try rewrite app_nil_r; auto.
rewrite IHl. auto.
Qed.

Theorem move_to_ll: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i IL LL (toimp fq form) ->
    LSL.seq prog (i-length fq-length fq) (rev (toiqlist fq)++IL)
            (rev (toqlist fq)++LL) form.
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl toimp in H0. simpl length.
  simpl toqlist. simpl toiqlist.
  repeat rewrite app_nil_l. assert (i-0-0 = i); try lia. rewrite  H1. auto.
- intros form i IL LL prog H0.
  specialize in_eq with (a:=a) (l:=fq). intro H1. apply H in H1.
  inversion H1.  subst. simpl toqlist. simpl toqlist. simpl rev.
  repeat rewrite <- app_assoc.
  simpl length. assert (forall n, i - S n - S n = i - 2 - n -  n).
  { intros. lia. }
  rewrite H2.  apply IHfq.
  + intros a H3. apply in_cons with (a:= CON (Qvar x)) in H3. auto.
  + simpl in H0. inversion H0. inversion H7.
    assert (i1+1+1-2 = i1); try lia.
    rewrite H15. auto.
Qed.

Theorem move_to_il: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i IL LL (toimpexp fq form) ->
    LSL.seq prog (i-length fq) (rev (toiqlist fq)++IL) LL form.
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl toimpexp in H0. simpl length.
  simpl toqlist. simpl toiqlist.
  repeat rewrite app_nil_l. assert (i-0 = i); try lia. rewrite H1. auto.
- intros form i IL LL prog H0. specialize in_eq with (a:=a) (l:=fq).
  intro H1. apply H in H1.
  inversion H1.  subst. simpl toqlist. simpl toqlist. simpl rev.
  repeat rewrite <- app_assoc.
  simpl length. assert (forall n, i - S n  = i - 1 - n ).
  { intros. lia. }
  rewrite H2.  apply IHfq.
  intros a H3. apply in_cons with (a:= CON (Qvar x)) in H3. auto.
  simpl in H0. inversion H0. assert (i0+1-1 = i0); try lia.
  rewrite H9. auto.
Qed.

Theorem move_from_ll: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i (rev (toiqlist fq)++IL) (rev (toqlist fq)++LL) form ->
    LSL.seq prog (i+length fq+length fq) IL LL (toimp fq form).
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl toimp. simpl length.
  simpl toqlist in H0.
  simpl rev in H0. rewrite app_nil_l in H0. assert (i+0 +0= i); try lia.
  rewrite  H1. auto.
- intros form i IL LL prog H0. specialize in_eq with (a:=a) (l:=fq).
  intro H1. apply H in H1.
  inversion H1.  subst. simpl toqlist in H0. simpl toiqlist in H0.
  simpl rev in H0.
  simpl length. assert (forall n, i + S n + S n= i + n + n + 1 + 1 ).
  { intros. lia. }
  rewrite H2.  repeat rewrite <- app_assoc in H0. simpl. apply i_imp,l_imp.
  apply IHfq.
  + intros a H3. apply in_cons with (a:= CON (Qvar x)) in H3. auto.
  + assert (forall (a:atm) l, a::l = [a]++l).
    { induction l;auto. }
    repeat rewrite <- H3 in H0. auto.
Qed.

Theorem move_from_il: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i (rev (toiqlist fq)++IL) LL form ->
    LSL.seq prog (i+length fq) IL LL (toimpexp fq form).
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl toimp. simpl length.
  simpl toqlist in H0.
  simpl rev in H0. rewrite app_nil_l in H0. assert (i+0= i); try lia.
  rewrite  H1. auto.
- intros form i IL LL prog H0. specialize in_eq with (a:=a) (l:=fq).
  intro H1. apply H in H1.
  inversion H1.  subst. simpl toqlist in H0. simpl toiqlist in H0.
  simpl rev in H0.
  simpl length. assert (forall n, i  + S n= i + n + 1 ).
  { intros. lia. }
  rewrite H2.  repeat rewrite <- app_assoc in H0. simpl. apply i_imp.
  apply IHfq.
  + intros a H3. apply in_cons with (a:= CON (Qvar x)) in H3. auto.
  + assert (forall (a:atm) l, a::l = [a]++l).
    { induction l;auto. }
    repeat rewrite <- H3 in H0. auto.
Qed.

Theorem toimp_ilength: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i IL LL (toimp fq form) -> (length fq)+(length fq)<= i.
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl. lia.
- intros form i IL LL prog H0. specialize in_eq with (a:=a) (l:=fq).
  intro H1. apply H in H1.
  inversion H1.  subst. simpl toimp in H0.
  inversion H0. inversion H6. simpl. apply IHfq in H12.
  + lia.
  + intros a H14. apply in_cons with (a:= CON (Qvar x)) in H14. auto.
Qed.

Theorem toimpexp_ilength: forall fq,
  (forall a, In a fq -> exists x, a = CON  (Qvar x)) ->
  forall form i IL LL prog,
    LSL.seq prog i IL LL (toimpexp fq form) -> (length fq)<= i.
Proof.
intros fq H. induction fq.
- intros form i IL LL prog H0. simpl. lia.
- intros form i IL LL prog H0. specialize in_eq with (a:=a) (l:=fq).
  intro H1. apply H in H1.
  inversion H1.  subst. simpl toimpexp in H0.
  inversion H0. simpl. apply IHfq in H6.
  + lia.
  + intros a H8. apply in_cons with (a:= CON (Qvar x)) in H8. auto.
Qed.

Lemma in_toiqlist:forall x l, In (CON (Qvar x)) l ->
  In (is_qexp (CON (Qvar x))) (toiqlist l).
Proof.
intros x l.
functional induction toiqlist l;intros; inversion H;auto; try inversion H0.
- apply in_eq.
- apply in_cons. auto.
Qed.

Theorem toiqlist_union: forall l1 l2,
  (forall a, In a  l1 -> In a l2) ->
  (forall a, In a (toiqlist l1) -> In a (toiqlist l2)).
Proof.
intros l1.
apply toiqlist_ind; intros;
try inversion H1; subst; try apply in_toiqlist; try apply H0;
try apply in_eq;
try apply H;auto;intros;try apply H0;try apply in_cons; auto.
inversion H0.
Qed.

Theorem vlc_toqlist: forall fq, vlcontext (toqlist fq).
Proof.
intros. functional induction toqlist fq;auto.
- apply vlc_init.
- apply vlc_general;auto. simpl. apply bQubit.
Qed.

Lemma in_toiqlistg: forall x l,
    In x (toiqlist l) ->
    exists y, x = (is_qexp (CON (Qvar y))).
Proof.
  intros x l.
  functional induction toiqlist l;intros;
    try inversion H ;auto. exists x0. auto.
Qed.

Inductive Subtypecontext:
  list atm-> list atm -> list atm ->list atm -> Prop :=
| subcnxt_i: Subtypecontext [] [] [] []
| subcnxt_q: forall a il il' ll ll',
             Subtypecontext il' ll' il ll ->
             Subtypecontext (is_qexp a::il') ll' (is_qexp a::il) ll
| subcnxt_iig: forall a t1 t2 il il' ll ll',
               Subtyping t1 t2 -> (exists c, t2 = bang c) ->
               Subtypecontext il' ll' il ll ->
               Subtypecontext (is_qexp a::typeof a t1::il') ll'
                              (is_qexp a::typeof a t2::il) ll
| subcnxt_llg: forall a t1 t2  il il' ll ll',
               validT (bang t1) ->
               validT (bang t2) ->
               Subtyping t1 t2 -> Subtypecontext il' ll' il ll ->
               Subtypecontext (is_qexp a::il') (typeof a t1::ll')
                              (is_qexp a::il) (typeof a t2::ll)
| subcnxt_lig: forall a t1 t2 il il' ll ll',
               validT(bang t2) -> (exists c,  t1 = bang c) ->
               Subtyping t1 t2 -> Subtypecontext il' ll' il ll ->
               Subtypecontext (is_qexp a::typeof a t1::il') ll'
                              (is_qexp a::il) (typeof a t2::ll).

Theorem rev_qlist_subcnxt: forall fq,forall IL LL IL' LL',
  Subtypecontext IL' LL' IL LL ->
  Subtypecontext (List.rev (toiqlist fq) ++ IL') LL'
                 (List.rev (toiqlist fq) ++ IL) LL.
Proof.
intro fq. functional induction toqlist fq; simpl; auto.
intros IL LL IL' LL' H. apply subcnxt_q with (a:=(CON (Qvar x))) in H.
repeat rewrite <- app_assoc. simpl. apply IHl. auto.
Qed.

Definition Pqexp (il' ll' il ll:list atm): Prop :=
  forall a, In (is_qexp a) il -> In (is_qexp a) il'.

Theorem qexp_inIL_alt: forall il' ll' il ll,
  Subtypecontext il' ll' il ll -> Pqexp il' ll' il ll.
Proof.
intros il' ll' il ll H. apply Subtypecontext_ind.
- unfold Pqexp. intros a H0. inversion H0.
- unfold Pqexp. intros a il0 il'0 ll0 ll'0 H0 H1 a0 H2.
  inversion H2.
  + inversion H3. apply in_eq.
  + apply in_cons. apply H1; auto.
- unfold Pqexp. intros a t1 t2 il0 il'0 ll0 ll'0 H0 H1 H2 H3 a0 H4.
  inversion H4.
  + injection H5. intros. subst. apply in_eq; auto.
  + inversion H5.
    * inversion H6.
    * apply H3 in H6. repeat apply in_cons;auto.
- unfold Pqexp. intros a t1 t2 il0 il'0 ll0 ll'0 H0 H1 H2 H3 H4 a0 H5.
  inversion H5.
  + inversion H6. apply in_eq.
  + apply H4 in H6. apply in_cons;auto.
- unfold Pqexp. intros a t1 t2 il0 il'0 ll0 ll'0 H0 H1 H2 H3 H4 a0 H5.
  inversion H5.
  + inversion H6. apply in_eq.
  + repeat apply in_cons.
    apply H4;auto.
- auto.
Qed.

Theorem qexp_inIL: forall a il' ll' il ll,
  Subtypecontext il' ll' il ll ->
  In (is_qexp a) il -> In (is_qexp a) il'.
Proof.
intros a il' ll' il ll H H0. apply qexp_inIL_alt in H. unfold Pqexp in H.
apply H;auto.
Qed.

Definition Pempty (il' ll' il ll:list atm): Prop :=
  ll = [] -> ll'=[].

Theorem inv_emptyll_alt: forall il il' ll' ll,
Subtypecontext il' ll' il ll -> Pempty il' ll' il ll.
Proof.
intros il il' ll' ll H.
apply Subtypecontext_ind;
  unfold Pempty; try auto; intros; try auto;  try inversion H6;auto.
- inversion H5.
- inversion H5.
Qed.

Theorem inv_emptyll: forall il il' ll',
  Subtypecontext il' ll' il [] -> ll' = [].
Proof.
intros il il' ll' H. apply inv_emptyll_alt in H. unfold P in H.
auto.
Qed.

Theorem In_cntxt_il: forall a t il ll il' ll',
  In (typeof a t) il -> Subtypecontext il' ll' il ll ->
  exists c, t = bang c.
Proof.
intros a t il ll il' ll' H H0. induction H0.
- inversion H.
- inversion H.
  + inversion H1.
  + apply IHSubtypecontext in H1. auto.
- inversion H. inversion H3. inversion H3.
  + inversion H4. subst. auto.
  + apply IHSubtypecontext in H4. auto.
- inversion H.
  + inversion H4.
  + apply IHSubtypecontext in H4. auto.
- inversion H.
  + inversion H4.
  + apply IHSubtypecontext in H4. auto.
Qed.

Theorem In_cntxt_il': forall a t il ll il' ll',
  In (typeof a t) il' -> Subtypecontext il' ll' il ll ->
  exists c, t = bang c.
Proof.
intros a t il ll il' ll' H H0. induction H0.
- inversion H.
- inversion H.
  + inversion H1.
  + apply IHSubtypecontext in H1. auto.
- inversion H.
  + inversion H3.
  + inversion H3.
    * inversion H4. inversion H1. subst.
      apply Subtyping_bang_inv in H0. inversion H0.
      inversion H5. exists x0. auto.
    * apply IHSubtypecontext in H4. auto.
- inversion H.
  + inversion H4.
  + apply IHSubtypecontext in H4. auto.
- inversion H.
  + inversion H4.
  + inversion H4.
    * inversion H5. subst. auto.
    * apply IHSubtypecontext in H5. auto.
Qed.

Theorem In_cntxt_ll: forall a t il ll il' ll',
  In (typeof a t) ll -> Subtypecontext il' ll' il ll ->
  validT (bang t).
Proof.
intros a t il ll il' ll' H H0. induction H0.
- inversion H.
- auto.
- apply IHSubtypecontext in H. auto.
- inversion H.
  + inversion H4. subst. auto.
  + apply IHSubtypecontext in H4. auto.
- inversion H.
  + injection H4. intros. subst. auto.
  + apply IHSubtypecontext in H4. auto.
Qed.

Theorem In_cntxt_ll': forall a t il ll il' ll',
  In (typeof a t) ll' -> Subtypecontext il' ll' il ll ->
  validT (bang t).
Proof.
intros a t il ll il' ll' H H0. induction H0.
- inversion H.
- auto.
- apply IHSubtypecontext in H. auto.
- inversion H.
  + inversion H4. rewrite H7 in H0. auto.
  + apply IHSubtypecontext in H4. auto.
- apply IHSubtypecontext in H. auto.
Qed.

Definition Psplit (il' ll' il ll:list atm): Prop :=
  forall ll1 ll2, LSL.split ll ll1 ll2 ->
  exists il1 il2 ll1' ll2',
    LSL.split ll' ll1' ll2' /\
    (forall a, In a il -> In a il1) /\
    (forall a, In a il -> In a il2) /\
    (forall a t, In (typeof a t) il1 -> In (is_qexp a) il1) /\
    (forall  a t, In (typeof a t) ll1 -> In (is_qexp a) il1) /\
    (forall a t, In (typeof a t) il2 -> In (is_qexp a) il2) /\
    (forall  a t, In (typeof a t) il2 -> In (is_qexp a) il2) /\
    Subtypecontext il' ll1' il1 ll1 /\
    Subtypecontext il'  ll2' il2 ll2.

Theorem subcnxt_split_alt: forall il il' ll ll',
  Subtypecontext il' ll' il ll -> Psplit  il' ll' il ll.
Proof.
intros il il' ll ll' H.
apply Subtypecontext_ind; unfold Psplit; intros; auto.
- apply split_nil in H0.
  inversion H0. subst.
  repeat exists []. split.
  { apply init. }
  split.
  { intros a H1. inversion H1. }
  repeat try split; intros; try inversion H1; apply subcnxt_i.
- apply H1 in H2. inversion H2. inversion H3.
  inversion H4. inversion H5. exists (is_qexp a::x).
  exists (is_qexp a::x0). exists x1. exists x2. inversion H6.
  inversion H8.  inversion H10. inversion H12. split.
  { auto. }
  split.
  { intros a0 H15. inversion H15.
    { subst. apply in_eq. }
    { apply in_cons. apply H9 in H16. auto. }}
  split.
  { intros a0 H15. inversion H15.
    { subst. apply in_eq. }
    { apply in_cons. apply H11 in H16. auto. }}
  { inversion H14. inversion H16. inversion H18.
    inversion H20.
    split.
    { intros a0 t H23. inversion H23.
      { subst. inversion H24. }
      { apply in_cons. apply H13 with t. auto. }}
    split.
    { intros a0 t H23. apply in_cons. apply H15 with t. auto. }
    split.
    { intros a0 t H23. inversion H23.
      { subst. inversion H24. }
      { apply in_cons. apply H17 with t. auto. }}
    split.
    { intros a0 t H23. inversion H23.
      { inversion H24. }
      { apply in_cons. apply H19 with t. auto. }}
    split.
    { apply subcnxt_q. auto. }
    { apply subcnxt_q. auto. }}
(* unfold Psplit.  intros. *)
- apply H3 in  H4. inversion H4. inversion H5.
  inversion H6. inversion H7.
  { exists (is_qexp a::typeof a t2::x).
    exists (is_qexp a::typeof a t2::x0). exists x1. exists x2.
    inversion H8. inversion H10. inversion H12. inversion H14.
    split; auto.
    split.
    { intros a0 H17. inversion H17.
      { subst. apply in_eq. }
      { inversion H18.
        { subst. apply in_cons. apply in_eq. }
        { apply H11 in H19. repeat apply in_cons;auto. }}}
    split.
    { intros a0 H17. inversion H17.
      { subst. apply in_eq. }
      { inversion H18.
        { subst. apply in_cons. apply in_eq. }
        { apply H13 in H19. repeat apply in_cons;auto. }}}
    inversion H16. inversion H18. inversion H20. inversion H22.
    split.
    { intros a0 t H25. inversion H25.
      { inversion H26. }
      { inversion H26.
        { inversion H27. apply in_eq. }
        { repeat apply in_cons. apply H15 with t. auto. }}}
    split.
    { intros a0 t H25. repeat apply in_cons. apply H17 with t. auto. }
    split.
    { intros a0 t H25. inversion H25.
      { inversion H26. }
      { inversion H26.
        { inversion H27. apply in_eq. }
        { repeat apply in_cons. apply H19 with t. auto. }}}
    split.
    { intros a0 t H25. inversion H25.
      { inversion H26. }
      { inversion H26.
        { inversion H27. apply in_eq. }
        { repeat apply in_cons. apply H19 with t. auto. }}}
    split.
    { apply subcnxt_iig;auto. }
    { apply subcnxt_iig;auto. }}
- inversion H5;
  [apply H4 in H10; inversion H10; inversion H11;
   inversion H12; inversion H13; inversion H14;
   inversion H16; inversion H18; inversion H20; inversion H22 as[h22 h22'];
   clear H22; inversion h22' as [H22 H22']; clear h22';
   inversion H22' as[h22' h22'']..];
  [exists (is_qexp a::x); exists (is_qexp a::x0);
          exists (typeof a t1::x1); exists (x2) |
          exists (is_qexp a::x); exists (is_qexp a::x0);
          exists x1; exists (typeof a t1::x2)];
  split;
  [apply splitr1;auto|idtac|apply splitr2;auto|idtac];
  split; repeat (split;intros); intros ;try inversion H23; subst;
  try apply in_eq;
  try assert(H24':=H24);try apply H17 in H24; try apply H19 in H24';
  try apply H21 in H24;try apply H21 in H24';
  try apply h22 in H24;try apply h22' in H24';
  try apply H22 in H24;try apply h22' in H24';
  try inversion H24;subst;
  try apply in_eq;auto; try apply in_cons;auto;
  auto;inversion h22'';try apply subcnxt_llg;auto;
  try apply subcnxt_q;auto.
  apply h22 in H23. auto.
- inversion H5;
  [apply H4 in H10; inversion H10; inversion H11;
   inversion H12; inversion H13; inversion H14;
   inversion H16;  inversion H18;  inversion H20;inversion H22 as[h22 h22'];
   clear H22; inversion h22' as[H22 H22']; clear h22';
   inversion H22' as[h22' h22'']..];
  [exists (is_qexp a::x); exists (is_qexp a::typeof a t1::x0);
          exists x1; exists (x2)|
          exists(is_qexp a::typeof a t1::x); exists (is_qexp a::x0);
          exists x1; exists (x2)];
  split; [auto|idtac|auto|idtac];
  split; repeat (split;intros); intros; try inversion H23; subst;
  try apply in_eq;
  try assert(H24':=H24);try apply H17 in H24; try apply H19 in H24';
  try apply H21 in H24;try apply H21 in H24';
  try apply h22 in H24;try apply h22' in H24';
  try apply H22 in H24;try apply h22' in H24';
  try inversion H24;subst; try inversion H6;
  tryif assert(H6':=H6) then idtac
                else assert(H6:=In_cntxt_ll);
                  try assert(H23':=H23);
                  apply2 H17 H23 H6; apply2 H21 H23 H6;
                  apply2 h22 H23 H6 ; apply2 H22 H23 H6;
                  apply2 H19 H23' H6' ; apply2 H21 H23' H6';
                  apply2 h22' H23' H6'; apply2 h22' H6' H23';
                  try apply in_eq;auto; try apply in_cons;auto;
                  try apply in_eq;auto; try apply in_cons;auto;
                  auto;inversion h22'';try apply subcnxt_iig;auto;
                  try apply subcnxt_lig;auto; try apply sub_ref;
                  apply SubAreVal in H2; inversion H2; auto.
Qed.

Theorem subcnxt_split: forall il il' ll ll' ll1 ll2,
  Subtypecontext il' ll' il ll -> LSL.split ll ll1 ll2 ->
  exists il1 il2 ll1' ll2',
    LSL.split ll' ll1' ll2' /\
    (forall a, In a il -> In a il1) /\ (forall a, In a il -> In a il2) /\
    (forall a t, In (typeof a t) il1 -> In (is_qexp a) il1) /\
    (forall  a t, In (typeof a t) ll1 -> In (is_qexp a) il1) /\
    (forall a t, In (typeof a t) il2 -> In (is_qexp a) il2) /\
    (forall  a t, In (typeof a t) il2 -> In (is_qexp a) il2) /\
    Subtypecontext il' ll1' il1 ll1 /\
    Subtypecontext il'  ll2' il2 ll2.
Proof.
intros il il' ll ll' ll1 ll2 H H0. apply subcnxt_split_alt in H;auto.
Qed.

Definition Pboth (il' ll' il ll:list atm): Prop :=
  (forall a t, In (typeof a t) il -> In (is_qexp a) il) /\
  (forall  a t, In (typeof a t) ll -> In (is_qexp a) il) /\
  (forall a t, In (typeof a t) il' -> In (is_qexp a) il') /\
  (forall  a t, In (typeof a t) ll' -> In (is_qexp a) il').

Theorem subcnxt_both_alt: forall il il' ll ll',
  Subtypecontext il' ll' il ll -> Pboth  il' ll' il ll.
Proof.
intros il il' ll ll' H.
apply Subtypecontext_ind;unfold Pboth;intros;auto;
  repeat split;intros; destruct_conj;subst;auto;
  repeat
    ((match goal with
        |[H:forall _ _, In _ ?x -> _ ,H2:In _ ?x|-_]=> try apply H in H2
        | _=> idtac end);
     (match goal with
        |[H:In (_) (_::_)|-_]=> inversion H;clear H
                                           | _=> idtac end)) ;
    (match goal with
       |[H:is_qexp _ = typeof _ _ |-_]=> inversion H
       | _=> idtac end);
    (match goal with
       |[H:In _ []|-_]=> inversion H
       | _=> idtac end);
    (match goal with
       |[H:is_qexp _ = is_qexp _ |-_]=> inversion H;subst
                                                   | _=> idtac end);
    (match goal with
       |[H:typeof _ _= typeof _ _|-_]=> inversion H;subst
                                                   | _=> idtac end);
  repeat (try apply in_eq;try apply in_cons);auto.
Qed.

Theorem subcnxt_both: forall il il' ll ll',
  Subtypecontext il' ll' il ll ->
  (forall a t, In (typeof a t) il -> In (is_qexp a) il) /\
  (forall  a t, In (typeof a t) ll -> In (is_qexp a) il) /\
  (forall a t, In (typeof a t) il' -> In (is_qexp a) il') /\
  (forall  a t, In (typeof a t) ll' -> In (is_qexp a) il').
Proof.
intros il il' ll ll' H. apply subcnxt_both_alt in H;auto.
Qed.

Definition Pconcat (il' ll' il ll:list atm): Prop :=
  forall ll1 ll2,
    ll = ll1++ll2 ->
    exists il1 il2 ll1' ll2',
      ll' = ll1'++ll2' /\
      (forall a, In a il -> In a il1) /\ (forall a, In a il -> In a il2) /\
      Subtypecontext il' ll1' il1 ll1 /\
      Subtypecontext il'  ll2' il2 ll2.

Theorem subcnxt_concat_alt: forall il il' ll ll',
  Subtypecontext il' ll' il ll -> Pconcat  il' ll' il ll.
Proof.
  intros il il' ll ll' H.
  apply Subtypecontext_ind;
    unfold Pconcat; intros;auto;
      [idtac|idtac|idtac|
       destruct ll1;
       [rewrite app_nil_l in H5;
        assert(ll0=tl ll2); subst; simpl tl; auto;
        rewrite <- app_nil_l in H6|inversion H5]..];
      (match goal with
       |[H:forall _ _, ?x = _ ++ _  -> _ ,H2:?x=_ ++ _|-_]=> try apply H in H2
       | _=> idtac end);rexists;destruct_conj;
        [symmetry in H0;
         apply app_eq_nil  in H0; inversion H0; subst;
         repeat exists []; repeat split;try apply subcnxt_i;intros;
                       try rewrite app_nil_l;auto;
                       inversion H1|
                       exists (is_qexp a::x);
                       exists (is_qexp a::x0); exists x1; exists x2|
                       exists (is_qexp a::typeof a t2::x);
                       exists (is_qexp a::typeof a t2::x0); exists x1; exists x2|
                       exists (is_qexp a::x);
                       exists (is_qexp a::x0);
                       exists []; exists (typeof a t1::x2)|
                       exists (is_qexp a::x); exists (is_qexp a::x0);
                       exists (typeof a t1::x1); exists x2|
                       exists (is_qexp a::typeof a t1::x); exists (is_qexp a::x0);
                       exists []; exists x2
                       |exists (is_qexp a::x); exists (is_qexp a::typeof a t1::x0);
                        exists x1; exists x2];
        [(repeat split;auto;
          intros;
          repeat ((match goal with
                   |[H:forall _ _, In _ ?x -> _ ,H2:In _ ?x|-_]=> try apply H in H2
                   | _=> idtac end);
                  (match goal with
                   |[H:In (_) (_::_)|-_]=> inversion H;clear H
                   | _=> idtac end)) ;
          (match goal with
           |[H:is_qexp _ = typeof _ _ |-_]=> inversion H
           | _=> idtac end);
          (match goal with
           |[H:In _ []|-_]=> inversion H
           | _=> idtac end);
          (match goal with
           |[H:is_qexp _ = is_qexp _ |-_]=> inversion H;subst
           | _=> idtac end);
          (match goal with
           |[H:typeof _ _= typeof _ _|-_]=> inversion H;subst
           | _=> idtac end);subst;
          repeat (try apply in_eq;try apply in_cons);auto;
          try apply subcnxt_lig;try apply subcnxt_llg;try apply subcnxt_iig;
          try apply subcnxt_q; auto)..];
        match goal with | [H:_ |- exists _, bang ?x3 = _] => exists x3|_=>idtac end; auto;
          assert(H8':=H8);  try apply inv_emptyll in H8; subst; auto;
            apply sub_ref; apply SubAreVal in H2;inversion H2;auto.
Qed.

Theorem subcnxt_concat: forall il il' ll ll' ll1 ll2,
  Subtypecontext il' ll' il ll -> ll = ll1++ll2 ->
  exists il1 il2 ll1' ll2',
    ll' = ll1'++ll2' /\
    (forall a, In a il -> In a il1) /\ (forall a, In a il -> In a il2) /\
    Subtypecontext il' ll1' il1 ll1 /\
    Subtypecontext il'  ll2' il2 ll2.
Proof.
intros il il' ll ll' ll1 ll2 H H0. apply subcnxt_concat_alt in H;auto.
Qed.

Theorem subcnxt_add: forall IL IL' fq,
  Subtypecontext IL' [] IL [] ->
  Subtypecontext (toiqlist fq++IL') (toqlist fq)
                 (toiqlist fq++IL) (toqlist fq).
Proof.
intros IL IL' fq H. functional induction toqlist fq;simpl; auto.
apply subcnxt_llg;auto;try apply bQubit; try apply QubitSub.
Qed.

Theorem subcnxt_add2: forall IL IL' LL LL' fq,
  Subtypecontext IL' LL' IL LL ->
  Subtypecontext (toiqlist fq++IL') LL'
                 (toiqlist fq++IL) LL.
Proof.
intros IL IL' LL LL' fq H. functional induction toqlist fq;simpl; auto.
apply subcnxt_q;auto;try apply bQubit; try apply QubitSub.
Qed.

Definition Psinglell (il' ll' il ll:list atm): Prop := forall A a,
  ll = [typeof a A] ->
  exists B, Subtyping B A /\
            (ll' = [typeof a B] \/ (In (typeof a B)  il' /\ ll' = [])).

Theorem inv_singlell_alt: forall il il' ll' ll,
  Subtypecontext il' ll' il ll -> Psinglell il' ll' il ll.
Proof.
  intros il il' ll' ll H.
  apply Subtypecontext_ind;
    unfold Psinglell; intros;auto;
      [inversion H0|(match goal with
                     |[H:forall _ _, ?x = _   -> _ ,H2:?x=_ |-_]=> try apply H in H2
                     | _=> idtac end);rexists;destruct_conj..];
      [ exists x|exists x|exists t1| exists t1];
      match goal with |[H:_\/_ |- _] => destruct H|_=>idtac end;split;
        auto;destruct_conj;[right|right|idtac|left|idtac|right];
          try split;subst;auto;  try inversion H5;
            subst;auto; repeat (try apply in_eq; try apply in_cons);auto;
              match goal with
              |[H: Subtypecontext _ _ _ [] |- _] =>
               apply inv_emptyll in H
              |_=>idtac end;subst;auto.
Qed.

Theorem inv_singlell: forall il il' ll' A a,
  Subtypecontext il' ll' il [typeof a A] ->
  exists B, Subtyping B A /\
            (ll' = [typeof a B] \/ (In (typeof a B)  il' /\ ll' = [])).
Proof.
intros il il' ll' A a H. apply inv_singlell_alt in H.
unfold Psinglell;auto.
Qed.

Definition Pinil (il' ll' il ll:list atm): Prop :=
  forall A a, In (typeof a A) il ->
              exists B, Subtyping B A /\ (In (typeof a B)  il').

Theorem inv_inil_alt: forall IL LL IL' LL',
    Subtypecontext IL' LL' IL LL -> Pinil IL' LL' IL LL.
Proof.
  intros il il' ll' ll H.
  apply Subtypecontext_ind;
    unfold Pinil; intros;auto;
      [inversion H0|
       repeat (match goal with
               |[H:In _ (_::_)|-_]=> inversion H; clear H
               |_=>idtac end);
       (match goal with
        |[H:is_qexp _ = typeof _ _ |-_]=> inversion H
        |_=>idtac end);
       (match goal with
        |[H:forall _ _, In _ ?x   -> _ ,H2:In _ ?x |-_]=> try apply H in H2
        | _=> idtac end);rexists;destruct_conj..];
      [exists x|exists t1|exists x..]; split;
        (match goal with
         |[H:typeof _ _ = typeof _ _|-_]=> inversion H;subst
         | _=> idtac end);
        repeat (try apply in_eq;try apply in_cons);auto.
Qed.

Theorem inv_inil: forall IL LL IL' LL' A a,
  Subtypecontext IL' LL' IL LL -> In (typeof a A) IL ->
  exists B, Subtyping B A /\ (In (typeof a B)  IL').
Proof.
intros IL LL IL' LL' A a H. apply inv_inil_alt in H. unfold Pinil in H.
auto.
Qed.

Definition Pcntxt_splits (il ll il' ll':list atm) :=
forall ll1 ll2, LSL.split ll ll1 ll2 ->
Subtypecontext il ll1 il ll1 /\ Subtypecontext il ll2 il ll2.

Theorem subcntxt_splits_alt: forall il ll,
Subtypecontext il ll il ll -> Pcntxt_splits il ll il ll.
intros. apply Subtypecontext_ind; unfold Pcntxt_splits;
auto; intros. apply split_nil in H0.
inversion H0. subst.  split;apply subcnxt_i.
apply H1 in H2. inversion H2. split; apply subcnxt_q;auto.
apply H3 in H4. inversion H4. split; apply subcnxt_iig;auto.
apply SubAreVal in H0. inversion H0. apply sub_ref;auto.
inversion H1. subst. apply Subtyping_bang_inv in H0.
inversion H0. inversion H7. exists x0. auto.
apply SubAreVal in H0. inversion H0. apply sub_ref;auto.
inversion H1. subst. apply Subtyping_bang_inv in H0.
inversion H0. inversion H7. exists x0. auto.
inversion H5.
apply H4 in H10. inversion H10. split.
apply subcnxt_llg;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
apply subcnxt_q;auto.

apply H4 in H10. inversion H10. split.
apply subcnxt_q;auto.
apply subcnxt_llg;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
apply H4 in H5.
inversion H5. split; apply subcnxt_iig;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
Qed.

Theorem subcntxt_splits: forall il ll ll1 ll2,
Subtypecontext il ll il ll -> LSL.split ll  ll1 ll2 ->
Subtypecontext il ll1 il ll1 /\ Subtypecontext il ll2 il ll2.
Proof.
intros. apply subcntxt_splits_alt in H.
unfold Pcntxt_splits in H. auto.
Qed.

Definition Pcntxt_concats (il ll il' ll':list atm) :=
forall ll1 ll2, ll = ll1++ll2 ->
Subtypecontext il ll1 il ll1 /\ Subtypecontext il ll2 il ll2.

Theorem subcntxt_concats_alt: forall il ll,
    Subtypecontext il ll il ll -> Pcntxt_concats il ll il ll.
Proof.
intros. apply Subtypecontext_ind; unfold Pcntxt_concats;
auto; intros. symmetry in  H0. apply app_eq_nil in H0.
inversion H0. subst.  split;apply subcnxt_i.
apply H1 in H2. inversion H2. split; apply subcnxt_q;auto.
apply H3 in H4. inversion H4. split; apply subcnxt_iig;auto.
apply SubAreVal in H0. inversion H0. apply sub_ref;auto.
inversion H1. subst. apply Subtyping_bang_inv in H0.
inversion H0. inversion H7. exists x0. auto.
apply SubAreVal in H0. inversion H0. apply sub_ref;auto.
inversion H1. subst. apply Subtyping_bang_inv in H0.
inversion H0. inversion H7. exists x0. auto.
destruct ll1. rewrite app_nil_l in H5.
assert(ll'=tl ll2). subst. simpl tl. auto. rewrite <- app_nil_l in H6.
apply H4 in H6. inversion H6. split.
apply subcnxt_q. auto. subst.
apply subcnxt_llg;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
inversion H5. apply H4 in H8. inversion H8. split. apply subcnxt_llg;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
apply  subcnxt_q. auto. apply H4 in H5.
inversion H5. split; apply subcnxt_iig;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
apply SubAreVal in H2. inversion H2. apply sub_ref;auto.
Qed.

Theorem subcntxt_concats: forall il ll ll1 ll2,
Subtypecontext il ll il ll -> ll = ll1++ll2 ->
Subtypecontext il ll1 il ll1 /\ Subtypecontext il ll2 il ll2.
Proof.
intros. apply subcntxt_concats_alt in H.
unfold Pcntxt_concats in H. auto.
Qed.

Lemma memb_il : forall (il il' ll ll':list atm) (M:qexp) (T:qtp),
   Subtypecontext il ll il' ll' ->
   In  (typeof M T) ll -> In (is_qexp M) il /\ In (is_qexp M)  il'.
Proof.
intros il il' ll ll' M T; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
injection h2; intros; subst; subst; simpl; auto.
apply IHSubtypecontext in h2. inversion h2. split;apply in_cons;auto.
Qed.

Lemma memb_il_il : forall (il il' ll ll':list atm) (M:qexp) (T:qtp),
   Subtypecontext il ll il' ll' ->
   In  (typeof M T) il -> In (is_qexp M) il /\ In (is_qexp M)  il'.
Proof.
intros il il' ll ll' M T; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
inversion h2;injection h2; intros; subst; subst; simpl; auto.
apply IHSubtypecontext in h2. inversion h2. split;apply in_cons;auto.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
inversion h2. destruct h2. inversion H2. subst.
split;apply in_eq.
apply IHSubtypecontext in H2. inversion H2.
split; repeat apply in_cons;auto.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
inversion h2.
apply IHSubtypecontext in h2. inversion h2.
split; repeat apply in_cons;auto.
intro h2; simpl in h2; destruct h2 as [h2 | h2].
inversion h2. destruct h2. inversion H3. subst.
split;apply in_eq.
apply IHSubtypecontext in H3. inversion H3.
split; repeat apply in_cons;auto.
Qed.

Theorem intoqlist_infq:forall a fq,
    In a (toqlist fq) ->
    exists q, a = typeof (CON (Qvar q)) qubit /\ In (CON (Qvar q)) fq.
Proof.
intros. functional induction toqlist fq.
inversion H.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
inversion H. exists x. split;auto. apply in_eq.
try apply IHl in H0; inversion H0; try inversion H1;
exists x0; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
try apply IHl in H; inversion H; try inversion H0;
exists x; split;auto; try apply in_cons; auto.
Qed.

Theorem infq_intoqlist: forall q fq, In (CON (Qvar q)) fq ->
In (typeof (CON (Qvar q)) qubit) (toqlist fq).
Proof.
intros. functional induction toqlist fq; try inversion H;
try inversion H0;subst;simpl;intuition.
Qed.

Lemma in_toqlist:forall x l, In (CON (Qvar x)) l ->
  In (typeof (CON (Qvar x)) qubit) (toqlist l).
Proof.
intros x l.
functional induction toqlist l;intros; inversion H;auto; try inversion H0.
- apply in_eq.
- apply in_cons. auto.
Qed.

Theorem toqlist_union: forall l1 l2,
  (forall a, In a  l1 -> In a l2) ->
  (forall a, In a (toqlist l1) -> In a (toqlist l2)).
Proof.
intros l1.
apply toqlist_ind;intros;
try inversion H1; subst; try apply in_toqlist; try apply H0;
try apply in_eq;
try apply H;auto;intros;try apply H0;try apply in_cons; auto;
inversion H0.
Qed.

Theorem intoiqlist_infq:forall a fq,
    In a (toiqlist fq) ->
    exists q, a = is_qexp (CON (Qvar q))  /\ In (CON (Qvar q)) fq.
Proof.
intros. functional induction toiqlist fq;
[try inversion H;
try apply IHl in H; inversion H;
try apply IHl in H1; try inversion H1; try inversion H2;try inversion H0;
 try exists x0; try exists x;split;auto; subst;
match goal with [ H:_ |- In ?a (?a::_)] => apply in_eq
| _ =>  try apply in_cons end; auto..].
Qed.

(****************************************************************
   Definition of prog
  ****************************************************************)

Variable circIn: Econ -> set qexp.
Variable circOut: Econ -> set qexp.
Variable circApp: Econ -> Econ -> Econ.
Variable circNew: list qexp -> nat.
Variable circRev: nat -> nat.

Definition  valid_c (C:Econ) (a:qexp) :Prop:=
  (exists c, C =  Crcons c) /\
  (forall q, In q (FQ a) -> In q (circOut C)).

Inductive prog : atm -> list oo_ -> list oo_ -> Prop :=
(* encoding of Well formedness rules *)
 | starq: prog (is_qexp (CON STAR)) [] []
 | trueq: prog (is_qexp (CON TRUE)) [] []
 | falseq: prog (is_qexp (CON FALSE)) [] []
 | boxq: forall T, valid T -> prog (is_qexp (CON (BOX T))) [] []
 | unboxq: prog (is_qexp (CON UNBOX)) [] []
 | revq: prog (is_qexp (CON REV)) [] []
 | qvar: forall i, prog (is_qexp (CON (Qvar i))) [] []
 | lambdaq: forall (E : qexp -> qexp), abstr E ->
   prog (is_qexp (Fun E))
        [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))] []
 | apq: forall E1 E2: qexp,
   prog (is_qexp (App E1 E2))
        [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))] []
 | prodq: forall E1 E2: qexp,
   prog (is_qexp (Prod E1 E2))
        [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))] []
 | letq: forall (E:qexp -> qexp -> qexp) (b:qexp),
         abstr (fun x => lambda (E x)) ->
         (*abstr (fun y => lambda (fun x =>  (E x y)))*)
         (forall x, proper x ->  abstr (E x)) ->
         (*(forall y, proper y ->  abstr (fun x=> E x y))->*)
   prog (is_qexp (Let E b))
         [(All (fun x : qexp => (All (fun y:qexp =>
           Imp (is_qexp x) (Imp (is_qexp y) (atom_ (is_qexp (E x y))))))));
          (atom_ (is_qexp b))] []
 | sletq: forall E b:qexp,
   prog (is_qexp (Slet E b))
         [And (atom_ (is_qexp E))  (atom_ (is_qexp b))] []
 | ifq: forall b a1 a2:qexp,
   prog (is_qexp (If b a1 a2))
        [And (atom_ (is_qexp b))
          (And (atom_ (is_qexp a1)) (atom_(is_qexp a2)))] []
 | Circq: forall (C:nat) (t a:qexp), quantum_data t ->
   prog (is_qexp (Circ t C a))
         [toimpexp (FQ a) (atom_ (is_qexp a))] []
(* encoding of evaluation rules *)
 | sletr: forall C C' a a' b, valid_c C (Slet a b) ->
          valid_c C' (Slet a' b) -> ~(is_value a) ->
   prog (reduct C (Slet b a) C' (Slet b a'))
         [atom_ (reduct C a C' a'); atom_ (is_qexp b)] []
 | starr: forall C  b, valid_c C (Slet  b (CON STAR))->
   prog (reduct C (Slet b (CON STAR)) C b)
         [atom_ (is_qexp b)] []
  | ifr: forall C C' b b' a1 a2, valid_c C (If b a1 a2) ->
         valid_c C' (If b' a1 a2) -> ~(is_value b) ->
   prog (reduct C (If b a1 a2) C' (If b' a1 a2))
        [atom_(reduct C b C'  b');
         atom_ (is_qexp a1); atom_(is_qexp a2)] []
 | truer: forall C a1 a2,  valid_c C (If (CON TRUE) a1 a2) ->
   prog (reduct C (If (CON TRUE) a1 a2) C a1)
        [atom_ (is_qexp a1); atom_(is_qexp a2)] []
 | falser: forall C a1 a2, valid_c C (If (CON TRUE) a1 a2) ->
   prog (reduct C (If (CON FALSE) a1 a2) C a2)
        [atom_ (is_qexp a1); atom_(is_qexp a2)] []
 | boxr: forall T v C,  valid T  -> is_value v ->
         circIn (Crcons (circNew (FQ(Spec (newqvar v) T)))) =
         FQ(Spec (newqvar v) T) ->
         circOut (Crcons (circNew (FQ(Spec (newqvar v) T)))) =
         List.rev(FQ(Spec (newqvar v) T)) ->
   prog (reduct C (App (CON (BOX T)) v) C
          (Circ (Spec (newqvar v) T) (circNew (FQ(Spec (newqvar v) T)))
            (App v (Spec (newqvar v) T))))
        [atom_(is_qexp  v)] []
 | unboxr: forall u u' v C C' D b',
           quantum_data u -> quantum_data u' -> quantum_data v ->
           circApp (Crcons C) (Crcons D)  = C' ->
           bind u' b'->  bind u v  ->
   prog (reduct (Crcons C)
                  (App (App (CON UNBOX) (Circ u D u')) v) C' b')
                [atom_ (is_qexp v); atom_ (is_qexp b')] []
 | revr: forall C t t', quantum_data t ->  quantum_data t' ->
         circIn (Crcons (circRev C)) = FQ t' ->
         circOut (Crcons (circRev C)) = FQ t ->
   prog (reduct (Crcons C) (App (CON REV) (Circ t C t'))
                (Crcons C) (Circ t' (circRev C) t)) [] []
 | lambdar: forall (E : qexp -> qexp) v C, abstr E ->
            valid_c C (Fun E) -> is_value v ->
   prog (reduct C (App (Fun E) v) C  (E v))
        [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))));
          atom_ (is_qexp v)] []
 | aprf: forall E1 E2 E1' C C', ~(is_value E1) ->
         valid_c C (App E1 E2) ->  valid_c C' (App E1' E2) ->
   prog (reduct C (App E1 E2) C' (App E1' E2))
        [atom_(reduct C E1 C' E1'); atom_ (is_qexp E2)] []
 | apra: forall E1 E2 E2' C C', is_value E1 ->
         valid_c C (App E1 E2) ->  valid_c C' (App E1 E2') ->
   prog (reduct C (App E1 E2) C' (App E1 E2'))
        [atom_(reduct C E2 C' E2'); atom_ (is_qexp E1)] []
 | prodrr: forall E1 E2 E2' C C', ~(is_value E2) ->
           valid_c C (Prod E1 E2) ->  valid_c C' (Prod E1 E2') ->
   prog (reduct C (Prod E1 E2) C' (Prod E1 E2'))
        [atom_(reduct C E2 C' E2'); atom_ (is_qexp E1)] []
 | prodrl: forall E1 E2 E1' C C', is_value E2 ->
           valid_c C (Prod E1 E2) ->  valid_c C' (Prod E1' E2) ->
   prog (reduct C (Prod E1 E2) C' (Prod E1' E2))
        [atom_(reduct C E1 C' E1'); atom_ (is_qexp E2)] []
 | letr1: forall (E:qexp -> qexp -> qexp) (b b':qexp) C C',
          (forall x, proper x ->  abstr (E x)) ->
          (* (forall y, proper y -> abstr (fun x => E x y)) -> *)
          abstr (fun x => lambda (E x)) ->
          (* abstr (fun y => lambda (fun x => (E x y))) -> *)
          ~(is_value b) -> valid_c C (Let E b) ->  valid_c C'  (Let E b') ->
   prog (reduct C (Let E b) C' (Let E b'))
        [atom_ (reduct C b C' b');
         (All (fun x : qexp => (All (fun y:qexp =>
           Imp (is_qexp x) (Imp (is_qexp y) (atom_ (is_qexp (E x y))))))))]
        []
 | letr2: forall (E:qexp -> qexp -> qexp) (v u:qexp) C,
          abstr (fun x => lambda (E x)) ->
          (* abstr (fun y => lambda (fun x =>  (E x y))) -> *)
          (forall x, proper x ->  abstr (E x)) ->
          (* (forall y, proper y -> abstr (fun x=> E x y))-> *)
          is_value v -> is_value u -> valid_c C (Let E (Prod v u))->
   prog (reduct C (Let E (Prod v u)) C (E v u))
        [(All (fun x : qexp => (All (fun y:qexp =>
           Imp (is_qexp x) (Imp (is_qexp y) (atom_ (is_qexp (E x y))))))));
         (atom_ (is_qexp v));(atom_ (is_qexp u))] []
  | Circr: forall C D D' (t a a':qexp), quantum_data t ->
           valid_c (Crcons D) a -> valid_c (Crcons D') a' ->
           circIn (Crcons D') = FQ(t) -> circOut (Crcons D') = FQ(a') ->
    prog (reduct C (Circ t D a) C (Circ t D' a'))
         [atom_(reduct (Crcons D) a (Crcons D') a')] []
(* encoding of typing rules *)
 | axc1: forall (A B:qtp) (x:qexp), validT (bang A) -> Subtyping A B ->
   prog (typeof x B) [atom_ (is_qexp x)] [atom_ (typeof x A)]
 | axc2: forall (A B:qtp) x, Subtyping (bang A) B ->
   prog (typeof x B)
        [(And (atom_ (typeof x (bang A))) (atom_ (is_qexp x)))] []
 | starl: prog (typeof (CON STAR) one) [] []
 | stari: prog (typeof (CON STAR) (bang one)) [] []
 | truel: prog (typeof (CON TRUE) bool) [] []
 | truei: prog (typeof (CON TRUE) (bang bool)) [] []
 | falsel: prog (typeof (CON FALSE) bool) [] []
 | falsei: prog (typeof (CON FALSE) (bang bool)) [] []
 | box: forall T U B, valid T -> valid U ->
        Subtyping (bang (arrow (bang (arrow T U)) (bang (circ T U)))) B ->
   prog (typeof (CON (BOX T)) B) [] []
 | unbox: forall T U B, valid T -> valid U ->
          Subtyping (bang (arrow (circ T U) (bang (arrow T U)))) B ->
   prog (typeof (CON UNBOX) B) [] []
 | rev: forall T U B, valid T -> valid U ->
    Subtyping (bang(arrow (circ T U) (bang (circ U T)) )) B ->
   prog (typeof (CON REV) B) [] []
 | lambda1l: forall (T1 T2: qtp) (E : qexp -> qexp),
             abstr E -> validT (bang T1) -> validT T2 ->
   prog (typeof (Fun E) (arrow T1 T2))
        []
        [(All (fun x : qexp =>
           Imp (is_qexp x) (lImp (typeof x T1) (atom_ (typeof (E x) T2)))))]
 | lambda1i: forall (T1 T2: qtp) (E : qexp -> qexp),
             abstr E -> validT (bang T1) -> validT T2 ->
   prog (typeof (Fun (fun x => E x)) (arrow (bang T1) T2))
        []
        [(All (fun x : qexp =>
           Imp (is_qexp x)
             (Imp (typeof x (bang T1)) (atom_ (typeof (E x) T2)))))]
 | lambda2i: forall (T1 T2: qtp) (E : qexp -> qexp),
             abstr E -> validT (bang T1) -> validT T2 ->
   prog (typeof (Fun (fun x => E x)) (bang(arrow (bang T1) T2)))
        [(All (fun x : qexp =>
           Imp (is_qexp x)
             (Imp (typeof x (bang T1)) (atom_ (typeof (E x) T2)))))]
        []
 | lambda2l: forall (T1 T2: qtp) (E : qexp -> qexp),
             abstr E ->  validT (bang T1) -> validT T2 ->
   prog (typeof (Fun (fun x => E x)) (bang(arrow T1 T2)))
        [(All (fun x : qexp =>
           Imp (is_qexp x) (lImp (typeof x T1) (atom_ (typeof (E x) T2)))))]
        []
 | tap: forall E1 E2: qexp, forall T T' : qtp,  validT (arrow T' T) ->
   prog (typeof (App E1 E2) T)
        []
        [(Conj (atom_ (typeof E1 (arrow T' T))) (atom_ (typeof E2 T')))]
 | ttensorl: forall E1 E2: qexp, forall T T' : qtp,
             validT (tensor T T') ->
   prog (typeof (Prod E1 E2) (tensor T T'))
        []
        [Conj (atom_ (typeof E1 T)) (atom_ (typeof E2 T'))]
 | ttensori: forall E1 E2: qexp, forall T T' : qtp,
             validT (bang T) -> validT (bang T') ->
   prog (typeof (Prod E1 E2) (bang(tensor T T')))
        []
        [Conj (atom_ (typeof E1 (bang T))) (atom_ (typeof E2 (bang T')))]
 | tletl: forall (E:qexp -> qexp -> qexp) (b:qexp), forall T1 T2 T3 : qtp,
          abstr (fun x => lambda (E x)) ->
          (* abstr (fun y => lambda (fun x =>  (E x y))) -> *)
          (forall x, proper x ->  abstr (E x)) ->
          (* (forall y, proper y ->  abstr (fun x=> E x y))-> *)
          validT (bang  T1) -> validT (bang T2) ->
   prog (typeof (Let E  b) T3)
        []
        [(All (fun x : qexp => (All( fun y:qexp =>
           Imp (is_qexp x) (Imp (is_qexp y)
             (lImp (typeof x T1)
                (lImp (typeof y T2) (atom_ (typeof (E x y) T3)))))))));
         atom_ (typeof b (tensor T1 T2))]
 | tleti: forall (E:qexp -> qexp -> qexp) (b:qexp), forall T1 T2 T3 : qtp,
          abstr (fun x => lambda (E x)) ->
          (* abstr (fun y => lambda (fun x =>  (E x y))) -> *)
          (forall x, proper x ->  abstr (E x)) ->
          (* (forall y, proper y ->  abstr (fun x=> E x y))-> *)
          validT (bang  T1) -> validT (bang T2) ->
   prog (typeof (Let E  b) T3)
        []
        [(All (fun x : qexp => (All( fun y:qexp =>
           Imp (is_qexp x) (Imp (is_qexp y)
             (Imp (typeof x (bang T1))
                (Imp (typeof y (bang T2)) (atom_ (typeof (E x y) T3)))))))));
         atom_ (typeof b (bang(tensor T1 T2)))]
 | tsletl: forall E b:qexp, forall T: qtp, validT T ->
   prog (typeof (Slet E  b) T)
        []
        [Conj (atom_ (typeof E T)) (atom_ (typeof b one))]
 | tsleti: forall E b:qexp, forall T: qtp, validT T ->
   prog (typeof (Slet E  b) T)
        []
        [Conj (atom_ (typeof E T)) (atom_ (typeof b (bang one)))]
 | tif: forall b a1 a2:qexp,forall T, validT T ->  FQ a1 = FQ a2 ->
   prog (typeof (If b a1 a2) T)
        []
        [Conj (atom_ (typeof b bool))
           (And (atom_ (typeof a1 T)) (atom_(typeof a2 T)))]
 | tCricl: forall (C:nat) (t a:qexp), forall T U,
           circIn (Crcons C) = FQ t -> circOut (Crcons C) = FQ a ->
           quantum_data t-> validT (circ T U) ->
   prog (typeof (Circ t C a) (circ T U))
        [And (toimp (FQ a) (atom_(typeof a U)))
             ((toimp (FQ t) (atom_(typeof t T))))]
        []
 | tCrici: forall (C:nat) (t a:qexp), forall T U,
           circIn (Crcons C) = FQ t -> circOut (Crcons C) = FQ a ->
           quantum_data t-> validT (circ T U) ->
   prog (typeof (Circ t C a) (bang ((circ T U))))
        [And (toimp (FQ a) (atom_(typeof a U)))
             ((toimp (FQ t) (atom_(typeof t T))))]
        [].

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> list atm -> oo_ -> Prop := LSL.seq prog.
Definition splitseq_ : nat -> list atm -> list atm -> list oo_ -> Prop := LSL.splitseq prog.

Hint Unfold seq_ : hybrid.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold seq_ : hybrid.

End Prog.
