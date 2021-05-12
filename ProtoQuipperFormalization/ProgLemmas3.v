(****************************************************************
   File: ProgLemmas3.v
   Authors: Mohamend Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Miscellaneous lemmas needed for subject reduction
   ***************************************************************)

Require Import ProgLemmas2.
Require Import ProgLemmas1.
Require Import PQAdequacy.
Require Import ProtoQuipperProg.
Require Import LSL.
Require Import ProtoQuipperSyntax.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import FunInd.
Import ListNotations.

Definition seq_ := ProgLemmas2.seq_.
Definition prog := ProgLemmas2.prog.

Theorem in_split_r: forall l l1 l2 :list atm,
    LSL.split l l1 l2 -> forall a, In a l2 -> In a l.
Proof.
  apply LSL.in_split_r; auto.
Qed.

Theorem in_split_l: forall l l1 l2 :list atm,
    LSL.split l l1 l2 -> forall a, In a l1 -> In a l.
Proof.
  apply LSL.in_split_l; auto.
Qed.

Theorem unique_in_split: forall l l1 l2: list atm,
LSL.split l l1 l2 -> forall a, 
count_occ ProgLemmas1.eq_dec l a = 1 ->
(~ (In a l1) /\ (In a l2)) \/ ( (In a l1) /\ ~(In a l2)) .
Proof.
  apply LSL.unique_in_split.
Qed.

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


Hint Resolve LSL.init LSL.splitr1 LSL.splitr2
              LSL.ss_init LSL.ss_general : hybrid.
Hint Resolve starq trueq falseq boxq unboxq revq lambdaq apq prodq letq
     sletq ifq Circq axc1 axc2 starl stari truel truei falsel falsei
     box unbox rev lambda1l lambda1i lambda2l lambda2i tap
     ttensorl ttensori tletl tleti tsletl tsleti tif tCricl
     tCrici subcnxt_i subcnxt_q subcnxt_iig subcnxt_llg subcnxt_lig: hybrid.

(******************************************)
(* More lemmas about toqlist and toiqlist *)
(******************************************)

Theorem count_occ_toqlist_lemma: forall a q,
count_occ ProgLemmas1.eq_dec (toqlist a) (typeof (CON (Qvar q)) qubit) = 
count_occ ProtoQuipperSyntax.eq_dec a (CON (Qvar q)).
Proof.
intros. functional induction toqlist a;simpl;auto.
destruct(eq_dec (CON qABS) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qAPP) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qPROD) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qLET) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON sLET) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qCIRC) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qIF) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON (BOX _x)) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON UNBOX) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON REV) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON TRUE) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON FALSE) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON STAR) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON (Qvar x)) (CON (Qvar q))). inversion e.
subst. destruct(ProgLemmas1.eq_dec (typeof (CON (Qvar q)) qubit)
    (typeof (CON (Qvar q)) qubit)). omega. 
contradict n. auto. destruct(ProgLemmas1.eq_dec (typeof (CON (Qvar x)) qubit)
    (typeof (CON (Qvar q)) qubit)). inversion e. subst. contradict n. auto.
auto.
destruct(eq_dec (CON (Crcons _x)) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (VAR Econ _x) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (BND Econ _x) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (APP _x _x0) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (ABS _x) (CON (Qvar q))). inversion e. auto.
Qed.

Theorem count_occ_toqlist: forall a b,
(forall q, count_occ ProtoQuipperSyntax.eq_dec a q= count_occ ProtoQuipperSyntax.eq_dec b q)
->
(forall q, count_occ ProgLemmas1.eq_dec (toqlist a) q = 
count_occ ProgLemmas1.eq_dec (toqlist b) q).
Proof.
intros. 
destruct (in_dec ProgLemmas1.eq_dec q (toqlist a)).
apply intoqlist_infq in i. inversion i.
inversion H0. subst. repeat rewrite count_occ_toqlist_lemma.
auto.
destruct (in_dec ProgLemmas1.eq_dec q (toqlist b)).
apply intoqlist_infq in i. inversion i.
 inversion H0. subst. repeat rewrite count_occ_toqlist_lemma.
auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in n,n0.
omega. 
Qed.

Theorem count_occ_toiqlist_lemma: forall a q,
count_occ ProgLemmas1.eq_dec (toiqlist a) (is_qexp (CON (Qvar q))) = 
count_occ ProtoQuipperSyntax.eq_dec a (CON (Qvar q)).
Proof.
intros. functional induction toiqlist a;simpl;auto.
destruct(eq_dec (CON qABS) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qAPP) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qPROD) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qLET) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON sLET) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qCIRC) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON qIF) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON (BOX _x)) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON UNBOX) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON REV) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON TRUE) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON FALSE) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON STAR) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (CON (Qvar x)) (CON (Qvar q))). inversion e.
subst. destruct(ProgLemmas1.eq_dec (is_qexp (CON (Qvar q)) )
    (is_qexp (CON (Qvar q)) )). omega. 
contradict n. auto. destruct(ProgLemmas1.eq_dec (is_qexp (CON (Qvar x)) )
    (is_qexp (CON (Qvar q)) )). inversion e. subst. contradict n. auto.
auto.
destruct(eq_dec (CON (Crcons _x)) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (VAR Econ _x) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (BND Econ _x) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (APP _x _x0) (CON (Qvar q))). inversion e. auto.
destruct(eq_dec (ABS _x) (CON (Qvar q))). inversion e. auto.
Qed.

Theorem count_occ_toiqlist: forall a b,
(forall q, count_occ ProtoQuipperSyntax.eq_dec a q= count_occ ProtoQuipperSyntax.eq_dec b q)
->
(forall q, count_occ ProgLemmas1.eq_dec (toiqlist a) q = 
count_occ ProgLemmas1.eq_dec (toiqlist b) q).
Proof.
intros. 
destruct (in_dec ProgLemmas1.eq_dec q (toiqlist a)).
apply in_toiqlistg in i. inversion i.
inversion H0. subst. repeat rewrite count_occ_toiqlist_lemma.
auto.
destruct (in_dec ProgLemmas1.eq_dec q (toiqlist b)).
apply in_toiqlistg in i. inversion i.
 inversion H0. subst. repeat rewrite count_occ_toiqlist_lemma.
auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in n,n0.
omega. 
Qed.

(*******************************************************)
(* More Inversion Lemmas about Subtypecontext and seq_ *)
(*******************************************************)

Theorem STAR_LL: forall i A IL LL, 
True -> 
~(In (is_qexp (CON STAR)) IL)->
Subtypecontext IL LL IL LL -> 
seq_ i IL LL (atom_(typeof (CON STAR) A)) 
 -> LL = [] /\ (A = one \/ A=bang one).
Proof.
intros i A IL LL h. intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.
apply memb_il_il  with (M:= CON STAR) (T:=A) in H0;auto.
inversion H0. contradict H. auto.
inversion H1;auto. inversion H4. subst.
inversion H8. inversion H15. subst.
apply split_ident in H7. subst.
inversion H13;auto. inversion H6.
subst. inversion H16. inversion H21.
subst. apply split_ident in H10.
subst. inversion H20.
inversion H9;auto. subst.
inversion H23. inversion H28.
subst. apply split_ident in H17. subst.
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=A)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H23. inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply seq_mono_cor with (k:=i0)  in H26;try omega. 
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
assert(i0+1+1= i);try omega. rewrite H29 in H26.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. subst.
inversion H23. apply Subtyping_Prop1_one in H22. subst.
apply Subtyping_Prop1_one in H14. subst. auto.
 subst.
inversion H19. 
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto. auto. 
subst. inversion H16. subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19.  assert(i0+1+1= i);try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
rewrite H24 in H22.
apply IHi in H22. auto.
apply sub_trans with (B:=A1);auto. 
subst. inversion H16. apply Subtyping_Prop1_one in H14. subst.
auto. subst. inversion H11. 
subst.
apply memb_il  with (M:= CON STAR) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON STAR) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. auto.
subst. inversion H8. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12.
inversion H15.
subst.  inversion H18.
subst. inversion H17. subst. inversion H9.
subst. inversion H9.  subst. inversion H19. apply split_nil in H9. inversion H9. subst.
inversion  H21.
apply seq_mono_cor with (k:=i2)  in H24;try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H24;auto.
assert(i2+1+1=i);try omega. rewrite H26 in H24. 
apply IHi in H24;auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H13. apply  Subtyping_Prop1_one in H6. subst.
auto. 
apply  Subtyping_Prop1_one in H6. subst.
split;auto.
apply memb_il_il  with (M:= CON STAR) (T:=bang A1) in H0;auto.
inversion H0. contradict H. auto. subst.
inversion H8. auto. subst. inversion H8. auto.
subst. 
apply memb_il  with (M:= CON STAR) (T:=A) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON STAR) (T:=A) in H0;auto.
inversion H0. contradict H. auto. 
Qed. 

Theorem True_LL3: forall i A IL LL, 
True -> 
~(In (is_qexp (CON TRUE)) IL)->
Subtypecontext IL LL IL LL -> 
seq_ i IL LL (atom_(typeof (CON TRUE) A)) 
 -> LL = [] /\ (A = bool \/ A=bang bool).
Proof.
intros i A IL LL h. intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.
apply memb_il_il  with (M:= CON TRUE) (T:=A) in H0;auto.
inversion H0. contradict H. auto.
inversion H1;auto. inversion H4. subst.
inversion H8. inversion H15. subst.
apply split_ident in H7. subst.
inversion H13;auto. inversion H6.
subst. inversion H16. inversion H21.
subst. apply split_ident in H10.
subst. inversion H20.
inversion H9;auto. subst.
inversion H23. inversion H28.
subst. apply split_ident in H17. subst.
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=A)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H23. inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply seq_mono_cor with (k:=i0)  in H26;try omega. 
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
assert(i0+1+1= i);try omega. rewrite H29 in H26.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. subst.
inversion H23. apply Subtyping_Prop1_bool in H22. subst.
apply Subtyping_Prop1_bool in H14. subst. auto.
 subst.
inversion H19. 
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto. auto. 
subst. inversion H16. subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19.  assert(i0+1+1= i);try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
rewrite H24 in H22.
apply IHi in H22. auto.
apply sub_trans with (B:=A1);auto. 
subst. inversion H16. apply Subtyping_Prop1_bool in H14. subst.
auto. subst. inversion H11. 
subst.
apply memb_il  with (M:= CON TRUE) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON TRUE) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. auto.
subst. inversion H8. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12.
inversion H15.
subst.  inversion H18.
subst. inversion H17. subst. inversion H9.
subst. inversion H9.  subst. inversion H19. apply split_nil in H9. inversion H9. subst.
inversion  H21.
apply seq_mono_cor with (k:=i2)  in H24;try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H24;auto.
assert(i2+1+1=i);try omega. rewrite H26 in H24. 
apply IHi in H24;auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H13. apply  Subtyping_Prop1_bool in H6. subst.
auto. 
apply  Subtyping_Prop1_bool in H6. subst.
split;auto.
apply memb_il_il  with (M:= CON TRUE) (T:=bang A1) in H0;auto.
inversion H0. contradict H. auto. subst.
inversion H8. auto. subst. inversion H8. auto.
subst. 
apply memb_il  with (M:= CON TRUE) (T:=A) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON TRUE) (T:=A) in H0;auto.
inversion H0. contradict H. auto. 
Qed. 

Theorem False_LL3: forall i A IL LL, 
True -> 
~(In (is_qexp (CON FALSE)) IL)->
Subtypecontext IL LL IL LL -> 
seq_ i IL LL (atom_(typeof (CON FALSE) A)) 
 -> LL = [] /\ (A = bool \/ A=bang bool).
Proof.
intros i A IL LL h. intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.
apply memb_il_il  with (M:= CON FALSE) (T:=A) in H0;auto.
inversion H0. contradict H. auto.
inversion H1;auto. inversion H4. subst.
inversion H8. inversion H15. subst.
apply split_ident in H7. subst.
inversion H13;auto. inversion H6.
subst. inversion H16. inversion H21.
subst. apply split_ident in H10.
subst. inversion H20.
inversion H9;auto. subst.
inversion H23. inversion H28.
subst. apply split_ident in H17. subst.
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=A)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H23. inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply seq_mono_cor with (k:=i0)  in H26;try omega. 
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
assert(i0+1+1= i);try omega. rewrite H29 in H26.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. subst.
inversion H23. apply Subtyping_Prop1_bool in H22. subst.
apply Subtyping_Prop1_bool in H14. subst. auto.
 subst.
inversion H19. 
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto. auto. 
subst. inversion H16. subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19.  assert(i0+1+1= i);try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
rewrite H24 in H22.
apply IHi in H22. auto.
apply sub_trans with (B:=A1);auto. 
subst. inversion H16. apply Subtyping_Prop1_bool in H14. subst.
auto. subst. inversion H11. 
subst.
apply memb_il  with (M:= CON FALSE) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON FALSE) (T:=A1) in H0;auto.
inversion H0. contradict H. auto. auto.
subst. inversion H8. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12.
inversion H15.
subst.  inversion H18.
subst. inversion H17. subst. inversion H9.
subst. inversion H9.  subst. inversion H19. apply split_nil in H9. inversion H9. subst.
inversion  H21.
apply seq_mono_cor with (k:=i2)  in H24;try omega.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H24;auto.
assert(i2+1+1=i);try omega. rewrite H26 in H24. 
apply IHi in H24;auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H13. apply  Subtyping_Prop1_bool in H6. subst.
auto. 
apply  Subtyping_Prop1_bool in H6. subst.
split;auto.
apply memb_il_il  with (M:= CON FALSE) (T:=bang A1) in H0;auto.
inversion H0. contradict H. auto. subst.
inversion H8. auto. subst. inversion H8. auto.
subst. 
apply memb_il  with (M:= CON FALSE) (T:=A) in H0;auto.
inversion H0. contradict H. auto. apply in_eq.
apply memb_il_il  with (M:= CON FALSE) (T:=A) in H0;auto.
inversion H0. contradict H. auto. 
Qed. 


Theorem True_LL2: forall i IL LL A, 
    ~(In (is_qexp (CON TRUE)) IL) ->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON TRUE) A)) -> LL = [].
Proof.
intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.

inversion H1;auto. inversion H4. subst.
inversion H8. inversion H15. subst.
apply split_ident in H7. subst.
inversion H13;auto. inversion H6.
subst. inversion H16. inversion H21.
subst. apply split_ident in H10.
subst. inversion H20.
inversion H9;auto. subst.
inversion H23. inversion H28.
subst. apply split_ident in H17. subst.
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=A)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto. auto.
subst. inversion H23. auto. subst.
inversion H23. auto.
 subst.
inversion H23. auto.
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
auto. auto. subst. inversion H16. auto.
subst. inversion H16. auto.
subst. inversion H16. auto.
apply notqext_nottyped with (lt:=lL2) (T:=A1) in H;auto.
inversion H. subst. contradict H12. apply in_eq.
auto. subst. inversion H8. auto.
subst. inversion H8. auto. subst. inversion H8. auto.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed. 

Theorem False_LL2: forall i IL LL A, 
    ~(In (is_qexp (CON FALSE)) IL) ->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON FALSE) A)) -> LL = [].
Proof.
intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.

inversion H1;auto. inversion H4. subst.
inversion H8. inversion H15. subst.
apply split_ident in H7. subst.
inversion H13;auto. inversion H6.
subst. inversion H16. inversion H21.
subst. apply split_ident in H10.
subst. inversion H20.
inversion H9;auto. subst.
inversion H23. inversion H28.
subst. apply split_ident in H17. subst.
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=A)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto. auto.
subst. inversion H23. auto. subst.
inversion H23. auto.
 subst.
inversion H23. auto.
apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
auto. auto. subst. inversion H16. auto.
subst. inversion H16. auto.
subst. inversion H16. auto.
apply notqext_nottyped with (lt:=lL2) (T:=A1) in H;auto.
inversion H. subst. contradict H12. apply in_eq.
auto. subst. inversion H8. auto.
subst. inversion H8. auto. subst. inversion H8. auto.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed. 

Theorem subcnxt_add2: forall IL IL' LL LL' fq,
  Subtypecontext IL' LL' IL LL -> 
  Subtypecontext (toiqlist fq++IL') LL' 
                 (toiqlist fq++IL) LL.
Proof.
intros IL IL' LL LL' fq H. functional induction toqlist fq;simpl; auto.
apply subcnxt_q;auto;try apply bQubit; try apply QubitSub.
Qed.

(****************************************************************
  Lemmas about Subtypecontext and typing of quantum data
  ****************************************************************)

Theorem qubit_typed: forall i j A IL LL, 
 (forall q T, In (typeof (CON (Qvar q)) T) LL -> T = qubit) ->
(forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
Subtypecontext IL LL IL LL ->   
seq_ i IL LL (atom_(typeof (CON (Qvar j)) A)) -> 
A = qubit /\ LL = [typeof (CON (Qvar j)) qubit].
Proof.
intros. induction i. inversion H2. omega.
subst. 
assert(In (typeof (CON (Qvar j)) A) [typeof (CON (Qvar j)) A]);
try apply in_eq.
apply H in H3. subst. auto.

apply H0 in H7. inversion H7. destruct H8.
inversion H8. destruct H8. inversion H8.
inversion H8. inversion H9. inversion H2.
Focus 2.
subst. 
assert(In (typeof (CON (Qvar j)) A) [typeof (CON (Qvar j)) A]);
try apply in_eq.
apply H in H3. subst. auto.
Focus 2.
apply H0 in H7. inversion H7. destruct H8.
inversion H8. destruct H8. inversion H8.
inversion H8. inversion H9.
inversion H5. subst.
inversion H9. inversion H16.  
subst. apply split_ident in H8. subst.
inversion H14. inversion H7.
subst. inversion H17. inversion H22. subst.
apply split_ident in H11. subst. inversion H21.
inversion H10. subst. inversion H24. inversion H29. subst.
apply split_ident in H18. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H28;auto.
assert(i=i0+1+1);try omega. rewrite <- H4 in H28. apply IHi in H28.
auto. apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H24. subst.
inversion H11. apply split_nil in H18. inversion H18. subst.
inversion H27. 
apply seq_mono_cor with (k:=i0) in H30; try omega.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H30;auto.
assert(i0+1+1=i);try omega. rewrite  H32 in H30. 
apply IHi in H30. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. 
subst.
assert(In (typeof (CON (Qvar j)) A2) [typeof (CON (Qvar j)) A2])
;try apply in_eq. apply H in H4. subst.
apply Subtyping_Prop1_qubit in H23. subst.
apply Subtyping_Prop1_qubit in H15. auto.
apply H0 in H18. inversion H18. destruct H19.
inversion H19. destruct H19. inversion H19.
inversion H19. inversion H24. auto.
subst. inversion H17. subst. inversion H8.
apply split_nil in H11. inversion H11. subst.
inversion H20.
assert(i0+1+1=i);try omega.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H23;auto.
rewrite  H25 in H23. 
apply IHi in H23. auto.
apply sub_trans with (B:=A1);auto.
subst.
assert(In (typeof (CON (Qvar j)) A1) [typeof (CON (Qvar j)) A1]);try apply in_eq.
apply H in H4.  subst.
apply Subtyping_Prop1_qubit in H15. auto.
subst. apply H0 in H11. inversion H11. destruct H4.
inversion H4. destruct H4. inversion H4.
inversion H4. inversion H7. auto.
subst. inversion H9. subst. inversion H6.
apply split_nil in H8. inversion H8. subst.
inversion H13. inversion H16. inversion H19. subst.
apply sub_not_bang in H30;auto. inversion H30. subst.
inversion H20. apply split_nil in H10. inversion H10. subst.
inversion H21.
apply seq_mono_cor with (k:=i2) in H23; try omega.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H23;auto.
assert(i2+1+1=i);try omega. rewrite  H26 in H23. 
apply IHi in H23. auto.
apply sub_trans with (B:=bang A1);auto.
apply H0 in H21. inversion H21. destruct H22.
inversion H22. destruct H22. inversion H22.
inversion H22. inversion H23. 
Qed.

Theorem quantum_data_typed: forall v, quantum_data v -> 
forall  i A IL LL, 
(*(forall q, In q (FQ v) ->count_occ ProgLemmas1.eq_dec  LL (typeof q qubit)= 1)*)
(forall q T, In (typeof (CON (Qvar q)) T) LL -> T = qubit)->
(forall q T, In (typeof (CON (Qvar q)) T) LL -> 
count_occ  ProgLemmas1.eq_dec LL (typeof (CON (Qvar q)) T) =1) ->
(forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
Subtypecontext IL LL IL LL ->   
seq_ i IL LL (atom_(typeof v A)) ->
(forall q, count_occ ProgLemmas1.eq_dec  (toqlist(FQ v)) q =
                  count_occ ProgLemmas1.eq_dec LL q) /\
Subtyping A (qtyper v).
Proof.
intros v H. induction H;intros. apply qubit_typed in H3;auto.
inversion H3. subst. simpl. split;auto. apply QubitSub.
(*
specialize H  with (CON (Qvar i)). unfold FQ in H.
assert(In (CON (Qvar i)) [CON (Qvar i)]); try apply in_eq.
apply H in H4.
assert(count_occ ProgLemmas1.eq_dec LL (typeof (CON (Qvar i)) qubit)>0);try omega.
apply <- count_occ_In in  H5. auto.*)

apply STAR_LL in H3;auto. inversion H3.
subst. simpl. split; auto. 
destruct H5;subst; try apply BangSub1;
try apply OneSub;try apply bOne. contradict H2.
apply H1 in H2. inversion H2. destruct H4.
inversion H4. destruct H4. inversion H4.
inversion H4.  inversion H5.

apply prod_typed in H5. 
destruct H5; rexists.
destruct_conj. destruct H8.
destruct_conj. inversion H10.
inversion H17. subst. apply split_ident in H12. subst.
inversion H16.
apply IHquantum_data1 in H15;auto.
apply IHquantum_data2 in H18;auto.
destruct_conj.
simpl. split. intros. rewrite nodup_union.
rewrite toqlist_app, 
count_app with (l1:=toqlist (FQ a)) 
(l2:=toqlist (rev(FQ b))), <- rev_toqlist, <- rev_count;auto.
rewrite count_split with (l:=lL2) (l1:=LL1) (l2:=LL2);auto.
apply fq_nodup. apply fq_nodup. intros.
assert(h15:=H15).
apply fq_all_qvar in h15. inversion h15.
subst.
apply in_toqlist in H15. subst.
rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H15.
assert(count_occ ProgLemmas1.eq_dec LL2
        (typeof (CON (Qvar x2)) qubit) > 0);try rewrite <- H19;auto.
rewrite <- count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H8.
assert(h11:=H11).
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in H11.
apply H2 in H11.
apply unique_in_split with (a:=(typeof (CON (Qvar x2)) qubit)) in h11.
destruct h11. inversion H9.
rewrite  count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H12.
rewrite <- H18 in H12. 
rewrite  <- count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H12.
contradict H12. 
apply in_toqlist. auto. inversion H9.
contradict H13. auto.
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in h11;auto.
auto.
inversion H5.
apply TensorSub.
assert (va:=valid_qtyper a).
apply subtyp_valid with (a:=x0);auto.
assert (vb:=valid_qtyper b).
apply subtyp_valid with (a:=x1);auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H1 in H11. auto.
intros.
assert(h11:=H11).
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H2 in H11. auto.
assert(h11':=h11).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h11;auto.
destruct h11. inversion H20.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h11';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H21.
omega.
inversion H20. contradict H22. auto.
apply subcntxt_splits with (il:=IL) in H11;auto.
inversion H11. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H1 in H11. auto.
intros.
assert(h11:=H11).
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H2 in H11. auto.
assert(h11':=h11).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h11;auto.
destruct h11. inversion H20. contradict H21. auto.
inversion H20.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h11';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H22.
omega.
apply subcntxt_splits with (il:=IL) in H11;auto.
inversion H11. auto. auto.

destruct_conj. inversion H11.
inversion H18. subst. apply split_ident in H13. subst.
inversion H17.
apply IHquantum_data1 in H16;auto.
apply IHquantum_data2 in H19;auto.
destruct_conj.
simpl. split. intros. rewrite nodup_union.
rewrite toqlist_app, 
count_app with (l1:=toqlist (FQ a)) 
(l2:=toqlist (rev(FQ b))), <- rev_toqlist, <- rev_count;auto.
rewrite count_split with (l:=lL2) (l1:=LL1) (l2:=LL2);auto.
apply fq_nodup. apply fq_nodup. intros.
assert(h16:=H16).
apply fq_all_qvar in h16. inversion h16.
subst.
apply in_toqlist in H16. subst.
rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H16.
assert(count_occ ProgLemmas1.eq_dec LL2
        (typeof (CON (Qvar x2)) qubit) > 0);try rewrite <- H20;auto.
rewrite <- count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H8.
assert(h12:=H12).
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in H12.
apply H2 in H12.
apply unique_in_split with (a:=(typeof (CON (Qvar x2)) qubit)) in h12.
destruct h12. inversion H10.
rewrite  count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H13.
rewrite <- H19 in H13. 
rewrite  <- count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H13.
contradict H13. 
apply in_toqlist. auto. inversion H10.
contradict H14. auto.
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in h12;auto.
auto.
inversion H5. inversion H23.
apply TensorSub.
assert (va:=valid_qtyper a).
apply subtyp_valid with (a:=x0);auto.
inversion H22. auto. rewrite <- H32 in va. inversion va.
assert (vb:=valid_qtyper b).
apply subtyp_valid with (a:=x1);auto.
inversion H21. auto. rewrite <- H32 in vb. inversion vb.
inversion H23.
apply BangSub1. apply TensorSub. 
assert (va:=valid_qtyper a).
apply subtyp_valid with (a:=x0);auto.
inversion H22. auto. rewrite <- H32 in va. inversion va.
assert (vb:=valid_qtyper b).
apply subtyp_valid with (a:=x1);auto.
inversion H21. auto. rewrite <- H32 in vb. inversion vb.
subst.  apply SubAreVal in H5. inversion H5. auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H1 in H12. auto.
intros.
assert(h12:=H12).
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H2 in H12. auto.
assert(h12':=h12).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h12;auto.
destruct h12. inversion H21.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h12';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H22.
omega.
inversion H21. contradict H23. auto.
apply subcntxt_splits with (il:=IL) in H12;auto.
inversion H12. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H1 in H12. auto.
intros.
assert(h12:=H12).
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H2 in H12. auto.
assert(h12':=h12).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h12;auto.
destruct h12. inversion H21. contradict H22. auto.
inversion H21.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h12';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H23.
omega.
apply subcntxt_splits with (il:=IL) in H12;auto.
inversion H12. auto. auto.

inversion H6. destruct H7.
destruct_conj. clear H11. inversion H10.
inversion H17. subst. apply split_ident in H12. subst.
inversion H16.
apply IHquantum_data1 in H15;auto.
apply IHquantum_data2 in H18;auto.
destruct_conj.
simpl. split. intros. rewrite nodup_union.
rewrite toqlist_app, 
count_app with (l1:=toqlist (FQ a)) 
(l2:=toqlist (rev(FQ b))), <- rev_toqlist, <- rev_count;auto.
rewrite count_split with (l:=lL2) (l1:=LL1) (l2:=LL2);auto.
apply fq_nodup. apply fq_nodup. intros.
assert(h15:=H15).
apply fq_all_qvar in h15. inversion h15.
subst.
apply in_toqlist in H15. subst.
rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H15.
assert(count_occ ProgLemmas1.eq_dec LL2
        (typeof (CON (Qvar x2)) qubit) > 0);try rewrite <- H19;auto.
rewrite <- count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
assert(h11:=H11).
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in H11.
apply H2 in H11.
apply unique_in_split with (a:=(typeof (CON (Qvar x2)) qubit)) in h11.
destruct h11. inversion H8.
rewrite  count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H12.
rewrite <- H18 in H12. 
rewrite  <- count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H12.
contradict H12. 
apply in_toqlist. auto. inversion H8.
contradict H13. auto.
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in h11;auto.
auto.
apply TensorSub;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H1 in H11. auto.
intros.
assert(h11:=H11).
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H2 in H11. auto.
assert(h11':=h11).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h11;auto.
destruct h11. inversion H20.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h11';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H21.
omega.
inversion H20. contradict H22. auto.
apply subcntxt_splits with (il:=IL) in H11;auto.
inversion H11. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H1 in H11. auto.
intros.
assert(h11:=H11).
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H11;auto.
apply H2 in H11. auto.
assert(h11':=h11).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h11;auto.
destruct h11. inversion H20. contradict H21. auto.
inversion H20.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h11';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H22.
omega.
apply subcntxt_splits with (il:=IL) in H11;auto.
inversion H11. auto. auto.

destruct_conj. clear H12. inversion H11.
inversion H18. subst. apply split_ident in H13. subst.
inversion H17.
apply IHquantum_data1 in H16;auto.
apply IHquantum_data2 in H19;auto.
destruct_conj.
simpl. split. intros. rewrite nodup_union.
rewrite toqlist_app, 
count_app with (l1:=toqlist (FQ a)) 
(l2:=toqlist (rev(FQ b))), <- rev_toqlist, <- rev_count;auto.
rewrite count_split with (l:=lL2) (l1:=LL1) (l2:=LL2);auto.
apply fq_nodup. apply fq_nodup. intros.
assert(h16:=H16).
apply fq_all_qvar in h16. inversion h16.
subst.
apply in_toqlist in H16. subst.
rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H16.
assert(count_occ ProgLemmas1.eq_dec LL2
        (typeof (CON (Qvar x2)) qubit) > 0);try rewrite <- H20;auto.
rewrite <- count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
assert(h12:=H12).
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in H12.
apply H2 in H12.
apply unique_in_split with (a:=(typeof (CON (Qvar x2)) qubit)) in h12.
destruct h12. inversion H8.
rewrite  count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H13.
rewrite <- H19 in H13. 
rewrite  <- count_occ_not_In  with (eq_dec:=ProgLemmas1.eq_dec) in H13.
contradict H13. 
apply in_toqlist. auto. inversion H8.
contradict H14. auto.
apply in_split_r with (a:=(typeof (CON (Qvar x2)) qubit)) in h12;auto.
auto.
apply BangSub1. apply TensorSub;auto. 
assert (va:=valid_qtyper a).
inversion H22. auto. rewrite <- H23 in va. inversion va.
assert (vb:=valid_qtyper b).
inversion H21. auto. rewrite <- H23 in vb. inversion vb.
subst.  apply bTensor;  apply bang_valid;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H1 in H12. auto.
intros.
assert(h12:=H12).
apply in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H2 in H12. auto.
assert(h12':=h12).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h12;auto.
destruct h12. inversion H21.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h12';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H22.
omega.
inversion H21. contradict H23. auto.
apply subcntxt_splits with (il:=IL) in H12;auto.
inversion H12. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H1 in H12. auto.
intros.
assert(h12:=H12).
apply in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H12;auto.
apply H2 in H12. auto.
assert(h12':=h12).
apply unique_in_split with (a:=(typeof (CON (Qvar q)) T)) in h12;auto.
destruct h12. inversion H21. contradict H22. auto.
inversion H21.
apply count_split with (eq_dec:=  ProgLemmas1.eq_dec) 
(a:=(typeof (CON (Qvar q)) T)) in h12';auto.
rewrite  count_occ_not_In with (eq_dec:=  ProgLemmas1.eq_dec) in H23.
omega.
apply subcntxt_splits with (il:=IL) in H12;auto.
inversion H12. auto. auto. auto.

contradict H4. apply H3 in H4. inversion H4. destruct H6.
inversion H6. destruct H6. inversion H6. inversion H6. inversion H7.
Qed.

Theorem IL_FQ_REPLACE: forall   u A IL fq LL,  forall i,
(forall q, In q fq -> exists j,  q= is_qexp(CON (Qvar j))) ->
seq_ i (fq++IL) LL (atom_(typeof u A)) ->
seq_ (i+length fq) IL LL (atom_(typeof u A)). 
Proof.
intros u A IL fq LL. induction fq. intros. simpl in H0.
apply seq_mono_cor with (j:=i); auto. omega. intros.
assert(h:=H). specialize H with a. assert( In a (a::fq));
try apply in_eq. apply H in H1. inversion H1.
subst. assert(seq_ (0+1) IL [] (atom_ (is_qexp (CON (Qvar x))))).
apply s_bc with [] [];auto. apply (atom_ (is_qexp (Var 0))).
apply qvar. apply ss_init. apply ss_init.
apply seq_cut_one_aux with (eq_dec:= ProgLemmas1.eq_dec) in H0;auto.
unfold P_seq_cut_one in H0. specialize H0 with (0+1) ((is_qexp (CON (Qvar x)))).
assert(In (is_qexp (CON (Qvar x))) ((is_qexp (CON (Qvar x)) :: fq) ++ IL));try apply in_eq.
apply H0 in  H3. simpl in H3.
destruct (ProgLemmas1.eq_dec (is_qexp (CON (Qvar x))) (is_qexp (CON (Qvar x)))).
apply IHfq in H3;auto. simpl. assert(i+S (length fq) = i+1 + length fq);try omega.
rewrite H4. auto. intros.  apply h. apply in_cons. auto. contradict n. auto.
simpl. destruct (ProgLemmas1.eq_dec (is_qexp (CON (Qvar x))) (is_qexp (CON (Qvar x)))).
assert(1=0+1);try omega. rewrite H4.
apply s_bc with [] [];auto. apply (atom_ (is_qexp (Var 0))).
apply qvar. apply ss_init. apply ss_init. contradict n. auto.
apply  (is_qexp (Var 0)).
Qed.

(****************************************************************
   The common_ll context relation, and lemmas about it
  ****************************************************************)

(* (common_ll a a' ll1 ll2) holds whenever contexts ll1 and ll2 have
   the same typing information about Proto-Quipper terms that are not
   quantum variables, and all typing information about quantum
   variables in ll1 is for quantum variables that occur free in a, and
   and all typing information about quantum variables in ll2 is for
   quantum variables that occur free in a'. *)

Inductive common_ll : qexp -> qexp -> list atm-> list atm  -> Prop :=
|com_empty: forall a a', common_ll a a' [] []
|com_l: forall q  a a' ll1 ll2, In q (FQ a) -> ~ (In q (FQ a')) ->
 common_ll  a a' ll1 ll2 -> 
~ (In (typeof q qubit) ll1) ->
 common_ll  a a' ((typeof q qubit)::ll1) ll2
|com_r: forall q  a a' ll1 ll2, In q (FQ a') -> ~ (In q (FQ a)) ->
 common_ll  a a' ll1 ll2 -> 
~ (In (typeof q qubit) ll2) ->
 common_ll  a a' ll1 ((typeof q qubit)::ll2)
|com_lr: forall q  a a' ll1 ll2, In q (FQ a) ->  (In q (FQ a')) ->
 common_ll  a a' ll1 ll2 -> 
~ (In (typeof q qubit) ll1) ->
~ (In (typeof q qubit) ll2) ->
 common_ll  a a'((typeof q qubit)::ll1) ((typeof q qubit)::ll2)
|common_g: forall  a a' e A ll1 ll2, common_ll a a' ll1 ll2 -> 
~(exists q, e = CON (Qvar q)) -> 
 common_ll a a' ((typeof e A)::ll1) ((typeof e A)::ll2).

Hint Resolve com_empty com_r com_l com_lr common_g LSL.init LSL.splitr1
LSL.splitr2. 

(* Old version

Theorem split_common: forall ll ll',
common_ll  ll ll' ->
forall ll1 ll2, LSL.split ll ll1 ll2 ->
exists ll1' ll2', LSL.split ll' ll1' ll2' /\
 common_ll ll1 ll1' /\ common_ll ll2 ll2'.
intros ll ll' H. induction H;intros.
apply split_nil in H.  inversion H. subst. exists [], [].
split;auto. inversion H0; apply IHcommon_ll in H5;
inversion H5; inversion H6; inversion H7; inversion H9;
exists x,x0;repeat split;auto. 
apply IHcommon_ll in H0.
inversion H0. inversion H1. inversion H2.
inversion H4. exists ((typeof (CON (Qvar q)) qubit)::x),(x0).
split; auto.
inversion H1; apply IHcommon_ll in H6;
inversion H6; inversion H7; inversion H8;inversion H10;
[exists (typeof a A::x),(x0)|exists (x),(typeof a A::x0)]
;split;auto.
Qed.*)

Theorem quantum_ll: forall a a' l1 l2, common_ll a a' l1 l2
-> (forall q, In q l1 -> In q (toqlist (FQ a)))
-> (forall q, In q l2 -> In q (toqlist (FQ a'))).
Proof.
intros a a' l1 l2 H. induction H. intros.
inversion H0. intro. apply IHcommon_ll. intros.
apply H3. apply in_cons. auto.
intros. inversion H4.  subst.
assert(h:=H).
apply fq_all_qvar in H.
inversion H. subst.
apply infq_intoqlist;auto. 
apply IHcommon_ll with (q:=q0) in H3;auto.
intros.
inversion H5.  subst.
assert(h:=H).
apply fq_all_qvar in H.
inversion H. subst.
apply infq_intoqlist;auto. 
apply IHcommon_ll;auto. intros.
apply H4. apply in_cons. auto.
intros. assert (In (typeof e A) (typeof e A :: ll1)).
apply in_eq. apply H1 in H3. apply intoqlist_infq in H3.
inversion H3. inversion H4. inversion H5. contradict H0.
exists x. auto.
Qed. 

Theorem in_common_r: forall a a' l l',
common_ll a a' l l' -> forall q, 
In (typeof (CON (Qvar q)) qubit) l'
-> In (CON (Qvar q))  (FQ a') /\ 
count_occ ProgLemmas1.eq_dec l' (typeof (CON (Qvar q)) qubit) = 1.
Proof.
intros a a' l l' H. induction H;intros;auto.
inversion H. inversion H3. inversion H4. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H4':=H4).
apply IHcommon_ll in H4;auto. inversion H4.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H4. inversion H5. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H3. 
subst.  auto. assert(H5':=H5).
apply IHcommon_ll in H5;auto. inversion H5.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H3. inversion H3. subst. auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
inversion H2. split;auto. rewrite count_occ_cons_neq ;auto.
contradict H0. inversion H0. subst. exists q. auto.
Qed.

Theorem in_common_r_T: forall a a'  T l l',
common_ll a a' l l' -> forall q, 
In (typeof (CON (Qvar q)) T) l'
-> T = qubit. 
Proof.
intros a a' T l l' H. induction H;intros;auto.
inversion H. apply IHcommon_ll with (q:=q0);auto.
inversion H3. inversion H4. subst. auto. 
apply IHcommon_ll in H4;auto. inversion H4.
inversion H5. subst. auto.
apply IHcommon_ll in H5;auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
Qed.


Theorem in_common_r2: forall a a' l l',
common_ll a a' l l' -> forall q T, 
In (typeof (CON (Qvar q)) T) l' -> T = qubit/\
count_occ ProgLemmas1.eq_dec l' (typeof (CON (Qvar q)) T) = 1.
Proof.
intros a a' l l' H. induction H;intros;auto.
inversion H. inversion H3. inversion H4. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H4':=H4).
apply IHcommon_ll in H4;auto. inversion H4.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H4. inversion H5. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H3. 
subst.  auto. assert(H5':=H5).
apply IHcommon_ll in H5;auto. inversion H5.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H3. inversion H3. subst. auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
inversion H2. split;auto. rewrite count_occ_cons_neq ;auto.
contradict H0. inversion H0. subst. exists q. auto.
Qed.

Theorem in_common_l: forall a a' l l',
common_ll a a' l l' -> forall q, 
In (typeof (CON (Qvar q)) qubit) l
-> In (CON (Qvar q))  (FQ a) /\ 
count_occ ProgLemmas1.eq_dec l (typeof (CON (Qvar q)) qubit) = 1.
Proof.
intros a a' l l' H. induction H;intros;auto.
inversion H. inversion H3. inversion H4. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H4':=H4).
apply IHcommon_ll in H4;auto. inversion H4.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H4. inversion H5. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H5':=H5).
apply IHcommon_ll in H5;auto. inversion H5.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
inversion H2. split;auto. rewrite count_occ_cons_neq ;auto.
contradict H0. inversion H0. subst. exists q. auto.
Qed.


Theorem in_common_l_T: forall a a'  T l l',
common_ll a a' l l' -> forall q, 
In (typeof (CON (Qvar q)) T) l
-> T = qubit. 
Proof.
intros a a' T l l' H. induction H;intros;auto.
inversion H. 
inversion H3. inversion H4. subst. auto. 
apply IHcommon_ll in H4;auto. 
apply IHcommon_ll with (q:=q0);auto.
inversion H4.
inversion H5. subst. auto.
apply IHcommon_ll in H5;auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
Qed.

Theorem in_common_l2: forall a a' l l',
common_ll a a' l l' -> forall q T, 
In (typeof (CON (Qvar q)) T) l
-> T=qubit /\ 
count_occ ProgLemmas1.eq_dec l (typeof (CON (Qvar q)) T) = 1.
Proof.
intros a a' l l' H. induction H;intros;auto.
inversion H. inversion H3. inversion H4. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H4':=H4).
apply IHcommon_ll in H4;auto. inversion H4.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H4. inversion H5. subst. 
rewrite count_occ_cons_eq;auto. 
rewrite count_occ_not_In with(eq_dec:=ProgLemmas1.eq_dec) in H2. 
subst.  auto. assert(H5':=H5).
apply IHcommon_ll in H5;auto. inversion H5.
split;auto. rewrite count_occ_cons_neq ;auto.
contradict H2. inversion H2. subst. auto. 
inversion H1. inversion H2. subst. contradict H0.
exists q. auto.  apply IHcommon_ll in H2;auto.
inversion H2. split;auto. rewrite count_occ_cons_neq ;auto.
contradict H0. inversion H0. subst. exists q. auto.
Qed.

Theorem common_eq: forall a a' l l', common_ll a a' l l' ->
(forall q, In q (FQ a) <-> In q (FQ a'))->
l = l'.
Proof.
intros a a' l l' H. induction H;intros;auto.
rewrite H3 in H. contradict H0. auto.
rewrite H3 in H0. contradict H0. auto.
apply IHcommon_ll in H4. subst. auto.
apply IHcommon_ll in H1. subst. auto.
Qed.

Theorem common_a_a: forall a a' l l',
common_ll a a' l l' -> (forall q, In q (FQ a) <-> In q (FQ a'))
-> l = l'.
Proof.
intros a a' ll ll' H. induction H;intros;auto.
rewrite H3 in H. contradict H0. auto.
rewrite <- H3 in H. contradict H0. auto. 
apply IHcommon_ll in H4. subst. auto.
apply IHcommon_ll in H1. subst. auto.
Qed.

Theorem split_common_l: forall a a' ll1 ll2,
common_ll a a' ll1 ll2 ->
forall l1 l2, 
LSL.split ll1 l1 l2 -> 
(forall q, In (typeof (CON (Qvar q)) qubit) l1 -> In (CON (Qvar q)) (FQ a)
/\ In (CON (Qvar q)) (FQ a')) -> exists l2', LSL.split ll2 l1 l2'
/\ common_ll a a' l2 l2'. 
Proof.
intros a a' ll ll' H. induction H;intros.
apply split_nil in H.  inversion H. subst. exists [].
split;auto. inversion H3. subst.
assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
assert(In (typeof (CON (Qvar x)) qubit) (typeof (CON (Qvar x)) qubit :: l3));
try apply in_eq. apply H4 in H5. inversion H5. contradict H0. auto.
assert(H9':=H9).  apply IHcommon_ll in H9. inversion H9.
inversion H10. exists x. split;auto.
apply com_l;auto. 
apply not_in_split with (a:= typeof q qubit) in H9';auto.
inversion H9'. auto. auto.

apply IHcommon_ll in H3;auto. inversion H3.
inversion H5. exists (typeof q qubit :: x). split;auto.
apply com_r;auto. apply not_in_split with (a:=(typeof q qubit) )in H6;auto.
inversion H6. auto.
inversion H4. apply  IHcommon_ll in H10.
inversion H10. inversion H11. 
exists x; split;auto. intros. apply H5. subst. apply in_cons. auto.
assert(H10':=H10). apply  IHcommon_ll in H10. 
inversion H10. inversion H11. 
exists (typeof q qubit::x); split;auto.
apply com_lr;auto.
apply not_in_split with (a:= typeof q qubit) in H10';auto.
inversion H10'. auto. 
apply not_in_split with (a:= typeof q qubit) in H12;auto.
inversion H12. auto.  auto. 

inversion H1. apply  IHcommon_ll in H7;auto. 
inversion H7. inversion H8. 
exists x; split;auto.
intros. apply H2. subst. apply in_cons;auto.
apply  IHcommon_ll in H7;auto. 
inversion H7. inversion H8. 
exists (typeof e A ::x); split;auto.
Qed.

Theorem split_common_r: forall a a' ll1 ll2,
common_ll a a' ll1 ll2 ->
forall l1 l2, 
LSL.split ll1 l1 l2 -> 
(forall q, In (typeof (CON (Qvar q)) qubit) l2 -> In (CON (Qvar q)) (FQ a)
/\ In (CON (Qvar q)) (FQ a')) -> exists l1', LSL.split ll2 l1' l2
/\ common_ll a a' l1 l1'. 
Proof.
intros a a' ll ll' H. induction H;intros.
apply split_nil in H.  inversion H. subst. exists [].
split;auto. inversion H3. subst.
assert(H9':=H9).  apply IHcommon_ll in H9. inversion H9.
inversion H5. exists x. split;auto.
apply com_l;auto. 
apply not_in_split with (a:= typeof q qubit) in H9';auto.
inversion H9'. auto. auto.
assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
assert(In (typeof (CON (Qvar x)) qubit) (typeof (CON (Qvar x)) qubit :: l4));
try apply in_eq. apply H4 in H5. inversion H5. contradict H0. auto.

apply IHcommon_ll in H3;auto. inversion H3.
inversion H5. exists (typeof q qubit :: x). split;auto.
apply com_r;auto. apply not_in_split with (a:=(typeof q qubit) )in H6;auto.
inversion H6. auto.
inversion H4.  assert(H10':=H10). 
apply  IHcommon_ll in H10. 
inversion H10. inversion H11. 
exists (typeof q qubit::x); split;auto.
apply com_lr;auto.
apply not_in_split with (a:= typeof q qubit) in H10';auto.
inversion H10'. auto. 
apply not_in_split with (a:= typeof q qubit) in H12;auto.
inversion H12. auto.  auto. 
apply  IHcommon_ll in H10.
inversion H10. inversion H11. 
exists x; split;auto. intros. apply H5. subst. apply in_cons. auto.

inversion H1. 
apply  IHcommon_ll in H7;auto. 
inversion H7. inversion H8. 
exists (typeof e A ::x); split;auto.
apply  IHcommon_ll in H7;auto. 
inversion H7. inversion H8. 
exists x; split;auto.
intros. apply H2. subst. apply in_cons;auto.
Qed.

Theorem sub_a_comm: forall a a' ll ll',
common_ll a a' ll ll' ->
forall a1 , (forall q, In  (typeof (CON (Qvar q)) qubit) ll -> 
In (CON (Qvar q))  (FQ a1)) -> 
(forall q, ~ (In q (FQ a)) -> ~ (In q (FQ a1))) -> 
common_ll a1 a' ll ll'.
Proof.
intros a a' ll ll' H. induction H;intros;auto.
assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
apply com_l;auto. apply H3. apply in_eq.
apply IHcommon_ll. intros. apply H3. apply in_cons;auto.
auto.

assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
apply com_lr;auto. apply H4;auto. apply in_eq.
apply IHcommon_ll;auto. intros. apply H4. apply in_cons;auto. 

apply common_g;auto. apply IHcommon_ll;auto. intros. apply H1,in_cons;auto.
Qed.

Theorem sub_a'_comml: forall a a' ll ll',
common_ll a a' ll ll' ->
forall a'1 , (forall q, In  (typeof (CON (Qvar q)) qubit) ll' -> 
In (CON (Qvar q))  (FQ a'1)) -> 
(forall q, ~ (In q (FQ a')) -> ~ (In q (FQ a'1))) -> 
common_ll a a'1 ll ll'.
Proof.
intros a a' ll ll' H. induction H;intros;auto.
assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
apply com_r;auto. apply H3. apply in_eq.
apply IHcommon_ll. intros. apply H3. apply in_cons;auto.
auto.

assert (H':=H). apply fq_all_qvar in H'. inversion H'. subst.
apply com_lr;auto. apply H4;auto. apply in_eq.
apply IHcommon_ll;auto. intros. apply H4. apply in_cons;auto. 

apply common_g;auto. apply IHcommon_ll;auto. intros. apply H1,in_cons;auto.
Qed.

Theorem app_common_ll_l: forall l l' a a' q,
common_ll a a'  l  l' ->  ~(In (typeof (CON (Qvar q)) qubit) l) -> 
(In (CON (Qvar q)) (FQ a))  -> ~(In (CON (Qvar q)) (FQ a'))  -> 
common_ll a a'  (l++[typeof (CON (Qvar q)) qubit])  l'.
Proof.
intros.  induction H. simpl.  apply com_l;auto. 
rewrite <- app_comm_cons.
eapply com_l;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H0. rewrite in_app_iff  in H0.
destruct H0. apply in_cons. contradict H5. auto.
inversion H0. inversion H6. subst. apply in_eq.
inversion H6. 

apply com_r;auto. rewrite <- app_comm_cons.
apply com_lr;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H0. rewrite in_app_iff  in H0.
destruct H0. apply in_cons. contradict H5. auto.
inversion H0. inversion H7. subst. apply in_eq.
inversion H7. 

rewrite <- app_comm_cons.
apply common_g;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
Qed.

Theorem app_common_ll_r: forall l l' a a' q,
common_ll a a'  l  l' ->  ~(In (typeof (CON (Qvar q)) qubit) l') -> 
(In (CON (Qvar q)) (FQ a'))  -> ~(In (CON (Qvar q)) (FQ a))  -> 
common_ll a a'  (l)  (l'++[typeof (CON (Qvar q)) qubit]).
Proof.
intros.  induction H. simpl.  apply com_r;auto. 
apply com_l;auto.
rewrite <- app_comm_cons.
eapply com_r;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H0. rewrite in_app_iff  in H0.
destruct H0. apply in_cons. contradict H5. auto.
inversion H0. inversion H6. subst. apply in_eq.
inversion H6. 

rewrite <- app_comm_cons.
apply com_lr;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H0. rewrite in_app_iff  in H0.
destruct H0.  contradict H6. auto.
inversion H0. inversion H7. subst. apply in_eq.
inversion H7. 

rewrite <- app_comm_cons.
apply common_g;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
Qed.


Theorem app_common_ll_lr: forall l l' a a' q,
common_ll a a'  l  l' ->  ~(In (typeof (CON (Qvar q)) qubit) l') -> 
~(In (typeof (CON (Qvar q)) qubit) l) ->
(In (CON (Qvar q)) (FQ a'))  -> (In (CON (Qvar q)) (FQ a))  -> 
common_ll a a'  (l++[typeof (CON (Qvar q)) qubit])  (l'++[typeof (CON (Qvar q)) qubit]).
Proof.
intros.  induction H. simpl.  apply com_lr;auto. 
rewrite <- app_comm_cons.
eapply com_l;auto. apply IHcommon_ll;auto.
contradict H1. apply in_cons. auto.
contradict H1. rewrite in_app_iff  in H1.
destruct H1.  contradict H6. auto.
inversion H1. inversion H7. subst. apply in_eq.
inversion H7. 

rewrite <- app_comm_cons.
apply com_r;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H0. rewrite in_app_iff  in H0.
destruct H0.  contradict H6. auto.
inversion H0. inversion H7. subst. apply in_eq.
inversion H7. 

repeat rewrite <- app_comm_cons. apply com_lr;auto.
apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H1.  apply in_cons. auto. 
contradict H1.  rewrite in_app_iff  in H1.
destruct H1.  contradict H6. auto.
inversion H1. inversion H8. subst. apply in_eq.
inversion H8. 
contradict H0. rewrite in_app_iff  in H0.
destruct H0.  contradict H7. auto.
inversion H0. inversion H8. subst. apply in_eq.
inversion H8. 

rewrite <- app_comm_cons.
apply common_g;auto. apply IHcommon_ll;auto.
contradict H0. apply in_cons. auto.
contradict H1. apply in_cons. auto.
Qed.




Theorem app_common_ll_g: forall l l' a a' e A,
common_ll a a'  l  l' ->  ~(exists i, e =  CON (Qvar i)) -> 
common_ll a a'  (l++[typeof e A])  (l'++[typeof e A]).
Proof.
intros.  induction H. simpl.  apply common_g;auto. 
rewrite <- app_comm_cons.
apply com_l;auto. contradict H3.
rewrite in_app_iff  in H3.
destruct H3.  auto.
inversion H3. inversion H4. subst.
apply fq_all_qvar in H. inversion H. subst. 
contradict H0. exists x. auto.
inversion H4. 

rewrite <- app_comm_cons.
apply com_r;auto. contradict H3.
rewrite in_app_iff  in H3.
destruct H3.  auto.
inversion H3. inversion H4. subst.
apply fq_all_qvar in H. inversion H. subst. 
contradict H0. exists x. auto.
inversion H4.

repeat rewrite <- app_comm_cons.
apply com_lr;auto. contradict H3.
repeat rewrite in_app_iff  in H3.
destruct H3.  auto.
inversion H3. inversion H5. subst.
apply fq_all_qvar in H. inversion H. subst. 
contradict H0. exists x. auto.
inversion H5.
contradict H4.
repeat rewrite in_app_iff  in H4.
destruct H4.  auto.
inversion H4. inversion H5. subst.
apply fq_all_qvar in H. inversion H. subst. 
contradict H0. exists x. auto.
inversion H5.

repeat rewrite <- app_comm_cons.
apply common_g;auto.
Qed.

Theorem rev_common_ll: forall l l' a a',
common_ll a a'  l  l' -> common_ll a a'  (rev l)  (rev l').
Proof.
intros. induction H. simpl. auto.
simpl. assert(h:=H). apply fq_all_qvar in h.
inversion h. subst.  apply app_common_ll_l;auto. 
rewrite <- in_rev. auto.

assert(h:=H). apply fq_all_qvar in h.
inversion h. subst.  apply app_common_ll_r;auto. 
rewrite <- in_rev. auto.

assert(h:=H). apply fq_all_qvar in h.
inversion h. subst.  apply app_common_ll_lr;auto. 
repeat rewrite <- in_rev. auto.
rewrite <- in_rev. auto.

apply app_common_ll_g;auto.
Qed. 

Theorem common_same: forall a a' l,
(forall q, In   q l  -> In  q (FQ a) )
-> 
(forall q, In   q l -> In q(FQ a') )
-> NoDup l -> 
common_ll a a'  (toqlist l) (toqlist l).
Proof.
intros. functional induction toqlist l;auto;[
assert((forall q : qexp, In  q t-> In q (FQ a) ));[
intros;
apply H,in_cons; auto|..];[ 
assert((forall q : qexp, In  q t-> In q (FQ a') ));
intros;
try apply H0,in_cons; auto|..]; inversion H1; auto..]. 
apply com_lr;auto;[| | contradict H6; apply intoqlist_infq in H6;
inversion H6; inversion H8; inversion H9;auto..].
apply H,in_eq.
apply H0,in_eq.
Qed.


Theorem common_app: forall a a'  l1 l2,
common_ll a a' l1 l2 ->  
(forall q, In   (typeof (CON (Qvar q)) qubit) l1  -> 
In  (CON (Qvar q)) (FQ a) /\ ~ (In  (CON (Qvar q)) (FQ a')))
-> 
(forall q, In   (typeof (CON (Qvar q)) qubit) l2 ->
 In  (CON (Qvar q)) (FQ a') /\ ~ (In  (CON (Qvar q)) (FQ a) )) -> 
forall l, common_ll a a' l l -> 
common_ll a a' (l1++l) (l2++l).
Proof.
intros a a' l1 l2 H h1 h2. induction H.
intros. rewrite app_nil_l. auto.
intros. rewrite <- app_comm_cons.
apply com_l;auto. apply IHcommon_ll;auto.
intros. apply h1,in_cons. auto. contradict H1. 
apply in_app_or in H1. destruct H1.
contradict H2. auto.
assert(h3:=H3).
apply fq_all_qvar in H. inversion H. subst.
apply in_common_r with (q:=x) in H3;auto.
apply in_common_l with (q:=x) in h3 ;auto.
inversion H3. inversion h3. contradict H0. auto.
intros. rewrite <- app_comm_cons.
apply com_r;auto. apply IHcommon_ll;auto.
intros. apply h2,in_cons. auto. contradict H2. 
apply in_app_or in H2. destruct H2.
auto.
assert(h3:=H3).
apply fq_all_qvar in H. inversion H. subst.
apply in_common_r with (q:=x) in H3;auto.
apply in_common_l with (q:=x) in h3 ;auto.
inversion H3. inversion h3. contradict H0. auto.
intros. repeat rewrite <- app_comm_cons.
apply com_lr;auto. apply IHcommon_ll;auto.
intros. apply h1,in_cons. auto.
intros. apply h2,in_cons. auto.
contradict H2. 
apply in_app_or in H2. destruct H2.
auto.
assert(h4:=H4).
apply fq_all_qvar in H. inversion H. subst.
apply in_common_r with (q:=x) in H4;auto.
inversion H4. 
assert(In (typeof (CON (Qvar x)) qubit) (typeof (CON (Qvar x)) qubit :: ll1))
;try apply in_eq. apply h1 in H7. inversion H7.  contradict H9. auto. 
contradict H3. 
apply in_app_or in H3. destruct H3.
auto.
apply fq_all_qvar in H. inversion H. subst.
apply in_common_r with (q:=x) in H4;auto.
inversion H4. 
assert(In (typeof (CON (Qvar x)) qubit) (typeof (CON (Qvar x)) qubit :: ll1))
;try apply in_eq. apply h1 in H7. inversion H7.  contradict H9. auto.

intros.  
repeat rewrite <- app_comm_cons.
apply common_g;auto. apply IHcommon_ll;auto.
intros. apply h1,in_cons. auto.
intros. apply h2,in_cons. auto.

Qed.

Theorem common_com: forall a a'  l,
(forall b, In  b  l -> exists q, b = (typeof (CON (Qvar q)) qubit) /\
In  (CON (Qvar q)) (FQ a) /\ (In  (CON (Qvar q)) (FQ a')))
-> NoDup l 
->  common_ll a a' l l.
Proof.
intros. induction l. auto. assert(In a0 (a0::l));try apply in_eq.
apply H in H1. inversion H1. destruct_conj.
subst. apply  com_lr;auto. apply IHl; auto. intros. 
assert(In b (typeof (CON (Qvar x)) qubit::l)); try apply in_cons;auto.
inversion H0. auto. inversion H0.
auto. inversion H0.
auto.
Qed.

Theorem common_fq_inter: forall a a' ,
common_ll a a' (toqlist (set_inter eq_dec (FQ a) (FQ a'))) 
(toqlist (set_inter eq_dec (FQ a) (FQ a'))).
Proof.
intros. apply common_com.
intros. apply intoqlist_infq in H. inversion H.
inversion H0.   rewrite set_inter_iff in H2.
exists x. split;auto.
apply nodup_toqlist,set_inter_nodup;apply fq_nodup.
Qed.


Theorem common_diff: forall a a'  l1 l2,
(forall b, In  b  l1 -> exists q, b = (typeof (CON (Qvar q)) qubit) /\
In  (CON (Qvar q)) (FQ a) /\ ~(In  (CON (Qvar q)) (FQ a')))
-> NoDup l1 
-> (forall b, In  b  l2 -> exists q, b = (typeof (CON (Qvar q)) qubit) /\
~(In  (CON (Qvar q)) (FQ a)) /\ (In  (CON (Qvar q)) (FQ a')))
-> NoDup l2 ->
common_ll a a'  l1 l2.
Proof.
intros. induction l1. induction l2. auto.
assert(In a0 (a0::l2));try apply in_eq.
apply H1 in H3. inversion H3. destruct_conj.
subst. apply com_r;auto. apply IHl2;auto. intros.
assert(In b (typeof (CON (Qvar x)) qubit::l2)); try apply in_cons;auto.
inversion H2. auto. inversion H2. auto. 
assert(In a0 (a0::l1));try apply in_eq.
apply H in H3. inversion H3. destruct_conj.
subst. apply com_l;auto. apply IHl1;auto. intros.
assert(In b (typeof (CON (Qvar x)) qubit::l1)); try apply in_cons;auto.
inversion H0. auto. inversion H0. auto.
Qed.

Theorem common_fq_diff: forall a a' ,
common_ll a a' (toqlist (set_diff eq_dec (FQ a) (FQ a'))) 
(toqlist (set_diff eq_dec (FQ a') (FQ a))).
Proof.
intros. apply common_diff.
intros. apply intoqlist_infq in H. inversion H.
inversion H0.   rewrite set_diff_iff in H2.
exists x. split;auto.
apply nodup_toqlist,set_diff_nodup;apply fq_nodup.
intros. apply intoqlist_infq in H. inversion H.
inversion H0.   rewrite set_diff_iff in H2. inversion H2.
exists x. split;auto.
apply nodup_toqlist,set_diff_nodup;apply fq_nodup.
Qed.


Theorem fq_common_ll: forall a a',
exists l l',  
(forall q, count_occ ProtoQuipperSyntax.eq_dec l q = 
count_occ  ProtoQuipperSyntax.eq_dec (FQ a) q)
/\ 
(forall q, count_occ ProtoQuipperSyntax.eq_dec l' q = 
count_occ  ProtoQuipperSyntax.eq_dec (FQ a') q)
/\ 
common_ll a a' (toqlist l) (toqlist l').
Proof.
intros.
exists ((set_diff eq_dec (FQ a) (FQ a'))++(set_inter eq_dec (FQ a) (FQ a'))).
exists ((set_diff eq_dec (FQ a') (FQ a))++(set_inter eq_dec (FQ a) (FQ a'))).
intros. repeat rewrite toqlist_app.
split. 
intros. 
rewrite count_app with (l1:=set_diff eq_dec (FQ a) (FQ a'))
(l2:=set_inter eq_dec (FQ a) (FQ a'));auto.
destruct (in_dec eq_dec q (FQ a) ).
assert (H:=fq_nodup a). rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H.
assert (h1:=i). apply H in i. rewrite i.
destruct (in_dec eq_dec q (set_diff eq_dec (FQ a) (FQ a')) ).
assert (NoDup (set_diff eq_dec (FQ a) (FQ a'))).
apply set_diff_nodup;apply fq_nodup.
  rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H0.
assert (h2:=i0). apply H0 in i0.
 rewrite i0.
assert (~ (In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_diff_iff in h2. destruct h2.
rewrite set_inter_iff. 
apply  or_not_and. right. auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in H1. omega.
assert(h2:=n). rewrite set_diff_iff in n.
apply not_and_or in n. destruct n.
contradict H0. auto. apply  not_not in H0.
assert ((In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_inter_iff. split;auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in h2.
assert (NoDup (set_inter eq_dec (FQ a) (FQ a'))).
apply set_inter_nodup;apply fq_nodup.
  rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H2. apply H2 in H1.
 omega. unfold decidable.   destruct(in_dec  eq_dec q (FQ a')).
left. auto. right. auto. assert(h:=n). 
assert (~ (In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_inter_iff. 
apply  or_not_and. left. auto.
assert (~ (In q (set_diff eq_dec (FQ a) (FQ a')))).
rewrite set_diff_iff. 
apply  or_not_and. left. auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n,H,H0.
omega.
split.
intros. 
rewrite count_app with (l1:=set_diff eq_dec (FQ a') (FQ a))
(l2:=set_inter eq_dec (FQ a) (FQ a'));auto.
destruct (in_dec eq_dec q (FQ a') ).
assert (H:=fq_nodup a'). rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H.
assert (h1:=i). apply H in i. rewrite i.
destruct (in_dec eq_dec q (set_diff eq_dec (FQ a') (FQ a)) ).
assert (NoDup (set_diff eq_dec (FQ a') (FQ a))).
apply set_diff_nodup;apply fq_nodup.
  rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H0.
assert (h2:=i0). apply H0 in i0.
 rewrite i0.
assert (~ (In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_diff_iff in h2. destruct h2.
rewrite set_inter_iff. 
apply  or_not_and. left. auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in H1. omega.
assert(h2:=n). rewrite set_diff_iff in n.
apply not_and_or in n. destruct n.
contradict H0. auto. apply  not_not in H0.
assert ((In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_inter_iff. split;auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in h2.
assert (NoDup (set_inter eq_dec (FQ a) (FQ a'))).
apply set_inter_nodup;apply fq_nodup.
  rewrite NoDup_count_occ' 
with (decA:=eq_dec)in H2. apply H2 in H1.
 omega. unfold decidable.   destruct(in_dec  eq_dec q (FQ a)).
left. auto. right. auto. assert(h:=n). 
assert (~ (In q (set_inter eq_dec (FQ a) (FQ a')))).
rewrite set_inter_iff. 
apply  or_not_and. right. auto.
assert (~ (In q (set_diff eq_dec (FQ a') (FQ a)))).
rewrite set_diff_iff. 
apply  or_not_and. left. auto.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n,H,H0.
omega.

apply common_app. apply common_fq_diff. 
intros. apply intoqlist_infq in H. inversion H.
inversion H0.   rewrite set_diff_iff in H2. inversion H2.
inversion H1. subst.
split;auto.
intros. apply intoqlist_infq in H. inversion H.
inversion H0.   rewrite set_diff_iff in H2. inversion H2.
inversion H1. subst.
split;auto.
apply common_fq_inter. 

Qed.


(***********************************************************************
   Definitions and lemmas about arguments to the Box and Unbox operators
  ***********************************************************************)

Fixpoint get_boxed (e:qexp): list qexp :=
match e with
(APP (APP (CON qAPP) (CON (BOX t))) V) => V::get_boxed V
|(APP (APP (CON qAPP) (CON UNBOX)) V) => V::get_boxed V

|_ => match e with
(APP (APP (CON qPROD) e1) e2) => (get_boxed e1)++(get_boxed e2)
|(APP (APP (CON qAPP) e1) e2)  => (get_boxed e1)++(get_boxed e2)
|APP (CON qABS) (ABS e)    => (get_boxed e)
|(APP (APP (APP (CON qIF) e1) e2) e3) => (get_boxed e1)++(get_boxed e2)++(get_boxed e3)
|(APP (APP (CON sLET)  e1) e2) => (get_boxed e1)++(get_boxed e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) => 
  (get_boxed e1)++(get_boxed e2)
|(APP (APP (APP (CON qCIRC) e1) (CON (Crcons i))) e2) => 
  (get_boxed e1)++(get_boxed e2)
|_ => []
(*match e with
  CON (Qvar x) => x+1
| APP e1 e2 => max (newqvar e1) (newqvar e2)
| ABS e' => newqvar e'
| _ => 0*)
end
end.

(*Functional Scheme get_box_ind := Induction for get_boxed Sort Prop. *)

Theorem value_bang_emptyll: forall j v, is_value v-> 
    forall IL LL A,
      Subtypecontext IL LL IL LL ->
  
     (forall V, In V (get_boxed v)  -> 
            ~ (exists i, V = (Var i) \/ V = (CON (Qvar i))))(* ~In (is_qexp V) IL )*)-> 
      (forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) -> validT (bang A) ->
      seq_ j IL LL  (atom_ (typeof v (bang A))) -> LL=[].
Proof.
intros j. induction j.
intros. inversion H4. omega. subst.
apply In_cntxt_ll' with (a:= v) (t:=bang A) in H0;try apply in_eq;auto.
inversion H0.
auto. intros. destruct H.

inversion H4;auto. inversion H6. inversion H16; subst; 
inversion H13. subst.
inversion H10. auto. subst. 
apply In_cntxt_ll'  with (a:=Var x) (t:=bang A) in H0;try apply in_eq.
inversion H0.


inversion H4;auto. inversion H6. inversion H16; subst; 
inversion H13. subst.
inversion H10. auto. subst. 
apply In_cntxt_ll'  with (a:=CON (Qvar x)) (t:=bang A) in H0;try apply in_eq.
inversion H0.

intros.
apply sub_Circ_inv in H4;auto.
destruct H4;rexists;destruct_conj; subst;auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply True_LL2 in H4;auto. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply False_LL2 in H4;auto. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply STAR_LL in H4;auto. inversion H4.  auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply BOX_LL in H4;auto. inversion H4. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply UNBOX_LL in H4;auto. inversion H4. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros.
apply REV_LL in H4;auto. inversion H4. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros. apply fun_typed2 in H4;auto.
destruct H4;try destruct H4; rexists;
destruct_conj. destruct H8; destruct_conj; inversion H8.
destruct H8;destruct_conj;subst;auto.
destruct H4;try destruct H4; rexists;
destruct_conj. destruct H8; destruct_conj; inversion H8.
destruct H8;destruct_conj;subst;auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

intros. apply prod_typed in H4.
repeat (match goal with
[H:_ \/ _ |- _] => destruct H;rexists;destruct_conj
|_=>idtac end). subst. inversion H4.
inversion H11. inversion H18. subst. apply split_ident in H13.
subst. 
inversion H17;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0;auto.
apply seq_mono_cor with (k:=j) in H16;try omega. 
apply seq_mono_cor with (k:=j) in H19;try omega.
apply IHj in H16;auto. apply IHj in H19;auto. subst.
inversion H12. auto.
intros. specialize H1 with V.  
simpl in H1. rewrite in_app_iff in H1.
intuition. 
intros. specialize H1 with V.  
simpl in H1. rewrite in_app_iff in H1.
intuition. 
auto.
inversion H7.
inversion H10. inversion H17. subst. apply split_ident in H12.
subst. 
inversion H16;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0;auto.
apply seq_mono_cor with (k:=j) in H18;try omega. 
apply seq_mono_cor with (k:=j) in H19;try omega.
apply IHj in H18;auto. apply IHj in H19;auto. subst.
inversion H12. auto.
intros. specialize H1 with V.  
simpl in H1. rewrite in_app_iff in H1.
intuition. 
intros. specialize H1 with V.  
simpl in H1. rewrite in_app_iff in H1.
intuition.
auto. auto.
contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.


assert(h4:=H4).
apply app_typed in H4.
destruct H4. rexists. destruct_conj. 
inversion H8. clear H8. inversion H15. subst.
apply split_ident in H10. subst.
inversion H14;auto. apply UNBOX_LL in H13;auto.
inversion H13.
rexists. inversion H18. inversion H20.
assert(Subtyping (bang (arrow x2 x3))  (bang A)).
apply sub_trans with (B:=x1);auto.
inversion H29. inversion H31.
inversion H32. subst.
apply sub_bangarrow_inv in h4;auto.
repeat (match goal with
[H:_ \/ _ |- _] => destruct H;rexists
|_=>idtac end); try  inversion H8; try inversion H7.
subst. apply sub_Circ_inv in H16;auto. clear H13.
destruct H16; rexists; destruct_conj; subst;inversion H9;auto.
apply subcntxt_splits with (ll1:=[]) (ll2:=LL2) in H0;auto.
inversion H0;auto.

contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
inversion H3. auto.
inversion H3. auto.

intros. simpl in H1. inversion H7.
subst. contradict H3. apply H2 in H3.
specialize H1 with v0.
assert(~ (exists i : var, v0 = Var i \/ v0 = CON (Qvar i))). intuition.
contradict H8. inversion H3. destruct H10.
inversion H10. exists  x. left. auto.
destruct H10. inversion H10. exists x. right . auto.
inversion H10. inversion H11.

apply Unboxappv;auto.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0;auto. auto.


rexists. destruct_conj. 
inversion H7. clear H7. inversion H14. subst.
apply split_ident in H9. subst.
inversion H13;auto. apply UNBOX_LL in H12;auto.
inversion H12.
rexists. inversion H17. inversion H19.
inversion H27. inversion H29.
inversion H30. subst.
apply sub_bangarrow_inv in h4;auto.
repeat (match goal with
[H:_ \/ _ |- _] => destruct H;rexists
|_=>idtac end); try  inversion H7; try inversion H6.
subst. apply sub_Circ_inv in H15;auto. 
destruct H15; rexists; destruct_conj; subst;inversion H8;auto.
apply subcntxt_splits with (ll1:=[]) (ll2:=LL2) in H0;auto.
inversion H0;auto.

contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
inversion H3. auto.
inversion H3. auto.

intros. simpl in H1. inversion H6.
subst. contradict H3. apply H2 in H3.
specialize H1 with v0.
assert(~ (exists i : var, v0 = Var i \/ v0 = CON (Qvar i))). intuition.
contradict H7. inversion H3. destruct H9.
inversion H9. exists  x. left. auto.
destruct H9. inversion H9. exists x. right . auto.
inversion H9. inversion H10.

apply Unboxappv;auto.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.


contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.

apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0;auto. auto.

auto.

contradict H1. apply H2 in H1.
inversion_clear H1 as [i0 e_dis]; destruct e_dis as [e_disl|e_disr]
;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
Qed.

(****************************************************************
   Definitions and lemmas about free quantum variables
  ****************************************************************)

Fixpoint FQUC (e:qexp) :set qexp :=
match e with
CON (Qvar x) => [CON  (Qvar x)]
|(APP (APP (CON qPROD) e1) e2) =>  (FQUC e1) ++(FQUC e2)
|(APP (APP (CON qAPP) e1) e2)  => (FQUC e1) ++(FQUC e2)
|APP (CON qABS) (ABS e)    => FQUC e
|(APP (APP (APP (CON qIF) e1) e2) e3) => (FQUC e1) ++(FQUC e2)++(FQUC e3)
|(APP (APP (CON sLET)  e1) e2) => (FQUC e1) ++(FQUC e2)
| (APP (CON qLET)  (APP (ABS e1) e2)) => 
  (FQUC e1) ++(FQUC e2)
|(APP (APP (APP (CON qCIRC) e1) (CON (Crcons i))) e2) => (FQUC e1) ++(FQUC e2)
|_ => []
end.
Functional Scheme FQUC_ind := Induction for FQUC Sort Prop. 


Theorem FQU_FQ: forall v q, In q (FQU v) <-> In q (FQ v).
Proof.
intros. 
apply FQ_ind;intros;simpl;split;intros; 
match goal  with
|[H:False|-_] => contradiction
|_=>idtac end;auto;
match goal with
|[H:In _ (_++_), H1: In _ _<-> In _ ?x, H2:In _ _<-> In _ ?y|- In _ (set_union eq_dec ?x ?y)] =>
  rewrite in_app_iff in H; rewrite set_union_iff;
 destruct H;[rewrite <- H1;left| rewrite <- H2;right];auto
|_=>idtac end;
match goal with
|[H:In _ (set_union eq_dec _ _), H1: In _ ?x<-> In _ _, H2:In _ ?y<-> In _ _|- In _ (?x++?y)] =>
  rewrite set_union_iff  in H; rewrite in_app_iff;
 destruct H;[rewrite  H1;left| rewrite  H2;right];auto
|_=>idtac end.
 rewrite <- H. auto.
rewrite H. auto.
repeat rewrite in_app_iff in H2; repeat rewrite set_union_iff;
 destruct H2. right. left. rewrite <- H0. auto.
destruct H2. right. right. rewrite <- H1. auto.
left. rewrite <- H. auto.
repeat rewrite set_union_iff in H2; repeat rewrite in_app_iff ;
destruct H2. right. right. rewrite H. auto.
destruct H2. left. rewrite  H0. auto.
right. left. rewrite H1. auto.
Qed.

Theorem FQU_FQ_qlist: forall v,
NoDup (FQU v) -> 
(forall q, count_occ ProgLemmas1.eq_dec  (toqlist(FQ v)) q =
                  count_occ ProgLemmas1.eq_dec (toqlist(FQU v)) q).
Proof.
intros. assert (H0:=fq_nodup v ).
apply nodup_toqlist in H.
apply nodup_toqlist in H0. assert (h:=H).
rewrite NoDup_count_occ' with (decA:=ProgLemmas1.eq_dec) in H0,h.
assert(h':=FQU_FQ v).  
destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ v))).
assert(i':=i).
apply intoqlist_infq in i. inversion i.
inversion H1. rewrite <- h' in H3.
apply in_toqlist in H3. subst. rewrite H0,h;auto.
destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQU v))).
apply intoqlist_infq in i. inversion i.
inversion H1. rewrite  h' in H3.
apply in_toqlist in H3. subst. contradict n. auto.
rewrite count_occ_not_In in n,n0. rewrite n,n0. auto.
Qed. 

Theorem typed_quantum_data: forall v, quantum_data v
 -> NoDup (FQU v)-> 
forall  IL LL,
(forall q, count_occ ProgLemmas1.eq_dec  (toqlist(FQ v)) q =
                  count_occ ProgLemmas1.eq_dec LL q) 
-> exists i, seq_ i IL LL (atom_(typeof v (qtyper v))).
Proof.
intros v  H h'. induction H. intros. unfold toqlist, FQ in H.
assert (h:=H).  apply count_occ_length in h.  simpl in h.
destruct LL. inversion h. destruct LL;[..| inversion h].
specialize H with a. simpl in H. destruct (ProgLemmas1.eq_dec a a).
destruct (ProgLemmas1.eq_dec (typeof (CON (Qvar i)) qubit) a).
subst.
exists 1. apply l_init. omega. contradict n. auto.

(*STAR CASE*)
intros. simpl in H.
symmetry in H. rewrite count_occ_inv_nil in H.
subst. simpl. exists (0+1). apply s_bc with (lL:=[]) (iL:=[]).
apply (atom_ (is_qexp (CON STAR))).
apply starl. apply ss_init. apply ss_init.

(*PROD CASE*)
intros. assert (h'':=h'). 
simpl in h'. apply nodup_concat with (l1:=FQU a) (l2:=FQU b) in h';auto.
inversion h' as [h1' h2'].
simpl.
specialize IHquantum_data1 with IL (toqlist (FQ a)).
simpl in IHquantum_data1.
assert(exists i : nat,
                    seq_ i IL (toqlist (FQ a)) (atom_ (typeof a (qtyper a)))).
auto.
specialize IHquantum_data2 with IL (toqlist (FQ b)).
simpl in IHquantum_data2.
assert(exists i : nat,
                    seq_ i IL (toqlist (FQ b)) (atom_ (typeof b (qtyper b)))).
auto.
inversion H2. inversion H3.
exists (x+x0+1+1). apply seq_exchange_cor 
with (ll:= toqlist (FQ a)++toqlist(FQ b)) (eq_dec:=ProgLemmas1.eq_dec).
apply s_bc with
(lL:=[Conj (atom_ (typeof a (qtyper a))) (atom_ (typeof b (qtyper b)))])
(iL:=[]).
apply (atom_ (is_qexp (CON STAR))).
apply ttensorl.
apply valid_is_T,Tensor; apply valid_qtyper.
apply ss_init.
apply ss_general with
(lL2:=toqlist (FQ a) ++ toqlist (FQ b))
(lL3:=[]). apply split_ref. 
apply m_and with (LL1:=toqlist (FQ a)) (LL2:=toqlist (FQ b)).
apply concat_split;auto.
apply seq_mono_cor with (j:=x);auto. omega.
apply seq_mono_cor with (j:=x0);auto. omega.
apply ss_init.
intros. rewrite <- H1. simpl.
 rewrite nodup_union, count_app with 
(l1:=toqlist (FQ a)) (l2:=toqlist (FQ b)),
 toqlist_app,
count_app with 
(l:=toqlist (FQ a) ++ toqlist ( rev (FQ b)))
 (l1:=toqlist (FQ a)) (l2:=toqlist (rev (FQ b))),
 FQU_FQ_qlist, FQU_FQ_qlist,
  <- rev_toqlist,<- rev_count,FQU_FQ_qlist;auto;try apply fq_nodup.
intros q. repeat rewrite <- FQU_FQ. intros.
simpl in h''.
  apply nodup_in_app with 
(l1:=FQU a) (l2:=FQU b) (a:=q) in h'';auto.
destruct h''. inversion H7. contradict H9. auto.
inversion H7. auto.
apply eq_dec.
rewrite in_app_iff. right. auto.
Qed.

Lemma FQU_subset_FQUC : forall (e x:qexp), In x (FQU e) -> In x (FQUC e).
Proof.
  intros e. functional induction FQU e; simpl; auto.
  - intros x H.  apply in_or_app. specialize in_app_or with (1:=H); intros [H0 | H0].
    + left; apply IHs; auto.
    + right; apply IHs0; auto.
  - intros x H.  apply in_or_app. specialize in_app_or with (1:=H); intros [H0 | H0].
    + left; apply IHs; auto.
    + right; apply IHs0; auto.
  - intros x H.  apply in_or_app. specialize in_app_or with (1:=H); intros [H0 | H0].
    + left; apply IHs; auto.
    + right; apply IHs0; auto.
  - intros x H.  apply in_or_app. specialize in_app_or with (1:=H); intros [H0 | H0].
    + left; apply IHs; auto.
    + right; apply IHs0; auto.
  - intros x H; elim H.
  - intros x H.  apply in_or_app. specialize in_app_or with (1:=H); intros [H0 | H0].
    + left; apply IHs; auto.
    + right. apply in_or_app. specialize in_app_or with (1:=H0); intros [H1 | H1].
      * left; apply IHs0; auto.
      * right; apply IHs1; auto.
Qed.

Lemma FQUC_FQU: forall e, NoDup (FQUC e) -> NoDup (FQU e).
Proof.
  intro e. functional induction FQU e; try constructor.
  - simpl; auto.
  - constructor.
  - intro H; apply IHs.
    simpl in H; auto.
  - simpl; intro H.
    rewrite disjoint_NoDup in *.
    destruct H as [[H H1] [H2 H3]].
    specialize IHs with (1:=H2); specialize IHs0 with (1:=H3).
    specialize (FQU_subset_FQUC e7); specialize (FQU_subset_FQUC e9); intros H4 H5.
    repeat split; auto.
    + intros x H6 H7. specialize H4 with (1:=H6).
      specialize H with (1:=H4); elim H.
      apply H5; auto.
    + intros x H6 H7. specialize H4 with (1:=H7).
      specialize H with (1:=H4).
      apply H; auto.
  - simpl; intro H.
    rewrite disjoint_NoDup in *.
    destruct H as [[H H1] [H2 H3]].
    specialize IHs with (1:=H2); specialize IHs0 with (1:=H3).
    specialize (FQU_subset_FQUC e2); specialize (FQU_subset_FQUC e4); intros H4 H5.
    repeat split; auto.
    + intros x H6 H7. specialize H4 with (1:=H6).
      specialize H with (1:=H4); elim H.
      apply H5; auto.
    + intros x H6 H7. specialize H4 with (1:=H7).
      specialize H with (1:=H4).
      apply H; auto.
  - simpl; intro H.
    rewrite disjoint_NoDup in *.
    destruct H as [[H H1] [H2 H3]].
    specialize IHs with (1:=H2); specialize IHs0 with (1:=H3).
    specialize (FQU_subset_FQUC e2); specialize (FQU_subset_FQUC e4); intros H4 H5.
    repeat split; auto.
    + intros x H6 H7. specialize H4 with (1:=H6).
      specialize H with (1:=H4); elim H.
      apply H5; auto.
    + intros x H6 H7. specialize H4 with (1:=H7).
      specialize H with (1:=H4).
      apply H; auto.
  - simpl; intro H.
    rewrite disjoint_NoDup in *.
    destruct H as [[H H1] [H2 H3]].
    specialize IHs with (1:=H2); specialize IHs0 with (1:=H3).
    specialize (FQU_subset_FQUC e2); specialize (FQU_subset_FQUC e4); intros H4 H5.
    repeat split; auto.
    + intros x H6 H7. specialize H4 with (1:=H6).
      specialize H with (1:=H4); elim H.
      apply H5; auto.
    + intros x H6 H7. specialize H4 with (1:=H7).
      specialize H with (1:=H4).
      apply H; auto.
  - simpl; intro H.
    repeat rewrite disjoint_NoDup in *.
    rewrite disjoint_app_r in *.
    destruct H as [[[H H0] [H1 H2]] [H3 [[H4 H5] [H6 H7]]]].
    specialize IHs with (1:=H3); specialize IHs0 with (1:=H6); specialize IHs1 with (1:=H7).
    specialize (FQU_subset_FQUC e2); specialize (FQU_subset_FQUC e4);
    specialize (FQU_subset_FQUC e7); intros H11 H12 H13.
    repeat split; auto; intros x H14 H15.
    + specialize H12 with (1:=H15). specialize H0 with (1:=H12); elim H0. apply H11; auto.
    + specialize H12 with (1:=H14). specialize H0 with (1:=H12); elim H0. apply H11; auto.
    + specialize H13 with (1:=H15). specialize H2 with (1:=H13); elim H2. apply H11; auto.
    + specialize H13 with (1:=H14). specialize H2 with (1:=H13); elim H2. apply H11; auto.
    + specialize H12 with (1:=H14). specialize H4 with (1:=H12); elim H4. apply H13; auto.
    + specialize H12 with (1:=H15). specialize H4 with (1:=H12); elim H4. apply H13; auto.
Qed.

Hypothesis  FQ_FUN: forall i E, abstr E ->
  FQ (Fun E) = FQ (E (Var i) ).

Hypothesis  FQ_LET: forall i E b, abstr (fun x => lambda (E x)) ->  
         (forall x, proper x ->  abstr (E x)) ->
  FQ (Let E b) = set_union eq_dec (FQ (E (Var i) (Var i))) (FQ b).

Hypothesis  FQU_LET: forall i E b, abstr (fun x => lambda (E x)) ->  
         (forall x, proper x ->  abstr (E x)) ->
  FQU (Let E b) =  (FQU (E (Var i) (Var i))) ++  (FQU b).

Theorem LL_FQ: forall  i u A IL LL, 
(forall q T, In (typeof (CON (Qvar q)) T) LL -> T = qubit)->
(forall q T, In (typeof (CON (Qvar q)) T) LL -> 
count_occ  ProgLemmas1.eq_dec LL (typeof (CON (Qvar q)) T) =1) ->
(forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
Subtypecontext IL LL IL LL ->   
seq_ i IL LL (atom_(typeof u A)) ->
(forall q, In (CON (Qvar q))  (FQ u)   <-> In (typeof (CON (Qvar q)) qubit) LL ).
Proof.
intros i. induction i. intros.
inversion H3. omega. subst.
apply memb_il with (M:=u) (T:=A) in H2.
inversion H2. apply H1 in H4.
inversion H4. destruct H6. inversion H6.
split. simpl. auto.
intros. inversion H7.  inversion H9. inversion  H9.
destruct H6. inversion H6. 
split. intros. simpl in H7. destruct H7; intuition.
inversion H7. subst. 
assert(In (typeof (CON (Qvar q)) A) [typeof (CON (Qvar q)) A]).
apply in_eq. apply H in H2. subst. apply in_eq.
intros. inversion H7. inversion H9. subst. simpl. auto.
inversion H9. inversion H6.  inversion H7. apply in_eq.
apply H1 in H8. inversion H8. destruct H9. inversion H9.
destruct H9. inversion H9.
inversion H9. inversion H10. simpl.
intuition.

intros. assert (h3:=H3). apply hastype_isterm_subctx in h3;auto.
inversion h3. inversion H6.

subst. apply STAR_LL in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

subst. apply True_LL2 in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

subst. apply False_LL2 in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.


subst. apply BOX_LL in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

subst. apply UNBOX_LL in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

subst. apply REV_LL in H3;auto. inversion H3.
subst. simpl; intuition. contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

subst. apply quantum_data_typed in H3;auto.
inversion H3. simpl in H5. split;intros.
simpl in H9. inversion H9. inversion H11. subst.
specialize H5  with (typeof (CON (Qvar q)) qubit).
destruct( ProgLemmas1.eq_dec (typeof (CON (Qvar q)) qubit)
         (typeof (CON (Qvar q)) qubit)). 
assert(In (typeof (CON (Qvar q)) qubit) LL).
rewrite  count_occ_In with (eq_dec:=ProgLemmas1.eq_dec).
omega. auto. contradict n. auto. intuition. 
auto. specialize H5  with (typeof (CON (Qvar q)) qubit).
destruct( ProgLemmas1.eq_dec (typeof (CON (Qvar i1)) qubit)
         (typeof (CON (Qvar q)) qubit)).
inversion e. subst. apply in_eq. 
symmetry  in H5. rewrite  <- count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H5.
contradict H5. auto. apply vQVAR.

subst. apply fun_typed2 in H3;auto. destruct H3.
rexists. destruct_conj. destruct H11.  destruct_conj.
inversion H13. inversion H20. subst. apply split_ident in H15.
subst. clear H20 H13. inversion H19. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H16 in H17. inversion H17. inversion H23.
apply seq_mono_cor with (k:=i) in H29;try omega.
apply IHi with (q:=q) in H29;auto.
rewrite <- FQ_FUN in H29;auto. rewrite H29.
split. intros. inversion H31. inversion H32.
auto. intros. apply in_cons. auto.
intros.  inversion H31. inversion H32.
apply H with (q:=q0). auto.
intros.  inversion H31. inversion H32.
simpl. 
destruct (ProgLemmas1.eq_dec (typeof (Var 0) x0) (typeof (CON (Qvar q0)) T)).
inversion e. apply H0 with (q:=q0). auto.
intros. inversion H31. subst. exists 0. left. auto.
apply H1 in H32. auto. 
apply subcnxt_llg;auto.
apply SubAreVal in H11. inversion H11.
inversion H31. apply sub_ref. auto. auto.

destruct_conj.
inversion H13. inversion H20. subst. apply split_ident in H15.
subst. clear H20 H13. inversion H19. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H16 in H17. inversion H17. inversion H23.
apply seq_mono_cor with (k:=i) in H29;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x0) ::  IL) in H29.
apply IHi with (q:=q) in H29;auto.
rewrite <- FQ_FUN in H29;auto. 
intros. inversion H31. 
subst. 
exists 0. left. auto.
inversion H32. exists 0. right. right. 
 exists (bang x0).  auto. 
 apply  H1 in H33. auto.
apply subcnxt_iig;auto.
apply SubAreVal in H11. inversion H11.
inversion H31. apply sub_ref. auto. exists x0. auto.
intros. inversion H31. subst. apply in_cons,in_eq.
inversion H32. subst. apply in_eq. apply in_cons,in_cons. auto.
auto.

destruct H3.
rexists. destruct_conj. destruct H11.  destruct_conj.
inversion H14. inversion H21. subst. apply split_ident in H16.
subst. clear H21 H14. inversion H20. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H16 in H17. inversion H17. inversion H23.
apply seq_mono_cor with (k:=i) in H29;try omega.
apply IHi with (q:=q) in H29;auto.
rewrite <- FQ_FUN in H29;auto. rewrite H29.
split. intros. inversion H31. inversion H32.
auto. intros. apply in_cons. auto.
intros.  inversion H31. inversion H32.
apply H with (q:=q0). auto.
intros.  inversion H31. inversion H32.
inversion H32.
intros. inversion H31. subst. exists 0. left. auto.
apply H1 in H32. auto. 
apply subcnxt_llg;auto.
apply SubAreVal in H11. inversion H11.
inversion H31. apply sub_ref. auto. auto.

destruct_conj.
inversion H14. inversion H21. subst. apply split_ident in H16.
subst. clear H21 H14. inversion H20. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H16 in H17. inversion H17. inversion H23.
apply seq_mono_cor with (k:=i) in H29;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x0) ::  IL) in H29.
apply IHi with (q:=q) in H29;auto.
rewrite <- FQ_FUN in H29;auto. 
intros. inversion H31. 
subst. 
exists 0. left. auto.
inversion H32. exists 0. right. right. 
 exists (bang x0).  auto. 
 apply  H1 in H33. auto.
apply subcnxt_iig;auto.
apply SubAreVal in H11. inversion H11.
inversion H31. apply sub_ref. auto. exists x0. auto.
intros. inversion H31. subst. apply in_cons,in_eq.
inversion H32. subst. apply in_eq. apply in_cons,in_cons. auto.
auto.

destruct H3.
rexists. destruct_conj. destruct H11.  destruct_conj.
inversion H13. inversion H20. subst. apply split_ident in H15.
subst. clear H20 H13. inversion H19. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H15 in H16. inversion H16. inversion H22.
apply seq_mono_cor with (k:=i) in H28;try omega.
apply IHi with (q:=q) in H28;auto.
rewrite <- FQ_FUN in H28;auto. rewrite H28.
split. intros. inversion H30. inversion H31.
auto. intros. apply in_cons. auto.
intros.  inversion H30. inversion H31.
apply H with (q:=q0). auto.
intros.  inversion H30. inversion H31.
simpl. 
destruct (ProgLemmas1.eq_dec (typeof (Var 0) x0) (typeof (CON (Qvar q0)) T)).
inversion e. apply H0 with (q:=q0). auto.
intros. inversion H30. subst. exists 0. left. auto.
apply H1 in H31. auto. 
apply subcnxt_llg;auto. apply bang_valid in H5.
apply sub_ref. auto. auto.

destruct_conj.
inversion H13. inversion H20. subst. apply split_ident in H15.
subst. clear H20 H13. inversion H19. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H15 in H16. inversion H16. inversion H22.
apply seq_mono_cor with (k:=i) in H28;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x0) ::  IL) in H28.
apply IHi with (q:=q) in H28;auto.
rewrite <- FQ_FUN in H28;auto. 
intros. inversion H30. 
subst. 
exists 0. left. auto.
inversion H31. exists 0. right. right. 
 exists (bang x0).  auto. 
 apply  H1 in H32. auto.
apply subcnxt_iig;auto.
apply sub_ref. auto. exists x0. auto.
intros. inversion H30. subst. apply in_cons,in_eq.
inversion H31. subst. apply in_eq. apply in_cons,in_cons. auto.
auto.

rexists. destruct_conj. destruct H11.  destruct_conj.
inversion H14. inversion H21. subst. apply split_ident in H16.
subst. clear H21 H14. inversion H20. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H15 in H16. inversion H16. inversion H22.
apply seq_mono_cor with (k:=i) in H28;try omega.
apply IHi with (q:=q) in H28;auto.
rewrite <- FQ_FUN in H28;auto. rewrite H28.
split. intros. inversion H30. inversion H31.
auto. intros. apply in_cons. auto.
intros.  inversion H30. inversion H31.
apply H with (q:=q0). auto.
intros.  inversion H30. inversion H31.
simpl. 
destruct (ProgLemmas1.eq_dec (typeof (Var 0) x0) (typeof (CON (Qvar q0)) T)).
inversion e. inversion H31. 
intros. inversion H30. subst. exists 0. left. auto.
apply H1 in H31. auto. 
apply subcnxt_llg;auto. apply bang_valid in H5.
apply sub_ref. auto. auto.



destruct_conj.
inversion H14. inversion H21. subst. apply split_ident in H16.
subst. clear H21 H14. inversion H20. 
assert(proper (Var 0)). apply proper_VAR;auto.
apply H15 in H16. inversion H16. inversion H22.
apply seq_mono_cor with (k:=i) in H28;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x0) ::  IL) in H28.
apply IHi with (q:=q) in H28;auto.
rewrite <- FQ_FUN in H28;auto. 
intros. inversion H30. 
subst. 
exists 0. left. auto.
inversion H31. exists 0. right. right. 
 exists (bang x0).  auto. 
 apply  H1 in H32. auto.
apply subcnxt_iig;auto.
apply sub_ref. auto. exists x0. auto.
intros. inversion H30. subst. apply in_cons,in_eq.
inversion H31. subst. apply in_eq. apply in_cons,in_cons. auto. auto.

contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

(*App CASE*)
-
subst. apply app_typed in H3;auto. destruct H3.
rexists. destruct_conj. inversion H11.
inversion H18. subst. apply split_ident in  H13. inversion H13.
subst. inversion H17.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
apply seq_mono_cor with (k:=i) in H21;try omega.
apply IHi with (q:=q) in H21;auto.
simpl. rewrite set_union_iff, H20,H21.
split;intros. destruct H22. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H14 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. contradict H25. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
contradict H25. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H25.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

rexists. destruct_conj. inversion H9.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.
(*Prod Case*)
- subst. apply prod_typed in H3.
destruct H3.
rexists.  destruct_conj. destruct H9;destruct_conj.
inversion H12.
inversion H19. subst. apply split_ident in  H14. inversion H14.
subst. inversion H18.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
apply seq_mono_cor with (k:=i) in H21;try omega.
apply IHi with (q:=q) in H21;auto.
simpl. rewrite set_union_iff, H20,H21.
split;intros. destruct H22. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H14 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. contradict H25. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
contradict H25. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H25.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

inversion H13.
inversion H20. subst. apply split_ident in  H15. inversion H15.
subst. inversion H19.
apply seq_mono_cor with (k:=i) in H21;try omega.
apply IHi with (q:=q) in H21;auto.
apply seq_mono_cor with (k:=i) in H22;try omega.
apply IHi with (q:=q) in H22;auto.
simpl. rewrite set_union_iff, H21,H22.
split;intros. destruct H23. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H15 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto.
intros. assert(h15:=H15).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H24. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H25.
omega. contradict H26. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto.
intros. assert(h15:=H15).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H24. 
contradict H26. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H26.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

rexists. destruct_conj. destruct H8. destruct_conj.
inversion H11.
inversion H18. subst. apply split_ident in  H13. inversion H13.
subst. inversion H17.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

destruct_conj.
inversion H12.
inversion H19. subst. apply split_ident in  H14. inversion H14.
subst. inversion H18.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
apply seq_mono_cor with (k:=i) in H21;try omega.
apply IHi with (q:=q) in H21;auto.
simpl. rewrite set_union_iff, H20,H21.
split;intros. destruct H22. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H14;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H14 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. contradict H25. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H with (q:=q0);auto.
intros. assert(h14:=H14).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H14;auto.
apply H0 with (q:=q0) in H14;auto.
assert(h14':=h14).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h14.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h14';auto.
destruct h14';inversion H23. 
contradict H25. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H25.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.
auto.
contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

(*Let Case*)
- subst. apply let_typed in H3.
rexists. destruct_conj. destruct H9.
rexists. destruct_conj. destruct H14.
inversion H11. inversion H20.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H26 in H27. inversion H27.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H32 in H33. inversion H33. inversion H38.
inversion H44. inversion H50. 
apply seq_mono_cor with (k:=i) in H56;try omega.
inversion H21. inversion H65. subst. apply split_ident in H60. subst.
apply seq_mono_cor with (k:=i) in H64;try omega.
rewrite FQ_LET with (i:=0);auto.
clear h3. assert(h3:=H3). assert(h5:=H5).
clear - IHi H H0 H1 H2 H4  h3 h5 H16 H56 H64.
apply IHi with (q:=q) in H64;auto.
apply IHi with (q:=q) in H56;auto.
rewrite set_union_iff, H56,H64.
split;intros. destruct H3. inversion H3.
inversion H5. inversion H5. inversion H6. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H16;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H16;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H16 ;auto. 
destruct H16. left. apply in_cons,in_cons;auto.
right. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H with (q:=q0);auto. 
inversion H3. inversion H5. inversion H5. inversion H6. auto.
intros. inversion H3. inversion H5. inversion H5. inversion H6.
assert(h16:=H16).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H0 with (q:=q0) in H16;auto.
assert(h16':=h16).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h16.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h16';auto.
destruct h16';inversion H7. contradict H9. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H9.
simpl. destruct (ProgLemmas1.eq_dec (typeof (Var 0) x1) (typeof (CON (Qvar q0)) T)).
inversion e. destruct (ProgLemmas1.eq_dec (typeof (Var 0) x0) (typeof (CON (Qvar q0)) T)).
inversion e.
omega. 
intros. inversion H3. exists 0. left. auto.
inversion H5. exists 0. left. auto.
apply H1 in H6;auto.
apply subcnxt_llg;auto. apply sub_ref,bang_valid;auto.
apply subcnxt_llg;auto. apply sub_ref,bang_valid;auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H with (q:=q0);auto.
intros. assert(h16:=H16).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H0 with (q:=q0) in H16;auto.
assert(h16':=h16).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h16.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h16';auto.
destruct h16';inversion H5. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
omega. 
contradict H7. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto. auto.

inversion H11. inversion H20.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H26 in H27. inversion H27.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H32 in H33. inversion H33. inversion H38.
inversion H44. inversion H50. 
apply seq_mono_cor with (k:=i) in H56;try omega.
inversion H21. inversion H65. subst. apply split_ident in H60. subst.
apply seq_mono_cor with (k:=i) in H64;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x1)
         :: is_qexp (Var 0) :: typeof (Var 0) (bang x0) :: IL) in H56.
rewrite FQ_LET with (i:=0);auto.
clear h3. assert(h3:=H3). assert(h5:=H5).
clear - IHi H H0 H1 H2 H4  h3 h5 H16 H56 H64.
apply IHi with (q:=q) in H64;auto.
apply IHi with (q:=q) in H56;auto.
rewrite set_union_iff, H56,H64.
split;intros. destruct H3.  
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H16;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H16;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H16 ;auto. 
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H with (q:=q0);auto. 
intros. assert(h16:=H16).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H0 with (q:=q0) in H16;auto.
assert(h16':=h16).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h16.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h16';auto.
destruct h16';inversion H5. contradict H7. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H7.
simpl.
omega. 
intros. inversion H3. exists 0. left. auto. 
inversion H5. exists 0.
right. right. exists (bang x1). auto.
inversion H6. 
exists 0. left. auto.
inversion H7. exists 0. right. right. exists (bang x0). auto.
apply H1 in H8;auto.
apply subcnxt_iig;auto. apply sub_ref;auto.
exists x1. auto.
apply subcnxt_iig;auto. apply sub_ref;auto.
exists x0. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H with (q:=q0);auto.
intros. assert(h16:=H16).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H16;auto.
apply H0 with (q:=q0) in H16;auto.
assert(h16':=h16).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h16.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h16';auto.
destruct h16';inversion H5. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
omega. 
contradict H7. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto. auto.
clear. intros. inversion H. subst. apply in_cons,in_eq.
inversion H0. subst. apply in_cons,in_cons,in_cons,in_eq.
inversion H1. subst. apply in_eq.
inversion H2. subst. apply in_eq.
repeat apply in_cons. auto. 
auto.

destruct_conj. destruct H11.
inversion H8. inversion H19.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H25 in H26. inversion H26.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H31 in H32. inversion H32. inversion H37.
inversion H43. inversion H49. 
apply seq_mono_cor with (k:=i) in H55;try omega.
inversion H20. inversion H64. subst. apply split_ident in H59. subst.
apply seq_mono_cor with (k:=i) in H63;try omega.
rewrite FQ_LET with (i:=0);auto.
clear h3. assert(h3:=H3). assert(h5:=H5).
clear - IHi H H0 H1 H2 H4  h3 h5 H15 H55 H63.
apply IHi with (q:=q) in H63;auto.
apply IHi with (q:=q) in H55;auto.
rewrite set_union_iff, H55,H63.
split;intros. destruct H3. inversion H3.
inversion H5. inversion H5. inversion H6. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H15 ;auto. 
destruct H15. left. apply in_cons,in_cons;auto.
right. auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto. 
inversion H3. inversion H5. inversion H5. inversion H6. auto.
intros. inversion H3. inversion H5. inversion H5. inversion H6.
assert(h15:=H15).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H7. contradict H9. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H9.
simpl. destruct (ProgLemmas1.eq_dec (typeof (Var 0) x1) (typeof (CON (Qvar q0)) T)).
inversion e. destruct (ProgLemmas1.eq_dec (typeof (Var 0) x0) (typeof (CON (Qvar q0)) T)).
inversion e.
omega. 
intros. inversion H3. exists 0. left. auto.
inversion H5. exists 0. left. auto.
apply H1 in H6;auto.
apply subcnxt_llg;auto. apply sub_ref,bang_valid;auto.
apply subcnxt_llg;auto. apply sub_ref,bang_valid;auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto.
intros. assert(h15:=H15).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H5. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
omega. 
contradict H7. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto. auto.

inversion H8. inversion H19.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H25 in H26. inversion H26.
assert(proper (Var 0)). apply proper_VAR;auto.
apply H31 in H32. inversion H32. inversion H37.
inversion H43. inversion H49. 
apply seq_mono_cor with (k:=i) in H55;try omega.
inversion H20. inversion H64. subst. apply split_ident in H59. subst.
apply seq_mono_cor with (k:=i) in H63;try omega.
apply seq_weakening_cor with (il':= is_qexp (Var 0) :: typeof (Var 0) (bang x1)
         :: is_qexp (Var 0) :: typeof (Var 0) (bang x0) :: IL) in H55.
rewrite FQ_LET with (i:=0);auto.
clear h3. assert(h3:=H3). assert(h5:=H5).
clear - IHi H H0 H1 H2 H4  h3 h5 H15 H55 H63.
apply IHi with (q:=q) in H63;auto.
apply IHi with (q:=q) in H55;auto.
rewrite set_union_iff, H55,H63.
split;intros. destruct H3.  
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H15;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H15 ;auto. 
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto. 
intros. assert(h15:=H15).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H5. contradict H7. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H7.
simpl.
omega. 
intros. inversion H3. exists 0. left. auto. 
inversion H5. exists 0.
right. right. exists (bang x1). auto.
inversion H6. 
exists 0. left. auto.
inversion H7. exists 0. right. right. exists (bang x0). auto.
apply H1 in H8;auto.
apply subcnxt_iig;auto. apply sub_ref;auto.
exists x1. auto.
apply subcnxt_iig;auto. apply sub_ref;auto.
exists x0. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H with (q:=q0);auto.
intros. assert(h15:=H15).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H15;auto.
apply H0 with (q:=q0) in H15;auto.
assert(h15':=h15).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h15.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h15';auto.
destruct h15';inversion H5. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H6.
omega. 
contradict H7. auto.
apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H2;auto.
inversion H2;auto. auto.
clear. intros. inversion H. subst. apply in_cons,in_eq.
inversion H0. subst. apply in_cons,in_cons,in_cons,in_eq.
inversion H1. subst. apply in_eq.
inversion H2. subst. apply in_eq.
repeat apply in_cons. auto. 
auto.
auto. auto. auto.

contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

(*Slet Case*)
- subst. apply sub_slet_inv in H3.
destruct H3;rexists; destruct_conj. destruct H9.
inversion H8.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

inversion H8.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

destruct H9.
inversion H8.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.

inversion H8.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
apply seq_mono_cor with (k:=i) in H20;try omega.
apply IHi with (q:=q) in H20;auto.
simpl. rewrite set_union_iff, H19,H20.
split;intros. destruct H21. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto. 
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H23.
omega. contradict H24. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. 
contradict H24. auto.
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto. auto.


contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

(*If Case*)
- subst. apply if_typed in H3.
destruct H3;rexists; destruct_conj. 
inversion H9.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
inversion H20.
apply seq_mono_cor with (k:=i) in H26;try omega.
apply IHi with (q:=q) in H26;auto.
apply seq_mono_cor with (k:=i) in H27;try omega.
apply IHi with (q:=q) in H27;auto.
simpl. rewrite set_union_iff, set_union_iff, H19,H26,H27.
assert(forall a b, a \/ b \/ a <-> b \/a); [intuition|..].
rewrite H28.
split;intros. destruct H29. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H29. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
omega. contradict H31. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H29. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
omega. contradict H31. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. contradict H23. auto. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.


inversion H9.
inversion H17. subst. apply split_ident in  H12. inversion H12.
subst. inversion H16.
apply seq_mono_cor with (k:=i) in H19;try omega.
apply IHi with (q:=q) in H19;auto.
inversion H20.
apply seq_mono_cor with (k:=i) in H26;try omega.
apply IHi with (q:=q) in H26;auto.
apply seq_mono_cor with (k:=i) in H27;try omega.
apply IHi with (q:=q) in H27;auto.
simpl. rewrite set_union_iff, set_union_iff, H19,H26,H27.
assert(forall a b, a \/ b \/ a <-> b \/a); [intuition|..].
rewrite H28.
split;intros. destruct H29. 
apply in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H13;auto.
apply in_split_or with (a:=(typeof (CON (Qvar q)) qubit)) in H13 ;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H29. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
omega. contradict H31. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H29. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
omega. contradict H31. auto.
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H with (q:=q0);auto.
intros. assert(h13:=H13).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H13;auto.
apply H0 with (q:=q0) in H13;auto.
assert(h13':=h13).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h13.
apply unique_in_split with (a:=(typeof (CON (Qvar q0)) T)) in h13';auto.
destruct h13';inversion H22. contradict H23. auto. 
rewrite count_occ_not_In with (eq_dec:=ProgLemmas1.eq_dec) in H24.
omega. 
apply subcntxt_splits with (ll1:= LL1) (ll2:=LL2) in H2;auto.
inversion H2;auto. auto.
auto.
contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

(*circ Case*)
-
subst. apply sub_Circ_inv in H3. 
destruct H3;rexists;destruct_conj;subst;simpl;intuition.
auto.
contradict H2. apply H1 in H2.
inversion H2. destruct H5. inversion H5.
destruct H5. inversion H5. inversion H5. inversion H8.

- apply H1 in H7. inversion H7.  inversion H8.
inversion H9. subst. inversion H3. inversion H6. subst.
inversion H13. inversion H20. subst. apply split_ident in H12. subst.
assert(i0=i);try omega. subst. apply IHi with (q:=q) in H18;auto.
auto. subst. inversion H13. simpl. intuition.

subst. simpl. split;intros. intuition. destruct H4.
inversion H4. intuition. subst. simpl. intuition.

inversion H9. inversion H10. subst. inversion H3. inversion H6. subst.
inversion H14. inversion H21. subst. apply split_ident in H13. subst.
assert(i0=i);try omega. subst. apply IHi with (q:=q) in H19;auto.
auto. subst. inversion H11. apply split_nil in H13. inversion H13. subst.
inversion H18. apply seq_mono_cor with (k:=i) in H21;try omega. inversion H14. subst.
apply IHi with (q:=q) in H21;auto.  

subst. simpl. split;intros. destruct H4. 
inversion H4.  subst. 
assert(In (typeof (CON (Qvar q)) A) [typeof (CON (Qvar q)) A]); try apply in_eq.
apply H in H5. subst. left. auto.
intuition. destruct H4.  inversion H4. subst. auto.
intuition. 

apply H1 in H12. inversion H12. destruct H13. inversion H13.
destruct H13. inversion H13. inversion H13. inversion H14.

inversion H10. inversion H11.
Qed.

Theorem LL_FQ_ALT_L: forall  i u A a a' IL LL LL' ll ll1, 
common_ll a a' ll LL'-> LSL.split ll LL ll1 ->
(forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
Subtypecontext IL ll IL ll ->   
seq_ i IL LL (atom_(typeof u A)) ->
(forall q, In (CON (Qvar q))  (FQ u)   <-> In (typeof (CON (Qvar q)) qubit) LL ).
Proof.
intros. apply LL_FQ with (q:=q) in H3;auto.
intros.
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H0;auto.
apply in_common_l_T with (q:=q0) (T:=T) in H;auto.
intros.
assert(h0:=H0).
apply in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H0;auto.
assert(h0':=h0).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h0.
assert(h:=H). apply in_common_l_T with (q:=q0) (T:=T) in h;auto.
subst.
apply in_common_l with (q:=q0) in H;auto. inversion H.
subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H4.
omega.
apply subcntxt_splits with (ll1:= LL) (ll2:=ll1) in H2;auto.
inversion H2;auto.
Qed.

Theorem LL_FQ_ALT_R: forall  i u A a a' IL LL LL' ll ll1, 
common_ll a a' ll LL'-> LSL.split ll ll1 LL ->
(forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
Subtypecontext IL ll IL ll ->   
seq_ i IL LL (atom_(typeof u A)) ->
(forall q, In (CON (Qvar q))  (FQ u)   <-> In (typeof (CON (Qvar q)) qubit) LL ).
intros. apply LL_FQ with (q:=q) in H3;auto.
intros.
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H0;auto.
apply in_common_l_T with (q:=q0) (T:=T) in H;auto.
intros.
assert(h0:=H0).
apply in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H0;auto.
assert(h0':=h0).
apply count_split with 
(eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h0.
assert(h:=H). apply in_common_l_T with (q:=q0) (T:=T) in h;auto.
subst.
apply in_common_l with (q:=q0) in H;auto. inversion H.
subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H4.
omega.
apply subcntxt_splits with (ll1:= ll1) (ll2:=LL) in H2;auto.
inversion H2;auto.
Qed.

