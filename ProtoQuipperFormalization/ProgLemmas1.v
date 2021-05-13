(****************************************************************
   File: ProgLemmas1.v
   Authors: Mohamend Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9

   Lemmas about atm, about equality on atm, about the Subtypecontext
   predicate, and about seq_ and prog.
   ***************************************************************)

Require Import PQAdequacy.
Require Import ProtoQuipperProg.
Require Import LSL.
Require Import ProtoQuipperSyntax.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import FunInd.
Import ListNotations.
Variable circIn: Econ -> set qexp.
Variable circOut: Econ -> set qexp.
Variable circApp: Econ -> Econ -> Econ .
Variable circNew: list qexp -> nat.
Variable circRev: nat -> nat.

Definition seq_ := PQAdequacy.seq_ circIn circOut circApp circNew circRev.
Definition prog := PQAdequacy.prog circIn circOut circApp circNew circRev.

Definition rev:=ProtoQuipperProg.rev.

(****************************************************************
   Miscellaneous lemmas about equality on type atm, contexts, etc.
  ****************************************************************)

Theorem eq_dec: forall x y:atm, {x=y}+{x<>y}.
Proof.
decide equality; decide equality; decide equality;
decide equality.
Qed.

Theorem remove_ident: forall (l:list atm) a, ~(In a l) ->
remove eq_dec a l = l.
Proof.
intros. induction l. simpl. auto.
apply not_in_cons in H. inversion H;auto.
unfold remove. case( eq_dec a a0).
intros. contradict H0. auto.
apply IHl in H1. unfold remove in H1.
rewrite H1. auto.
Qed.

Theorem count_app:forall l, forall  l1 l2 (q:atm),
      l = l1 ++ l2 ->
      count_occ eq_dec l q =
      count_occ eq_dec l1 q + count_occ eq_dec l2 q.
Proof.
  intro l. induction l;intros.
  - symmetry in H. apply app_eq_nil in H. inversion H. subst.
    simpl. auto.
  - destruct l1.
    + rewrite app_nil_l in H.
      rewrite <- H in *. simpl in *. auto.
    + inversion H. assert(h:=H2).
      apply IHl with (q:=q) in H2. simpl.
      destruct (eq_dec a0 q);rewrite <- h,H2; lia.
Qed.

Theorem rev_count:forall LL q,
    count_occ eq_dec LL q = count_occ eq_dec (List.rev LL) q.
Proof.
  intros. induction LL.
  - simpl. auto.
  - simpl.
    rewrite count_app with (l:=List.rev LL ++ [a])
                           (l1:=(List.rev LL)) (l2:=[a]); auto.
    rewrite IHLL. simpl. destruct (eq_dec a q); lia.
Qed.

Fixpoint get_L (l:list atm) (fq:set atm) :list atm :=
  match l with
    [] => []
  | x::t => if In_dec eq_dec x fq
            then x::get_L t (remove_one eq_dec fq x)
            else get_L t fq
  end.

Theorem nodup_toqlist:forall fq, NoDup fq -> NoDup (toqlist fq).
Proof.
  intros. functional induction toqlist fq;
            try apply NoDup_nil; inversion H; auto.
  apply NoDup_cons;auto.
  destruct (In_dec eq_dec (typeof (CON (Qvar x)) qubit) (toqlist t)); auto.
  apply intoqlist_infq in i. inversion i.
  inversion H4. inversion H5. subst. contradict H2. auto.
Qed.

Theorem count_app_alt: forall l1 l2 q,
    count_occ eq_dec (l1++l2) q =
    count_occ eq_dec l1 q + count_occ eq_dec l2 q.
Proof.
  intros.
  assert(l1++l2 = l1++l2);auto.
  apply count_app with (q:=q) in H. auto.
Qed.

Theorem split_get: forall  l l1 l2,
    NoDup l ->
    (forall q, count_occ eq_dec (l1++l2) q = count_occ eq_dec l q) ->
    LSL.split l (get_L l l1) (get_L l l2).
Proof.
intro l . induction l;intros.
simpl in *. apply init.
simpl. destruct (in_dec eq_dec a l1).
destruct(in_dec eq_dec a l2).
inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_In with (eq_dec:=eq_dec) in i0.
lia. contradict n. auto.
assert(forall q : atm,
     count_occ eq_dec ((remove_one eq_dec l1 a) ++ l2) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l1) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto.

apply IHl in H1. apply splitr1. auto.
inversion H. auto.

destruct(in_dec eq_dec a l2).
assert(forall q : atm,
     count_occ eq_dec (l1++(remove_one eq_dec l2 a) ) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l2) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto.
apply IHl in H1. apply splitr2. auto.
inversion H. auto.

inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n0.
lia. contradict n1. auto.
Qed.


Theorem count_getl: forall l l1 l2,
    NoDup l ->
    (forall q, count_occ eq_dec (l1++l2) q = count_occ eq_dec l q) ->
    forall q, count_occ eq_dec l1 q = count_occ eq_dec (get_L l l1) q.
Proof.
intro. induction l;intros l1 l2 H. intros. simpl in *.
specialize H0 with q. rewrite count_app_alt in H0.
lia. intro.
simpl. destruct(in_dec eq_dec a l1).
destruct(in_dec eq_dec a l2).
inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_In with (eq_dec:=eq_dec) in i0.
intros. lia. contradict n. auto.
assert(forall q : atm,
     count_occ eq_dec ((remove_one eq_dec l1 a) ++ l2) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In  with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l1) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto.

intros. apply IHl with(q:=q) in H1.
simpl. destruct (eq_dec a q).
subst. rewrite count_occ_In  with (eq_dec:=eq_dec) in i.
rewrite count_occ_remove_in in H1.  lia.
apply  count_occ_remove_nin with  (eq_dec:=eq_dec) (l:=l1) in n0.
rewrite n0 in H1. auto.
inversion H. auto.

destruct(in_dec eq_dec a l2).
assert(forall q : atm,
     count_occ eq_dec (l1++(remove_one eq_dec l2 a) ) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l2) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto. intros.
apply IHl with(q:=q) in H1. auto.
inversion H. auto.

inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n0.
intros. lia. contradict n1. auto.
Qed.


Theorem count_getr: forall l l1 l2,
    NoDup l ->
    (forall q, count_occ eq_dec (l1++l2) q = count_occ eq_dec l q) ->
    forall q, count_occ eq_dec l2 q = count_occ eq_dec (get_L l l2) q.
Proof.
intro. induction l;intros l1 l2 H. intros. simpl in *.
specialize H0 with q. rewrite count_app_alt in H0.
lia. intro.
simpl. destruct(in_dec eq_dec a l1).
destruct(in_dec eq_dec a l2).
inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_In with (eq_dec:=eq_dec) in i0.
intros. lia. contradict n. auto.
assert(forall q : atm,
     count_occ eq_dec ((remove_one eq_dec l1 a) ++ l2) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In  with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l1) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto.

intros. apply IHl with(q:=q) in H1. auto.
inversion H. auto.

destruct(in_dec eq_dec a l2).
assert(forall q : atm,
     count_occ eq_dec (l1++(remove_one eq_dec l2 a) ) q =
     count_occ eq_dec l q).
intros. rewrite count_app_alt.
destruct(eq_dec a q). subst.
rewrite count_occ_remove_in.
specialize H0 with q.
rewrite count_app_alt in H0. simpl in H0.
inversion H.
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_In with (eq_dec:=eq_dec) in i.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite H3,n in *.
destruct(eq_dec q q). lia.
contradict n0. auto. assert(n0':=n0). apply count_occ_remove_nin
with (eq_dec:=eq_dec) (l:=l2) in n0.
rewrite n0. simpl in H0. specialize H0 with q.
destruct(eq_dec a q).
contradict n0'. auto. rewrite count_app_alt in H0.
auto. intros.
apply IHl with(q:=q) in H1. auto.
simpl. destruct (eq_dec a q).
subst. rewrite count_occ_In  with (eq_dec:=eq_dec) in i.
rewrite count_occ_remove_in in H1.  lia.
apply  count_occ_remove_nin with  (eq_dec:=eq_dec) (l:=l2) in n0.
rewrite n0 in H1. auto.
inversion H. auto.

inversion H. specialize H0 with a.
rewrite count_app_alt in H0. simpl in H0.
destruct(eq_dec a a).
rewrite count_occ_not_In with  (eq_dec:=eq_dec) in H3.
subst. rewrite count_occ_not_In with (eq_dec:=eq_dec) in n.
rewrite count_occ_not_In with (eq_dec:=eq_dec) in n0.
intros. lia. contradict n1. auto.
Qed.

Theorem union_split: forall v t1 t2 LL,
    (forall q, count_occ eq_dec
                         (toqlist ((FQ (Prod (Spec v t1)
                                             (Spec (Nat.max v (newqvar (Spec v t1))) t2))))) q
               = count_occ eq_dec LL q) ->
    exists l1 l2,
      LSL.split LL l1 l2 /\
      (forall q, count_occ eq_dec (toqlist (FQ (Spec v t1))) q = count_occ eq_dec l1 q) /\
      (forall q, count_occ eq_dec
                           (toqlist (FQ (Spec (Nat.max v (newqvar (Spec v t1))) t2))) q
                 = count_occ eq_dec l2 q).
Proof.
intros.
assert(NoDup LL) as hnodup.
rewrite NoDup_count_occ' with (decA:= eq_dec).
intros. rewrite count_occ_In,<- H, <- count_occ_In in H0.
assert(NoDup (toqlist
          (FQ (Prod (Spec v t1) (Spec (Nat.max v (newqvar (Spec v t1))) t2))))).
simpl.  apply nodup_toqlist, set_union_nodup, nodup_fq.
apply nodup_fq. rewrite NoDup_count_occ' with (decA:= eq_dec)
 in H1. apply H1 in H0. rewrite <-H,H0. auto.
 simpl in H. rewrite nodup_union in H; try apply nodup_fq.
 rewrite toqlist_app,<- rev_toqlist in H.

exists (get_L LL (toqlist(FQ (Spec v t1)))).
exists (get_L LL ( (toqlist (FQ (Spec (Nat.max v (newqvar (Spec v t1))) t2))))).
split. apply split_get;auto.
intros. specialize H with q. rewrite count_app_alt,<- rev_count in *.
auto.
split. intros. apply count_getl with (q:=q)
(l2:= (toqlist (FQ (Spec (Nat.max v (newqvar (Spec v t1))) t2))));auto.
intros. specialize H with q0. rewrite count_app_alt,<- rev_count in *.
auto.
intros. apply count_getr with (q:=q)
(l1:=toqlist (FQ (Spec v t1)));auto.
intros. specialize H with q0. rewrite count_app_alt,<- rev_count in *.
auto.

intros. assert(h:= disjoint_fq (Spec v t1)  t2 a).
destruct (le_ge_dec   v   (newqvar (Spec v t1))).
apply max_r in l.
rewrite l in H0.
destruct (In_dec ProtoQuipperSyntax.eq_dec a  (FQ (Spec v t1))).
apply h in i.  contradict i. auto. auto.
assert(g':=g). apply max_l in g.
rewrite g in H0. assert(h0:=H0).
destruct (In_dec ProtoQuipperSyntax.eq_dec a  (FQ (Spec v t1))).
apply fq_all_qvar in H0. inversion H0. subst.
apply spec_gt2 in h0. apply spec_gt in i.
lia. auto.
Qed.

(****************************************************************
   Lemmas about Subtypecontext
  ****************************************************************)

Theorem spec_typing: forall v T i IL LL,
    valid T -> Subtypecontext IL LL IL LL ->
    (forall q, count_occ eq_dec (toqlist (FQ (Spec v T))) q =
               count_occ eq_dec LL q) ->
    exists j, j>= i+1 /\ seq_ j IL LL (atom_(typeof (Spec v T) T)).
Proof.
intros v T. functional induction Spec v T; intros.
assert(h1:=H1). apply count_occ_length in H1.
simpl in H1. destruct LL. inversion H1.
destruct LL.
unfold toqlist,FQ in h1.
assert(In  (typeof (CON (Qvar ( v))) qubit) [typeof (CON (Qvar ( v))) qubit]); try apply in_eq.
rewrite count_occ_In with (eq_dec:= eq_dec),h1,<- count_occ_In in H2.
inversion H2.
subst. exists (i+1). split;try lia.
 apply l_init.  inversion H3. inversion H1.

assert(h1:=H1). apply count_occ_length in H1.
simpl in H1. symmetry in H1. rewrite length_zero_iff_nil in  H1.  subst.
exists (i+1). split;try lia.
apply s_bc with [] []. apply (atom_ (is_qexp (CON STAR))).
apply starl. apply ss_init. apply ss_init. inversion H.

apply union_split in H1. inversion H1.
inversion H2. inversion H3. inversion H5.
inversion H. apply IHq0 with (IL:=IL) (LL:=x) (i:=i) in H10;auto.
apply IHq1 with (IL:=IL) (LL:=x0) (i:=i) in H11;auto.
inversion H10. inversion H11.
inversion H12. inversion H13.
exists (x1+x2+1+1). split;try lia.
apply s_bc with (iL:=[])
 (lL:= [Conj (atom_ (typeof (Spec v t1) t1))
(atom_ (typeof (Spec (Nat.max v (newqvar (Spec v t1))) t2) t2))]).
apply (atom_ (is_qexp (CON STAR))). apply ttensorl.
inversion H. apply vTensor; apply valid_is_T;auto.
apply ss_init.
 apply ss_general with (lL2:=LL) (lL3:=[]).
apply split_ref. apply m_and with (LL1:=x) (LL2:=x0);auto.
apply seq_mono_cor with (j:=x1). try lia.
auto.
apply seq_mono_cor with (j:=x2). try lia.
auto. apply ss_init. apply subcntxt_splits_alt with (il:=IL) in H4;auto.
inversion H4. auto.
apply subcntxt_splits_alt with (il:=IL) in H4;auto.
inversion H4. auto.
inversion H. inversion H. inversion H.
Qed.

Theorem subtypecontext_strengthen: forall i, forall a IL IL' LL LL',
  Subtypecontext  IL' LL' IL LL ->
  seq_ i IL [] (atom_ (is_qexp a)) -> seq_ (i+1) IL' [] (atom_ (is_qexp a )).
Proof.
intro i. generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall a IL IL' LL LL', Subtypecontext  IL' LL' IL LL ->
     seq_ i IL [] (atom_ (is_qexp a)) ->
     seq_ (i+1) IL' [] (atom_ (is_qexp a)))).
intro H'.
apply H'; clear H' i; auto.
intros n indr a IL IL' LL LL'  H0  H5.
inversion H5.
(* s_bc case *)
inversion H1; subst;
  [apply s_bc with [] []; auto;
   repeat apply ss_init.. | idtac|idtac|idtac|idtac|idtac|idtac|idtac];
  inversion H2; apply split_nil in H4; inversion H4.
- rewrite H13 in H11. inversion H11.
  apply s_bc with [] [All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x))))];auto.
  + apply ss_general with [] [] .
    { apply init. }
    { apply s_all. intros x H20. apply H19 in H20. apply i_imp. inversion H20.
      apply indr with (IL:=is_qexp x :: IL) (LL:=LL) (LL':=LL');auto; try lia.
      apply subcnxt_q;auto. }
    { repeat apply ss_init. }
  + apply ss_init.
- rewrite H12 in H10. inversion H10.
  apply s_bc with [] [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { apply a_and;auto.
      { apply indr with IL LL LL';auto. lia. }
      { apply indr with IL LL LL';auto. lia. }}
    { apply ss_init. }
  + apply ss_init.
- rewrite H12 in H10. inversion H10.
  apply s_bc with [] [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { apply a_and;auto.
      { apply indr with IL LL LL';auto. lia. }
      { apply indr with IL LL LL';auto. lia. }}
    { apply ss_init. }
  + apply ss_init.
- rewrite H14 in H12.
  apply s_bc with [] [
           (All
              (fun x : qexp =>
               All
                 (fun y : qexp =>
                  Imp (is_qexp x) (Imp (is_qexp y) (atom_ (is_qexp (E x y)))))))
           ;(atom_ (is_qexp b0))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { inversion H12.
      apply s_all. intros. apply H20 in H21. inversion H21.
      apply s_all. intros. apply H26 in H27. inversion H27.
      inversion H32. repeat apply i_imp.
      apply indr with (is_qexp x0 :: is_qexp x :: IL) LL LL';auto; try lia.
      repeat apply subcnxt_q;auto. }
    { apply ss_general with [][];auto.
      { apply init. }
      { inversion H13. inversion H23. subst. apply split_ident in H18.
        { subst.  apply indr with IL LL LL';auto.
          lia.  }
        { auto. }}
      { apply ss_init. }}
  + apply ss_init.
- rewrite H12 in H10. inversion H10.
  apply s_bc with [] [And (atom_ (is_qexp E)) (atom_ (is_qexp b0))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { apply a_and;auto.
      { apply indr with IL LL LL';auto. lia. }
      { apply indr with IL LL LL';auto. lia. }}
    { apply ss_init. }
  + apply ss_init.
- rewrite H12 in H10. inversion H10.
  inversion H20.
  apply s_bc with [] [(And (atom_ (is_qexp b0))
           (And (atom_ (is_qexp a1)) (atom_ (is_qexp a2))))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { apply a_and;auto.
      { apply indr with IL LL LL';auto; try lia.
        subst. auto. }
      { apply a_and;auto.
        { apply indr with IL LL LL';auto. lia. }
        { apply indr with IL LL LL';auto. lia. }}}
    { apply ss_init. }
  + apply ss_init.
- rewrite H13 in H11.
  apply s_bc with [] [toimpexp (FQ a0) (atom_ (is_qexp a0))];auto.
  + apply ss_general with [] [].
    { apply init. }
    { assert (H11':=H11). apply toimpexp_ilength in H11'.
      { apply move_to_il in H11;auto.
        { apply indr with (IL':= List.rev (toiqlist (FQ a0)) ++ IL')
                          (LL:=LL) (LL':=LL') in H11;auto.
          { apply move_from_il in H11;auto.
            { assert (length (FQ a0) <=
                      i-> i - length (FQ a0) + 1 + length (FQ a0) = i+1); try lia.
              rewrite <- H15;auto. }
            { apply fq_all_qvar. }}
          { lia. }
          { apply rev_qlist_subcnxt;auto. }}
        { apply fq_all_qvar. }}
      { apply fq_all_qvar. }}
    { apply ss_init. }
  + apply ss_init.
(* context case *)
- apply qexp_inIL with (a:=a) in H0;auto.
  apply i_init;auto.
Qed.

Theorem subtypecontext_subtyping: forall i,
  forall a IL IL' LL LL' B A,
  Subtypecontext  IL' LL' IL LL  ->
  seq_ (i) IL LL (atom_ (typeof a A)) ->
  Subtyping  A B ->
  seq_ (i+1+1) IL' LL' (atom_ (typeof a  B)).
Proof.
intro i. generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall a IL IL' LL LL' B A,
       Subtypecontext  IL' LL' IL LL ->
       seq_ (i) IL LL (atom_ (typeof a A)) ->
       Subtyping  A B->
       seq_ (i+1+1) IL' LL' (atom_ (typeof a  B)))).
intro H'.
apply H'; clear H' i; auto.
intros n indr a IL IL' LL LL' B A H0 H5 H7.
inversion H5.
- (* s_bc case *)
  inversion H1;  subst.
  + inversion H8.
    inversion H13.  subst.  apply split_ident in H4;auto.
    rewrite <- H4 in H12.
    apply s_bc with [atom_ (typeof a A)] [atom_ (is_qexp a)];auto.
    * apply axc1;auto. apply sub_not_bang with A1;auto.
    * apply ss_general with [] [].
      apply init.
      inversion H2.
        apply split_nil in H6. inversion H6. rewrite H18 in H16.
        apply subtypecontext_strengthen with IL LL LL';auto.
        apply seq_mono_cor with i;auto; try lia.
      apply ss_init.
    * apply ss_general with LL' [].
      apply split_ref.
      apply indr with IL LL A1; auto;try lia.
      apply ss_init.
  + inversion H8.  subst.  assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    assert (H7':=H7). apply sub_bang_ornot in H7'.
    destruct H7'.
    * apply s_bc with  [atom_ (typeof a A)] [atom_ (is_qexp a)];auto.
      apply axc1;auto.
      apply ss_general with [] [].
        apply init.
        inversion H2.
          apply split_nil in H4. inversion H4. rewrite H14 in H11.
          inversion H11.
          apply subtypecontext_strengthen with IL [] [];auto. apply  seq_mono_cor with i1;auto.
          lia.
        apply ss_init.
      apply ss_general with [] [].
        apply init.
        inversion H2. apply split_nil in H4.
          inversion H4. subst.
          apply indr with IL [] (bang A1); auto;try lia.
          inversion H11. apply  seq_mono_cor with i0;auto.
          lia.
          apply ss_init.
    * inversion H. subst.
      apply s_bc with  [] [And (atom_ (typeof a (bang x)))(atom_ (is_qexp a))];auto.
      apply axc2;auto.
      apply ss_general with [] [].
        apply init.
        inversion  H2. apply split_nil in H4.
          inversion H4. subst. inversion H11.
          apply a_and;auto.
          apply indr with IL [] (bang A1); auto;try lia.
          apply subtypecontext_strengthen with IL [] [];auto.
            apply seq_mono_cor with i0;auto; try lia.
        apply ss_init.
      apply ss_init.
  + apply Subtyping_Prop1_one in H7.
    subst. inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto; apply ss_init.
  + apply Subtyping_bang_one in H7. destruct H7.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply starl.
      apply ss_init.
      apply ss_init.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply ss_init.
      apply ss_init.
  + apply Subtyping_Prop1_bool in H7.
    subst. inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto; apply ss_init.
  + apply Subtyping_bang_bool in H7. destruct H7.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply truel.
      apply ss_init.
      apply ss_init.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply ss_init.
      apply ss_init.
  + apply Subtyping_Prop1_bool in H7.
    subst. inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto; apply ss_init.
  + apply Subtyping_bang_bool in H7. destruct H7.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply falsel.
      apply ss_init.
      apply ss_init.
    * subst. inversion H8. subst.
      assert(H0':=H0).
      apply inv_emptyll in H0;auto. subst.
      apply s_bc with [] [];auto.
      apply ss_init.
      apply ss_init.
  + inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto.
    * apply  box with U;auto. apply sub_trans with A;auto.
    * apply ss_init.
    * apply ss_init.
  + inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto.
    * apply  unbox with T U;auto. apply sub_trans with A;auto.
    * apply ss_init.
    * apply ss_init.
  + inversion H8. subst.
    assert(H0':=H0).
    apply inv_emptyll in H0;auto. subst.
    apply s_bc with [] [];auto.
    * apply rev with T U;auto. apply sub_trans with A;auto.
    * apply ss_init.
    * apply ss_init.
  + assert (H7':=H7). apply Subtyping_arrow_inv in H7'.
    inversion H7'. inversion H. inversion H3.
    inversion H6. subst. inversion H8. inversion H20.
    subst. apply split_ident in H14.
    * rewrite <- H14 in H19. inversion H19;auto.
      assert (H9':=H9). apply sub_bang_ornot in H9'.
      destruct H9'.
      apply s_bc with
            [All (fun y : qexp =>
                    Imp (is_qexp y)
                        (lImp (typeof y x) (atom_ (typeof (E y) x0))))] [];auto.
        apply lambda1l;auto. apply SubAreVal in H10.
          inversion H10. auto.
        apply ss_init.
        apply ss_general with LL' [].
          apply split_ref.
          apply s_all. intros. apply H18 in H22.
            inversion H22. inversion H27. apply i_imp. apply l_imp.
            apply indr with (is_qexp x1::IL) (typeof x1 T1 :: LL) T2;auto.
            lia.
            apply subcnxt_llg;auto.
          apply ss_init.
      inversion H21. rewrite H22.
        apply s_bc with
            [All (fun y : qexp =>
                    Imp (is_qexp y)
                        (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))] [];auto.
        apply lambda1i;auto.
          apply SubAreVal in H9.
            inversion H9. subst. auto.
          apply SubAreVal in H10.
            inversion H10. subst. auto.
        apply ss_init.
        apply ss_general with LL' [].
          apply split_ref.
          apply s_all. intros. apply H18 in H23.
            inversion H23. inversion H28. repeat apply i_imp.
            apply seq_weakening_cor with (is_qexp x2::typeof x2 (bang x1)  :: IL').
            apply indr with (is_qexp x2::IL) (typeof x2 T1 :: LL)  T2;auto.
              lia.
              apply subcnxt_lig;auto.
                exists x1;auto.
                subst. auto.
            intros. inversion H36.
              subst. apply in_cons,in_eq.
              inversion H37.
                subst. apply in_eq.
                repeat apply in_cons;auto.
          apply ss_init.
    * apply ([typeof (Var 0) T1]).
  + assert (H7':=H7). apply Subtyping_arrow_inv in H7'.
    inversion H7'. inversion H. inversion H3.
    inversion H6. subst.
    assert (H9':=H9).
    apply Subtyping_bang_inv  in H9.  inversion H9.
    inversion H4. subst.
    inversion H8. inversion H22.
    subst. apply split_ident in H17.
    * rewrite <- H17 in H21. inversion H21;auto.
      apply s_bc with
          [All (fun y : qexp =>
                  Imp (is_qexp y)
                      (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))] [];auto.
      apply lambda1i;auto.
        apply SubAreVal in H9'.
          inversion H9'. auto.
        apply SubAreVal in H10.
          inversion H10. auto.
      apply ss_init.
      apply ss_general with LL' [].
        apply split_ref.
        apply s_all. intros. apply H20 in H23.
          inversion H23. inversion H28. repeat apply i_imp.
          apply seq_weakening_cor with (is_qexp x::typeof x (bang x1)  :: IL').
          apply indr with (is_qexp x::typeof x (bang T1) ::  IL) LL T2;auto.
            lia.
            apply subcnxt_iig;auto. exists T1. auto.
            apply seq_weakening_cor with (typeof x (bang T1)::is_qexp x  :: IL).
              auto.
              intros. inversion H36.
                subst. apply in_cons,in_eq.
                inversion H37.
                  subst. apply in_eq.
                  repeat apply in_cons;auto.
          intros. inversion H36.
            subst. apply in_cons,in_eq.
            inversion H37.
              subst. apply in_eq.
              repeat apply in_cons;auto.
        apply ss_init.
      * apply ([typeof (Var 0) T1]).
  + inversion H7.
    * assert(H3':=H3).  apply Subtyping_arrow_inv in H3'.
      inversion H3'. inversion H9. inversion H10.
      inversion H14. assert (H16':=H16).
      apply Subtyping_bang_inv  in H16.  inversion H16.
      inversion H18. subst.
      inversion H8. subst. inversion H2.
      inversion H24. apply split_nil in H13.
      inversion H13. subst.
      inversion H23.
      apply s_bc with
          [All (fun y : qexp =>
                  Imp (is_qexp y)
                      (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))] [];auto.
      apply lambda1i;auto.
        apply SubAreVal in H16'.
          inversion H16'. auto.
        apply SubAreVal in H17.
          inversion H17. auto.
      apply ss_init.
      assert(H0':=H0).
        apply inv_emptyll in H0;auto. subst.
        apply ss_general with [] [].
        apply init.
        apply s_all. intros. apply H22 in H.
          inversion H. inversion H25. repeat apply i_imp.
          apply seq_weakening_cor with (is_qexp x::typeof x (bang x1):: IL').
          apply indr with ( is_qexp x::typeof x (bang T1) :: IL) [] T2;auto.
            lia.
            apply subcnxt_iig;auto. exists T1. auto.
            apply seq_weakening_cor with (typeof x (bang T1)::is_qexp x:: IL).
              auto.
              intros. inversion H34.
                subst. apply in_cons,in_eq.
                inversion H35.
                  subst. apply in_eq.
                  repeat apply in_cons;auto.
          intros. inversion H34.
            subst. apply in_cons,in_eq.
            inversion H35.
              subst. apply in_eq.
              repeat apply in_cons;auto.
        apply ss_init.
    * assert(H3':=H3).  apply Subtyping_arrow_inv in H3'.
      inversion H3'. inversion H9. inversion H10.
      inversion H14. assert (H16':=H16).
      apply Subtyping_bang_inv  in H16.  inversion H16.
      inversion H18. subst.
      inversion H8. subst. inversion H2.
      inversion H24. apply split_nil in H13.
      inversion H13. subst.
      inversion H23.
      apply s_bc with
          []
          [All (fun y : qexp =>
                  Imp (is_qexp y)
                      (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))];auto.
      apply lambda2i;auto.
        apply SubAreVal in H16'.
          inversion H16'. auto.
        apply SubAreVal in H17.
          inversion H17. auto.
      apply ss_general with [] [].
        apply init.
        apply s_all. intros. apply H22 in H25.
          inversion H25. inversion H31. repeat apply i_imp.
          apply seq_weakening_cor with (is_qexp x::typeof x (bang x1):: IL').
          apply indr with ((is_qexp x):: typeof x (bang T1) ::IL) [] T2;auto.
            lia.
            apply subcnxt_iig;auto.
              exists T1. auto.
              assert(H0':=H0).
                apply inv_emptyll in H0;auto. subst. auto.
            apply seq_weakening_cor with (typeof x (bang T1)::is_qexp x:: IL).
              auto.
              intros. inversion H39.
                subst. apply in_cons,in_eq.
                inversion H40.
                  subst. apply in_eq.
                  repeat apply in_cons;auto.
          intros. inversion H39.
            subst. apply in_cons,in_eq.
            inversion H40.
              subst. apply in_eq.
              repeat apply in_cons;auto.
        apply ss_init.
      apply inv_emptyll in H0;auto. subst. auto.
        apply ss_init.
  + inversion H7.
    * assert(H3':=H3).  apply Subtyping_arrow_inv in H3'.
      inversion H3'. inversion H9. inversion H10.
      inversion H14. assert (H16':=H16).
      apply sub_bang_ornot in H16'.
      destruct H16'.
      inversion H8. subst.
        assert(H0':=H0).
        apply inv_emptyll in H0;auto. subst.
        apply s_bc with
            [All (fun y : qexp =>
                    Imp (is_qexp y)
                        (lImp (typeof y x) (atom_ (typeof (E y) x0))))] [];auto.
        apply lambda1l;auto. apply SubAreVal in H17.
          inversion H17. auto.
        apply ss_init.
        apply ss_general with [] [].
          apply init.
          apply s_all. intros. inversion H2.
            inversion H22. apply H28 in H.
            apply split_nil in H13. inversion H13. subst.
            inversion H. inversion H21. apply i_imp.  apply l_imp.
            apply indr with (is_qexp x1::IL) [typeof x1 T1] T2;auto.
            lia.
            apply subcnxt_llg;auto.
          apply ss_init.
      inversion H18. subst.  inversion H8. subst. inversion H2.
        inversion H22. apply split_nil in H13.
        inversion H13. subst.
        inversion H22.
        apply s_bc with
            [All (fun y : qexp =>
                    Imp (is_qexp y)
                        (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))] [];auto.
        apply lambda1i;auto.
          apply SubAreVal in H16.
            inversion H16. auto.
          apply SubAreVal in H17.
            inversion H17. auto.
        apply ss_init.
        assert(H0':=H0).
          apply inv_emptyll in H0;auto. subst.
          apply ss_general with [] [].
          apply init.
          apply s_all. intros. apply H21 in H0.
            inversion H0. inversion H25.  repeat  apply i_imp.
            apply seq_weakening_cor with (is_qexp x::typeof x (bang x1):: IL').
            apply indr with (is_qexp x::IL)  [typeof x T1]  T2;auto.
              lia.
              apply subcnxt_lig;auto.
            intros. inversion H34.
              subst. apply in_cons,in_eq.
              inversion H35.
                subst. apply in_eq.
                repeat apply in_cons;auto.
          apply ss_init.
      * assert(H3':=H3).  apply Subtyping_arrow_inv in H3'.
        inversion H3'. inversion H9. inversion H10.
        inversion H14. inversion H8. subst.
        assert(H0':=H0).
        apply inv_emptyll in H0;auto. subst.
        inversion H2.
        apply split_nil in H6.
        inversion H6. subst.
        assert (H16':=H16).
        apply sub_bang_ornot in H16'.
        destruct H16'.
        apply s_bc with
              []
              [All (fun y : qexp =>
                      Imp (is_qexp y)
                          (lImp (typeof y x) (atom_ (typeof (E y) x0))))];auto.
          apply lambda2l;auto. apply SubAreVal in H17.
            inversion H17. auto.
          apply ss_general with [] [].
            apply init.
            apply s_all. intros. inversion H20.  apply H23 in H0.
              inversion H0. inversion H28. apply i_imp. apply l_imp.
              apply indr with (is_qexp x1::IL) [typeof x1 T1] T2;auto.
              lia.
              apply subcnxt_llg;auto.
            apply ss_init.
          apply ss_init.
          inversion H. subst.
            apply s_bc with
                []
                [All (fun y : qexp =>
                        Imp (is_qexp y)
                            (Imp (typeof y (bang x1)) (atom_ (typeof (E y) x0))))];auto.
            apply lambda2i;auto.
              apply SubAreVal in H16.
                inversion H16. auto.
              apply SubAreVal in H17.
                inversion H17. auto.
            apply ss_general with [] [].
              apply init.
              apply s_all. intros. inversion H20.  apply H23 in H0.
                inversion H0. inversion H28. repeat apply i_imp.
                apply seq_weakening_cor with (is_qexp x::typeof x (bang x1):: IL').
                apply indr with (is_qexp x::IL) [typeof x T1] T2;auto.
                  lia.
                  apply subcnxt_lig;auto.
                intros. inversion H36.
                  subst. apply in_cons,in_eq.
                  inversion H37.
                    subst. apply in_eq.
                    repeat apply in_cons;auto.
              apply ss_init.
            apply ss_init.
  + inversion H8. inversion H12. subst. apply split_ident in H4.
    * rewrite <- H4 in H11. inversion H11.
      apply s_bc with
          [Conj (atom_ (typeof E1 (arrow T' B))) (atom_ (typeof E2 T'))] [];auto.
      { apply tap;auto. inversion H13. apply vArrow;auto.
        apply SubAreVal in H7. inversion H7. auto. }
      { apply ss_init. }
      { assert(H0':=H0).
        apply subcnxt_split with (ll1:=LL1) (ll2:=LL2) in H0'.
        { inversion H0'.   inversion H17.
          inversion H18. inversion H19. inversion H20.
          inversion H22. inversion H24.
          inversion H26. inversion H28. inversion H30.
          inversion H32. inversion H34.
          apply ss_general with LL' [].
          { apply split_ref. }
          { subst. apply m_and with (LL1:=x1) (LL2:=x2);auto.
            { apply indr with x LL1 (arrow T' A);auto.
              { lia.  }
              { apply seq_weakening_cor with IL;auto. }
              { apply ArrowSub;auto. apply sub_ref. inversion H13;auto. }}
            { apply indr with x0 LL2 (T');auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }
              { apply sub_ref. inversion H13;auto. }}}
          { apply ss_init. }}
        { auto. }}
    * auto.
  + inversion H8. inversion H12. subst. apply split_ident in H4.
    * rewrite <- H4 in H11. inversion H11. inversion H7.
      apply s_bc with
          [Conj (atom_ (typeof E1 B1)) (atom_ (typeof E2 B2))] [];auto.
      { apply ttensorl;auto. subst.
        apply SubAreVal in H7. inversion H7. auto. }
      { apply ss_init. }
      { assert(H0':=H0).
        apply subcnxt_split with (ll1:=LL1) (ll2:=LL2) in H0'.
        { inversion H0'.  inversion H22.
          inversion H23. inversion H24. inversion H25.
          inversion H27. inversion H29. inversion H31.
          inversion H33. inversion H35.
          inversion H37. inversion H39.
          apply ss_general with LL' [].
          { apply split_ref. }
          { subst. apply m_and with (LL1:=x1) (LL2:=x2);auto .
            { apply indr with x LL1 T;auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }}
            { apply indr with x0 LL2 T';auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }}}
          { apply ss_init. }}
        { auto. }}
    * auto.
  + inversion H8. inversion H13. subst. apply split_ident in H4.
    * rewrite <- H4 in H12. inversion H12. inversion H7.
      { inversion H19.
        apply s_bc with
            [Conj (atom_ (typeof E1 B2)) (atom_ (typeof E2 B3))] [];auto.
        { apply ttensorl;auto. subst.
          apply SubAreVal in H7. inversion H7. auto. }
        { apply ss_init. }
        { assert(H0':=H0).
          apply subcnxt_split with (ll1:=LL1) (ll2:=LL2) in H0';auto.
          inversion H0'.   inversion H27.
          inversion H28. inversion H29. inversion H30.
          inversion H32. inversion H34. inversion H36.
          inversion H38. inversion H40. inversion H42.
          inversion H44.  apply ss_general with LL' [].
          { apply split_ref. }
          { subst. apply m_and with (LL1:=x1) (LL2:=x2);auto.
            { apply indr with x LL1 (bang T);auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }
              { apply sub_trans with T;auto. apply Prop2_14;auto. }}
            { apply indr with x0 LL2 (bang T');auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }
              { apply sub_trans with T';auto. apply Prop2_14;auto. }}}
          { apply ss_init. }}}
      { auto.
        inversion H19.
        apply s_bc with
            [Conj (atom_ (typeof E1 (bang B2))) (atom_ (typeof E2 (bang B3)))] [];auto.
        { apply ttensori;auto. apply sub_not_bang in H24;auto.
          apply sub_not_bang in H26;auto.  }
        { apply ss_init. }
        { assert(H0':=H0).
          apply subcnxt_split with (ll1:=LL1) (ll2:=LL2) in H0';auto.
          inversion H0'.  inversion H27.
          inversion H28. inversion H29. inversion H30.
          inversion H32. inversion H34. inversion H36.
          inversion H38. inversion H40. inversion H42.
          inversion H44. apply ss_general with LL' [].
          { apply split_ref. }
          { subst. apply m_and with (LL1:=x1) (LL2:=x2);auto.
            { apply indr with x LL1 (bang T);auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }
              { apply BangSub2;auto. }}
            { apply indr with x0 LL2 (bang T');auto.
              { lia. }
              { apply seq_weakening_cor with IL;auto. }
              { apply BangSub2;auto. }}}
          { apply ss_init. }}}
    * auto.
  + inversion H8. inversion H14.
    apply s_bc with
        [(All (fun x : qexp =>
                 (All (fun y:qexp =>
                         Imp (is_qexp x)
                             (Imp (is_qexp y)
                                  (lImp (typeof x T1)
                                        (lImp (typeof y T2) (atom_ (typeof (E x y) B)))))))));
         atom_ (typeof b0 (tensor T1 T2))] [];auto.
    * apply tletl;auto.
    * apply ss_init.
    * assert(H0':=H0).
      apply subcnxt_split   with (ll1:=lL2) (ll2:=lL3) in H0';auto.
      inversion H0'. inversion H22. inversion H23. inversion H24.
      inversion H25. inversion H27. inversion H29. inversion H31.
      apply ss_general with x1 x2;auto.
      { apply s_all. intros.  apply  H21 in H34.
        inversion H34. apply s_all. intros.  apply H39 in H40.
        inversion H40. inversion H45. inversion H51. inversion H57.
        repeat apply i_imp. repeat apply l_imp.
        apply seq_weakening_cor with (il':=is_qexp x4 :: is_qexp x3::x) in H63;auto.
        { apply indr with (IL:=is_qexp x4 :: is_qexp x3::x)
                          (LL:=typeof x4 T2 :: typeof x3 T1 :: lL2) (A:=A);auto.
          { lia. }
          { apply subcnxt_llg;auto.
            { apply sub_ref;apply isval_bang_val;auto. }
            { apply subcnxt_llg;auto.
              apply sub_ref;apply isval_bang_val;auto. inversion H33.
              inversion H66. inversion H68. inversion H70. auto. }}}
        { intros. inversion H65.
          { subst.
            apply in_eq. }
          { inversion H66.
            { subst. apply in_cons. apply in_eq. }
            { repeat apply in_cons. auto. }}}}
      { apply ss_general with x2[];auto.
        { apply split_ref. }
        { inversion H15. inversion H41. subst. apply split_ident in H36;auto. subst.
          apply seq_weakening_cor with (il':=x0) in H40;auto.
          apply indr with (IL:=x0) (LL:=lL4) (A:= tensor T1 T2);auto.
          { lia. }
          { inversion H33. inversion H3. inversion H9. inversion H17.
            auto. }
          { apply sub_ref;apply vTensor; apply isval_bang_val;auto. }}
        { apply ss_init. }}

  + inversion H8. inversion H14.
    apply s_bc with
        [(All (fun x : qexp =>
                 (All( fun y:qexp =>
                         Imp (is_qexp x)
                             (Imp (is_qexp y)
                                  (Imp (typeof x (bang T1))
                                       (Imp (typeof y (bang T2))
                                            (atom_ (typeof (E x y) B)))))))));
         atom_ (typeof b0 (bang (tensor T1 T2)))] [];auto.
    * apply tleti;auto.
    * apply ss_init.
    * assert(H0':=H0).
      apply subcnxt_split   with (ll1:=lL2) (ll2:=lL3) in H0';auto.
      inversion H0'. inversion H22. inversion H23. inversion H24.
      inversion H25. inversion H27. inversion H29. inversion H31.
      apply ss_general with x1 x2;auto.
      { apply s_all. intros.  apply  H21 in H34.
        inversion H34. apply s_all. intros.  apply H39 in H40.
        inversion H40. inversion H45. inversion H51. inversion  H57.
        repeat apply i_imp.
        apply seq_weakening_cor
          with (is_qexp x4 ::typeof x4 (bang T2) :: is_qexp x3 ::typeof x3 (bang T1):: IL');auto.
        { apply indr with
              (IL:=is_qexp x4::typeof x4 (bang T2)::is_qexp x3::typeof x3 (bang T1)::x)
              (LL:=lL2) (A:=A);auto.
          { lia. }
          { repeat apply subcnxt_iig;auto.
            { apply sub_ref;auto. }
            { exists T2.  auto. }
            { apply sub_ref;auto. }
            { exists T1. auto. }
            { inversion H33.
              inversion H66. inversion H68. inversion H70. auto. }}
          { apply seq_weakening_cor
              with (typeof x4 (bang T2)::typeof x3 (bang T1)::is_qexp x4 ::is_qexp x3 ::IL);auto.
            intros. inversion H65.
            { subst. apply in_cons,in_eq. }
            { inversion H66.
              { subst. apply in_cons,in_cons,in_cons,in_eq. }
              { inversion H67.
                { subst. apply in_eq. }
                { inversion H68.
                  { subst. apply in_cons,in_cons,in_eq. }
                  { repeat apply  in_cons;auto. }}}}}}
        { intros. inversion H65.
          { subst. apply in_cons,in_cons,in_eq. }
          { inversion H66.
            { subst. apply in_eq. }
            { inversion H67.
              { subst. apply in_cons,in_cons,in_cons,in_eq. }
              { inversion H68.
                { subst. apply in_cons,in_eq. }
                { repeat apply  in_cons;auto. }}}}}}
      { apply ss_general with x2[];auto.
        { apply split_ref. }
        { inversion H15. inversion H41. subst. apply split_ident in H36;auto. subst.
          apply seq_weakening_cor with (il':=x0) in H40;auto.
          apply indr with (IL:=x0) (LL:=lL4) (A:= bang(tensor T1 T2));auto.
          { lia. }
          { inversion H33. inversion H3. inversion H9.
            inversion H17. auto. }
          { apply sub_ref;apply bTensor; apply isval_bang_val;auto. }}
        { apply ss_init. }}
  + inversion H8. inversion H12. subst. apply split_ident in H4.
    * rewrite <- H4 in H11.
      apply s_bc with
          [Conj (atom_ (typeof E B))  (atom_ (typeof b0 one))] [];auto.
      { apply tsletl;auto. apply SubAreVal in H7.
        inversion H7. auto. }
      { apply ss_init. }
      { assert(H0':=H0). inversion H11.
        apply subcnxt_split   with (ll1:=LL1) (ll2:=LL2) in H0';auto.
        inversion H0'.  inversion H17.
        inversion H18. inversion H19. inversion H20.
        inversion H22. inversion H24.
        inversion H26. inversion H28. inversion H30.
        inversion H32. inversion H34.
        apply ss_general with LL' [];auto.
        { apply split_ref. }
        { apply m_and  with (LL1:=x1) (LL2:=x2);auto.
          { apply seq_weakening_cor with (il':=x) in H15;auto.
            apply indr with (IL:=x) (LL:=LL1) (A:=A);auto.
            lia. }
          { apply seq_weakening_cor with (il':=x0) in H16;auto.
            apply indr with (IL:=x0) (LL:=LL2) (A:= one);auto.
            { lia. }
            { apply OneSub. }}}
        { apply ss_init. }}
      * auto.
  + inversion H8. inversion H12. subst. apply split_ident in H4.
    * rewrite <- H4 in H11.
      apply s_bc with
          [Conj (atom_ (typeof E B))  (atom_ (typeof b0 (bang one)))] [];auto.
      { apply tsleti;auto. apply SubAreVal in H7.
        inversion H7. auto. }
      { apply ss_init. }
      { assert(H0':=H0). inversion H11.
        apply subcnxt_split   with (ll1:=LL1) (ll2:=LL2) in H0';auto.
        inversion H0'.  inversion H17.
        inversion H18. inversion H19. inversion H20.
        inversion H22. inversion H24.
        inversion H26. inversion H28. inversion H30.
        inversion H32. inversion H34.
        apply ss_general with LL' [];auto.
        { apply split_ref. }
        { apply m_and with (LL1:=x1) (LL2:=x2);auto.
          { apply seq_weakening_cor with (il':=x) in H15;auto.
            apply indr with (IL:=x) (LL:=LL1) (A:=A);auto.
            lia. }
          { apply seq_weakening_cor with (il':=x0) in H16;auto.
            apply indr with (IL:=x0) (LL:=LL2) (A:= bang one);auto.
            { lia. }
            { apply BangSub2.
              { apply OneSub. }
              { apply bOne. }}}}
        { apply ss_init. }}
      * auto.
  + inversion H8. inversion H13. subst. apply split_ident in H4.
    * rewrite <- H4 in H12.
      apply s_bc with
          [Conj (atom_ (typeof b0 bool))
                (And (atom_ (typeof a1 B)) (atom_(typeof a2 B)))] [];auto.
      { apply tif;auto. apply SubAreVal in H7.
        inversion H7. auto. }
      { apply ss_init. }
      { assert(H0':=H0). inversion H12.
        apply subcnxt_split   with (ll1:=LL1) (ll2:=LL2) in H0';auto.
        inversion H0'.
        inversion H18. inversion H19. inversion H20.
        inversion H21. inversion H23.
        inversion H25. inversion H27. inversion H29.
        inversion H31. inversion H33. inversion H35.
        apply ss_general with LL' [];auto.
        { apply split_ref. }
        { apply m_and with (LL1:=x1) (LL2:=x2);auto.
          { apply seq_weakening_cor with (il':=x) in H16;auto.
            apply indr with (IL:=x) (LL:=LL1) (A:=bool);auto.
            { lia. }
            { apply BoolSub. }}
          { inversion H17. apply a_and;auto.
            { apply seq_weakening_cor with (il':=x0) in H43;auto.
              apply indr with (IL:=x0) (LL:=LL2) (A:= A);auto.
              lia. }
            { apply seq_weakening_cor with (il':=x0) in H44;auto.
              apply indr with (IL:=x0) (LL:=LL2) (A:= A);auto.
              lia.  }}}
        { apply ss_init. }}
    * auto.
  + inversion H2. apply split_nil in H4.
    inversion H4. subst. inversion H8.  subst. assert(H0':= H0).
    apply  inv_emptyll in H0.  subst.
    auto. assert(H7':=H7). apply Subtyping_circ_inv in H7'.
    inversion H7'. inversion H. inversion H0. inversion H6.
    subst. inversion H14. inversion H16.
    apply valid_sub_eq in H9;auto.
    * subst. assert(H21':=H21).
      apply toimp_ilength in H21'; try apply fq_all_qvar.
      assert(H22':=H22).
      apply toimp_ilength in H22'; try apply fq_all_qvar.
      apply  move_to_ll in H21; try apply fq_all_qvar.
      apply  move_to_ll in H22; try apply fq_all_qvar.
      apply s_bc with []
                      [And (toimp (FQ a0) (atom_(typeof a0 x0)))
                           ((toimp (FQ t) (atom_(typeof t T))))];auto.
      { apply tCricl;auto. apply SubAreVal in H7.
        inversion H7. auto. }
      { apply ss_general with [] [];auto.
        { apply init. }
        { apply a_and;auto.
          { apply indr with (IL':=(List.rev (toiqlist (FQ a0)))++IL')
                            (LL':=(List.rev (toqlist (FQ a0))))
                            (B:=x0) in H21;auto;try lia.
            { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ a0)))) in H21.
              apply move_from_ll with (LL:=[])in H21;try apply fq_all_qvar.
              assert(forall i j, j+j<=i -> i- j-j+ 1 +1+ j +j= i +1+1).
              { intros. lia. }
              { rewrite H3 in H21;try lia. auto. }}
            { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
              apply subcnxt_add;auto. }}
          { apply indr with (IL':=List.rev (toiqlist (FQ t))++IL')
                            (LL':=(List.rev (toqlist (FQ t))))
                            (B:=T) in H22;auto;try lia.
            { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ t)))) in H22.
              apply move_from_ll with (LL:=[])in H22;try apply fq_all_qvar.
              assert(forall i j, j+j<=i -> i- j-j+ 1+1 + j+j = i+1 +1).
              { intros. lia. }
              rewrite H3 in H22;try lia. auto. }
            { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
              apply subcnxt_add;auto. }
            { apply sub_ref.
              apply valid_is_T. auto. }}}
        { apply ss_init. }}
      { apply ss_init. }
    * apply SubAreVal in H7. inversion H7. inversion H28. auto.
  + inversion H2. apply split_nil in H4.
    inversion H4. subst. inversion H8.  subst. assert(H0':= H0).
    apply  inv_emptyll in H0.  subst.
    auto. assert(H7':=H7). inversion H7'; inversion H0.
    * inversion H3. inversion H19.
      apply valid_sub_eq in H17;auto.
      { subst.
        inversion H14.  assert (H20':=H20).
        apply toimp_ilength in H20'; try apply fq_all_qvar.
        assert(H22':=H22).
        apply toimp_ilength in H22'; try apply fq_all_qvar.
        apply  move_to_ll in H20; try apply fq_all_qvar.
        apply  move_to_ll in H22; try apply fq_all_qvar.
        apply s_bc with []
                        [And (toimp (FQ a0) (atom_(typeof a0 B2)))
                             ((toimp (FQ t) (atom_(typeof t T))))];auto.
        { apply tCricl;auto. }
        { apply ss_general with [] [];auto.
          { apply init. }
          { apply a_and;auto.
            { apply indr with (IL':=List.rev (toiqlist (FQ a0))++IL')
                              (LL':=(List.rev (toqlist (FQ a0))))
                              (B:=B2) in H20;auto;try lia.
              { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ a0)))) in H20.
                apply move_from_ll with (LL:=[])in H20;try apply fq_all_qvar.
                assert(forall i j, j+j<=i -> i-j-j+1+ 1 + j+j = i +1+1).
                { intros. lia. }
                { rewrite H23 in H20;try lia. auto. }}
              { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
                apply subcnxt_add;auto. }}
            { apply indr with (IL':=List.rev (toiqlist (FQ t))++IL')
                              (LL':=(List.rev (toqlist (FQ t))))
                              (B:=T) in H22;auto;try lia.
              { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ t)))) in H22.
                apply move_from_ll with (LL:=[])in H22;try apply fq_all_qvar.
                assert(forall i j, j+j<=i -> i-j- j+1+ 1 + j+j = i+1 +1).
                { intros. lia. }
                { rewrite H23 in H22;try lia. auto. }}
              { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
                apply subcnxt_add;auto. }
              { apply sub_ref.
                apply valid_is_T. auto. }}}
          { apply ss_init. }}
        { apply ss_init. }}
      { inversion H21. auto. }
    * inversion H3. inversion H21.
      apply valid_sub_eq in H17;auto. subst.
      inversion H14.  assert (H20':=H20).
      apply toimp_ilength in H20'; try apply fq_all_qvar.
      assert(H22':=H22).
      apply toimp_ilength in H22'; try apply fq_all_qvar.
      apply  move_to_ll in H20; try apply fq_all_qvar.
      apply  move_to_ll in H22; try apply fq_all_qvar.
      apply s_bc with []
                      [And (toimp (FQ a0) (atom_(typeof a0 B2)))
                           ((toimp (FQ t) (atom_(typeof t T))))];auto.
      { apply tCrici;auto. }
      { apply ss_general with [] [];auto.
        { apply init. }
        { apply a_and;auto.
          { apply indr with (IL':=List.rev (toiqlist (FQ a0))++IL')
                            (LL':=(List.rev (toqlist (FQ a0))))
                            (B:=B2) in H20;auto;try lia.

            { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ a0)))) in H20.
              apply move_from_ll with (LL:=[])in H20;try apply fq_all_qvar.
              assert(forall i j, j+j<=i -> i-j- j+1+ 1 + j +j= i+1 +1).
              { intros. lia. }
              { rewrite H23 in H20;try lia. auto. }}
            { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
              apply subcnxt_add;auto. }}
          { apply indr with (IL':=List.rev (toiqlist (FQ t))++IL')
                            (LL':=(List.rev (toqlist (FQ t))))
                            (B:=T) in H22;auto;try lia.
            { rewrite <- app_nil_r with (l:=(List.rev (toqlist (FQ t)))) in H22.
              apply move_from_ll with (LL:=[])in H22;try apply fq_all_qvar.
              assert(forall i j, j+j<=i -> i- j-j+ 1+1 + j+j = i+1 +1).
              { intros. lia. }
              { rewrite H23 in H22;try lia. auto. }}
            { rewrite app_nil_r. rewrite rev_toqlist,rev_toiqlist.
              apply subcnxt_add;auto. }
            { apply sub_ref.
              apply valid_is_T. auto. }}}
        { apply ss_init. }}
      { apply ss_init. }
- subst. assert (H0':=H0). apply inv_singlell in H0'.
  inversion H0'. clear H0'.  inversion H. destruct H2.
  + subst.
    assert (H0':= H0).
    apply In_cntxt_ll'  with (a:=a) (t:=x) in H0';auto.
    * simpl atmtype in H0'.
      apply s_bc with  [atom_ (typeof a x)] [atom_ (is_qexp a)];auto.
      { apply (atom_ (typeof (Var 0) A)). }
      { apply axc1;auto.
        apply sub_trans with A; auto. }
      { apply ss_general with [] [].
        { apply init. }
        { apply subcnxt_both in H0. inversion H0. inversion H3.
          inversion H6.
          assert (In (typeof a x) [typeof a x]).
          { apply in_eq. }
          { apply H9 in H10. apply i_init;auto. }}
        { apply ss_init. }}
      { apply ss_general with (lL2:= [(typeof a x)]) (lL3:= []).
        { apply split_ref. }
        { apply l_init;auto. }
        { apply ss_init. }}
    * apply in_eq.
  + inversion H2. subst.
    assert(H3':=H3).
    apply In_cntxt_il' with (il:=IL) (ll:=[typeof a A]) (ll':= []) in H3;auto.
    inversion H3.  simpl atmtype in H4.
    apply s_bc with  [] [And (atom_ (typeof a x)) (atom_ (is_qexp a))];auto.
    * apply (atom_ (typeof (Var 0) A)).
    * subst.
      apply axc2;auto.
      apply sub_trans with A; auto.
    * apply ss_general with [] [].
      { apply init. }
      { apply a_and.
        { auto. }
        { apply i_init;auto. }
        { apply subcnxt_both in H0. inversion H0. inversion H8.
          inversion H10.
          apply H11 in H3'. apply i_init;auto. }}
      { apply ss_init. }
    * apply ss_init.
- subst.
  assert(H0':=H0).
  apply  inv_emptyll in H0;auto. subst.
  apply inv_inil with (LL:=[]) (IL':=IL') (LL':=[]) in H4;auto.
  inversion H4. inversion H.
  apply s_bc with [] [And (atom_ (typeof a x)) (atom_(is_qexp a))];auto.
  + apply (atom_ (typeof (Var 0) A)).
  + apply In_cntxt_il' with (il:=IL) (ll:=[]) (ll':=[]) in H1;auto.
    inversion H1. simpl atmtype in H2. subst.
    apply axc2. apply sub_trans with A; auto.
  + apply ss_general with (lL2:= []) (lL3:= []).
    * apply init.
    * apply a_and.
      { auto. }
      { apply i_init;auto. }
      { apply subcnxt_both in H0'. inversion H0'. inversion H3.
        inversion H8. apply H9 in H1. apply i_init;auto. }
    * apply ss_init.
  + apply ss_init.
Qed.

(*****************************************)
(* Inversion Lemmas about Subtypecontext *)
(*****************************************)

Definition PTctxR0 (it lt it' lt':list atm) : Prop:= forall a T,
 ~(In (is_qexp a) it) -> ~(In (typeof a T) it) /\ ~(In (typeof a T) lt).

Theorem notqext_nottyped_alt: forall it lt, Subtypecontext it lt it lt
-> PTctxR0 it lt it lt.
Proof.
intros it lt H. apply Subtypecontext_ind; unfold PTctxR0;
 intros; auto;  split.
simpl in H2; apply not_or_and in H2;inversion H2; clear H2.
apply H1 with (T:=T) in H4. simpl. apply and_not_or.  inversion H4.
clear H5. try split;auto. contradict H3. inversion H3.
apply not_or_and in H2. inversion H2.  clear H2.
apply H1 with (T:=T) in H4.  inversion H4. auto.
apply not_or_and in H4. inversion H4. clear H4. apply not_or_and in H6.
inversion H6. clear H6.
apply H3 with (T:=T) in H7.  apply and_not_or. split.
contradict H5. inversion H5.   apply and_not_or.
split.  contradict H5. inversion H5.  auto. inversion H7.
auto.  apply not_or_and in H4.  inversion H4. clear H4.
apply not_or_and in H6. inversion H6. clear H6.
apply H3 with (T:=T) in H7. inversion H7. auto.
apply not_or_and in H5.  inversion H5.
clear H5. apply H4 with (T:=T) in H7.
inversion H7. clear H7.  apply and_not_or.  split;auto.
contradict H6. inversion H6.
apply not_or_and in H5. inversion H5. clear H5.
apply H4 with (T:=T) in H7.    apply and_not_or. split.
contradict H6. inversion H6. subst. auto. inversion H7.
auto.  apply not_or_and in H5. inversion H5.  clear H5.
apply not_or_and in H7. inversion H7. clear H7.
apply H4 with (T:=T) in H8. inversion H8. clear H8.
apply and_not_or. split. contradict H6. inversion H6.
apply and_not_or. split.  contradict H6. inversion H6.
subst. auto. auto. apply not_or_and in H5. inversion H5.
apply not_or_and in H7. inversion H7.
apply  H4 with (T:=T) in H9. inversion H9. auto.
Qed.


Theorem notqext_nottyped: forall it lt,
Subtypecontext it lt it lt -> forall a T,
 ~(In (is_qexp a) it) -> ~(In (typeof a T) it) /\ ~(In (typeof a T) lt).
Proof.
intros it lt H. apply  notqext_nottyped_alt in H;auto.
Qed.


Lemma unbox_arrow_one: forall i IL T,
Subtypecontext IL [] IL [] ->
seq_ i IL [] (atom_(typeof (CON UNBOX) (arrow T (bang one))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T (bang one)).
auto. inversion H0. inversion H3. subst.  inversion H7.
apply split_nil  in H6.  inversion H6. subst. inversion H12.
inversion  H5. subst. inversion H16.  apply split_nil  in H11.
inversion H11. inversion H20.  inversion H26.  subst.
inversion H31. apply split_nil in  H15. inversion H15. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang one)) in H24;auto.
assert (i = i2+1+1 );try lia. rewrite <- H2 in H24.
auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. subst. inversion H27.
apply split_nil in  H15. inversion H15. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang one)) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto.  inversion H13. subst.
inversion H13. assert (H23':=H23). apply Subtyping_bang_inv in H23.
inversion H23.  inversion H24. subst.   apply bang_one in H23'. subst.
inversion H22. subst. assert (H25':=H25). apply Subtyping_bang_inv in H25.
inversion H25.  inversion H2. subst.   apply bang_one in H25'. subst.
inversion H35. inversion H29. apply Subtyping_bang_inv in H43.
inversion H43. inversion H44.  inversion H45. subst.  inversion H46.
subst. inversion H19.  subst. inversion H10. subst. inversion H27.
exists A1. auto. subst. inversion H8.
apply split_nil in  H11. inversion H11. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang one)) in H22;auto.
assert (i = i0+1+1);try lia.
rewrite <- H24 in H22. auto. apply sub_trans with (B:=A0);auto.
inversion H13. subst.
inversion H13. assert (H21':=H21). apply Subtyping_bang_inv in H21.
inversion H21.  inversion H22. subst.   apply bang_one in H21'. subst.
inversion H20. inversion H9. apply Subtyping_bang_inv in H31.
inversion H31. inversion H32.  inversion H33. subst.  inversion H34.
subst. inversion H10. exists A0.  auto.
subst.  inversion H4. apply  split_nil  in H6. inversion H6.
subst.  inversion H11.   inversion H14. inversion H17.
apply Subtyping_bang_inv in H28.  inversion H28.  inversion H29.
subst. inversion H25. subst. inversion H18.
apply  split_nil  in H8. inversion H8. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang one)) in H21;auto.
assert (i = i0+1+1+1)    ;try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H21;try lia.
rewrite <- H24 in H21. auto. apply sub_trans with (B:=bang A0);auto.
apply Subtyping_bang_inv in H26. inversion H26. inversion H29.
inversion H30. subst. inversion H12. inversion H5. assert (H21':=H21).
apply Subtyping_bang_inv in H21.
inversion H21.  inversion H23. subst.   apply bang_one in H21'. subst.
inversion H31.  apply Subtyping_bang_inv in H27.
 inversion H27.  inversion H32. inversion H33.  subst.  inversion H34.
subst. inversion H8. exists (bang A0).  auto.
inversion H11. inversion H15.
apply Subtyping_bang_inv in H23.
inversion H23.  inversion H24. inversion H25. subst. inversion H26.
exists (arrow T (bang one)).  auto.
Qed.


Lemma unbox_arrow_one2: forall i IL T,
Subtypecontext IL [] IL [] ->
seq_ i IL [] (atom_(typeof (CON UNBOX) (arrow T one)))
-> exists T',  (In (typeof (CON UNBOX) T')) IL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T one).
auto. inversion H0. inversion H3. subst.  inversion H7.
apply split_nil  in H6.  inversion H6. subst. inversion H12.
inversion  H5. subst. inversion H16.  apply split_nil  in H11.
inversion H11. inversion H20.  inversion H26.  subst.
inversion H31. apply split_nil in  H15. inversion H15. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T one) in H24;auto.
assert (i = i2+1+1 );try lia. rewrite <- H2 in H24.
auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. subst. inversion H27.
apply split_nil in  H15. inversion H15. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T one) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto.  inversion H13. subst.
inversion H13.  apply one_bang_one in H23. destruct H23.
subst.
inversion H22. subst. apply one_bang_one in H23. destruct H23. subst.
inversion H35.  inversion H9. subst. inversion H32. inversion H23.
subst. inversion H35.  inversion H9. subst. apply bang_one in H32.
inversion H32. subst.  inversion H19.  subst.
inversion H22. subst. assert(H23':=H23). apply Subtyping_bang_inv in H23.
inversion H23. inversion H2.  subst.  apply bang_one in H23'.
subst.
inversion H35.  inversion H9. subst. inversion H24. inversion H37.
inversion H39. inversion H40.
subst. inversion H19. subst. inversion H10.  subst. inversion H27.
exists A1. auto. subst. inversion H8.
apply split_nil in  H11. inversion H11. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T  one) in H22;auto.
assert (i = i0+1+1);try lia.
rewrite <- H24 in H22. auto. apply sub_trans with (B:=A0);auto.

inversion H13. subst.
inversion H13.  apply one_bang_one in H21. destruct H21.
subst.
inversion H20.  inversion H9. subst. inversion H28. inversion H17.
subst. inversion H20. subst. inversion H9.  subst.
apply bang_one in H24. inversion H24. subst. inversion H10.
exists A0. auto. subst. inversion H4.
apply split_nil in  H6. inversion H6. subst. inversion H11.
inversion H14. inversion H17. apply  Subtyping_bang_inv in H28.
inversion H28. inversion H29. subst. inversion H25. subst.
inversion H18. apply split_nil in  H8. inversion H8. subst.
inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T  one) in H21;auto.
assert (i = i0+1+1+1);try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H21;try lia.
rewrite <- H24 in H21. auto. apply sub_trans with (B:=bang A0);auto.
inversion H12.  inversion H30. apply one_bang_one in H37. destruct H37.
subst. inversion H26. inversion H5.  inversion H8. inversion H23.
inversion H28. subst.  inversion H26.  inversion H5. inversion H8.
apply bang_one in H23. inversion H23. subst. inversion H31.
exists (bang A0).  auto.
inversion H11. inversion H15.
inversion H23.  inversion H25.
exists (arrow T  one).  auto.
Qed.


Lemma unbox_arrow_bool: forall i IL T,
Subtypecontext IL [] IL [] ->
seq_ i IL [] (atom_(typeof (CON UNBOX) (arrow T (bang bool))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T (bang bool)).
auto. inversion H0. inversion H3. subst.  inversion H7.
apply split_nil  in H6.  inversion H6. subst. inversion H12.
inversion  H5. subst. inversion H16.  apply split_nil  in H11.
inversion H11. inversion H20.  inversion H26.  subst.
inversion H31. apply split_nil in  H15. inversion H15. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang bool)) in H24;auto.
assert (i = i2+1+1 );try lia. rewrite <- H2 in H24.
auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. subst. inversion H27.
apply split_nil in  H15. inversion H15. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang bool)) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto.  inversion H13. subst.
inversion H13. assert (H23':=H23). apply Subtyping_bang_inv in H23.
inversion H23.  inversion H24. subst.   apply bang_bool in H23'. subst.
inversion H22. subst. assert (H25':=H25). apply Subtyping_bang_inv in H25.
inversion H25.  inversion H2. subst.   apply bang_bool in H25'. subst.
inversion H35. inversion H29. apply Subtyping_bang_inv in H43.
inversion H43. inversion H44.  inversion H45. subst.  inversion H46.
subst. inversion H19.  subst. inversion H10. subst. inversion H27.
exists A1. auto. subst. inversion H8.
apply split_nil in  H11. inversion H11. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang bool)) in H22;auto.
assert (i = i0+1+1);try lia.
rewrite <- H24 in H22. auto. apply sub_trans with (B:=A0);auto.
inversion H13. subst.
inversion H13. assert (H21':=H21). apply Subtyping_bang_inv in H21.
inversion H21.  inversion H22. subst.   apply bang_bool in H21'. subst.
inversion H20. inversion H9. apply Subtyping_bang_inv in H31.
inversion H31. inversion H32.  inversion H33. subst.  inversion H34.
subst. inversion H10. exists A0.  auto.
subst.  inversion H4. apply  split_nil  in H6. inversion H6.
subst.  inversion H11.   inversion H14. inversion H17.
apply Subtyping_bang_inv in H28.  inversion H28.  inversion H29.
subst. inversion H25. subst. inversion H18.
apply  split_nil  in H8. inversion H8. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang bool)) in H21;auto.
assert (i = i0+1+1+1)    ;try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H21;try lia.
rewrite <- H24 in H21. auto. apply sub_trans with (B:=bang A0);auto.
apply Subtyping_bang_inv in H26. inversion H26. inversion H29.
inversion H30. subst. inversion H12. inversion H5. assert (H21':=H21).
apply Subtyping_bang_inv in H21.
inversion H21.  inversion H23. subst.   apply bang_bool in H21'. subst.
inversion H31.  apply Subtyping_bang_inv in H27.
 inversion H27.  inversion H32. inversion H33.  subst.  inversion H34.
subst. inversion H8. exists (bang A0).  auto.
inversion H11. inversion H15.
apply Subtyping_bang_inv in H23.
inversion H23.  inversion H24. inversion H25. subst. inversion H26.
exists (arrow T (bang bool)).  auto.
Qed.


Lemma unbox_arrow_bool2: forall i IL T,
Subtypecontext IL [] IL [] ->
seq_ i IL [] (atom_(typeof (CON UNBOX) (arrow T bool)))
-> exists T',  (In (typeof (CON UNBOX) T')) IL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T bool).
auto. inversion H0. inversion H3. subst.  inversion H7.
apply split_nil  in H6.  inversion H6. subst. inversion H12.
inversion  H5. subst. inversion H16.  apply split_nil  in H11.
inversion H11. inversion H20.  inversion H26.  subst.
inversion H31. apply split_nil in  H15. inversion H15. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T bool) in H24;auto.
assert (i = i2+1+1 );try lia. rewrite <- H2 in H24.
auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. subst. inversion H27.
apply split_nil in  H15. inversion H15. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T bool) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto.  inversion H13. subst.
inversion H13.  apply bool_bang_bool in H23. destruct H23.
subst.
inversion H22. subst. apply bool_bang_bool in H23. destruct H23. subst.
inversion H35.  inversion H9. subst. inversion H32. inversion H23.
subst. inversion H35.  inversion H9. subst. apply bang_bool in H32.
inversion H32. subst.  inversion H19.  subst.
inversion H22. subst. assert(H23':=H23). apply Subtyping_bang_inv in H23.
inversion H23. inversion H2.  subst.  apply bang_bool in H23'.
subst.
inversion H35.  inversion H9. subst. inversion H24. inversion H37.
inversion H39. inversion H40.
subst. inversion H19. subst. inversion H10.  subst. inversion H27.
exists A1. auto. subst. inversion H8.
apply split_nil in  H11. inversion H11. subst. inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T  bool) in H22;auto.
assert (i = i0+1+1);try lia.
rewrite <- H24 in H22. auto. apply sub_trans with (B:=A0);auto.

inversion H13. subst.
inversion H13.  apply bool_bang_bool in H21. destruct H21.
subst.
inversion H20.  inversion H9. subst. inversion H28. inversion H17.
subst. inversion H20. subst. inversion H9.  subst.
apply bang_bool in H24. inversion H24. subst. inversion H10.
exists A0. auto. subst. inversion H4.
apply split_nil in  H6. inversion H6. subst. inversion H11.
inversion H14. inversion H17. apply  Subtyping_bang_inv in H28.
inversion H28. inversion H29. subst. inversion H25. subst.
inversion H18. apply split_nil in  H8. inversion H8. subst.
inversion H19.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T  bool) in H21;auto.
assert (i = i0+1+1+1);try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H21;try lia.
rewrite <- H24 in H21. auto. apply sub_trans with (B:=bang A0);auto.
inversion H12.  inversion H30. apply bool_bang_bool in H37. destruct H37.
subst. inversion H26. inversion H5.  inversion H8. inversion H23.
inversion H28. subst.  inversion H26.  inversion H5. inversion H8.
apply bang_bool in H23. inversion H23. subst. inversion H31.
exists (bang A0).  auto.
inversion H11. inversion H15.
inversion H23.  inversion H25.
exists (arrow T  bool).  auto.
Qed.

Lemma unbox_arrow_cic: forall i IL LL T A B,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON UNBOX) (arrow T (bang (circ A B)))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL \/ (In (typeof (CON UNBOX) T')) LL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T (bang (circ A B))).
right. apply in_eq. exists (arrow T (bang (circ A B))).
auto. inversion H0. inversion H3. subst.  inversion H7.
inversion H14. subst. apply split_ident in  H6. subst.
inversion H12. inversion H5. subst. inversion H15.  inversion H20.
subst. apply split_ident in H9. subst.
inversion H19.  inversion H8.  subst. inversion H22.
inversion H27. subst. apply split_ident in H16.
subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T (bang (circ A B)))
 in H26;auto.
assert (i = i0+1+1 );try lia. rewrite <- H2 in H26.
auto. apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst.  inversion H9. apply split_nil in H16. inversion H16. subst.
inversion H25. inversion  H22.
 subst. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (circ A B)))
 in H28;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H28;try lia.
rewrite <- H2 in H28. auto.
  apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:=A1);auto.
inversion H13.
apply Subtyping_bang_inv in H33. inversion H33. inversion H34.
inversion H36. subst. inversion H21.
apply Subtyping_bang_inv in H23. inversion H23.
inversion H27. inversion H29. subst.
inversion H26. inversion H11. apply Subtyping_bang_inv in H47.
inversion H47. inversion H48. inversion H49. subst.
inversion H50. subst. apply SubAreVal in H21.
inversion H21. inversion H2. inversion H37. subst.
inversion H18. subst. apply SubAreVal in H13.
inversion H13. inversion H2. inversion H27.
subst. inversion H10. subst. exists A2. right.
apply in_eq. subst. exists A2. auto.
auto. subst. inversion H15. subst.
inversion H6. apply split_nil in H9. inversion H9.
subst.  inversion H18.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (circ A B)))
 in H21;auto.
assert (i = i0+1+1 );try lia.
rewrite <- H23 in H21. auto.
  apply sub_trans with (B:= A1);auto.

inversion H13.
apply Subtyping_bang_inv in H26. inversion H26. inversion H27.
inversion H29. subst. inversion H19.
inversion H8. apply Subtyping_bang_inv in H24.
inversion H24. inversion H28. inversion H30. subst.
inversion H31. subst. apply SubAreVal in H19.
inversion H19. inversion H8. inversion H20.
subst. inversion H10. subst. exists A1.
right. apply in_eq. exists A1. auto. auto.
subst. inversion H7. subst. inversion H4.
apply split_nil in H6. inversion H6. subst.
inversion H11. inversion H14.
subst. inversion H17. subst.
inversion H22. apply split_nil in H9. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (circ A B)))
 in H21;auto.
assert (i = i2+1+1 );try lia.
rewrite <- H2 in H21. auto.
  apply sub_trans with (B:= bang A1);auto.
subst. inversion H18. apply split_nil in H8. inversion H8. subst.
inversion H20. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (circ A B)))
 in H23;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H23;try lia.
rewrite <- H25 in H23. auto.
  apply sub_trans with (B:= bang A1);auto.
inversion H12. inversion H20. apply Subtyping_bang_inv in H28.
inversion H28. inversion H29. inversion H31. subst.
apply Subtyping_bang_inv in H9. inversion H9.
inversion H2. inversion H10. subst. inversion H16.
apply Subtyping_bang_inv in H30. inversion H30.
inversion H32. inversion H33. subst. inversion H36.
subst.  apply SubAreVal in H20. inversion H20.
inversion H21. inversion H24. subst. inversion H21.
exists (bang A1). auto. inversion H11.
inversion H15. apply Subtyping_bang_inv in H23.
inversion H23. inversion H24. inversion H25.
subst. inversion H26. subst. exists ( arrow T (bang (circ A B))).
right. apply in_eq.  exists ( arrow T (bang (circ A B))).
auto.
Qed.

Lemma unbox_arrow_circ2 : forall i IL LL T A B,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON UNBOX) (arrow T (circ A B))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL \/ (In (typeof (CON UNBOX) T')) LL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T ( (circ A B))).
right. apply in_eq. exists (arrow T ( (circ A B))).
auto. inversion H0. inversion H3. subst.  inversion H7.
inversion H14. subst. apply split_ident in  H6. subst.
inversion H12. inversion H5. subst. inversion H15.  inversion H20.
subst. apply split_ident in H9. subst.
inversion H19.  inversion H8.  subst. inversion H22.
inversion H27. subst. apply split_ident in H16.
subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T ( (circ A B)))
 in H26;auto.
assert (i = i0+1+1 );try lia. rewrite <- H2 in H26.
auto. apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst.  inversion H9. apply split_nil in H16. inversion H16. subst.
inversion H25. inversion  H22.
 subst. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (circ A B)))
 in H28;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H28;try lia.
rewrite <- H2 in H28. auto.
  apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:=A1);auto.
inversion H13.
inversion H33. subst. inversion H21.
inversion H23. subst.
inversion H26. inversion H11.
inversion H43. inversion H45.
subst. inversion H26. inversion H11.
apply Subtyping_bang_inv in H41.
 inversion H41. inversion H42. inversion H43.
subst. apply sub_trans with (C:= circ A5 B3) in H44;auto.
 inversion H44.  subst.
inversion H18. subst.
inversion H21. subst. inversion H21.
subst. inversion H26. inversion H11. inversion H39.
 apply sub_trans with (C:= bang A5) in H41;auto.
apply sub_trans with (C:= circ A B) in H41;auto.
inversion H41. subst. inversion H41.
subst. apply sub_trans with (C:= circ A B) in H23;auto.
inversion H23. inversion H28. subst. inversion H18.
subst. inversion H10. subst. exists A2. right.
apply in_eq. subst. exists A2. auto.
auto. subst. inversion H15. subst.
 inversion H6. apply split_nil in H9. inversion H9.
subst.  inversion H18.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (circ A B)))
 in H21;auto.
assert (i = i0+1+1 );try lia.
rewrite <- H23 in H21. auto.
  apply sub_trans with (B:= A1);auto.

inversion H13.



inversion H26. subst. inversion H19.
inversion H8. inversion H24. inversion H28.
subst. inversion H19. inversion H8.
apply sub_trans with (C:= circ A B) in H24;auto.
 inversion H24.  inversion H30. subst. inversion H10.
subst. exists A1. right.
apply in_eq. subst. exists A1. auto.
auto.
subst. inversion H7. subst. inversion H4.
apply split_nil in H6. inversion H6. subst.
inversion H11. inversion H14.
subst. inversion H17. subst.
inversion H22. apply split_nil in H9. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (circ A B)))
 in H21;auto.
assert (i = i2+1+1 );try lia.
rewrite <- H2 in H21. auto.
  apply sub_trans with (B:= bang A1);auto.
subst. inversion H18. apply split_nil in H8. inversion H8. subst.
inversion H20. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (circ A B)))
 in H23;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H23;try lia.
rewrite <- H25 in H23. auto.
  apply sub_trans with (B:= bang A1);auto.
apply Subtyping_bang_inv in H9.  inversion H9.
inversion H19. inversion H20. subst.
inversion H12. inversion H10. subst. inversion H10.
inversion H29. subst. inversion H21.
inversion H31. inversion H37. subst. inversion H21.
apply sub_trans with (C:= circ A B) in H33;auto.
inversion H33. inversion H35.
subst. inversion H16.
exists (bang A1). auto. inversion H11.
inversion H15. inversion H23. inversion H25.
subst.  exists ( arrow T ( (circ A B))).
right. apply in_eq.  exists ( arrow T ( (circ A B))).
auto.
Qed.

(* Formerly called testing6 *)
Theorem sub_circ_inv: forall i IL LL a T U,
    ~(In (is_qexp (CON UNBOX)) IL) ->
    valid T -> valid U ->
    is_value a ->
    Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
    seq_ i IL LL (atom_(typeof a (circ T U))) ->
    exists t u i, a = Circ t i u.
Proof.
intros i IL LL a T U H100 H101 H102. intros. inversion H;subst.
inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= circ T U) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.
inversion H2.   auto.  inversion H4. subst.  contradict H8.
subst. apply in_eq. subst. contradict H8. subst. apply in_eq.
subst. inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto. inversion H1.
clear H1.  contradict H3. auto.


assert (exists A, In (typeof (CON (Qvar x)) A) IL \/ In (typeof (CON (Qvar x)) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON (Qvar x)) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x0) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.




exists t. exists a0. exists i0. auto.

assert (exists A, In (typeof (CON TRUE) A) IL \/ In (typeof (CON TRUE) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON TRUE) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

assert (exists A, In (typeof (CON FALSE) A) IL \/ In (typeof (CON FALSE) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON FALSE) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.



assert (exists A, In (typeof (CON STAR) A) IL \/ In (typeof (CON STAR) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON STAR) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (CON (BOX T0)) A) IL \/ In (typeof (CON (BOX T0)) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H28.   subst.
inversion H18. inversion H27.  subst. apply  split_ident in H12.
subst. inversion H26.  inversion H11.  inversion H39. subst.
inversion H29. inversion H38. subst.  apply split_ident in H21.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H37;auto.
rewrite <- H5  in H37. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H36. inversion H38. inversion H40. subst. inversion H12.
inversion H36.  apply split_nil in H21.  inversion H21. subst.
inversion H29. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H50;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H50;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H50.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H41.
inversion H37. inversion H41. inversion H40. inversion H44.
inversion H40. inversion H43. inversion H40. inversion H45.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON (BOX T0)) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H11. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H5. auto. auto. subst. inversion H25.
inversion H27. inversion H29.   inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H25. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H32 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H9. apply split_nil in H12. inversion H12.
subst. inversion H25. inversion H18. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H5 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H30.
inversion H26. inversion H30.
inversion H29. inversion H33. inversion H29. inversion H32.
inversion H29. inversion H34.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON (BOX T0)) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. inversion H15. inversion H17.
subst. inversion H7. apply split_nil in H9. inversion H9. subst.
inversion H14.
inversion H19.  inversion H24. apply Subtyping_bang_inv in H37.
inversion H37. inversion H38. subst. inversion H34. assert(H36':=H36).
apply Subtyping_bang_inv in H36. inversion H36.
inversion H37. inversion H38. inversion H39. subst.
inversion H27. apply split_nil in H11. inversion H11. subst.
inversion H28. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H30.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H36'.
inversion H36'. inversion H5.  apply Subtyping_bang_inv in H38.
inversion H38. inversion H39.  inversion H40. subst. inversion H41.
inversion H10. subst. apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H5. auto. subst.
apply SubAreVal in  H15. inversion H15. inversion H5.
inversion H17. inversion H19.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON (BOX T0)) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H5. auto. subst. auto.
 inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.

assert (exists A, In (typeof (CON UNBOX) A) IL \/ In (typeof (CON UNBOX) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
inversion H36. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON UNBOX) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
inversion H25. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON UNBOX) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4.  apply Subtyping_bang_inv in H34.
inversion H34. inversion H37.  inversion H38. subst. inversion H39.
inversion H9. subst. apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
inversion H13. inversion H17.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON UNBOX) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

assert (exists A, In (typeof (CON REV) A) IL \/ In (typeof (CON REV) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H27.   subst.
inversion H17. inversion H26.  subst. apply  split_ident in H11.
subst. inversion H25.  inversion H10.  inversion H38. subst.
inversion H28. inversion H37. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H36;auto.
rewrite <- H4  in H36. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H35. inversion H37. inversion H39. subst. inversion H11.
inversion H35.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H49;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H49;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H49.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H40.
inversion H36. inversion H40.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON REV) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H24.
inversion H26. inversion H28.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H8. apply split_nil in H11. inversion H11.
subst. inversion H24. inversion H17. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H27;auto.
rewrite <- H4 in H27. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H29.
inversion H25. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (CON REV) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. inversion H14. inversion H16.
subst. inversion H6. apply split_nil in H8. inversion H8. subst.
inversion H13.
inversion H18.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H10. inversion H10. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H29.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H4.  apply Subtyping_bang_inv in H34.
inversion H34. inversion H37.  inversion H38. subst. inversion H39.
inversion H9. subst. apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst.
apply SubAreVal in  H14. inversion H14. inversion H4.
inversion H13. inversion H17.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON REV) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

assert (exists A, In (typeof (Fun f) A) IL \/ In (typeof (Fun f) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H28.   subst.
inversion H18. inversion H27.  subst. apply  split_ident in H12.
subst. inversion H26.  inversion H11.  inversion H39. subst.
inversion H29. inversion H38. subst.  apply split_ident in H21.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H37;auto.
rewrite <- H5  in H37. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H36. inversion H38. inversion H40. subst. inversion H12.
inversion H36.  apply split_nil in H21.  inversion H21. subst.
inversion H29. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H50;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H50;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H50.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H41.
subst. apply notqext_nottyped with
 (lt:=[typeof (Fun f) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H11. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H5. auto. auto. subst. inversion H25.
inversion H27. inversion H29.   inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H25. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H32 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H9. apply split_nil in H12. inversion H12.
subst. inversion H25. inversion H18. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H5 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H30.
subst.  apply notqext_nottyped with
 (lt:=[typeof (Fun f) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. inversion H15. inversion H17.
subst. inversion H7. apply split_nil in H9. inversion H9. subst.
inversion H14.
inversion H19.  inversion H24. apply Subtyping_bang_inv in H37.
inversion H37. inversion H38. subst. inversion H34. assert(H36':=H36).
apply Subtyping_bang_inv in H36. inversion H36.
inversion H37. inversion H38. inversion H39. subst.
inversion H27. apply split_nil in H11. inversion H11. subst.
inversion H28. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H30.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H36'.
inversion H36'. inversion H5.
subst.
inversion H10. subst. apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H5. auto. subst.
apply SubAreVal in  H15. inversion H15. inversion H5.
subst. apply  notqext_nottyped with
(lt:=[typeof (Fun f) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H5. auto. subst. auto.
 inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.


assert (exists A, In (typeof (Prod v w) A) IL \/ In (typeof (Prod v w) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H7. inversion H17.  subst.
 inversion H11. inversion H18. subst. apply split_ident in H10.
subst. inversion H16. inversion H9.  inversion H29.   subst.
inversion H19. inversion H28.  subst. apply  split_ident in H13.
subst. inversion H27.  inversion H12.  inversion H40. subst.
inversion H30. inversion H39. subst.  apply split_ident in H22.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H38;auto.
rewrite <- H6  in H38. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H37. inversion H39. inversion H41. subst. inversion H13.
inversion H37.  apply split_nil in H22.  inversion H22. subst.
inversion H30. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H51;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H51;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H6 in H51.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H42.
subst. apply notqext_nottyped with
 (lt:=[typeof (Prod v w) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H12. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H6. auto. auto. subst. inversion H26.
inversion H28. inversion H30.   inversion H19. subst.
inversion H10. apply split_nil in H13.  inversion H13. subst.
inversion H26. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
rewrite <- H33 in H29. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H10. apply split_nil in H13. inversion H13.
subst. inversion H26. inversion H19. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H29;auto.
rewrite <- H6 in H29. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H31.
subst.  apply notqext_nottyped with
 (lt:=[typeof (Prod v w) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H9. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H6. auto. auto.
subst. inversion H14. inversion H16. inversion H18.
subst. inversion H8. apply split_nil in H10. inversion H10. subst.
inversion H15.
inversion H20.  inversion H25. apply Subtyping_bang_inv in H38.
inversion H38. inversion H39. subst. inversion H35. assert(H37':=H37).
apply Subtyping_bang_inv in H37. inversion H37.
inversion H38. inversion H39. inversion H40. subst.
inversion H28. apply split_nil in H12. inversion H12. subst.
inversion H29. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H31;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H31;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H6 in H31.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H37'.
inversion H37'. inversion H6.
subst.
inversion H11. subst. apply notqext_nottyped with (lt:=[]) (T:= bang(circ A2 B1)) in H1;auto.
 inversion H1. contradict H6. auto. subst.
apply SubAreVal in  H16. inversion H16. inversion H6.
subst. apply  notqext_nottyped with
(lt:=[typeof (Prod v w) (circ T U)]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H6. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= circ T U) in H1;auto.
 inversion H1. contradict H6. auto. subst. auto.
 inversion H5. destruct H6;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H7. auto. contradict H8. auto.


assert (exists A, In (typeof (App (CON UNBOX) v) A) IL \/
In (typeof (App (CON UNBOX) v) A) LL).
induction i. inversion H2.  lia. exists (circ T U). right. apply in_eq.
exists (circ T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H28.   subst.
inversion H18. inversion H27.  subst. apply  split_ident in H12.
subst. inversion H26.  inversion H11.  inversion H39. subst.
inversion H29. inversion H38. subst.  apply split_ident in H21.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= circ T U) in H37;auto.
rewrite <- H5  in H37. auto.  apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. auto. subst.
inversion H36. inversion H38. inversion H40. subst. inversion H12.
inversion H36.  apply split_nil in H21.  inversion H21. subst.
inversion H29. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H50;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H50;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H50.   auto.
apply sub_trans with (B:= circ A2 B0);auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H41.
subst.
inversion H29. inversion H37. subst.
apply split_ident in H21. subst. inversion H36.
apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_circ2 in H38;auto.
inversion H38. inversion H43;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H45. auto. contradict H46.  auto.
auto.
subst. apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (circ A2 B0)]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H11. apply in_eq.
 subst.
apply notqext_nottyped with (lt:=[]) (T:= circ A2 B0) in H1;auto.
 inversion H1. contradict H5. auto.
auto.
subst. inversion H25.
inversion H27. inversion H29.   inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H25. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H32 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto.
subst. inversion H9. apply split_nil in H12. inversion H12.
subst. inversion H25. inversion H18. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H28;auto.
rewrite <- H5 in H28. auto.
apply sub_trans with (B:= circ A1 B1);auto. subst. inversion H30.
subst. inversion H18. inversion H26.
subst. apply split_ident in H12. subst.
inversion H25.
apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_circ2 in H27;auto.
inversion H27. inversion H32;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H34. auto. contradict H35.  auto.
auto.

subst.
  apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (circ A1 B1)]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= circ A1 B1) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. inversion H15. inversion H17.
subst. inversion H7. apply split_nil in H9. inversion H9. subst.
inversion H14.
inversion H19.  inversion H24. apply Subtyping_bang_inv in H37.
inversion H37. inversion H38. subst. inversion H34. assert(H36':=H36).
apply Subtyping_bang_inv in H36. inversion H36.
inversion H37. inversion H38. inversion H39. subst.
inversion H27. apply split_nil in H11. inversion H11. subst.
inversion H28. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= circ T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H30.  auto.
apply sub_trans with (B:= bang (circ A2 B1)); subst; auto.
subst. apply SubAreVal in H36'.
inversion H36'. inversion H5. inversion H10.
subst. inversion H31. apply split_nil in H11.
inversion H11. subst.  inversion H28.
apply split_nil  in H12.
inversion H12. subst.
apply unbox_arrow_cic in H32;auto.
inversion H32. inversion H5.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto;
inversion H100. contradict H13. auto. inversion H8.
exists (bang (circ A2 B1)). left. auto.
subst. inversion H18. subst. inversion H10.
inversion H15. subst. apply split_ident in H9. subst.
inversion H14. apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_circ2 in H17;auto.
inversion H17. inversion H21;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H23. auto. contradict H24.  auto.
auto. subst. exists (circ T U). right. apply in_eq.
subst. exists (circ T U). left. auto.
inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.
Qed.


(* Formerly called testing6' *)
Theorem sub_bangcirc_inv: forall i IL LL a T U,
    ~(In (is_qexp (CON UNBOX)) IL) ->
    is_value a ->
    Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
    seq_ i IL LL (atom_(typeof a (bang (circ T U)))) ->
    exists t u i, a = Circ t i u.
Proof.
intros i IL LL a T U H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= bang (circ T U)) in H1;auto. inversion H1.
clear H1.  subst. contradict H8. apply in_eq.
apply notqext_nottyped with (lt:=LL) (T:= bang (circ T U)) in H1;auto. inversion H1.
clear H1. contradict H7. auto.


assert (exists A, In (typeof (CON (Qvar x)) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:= x0) in H0;auto.
inversion H0. contradict H5. auto.

exists t. exists a0. exists i0. auto.

assert (exists A, In (typeof (CON TRUE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON TRUE) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON TRUE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.

assert (exists A, In (typeof (CON FALSE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON FALSE) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON FALSE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON STAR) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON STAR) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON STAR) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.

assert (exists A, In (typeof (CON (BOX T0)) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON (BOX T0)) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13. assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H25. subst.
apply  Subtyping_bang_inv in H22. inversion H22.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H22. clear H22.
inversion H13. clear H13. inversion H27. subst.
clear H27. inversion H26. apply split_nil in H11.
inversion H11. subst. inversion H27. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H32;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H32;try lia.
rewrite <- H5 in H32. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
subst. apply Subtyping_bang_inv in  H27. inversion H27.
inversion H5. inversion H8. subst. inversion H13.
apply  notqext_nottyped with (a:=CON (BOX T0)) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H5. auto.
subst. apply SubAreVal in H15'. inversion H15'. inversion H5.
subst. apply Subtyping_bang_inv in  H17. inversion H17.
inversion H5. inversion H8. subst. inversion H9. subst.
apply In_cntxt_ll with (a:=CON (BOX T0)) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=CON (BOX T0)) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.




assert (exists A, In (typeof (CON UNBOX) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON UNBOX) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst. apply Subtyping_bang_inv in  H11. inversion H11.
inversion H4. inversion H12. subst. inversion H21.
apply  notqext_nottyped with (a:=CON UNBOX) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst. apply Subtyping_bang_inv in  H13. inversion H13.
inversion H4. inversion H7. subst. inversion H8. subst.
apply In_cntxt_ll with (a:=CON UNBOX) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON UNBOX) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON REV) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON REV) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H21. clear H21.
inversion H12. clear H12. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H10.
inversion H10. subst. inversion H26. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H31;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H31;try lia.
rewrite <- H4 in H31. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst. apply Subtyping_bang_inv in  H11. inversion H11.
inversion H4. inversion H12. subst. inversion H21.
apply  notqext_nottyped with (a:=CON REV) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst. apply Subtyping_bang_inv in  H13. inversion H13.
inversion H4. inversion H7. subst. inversion H8. subst.
apply In_cntxt_ll with (a:=CON REV) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON REV) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (Fun f) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Fun f) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13. assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H25. subst.
apply  Subtyping_bang_inv in H22. inversion H22.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H22. clear H22.
inversion H13. clear H13. inversion H27. subst.
clear H27. inversion H26. apply split_nil in H11.
inversion H11. subst. inversion H27. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H32;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H32;try lia.
rewrite <- H5 in H32. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
apply  notqext_nottyped with (a:=Fun f) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H5. auto. subst.
subst. apply SubAreVal in H15'. inversion H15'. inversion H5.
 subst.
apply In_cntxt_ll with (a:=Fun f) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=Fun f) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.

assert (exists A, In (typeof (Prod v w) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Prod v w) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14. assert(H16':=H16).
apply Subtyping_bang_inv in H16. inversion H16. inversion H17.
clear H16 H17. inversion H18. inversion H19.  subst. inversion H8.
apply split_nil  in H10. inversion H11. subst.  inversion H15.
inversion H17. subst. inversion H26. subst.
apply  Subtyping_bang_inv in H23. inversion H23.
inversion H6. subst. inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14.
inversion H14; clear H14. inversion H23. clear H23.
inversion H14. clear H14. inversion H28. subst.
clear H28. inversion H27. apply split_nil in H12.
inversion H12. subst. inversion H28. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H33;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H33;try lia.
rewrite <- H6 in H33. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H6.
subst. inversion H10. inversion H6.
apply  notqext_nottyped with (a:=Prod v w) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H30. auto. subst.
subst. apply SubAreVal in H16'. inversion H16'. inversion H6.
 subst.
apply In_cntxt_ll with (a:= Prod v w) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H5.
apply  notqext_nottyped with (a:=Prod v w) (T:= x) in H0;auto.
inversion H0. contradict H7. auto.


assert (exists A, In (typeof (App (CON UNBOX) v) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= App (CON UNBOX) v) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (circ T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13. assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H25. subst.
apply  Subtyping_bang_inv in H22. inversion H22.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H22. clear H22.
inversion H13. clear H13. inversion H27. subst.
clear H27. inversion H26. apply split_nil in H11.
inversion H11. subst. inversion H27. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(circ T U)) in H32;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H32;try lia.
rewrite <- H5 in H32. auto.
 apply sub_trans with (B:= bang(circ A1 B1)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
subst. inversion H30.
apply split_nil in H11.  inversion H11. subst.
inversion H28.
apply split_nil  in H12.  inversion H12. subst.
inversion H10. subst.
apply unbox_arrow_cic in H32;auto. inversion H32. inversion H5.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H13. auto. inversion H8.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:=bang (circ A1 B1)) in H0;auto.
inversion H0. contradict H28. auto. subst.
apply SubAreVal in H15'. inversion H15'. inversion H5.
 subst.
inversion H10. inversion H15.  subst. inversion H14.
apply split_ident in H9. subst. apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_cic in H18;auto. inversion H18. inversion H9;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
 inversion H100. contradict H13. auto. contradict H17. auto. auto. subst.
apply In_cntxt_ll with (a:=App (CON UNBOX) v) (t:= bang (circ T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (circ T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.
Qed.


Lemma unbox_arrow_tensor: forall i IL LL T A B,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON UNBOX) (arrow T (bang (tensor A B)))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL \/ (In (typeof (CON UNBOX) T')) LL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T (bang (tensor A B))).
right. apply in_eq. exists (arrow T (bang (tensor A B))).
auto. inversion H0. inversion H3. subst.  inversion H7.
inversion H14. subst. apply split_ident in  H6. subst.
inversion H12. inversion H5. subst. inversion H15.  inversion H20.
subst. apply split_ident in H9. subst.
inversion H19.  inversion H8.  subst. inversion H22.
inversion H27. subst. apply split_ident in H16.
subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T (bang (tensor A B)))
 in H26;auto.
assert (i = i0+1+1 );try lia. rewrite <- H2 in H26.
auto. apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst.  inversion H9. apply split_nil in H16. inversion H16. subst.
inversion H25. inversion  H22.
 subst. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (tensor A B)))
 in H28;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H28;try lia.
rewrite <- H2 in H28. auto.
  apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:=A1);auto.
inversion H13.
apply Subtyping_bang_inv in H33. inversion H33. inversion H34.
inversion H36. subst. inversion H21.
apply Subtyping_bang_inv in H23. inversion H23.
inversion H27. inversion H29. subst.
inversion H26. inversion H11. apply Subtyping_bang_inv in H43.
inversion H43. inversion H44. inversion H45. subst.
inversion H46. subst. apply SubAreVal in H21.
inversion H21. inversion H2. inversion H37. subst.
inversion H18. subst. apply SubAreVal in H13.
inversion H13. inversion H2. inversion H27.
subst. inversion H10. subst. exists A2. right.
apply in_eq. subst. exists A2. auto.
auto. subst. inversion H15. subst.
inversion H6. apply split_nil in H9. inversion H9.
subst.  inversion H18.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (tensor A B)))
 in H21;auto.
assert (i = i0+1+1 );try lia.
rewrite <- H23 in H21. auto.
  apply sub_trans with (B:= A1);auto.

inversion H13.
apply Subtyping_bang_inv in H26. inversion H26. inversion H27.
inversion H29. subst. inversion H19.
inversion H8. apply Subtyping_bang_inv in H24.
inversion H24. inversion H28. inversion H30. subst.
inversion H31. subst. apply SubAreVal in H19.
inversion H19. inversion H8. inversion H20.
subst. inversion H10. subst. exists A1.
right. apply in_eq. exists A1. auto. auto.
subst. inversion H7. subst. inversion H4.
apply split_nil in H6. inversion H6. subst.
inversion H11. inversion H14.
subst. inversion H17. subst.
inversion H22. apply split_nil in H9. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (tensor A B)))
 in H21;auto.
assert (i = i2+1+1 );try lia.
rewrite <- H2 in H21. auto.
  apply sub_trans with (B:= bang A1);auto.
subst. inversion H18. apply split_nil in H8. inversion H8. subst.
inversion H20. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T (bang (tensor A B)))
 in H23;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H23;try lia.
rewrite <- H25 in H23. auto.
  apply sub_trans with (B:= bang A1);auto.
inversion H12. inversion H20. apply Subtyping_bang_inv in H28.
inversion H28. inversion H29. inversion H31. subst.
apply Subtyping_bang_inv in H9. inversion H9.
inversion H2. inversion H10. subst. inversion H16.
apply Subtyping_bang_inv in H30. inversion H30.
inversion H32. inversion H33. subst. inversion H34.
subst.  apply SubAreVal in H20. inversion H20.
inversion H2. inversion H24. subst. inversion H21.
exists (bang A1). auto. inversion H11.
inversion H15. apply Subtyping_bang_inv in H23.
inversion H23. inversion H24. inversion H25.
subst. inversion H26. subst. exists ( arrow T (bang (tensor A B))).
right. apply in_eq.  exists ( arrow T (bang (tensor A B))).
auto.
Qed.


Lemma unbox_arrow_tensor2 : forall i IL LL T A B,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON UNBOX) (arrow T (tensor A B))))
-> exists T',  (In (typeof (CON UNBOX) T')) IL \/ (In (typeof (CON UNBOX) T')) LL.
Proof.
intros. induction i. inversion H0.  lia. exists (arrow T ( (tensor A B))).
right. apply in_eq. exists (arrow T ( (tensor A B))).
auto. inversion H0. inversion H3. subst.  inversion H7.
inversion H14. subst. apply split_ident in  H6. subst.
inversion H12. inversion H5. subst. inversion H15.  inversion H20.
subst. apply split_ident in H9. subst.
inversion H19.  inversion H8.  subst. inversion H22.
inversion H27. subst. apply split_ident in H16.
subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T ( (tensor A B)))
 in H26;auto.
assert (i = i0+1+1 );try lia. rewrite <- H2 in H26.
auto. apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst.  inversion H9. apply split_nil in H16. inversion H16. subst.
inversion H25. inversion  H22.
 subst. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (tensor A B)))
 in H28;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H28;try lia.
rewrite <- H2 in H28. auto.
  apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:=A1);auto.
inversion H13.
inversion H33. subst. inversion H21.
inversion H23. subst.
inversion H26. inversion H11.
inversion H39. inversion H41.
subst. inversion H26. inversion H11.
apply Subtyping_bang_inv in H39.
 inversion H39. inversion H40. inversion H41.
subst. apply sub_trans with (C:= tensor A5 A6) in H42;auto.
 inversion H42.  subst.
inversion H18. subst.
inversion H21. subst. inversion H21.
subst. inversion H26. inversion H11. inversion H39.
 apply sub_trans with (C:= bang A5) in H41;auto.
apply sub_trans with (C:= tensor A B) in H41;auto.
inversion H41. subst. inversion H41.
subst. apply sub_trans with (C:= tensor A B) in H23;auto.
inversion H23. inversion H28. subst. inversion H18.
subst. inversion H10. subst. exists A2. right.
apply in_eq. subst. exists A2. auto.
auto. subst. inversion H15. subst.
 inversion H6. apply split_nil in H9. inversion H9.
subst.  inversion H18.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (tensor A B)))
 in H21;auto.
assert (i = i0+1+1 );try lia.
rewrite <- H23 in H21. auto.
  apply sub_trans with (B:= A1);auto.

inversion H13.



inversion H26. subst. inversion H19.
inversion H8. inversion H24. inversion H28.
subst. inversion H19. inversion H8.
apply sub_trans with (C:= tensor A B) in H24;auto.
 inversion H24.  inversion H30. subst. inversion H10.
subst. exists A1. right.
apply in_eq. subst. exists A1. auto.
auto.
subst. inversion H7. subst. inversion H4.
apply split_nil in H6. inversion H6. subst.
inversion H11. inversion H14.
subst. inversion H17. subst.
inversion H22. apply split_nil in H9. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (tensor A B)))
 in H21;auto.
assert (i = i2+1+1 );try lia.
rewrite <- H2 in H21. auto.
  apply sub_trans with (B:= bang A1);auto.
subst. inversion H18. apply split_nil in H8. inversion H8. subst.
inversion H20. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T ( (tensor A B)))
 in H23;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H23;try lia.
rewrite <- H25 in H23. auto.
  apply sub_trans with (B:= bang A1);auto.
apply Subtyping_bang_inv in H9.  inversion H9.
inversion H19. inversion H20. subst.
inversion H12. inversion H10. subst. inversion H10.
inversion H29. subst. inversion H21.
inversion H31. inversion H35. subst. inversion H21.
apply sub_trans with (C:= tensor A B) in H33;auto.
inversion H33. inversion H35.
subst. inversion H16.
exists (bang A1). auto. inversion H11.
inversion H15. inversion H23. inversion H25.
subst.  exists ( arrow T ( (tensor A B))).
right. apply in_eq.  exists ( arrow T ( (tensor A B))).
auto.
Qed.


Lemma unbox_arrow: forall i IL LL T U,
Subtypecontext IL LL IL LL
-> ~(In (is_qexp (CON UNBOX)) IL) ->
seq_ i IL LL (atom_(typeof (CON UNBOX) (arrow T U)))
-> exists t u a b,  Subtyping T (circ t u) /\ Subtyping (bang(arrow a b)) U.
Proof.
intros i IL LL T U H H100 H0. induction i. inversion H0.  lia.
subst.
apply notqext_nottyped with (lt:=[typeof (CON UNBOX) (arrow T U)])
 (T:= arrow T U) in H100;auto. inversion H100.
contradict H2. apply in_eq. subst.
apply notqext_nottyped with (lt:=[])
 (T:= arrow T U) in H100;auto. inversion H100.
contradict H1. auto.
inversion H0. inversion H3. subst.  inversion H7.
inversion H14. subst. apply split_ident in  H6. subst.
inversion H12. inversion H5. subst. inversion H15.  inversion H20.
subst. apply split_ident in H9. subst.
inversion H19.  inversion H8.  subst. inversion H22.
inversion H27. subst. apply split_ident in H16.
subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U)
 in H26;auto.
assert (i = i0+1+1 );try lia. rewrite <- H2 in H26.
auto. apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. auto.
subst.  inversion H9. apply split_nil in H16. inversion H16. subst.
inversion H25. inversion  H22.
 subst. apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U)
 in H28;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H28;try lia.
rewrite <- H2 in H28. auto.
  apply sub_trans with (B:= A1);auto.
apply sub_trans with (B:=A0);auto.
inversion H26. inversion H30. inversion H35.
inversion H37. inversion H46. subst.
inversion H21.  inversion H16. inversion H23. subst.
inversion H13. exists A3. exists B0. exists A7. exists B6.
split;auto.
apply BangSub1;auto. apply SubAreVal in H33.
inversion H33. inversion H38. apply bArrow;auto.
subst. inversion H23. inversion H27. subst. inversion H13.
exists A0. exists B4. exists A2. exists B0.
split. apply sub_trans with (B:= bang(circ A0 B4));auto.
apply Prop2_14.
apply SubAreVal in H33. inversion H33. auto.
apply BangSub1. auto.
apply SubAreVal in H39. inversion H39.
inversion H48.
apply bArrow; auto.
subst. inversion H28. subst. inversion H46.
subst. inversion H21. inversion H17. inversion H28.
subst. inversion H45. subst.
inversion H13. exists A4. exists B4.
exists A0. exists B5. split; auto.
apply BangSub1;auto.
apply SubAreVal in H49. inversion H49.
inversion H50.
apply bArrow; auto.
subst. apply Subtyping_bang_inv in H28.
inversion H28. inversion H2. inversion H11.
subst. inversion H27.
subst. inversion H13. exists A4.
exists B4. exists A0. exists B0.
split;auto. subst. inversion H17.
inversion H28. inversion H36.
inversion H11. subst. inversion H13.
exists A6. exists B6. exists A4. exists B5.
split. apply sub_trans with (B:= bang(circ A6 B6));auto.
apply Prop2_14.
apply SubAreVal in H39. inversion H39. auto.
apply BangSub1. auto.
apply SubAreVal in H45. inversion H45.
inversion H49.
apply bArrow; auto.
subst. inversion H27.
subst. inversion H36. inversion H29.
subst. inversion H13.
exists A3. exists B5. exists A0. exists B4.
split. apply sub_trans with (B:= bang(circ A3 B5));auto.
apply Prop2_14.
apply SubAreVal in H45. inversion H45. auto.
auto. subst. inversion H32.
subst. inversion H38;subst;[simpl|inversion H39].
inversion H37. inversion H11. subst.
inversion H21. inversion H36.
inversion H32.
apply Subtyping_bang_inv in H46.
inversion H46. inversion H50.
subst. inversion H47. inversion H47; subst;[simpl|inversion H49].
inversion H13.
exists A7. exists B6. exists A6. exists B5.
split. apply sub_trans with (B:= bang(circ A7 B6));auto.
apply Prop2_14.
apply SubAreVal in H41. inversion H41. auto.
apply BangSub1. auto.
apply SubAreVal in H44. inversion H44.
inversion H46.
apply bArrow; auto.
subst. inversion H11. subst.
inversion H21.
assert(H33':=H33).
apply Subtyping_bang_inv in H33.
inversion H33. inversion H41.
inversion H43. inversion H40.
inversion H52. subst. inversion H13.
exists A5. exists B4. exists A8. exists B7.
split. apply sub_trans with (B:= bang(circ A5 B4));auto.
apply Prop2_14.
apply SubAreVal in H42. inversion H42. auto.
apply BangSub1. auto.
apply SubAreVal in H45. inversion H45. auto.
inversion H48.
apply bArrow; auto. inversion H52.
subst. inversion H13.
exists A5. exists B4. exists A8. exists B7.
split. apply sub_trans with (B:= bang(circ A5 B4));auto.
apply Prop2_14.
apply SubAreVal in H42. inversion H42. auto.
auto. subst.
apply SubAreVal in H33'. inversion H33'.
inversion H2.
subst. inversion H18.
 subst. apply notqext_nottyped  with (lt:=[typeof (CON UNBOX) A1])
(T:=A1) in H100;auto. inversion H100.
contradict H8. apply in_eq.

subst. apply notqext_nottyped  with (lt:=[])
(T:=A1) in H100;auto. inversion H100.
contradict H2. auto.

auto.

subst. inversion H15. subst.
inversion H6. apply split_nil in H9. inversion H9.
subst.  inversion H18.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= (arrow T U))
 in H21;auto.
assert (i = i0+1+1 );try lia.
rewrite <- H23 in H21. auto.
  apply sub_trans with (B:= A0);auto.

inversion H19; subst; [simpl|inversion H10].
inversion H23. inversion H9. inversion H16.
inversion H30. subst. inversion H13.
exists A3. exists B0. exists A6. exists B5.
split. auto. apply BangSub1. auto.
apply SubAreVal in H26. inversion H26.
inversion H29.
apply bArrow; auto. inversion H30.
subst. inversion H13.
exists A3. exists B0. exists A6. exists B5.
split;auto.
inversion H20;subst;[simpl|inversion H21].
inversion H16. inversion H8. subst.
inversion H13.
exists A3. exists B0. exists A2. exists B3.
assert(H26':=H26).
apply Subtyping_bang_inv in H26. inversion H26.
inversion H35. inversion H37.
subst. inversion H13. inversion H30.
inversion H42. split. apply BangSub1;auto.
apply BangSub1;auto. apply SubAreVal in H38.
inversion H38. inversion H47.
apply bArrow;auto. subst.
apply SubAreVal in H26'.
inversion H26'. inversion H2. subst.
inversion H8. subst.
inversion H13.
exists A3. exists B0. exists A2. exists B2.
assert(H30':=H30).
apply Subtyping_bang_inv in H30. inversion H30.
inversion H35.  inversion H37.
subst. inversion H13. inversion H33.
inversion H42. split. apply BangSub1;auto.
auto. subst.
apply SubAreVal in H30'.
inversion H30'. inversion H2.
subst.
apply notqext_nottyped  with (lt:=[typeof (CON UNBOX) A0])
(T:=A0) in H100;auto. inversion H100.
contradict H5. apply in_eq.


subst. apply notqext_nottyped  with (lt:=[])
(T:=A0) in H100;auto. inversion H100.
contradict H2. auto.


auto.

inversion H12. inversion H14;subst;[simpl|inversion H15].
inversion H7. inversion H4. subst.
apply split_nil in H10. inversion H10. subst.
inversion H17. inversion H11.
inversion H19.  apply Subtyping_bang_inv in H32.
inversion H32. inversion H33. subst. inversion H29.
assert(H31':=H31).
apply Subtyping_bang_inv in H31.
inversion H31. inversion H32. inversion H33.
inversion H34. subst.
inversion H22. subst.
apply split_nil in H6. inversion H6. subst.
inversion H23.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U)
 in H25;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H25;try lia.
rewrite <- H28 in H25. auto.
  apply sub_trans with (B:= bang (arrow A2 B1));auto.
subst. apply SubAreVal in H31'. inversion H31'.
inversion H2.

inversion H30. inversion H34.
inversion H35. inversion H12.
inversion H44.
exists T0. exists U0. exists T0. exists U0.
split. apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:= B1);auto.

subst.  apply notqext_nottyped  with (lt:=[])
(T:=bang(arrow A2 B1)) in H100;auto. inversion H100.
contradict H1. auto.

inversion H11.  inversion H15.
exists T0. exists U0. exists T0. exists U0.
split;auto.

subst. apply notqext_nottyped  with (lt:=[typeof (CON UNBOX) (arrow T U)])
(T:=arrow T U) in H100;auto. inversion H100.
contradict H2. apply in_eq.


subst. apply notqext_nottyped  with (lt:=[])
(T:=arrow T U) in H100;auto. inversion H100.
contradict H1. auto.
Qed.

(* Formerly called testing8' *)
Theorem sub_bangarrow_inv: forall i IL LL a T U,
    ~(In (is_qexp (CON UNBOX)) IL)->
    validT T -> validT U ->
    (forall v, a= App (CON UNBOX) v -> ~(In (is_qexp v) IL)) ->
    is_value a ->
    Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
    seq_ i IL LL (atom_(typeof a (bang(arrow T U)))) ->
    (exists f,  a = Fun f) \/ (exists T0, a = CON (BOX T0)) \/
    (a=CON UNBOX) \/ (a=CON REV) \/
    (exists t i u, a = App (CON UNBOX) (Circ t i u)).
Proof.
intros i IL LL a T U H100 H101 H102 H103. intros. inversion H;subst.
inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= (bang (arrow T U))) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.
inversion H2.   auto.  inversion H4. subst.  contradict H8.
subst. apply in_eq. subst. contradict H8. subst. apply in_eq.
subst. inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= (bang (arrow T U))) in H1;auto. inversion H1.
clear H1.  contradict H3. auto.

assert (exists A, In (typeof (CON (Qvar x)) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:= x0) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (Circ t i0 a0 ) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Circ t i0 a0 ) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14. assert(H16':=H16).
apply Subtyping_bang_inv in H16. inversion H16. inversion H17.
clear H16 H17. inversion H18. inversion H19.  subst. inversion H8.
apply split_nil  in H10. inversion H11. subst.  inversion H15.
inversion H17. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H6. subst. inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14.
inversion H14; clear H14. inversion H21. clear H21.
inversion H14. clear H14. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H12.
inversion H12. subst. inversion H26. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H28;auto.
assert(i=i1+1+1+1); try lia.
apply seq_mono_cor with (k:= i1+1+1 + 1 ) in H28;try lia.
rewrite <- H6 in H28. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H6.
subst. inversion H10. inversion H6.
apply  notqext_nottyped with (a:=Circ t i0 a0 ) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H28. auto. subst.
subst. apply SubAreVal in H16'. inversion H16'. inversion H6.
 subst.
apply In_cntxt_ll with (a:= Circ t i0 a0) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H5.
apply  notqext_nottyped with (a:=Circ t i0 a0) (T:= x) in H0;auto.
inversion H0. contradict H7. auto.

assert (exists A, In (typeof (CON TRUE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON TRUE) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON TRUE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON FALSE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON FALSE) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON FALSE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON STAR) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON STAR) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON STAR) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.



right. left.  exists T0. auto.

right. right. left. auto.

right. right. right. left. auto.

left. exists f. auto.

assert (exists A, In (typeof (Prod v w) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Prod v w) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (arrow T U)).  auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14. assert(H16':=H16).
apply Subtyping_bang_inv in H16. inversion H16. inversion H17.
clear H16 H17. inversion H18. inversion H19.  subst. inversion H8.
apply split_nil  in H10. inversion H10. subst.
inversion H11. subst.  inversion H15.
inversion H17. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H6. subst. inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14.
inversion H14; clear H14. inversion H21. clear H23.
inversion H14. clear H14. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H12.
inversion H12. subst. inversion H26.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H28;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H28;try lia.
rewrite <- H33 in H28. auto.
 apply sub_trans with (B:= bang(arrow A1 B1)); auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H6.
subst. inversion H10. inversion H6.
apply  notqext_nottyped with (a:=Prod v w) (T:=bang (arrow A1 B1)) in H0;auto.
inversion H0. contradict H12. auto. subst.
subst. apply SubAreVal in H16'. inversion H16'. inversion H6.
 subst.
apply In_cntxt_ll with (a:= Prod v w) (t:= bang (arrow T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (arrow T U)).
auto. inversion H5.
apply  notqext_nottyped with (a:=Prod v w) (T:= x) in H0;auto.
inversion H0. contradict H7. auto.




assert(exists j t u LL', (seq_ j IL LL' (atom_ (typeof v (circ t u)))
\/ seq_ j IL LL' (atom_ (typeof v (bang (circ t u)))))
 /\ valid t /\ valid u /\ Subtypecontext IL LL' IL LL').

induction i. inversion H2. lia.
subst. apply notqext_nottyped with (lt:=[typeof (App (CON UNBOX) v) (bang (arrow T U))])
 (T:= bang (arrow T U)) in H1;auto.
inversion H1. contradict H5. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang (arrow T U)) in H1;auto.
inversion H1. contradict H4. auto. inversion H2. inversion H6.
subst. inversion H16;subst;inversion H13.
subst. inversion H7.
apply split_nil in H9. inversion H9. subst.
inversion H14. inversion H17. inversion H20.
subst. inversion H25.
apply split_nil in H11. inversion H11. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H22;auto.
 assert(i=i2+1+1); try lia. rewrite <- H5 in H22.  auto.
apply sub_trans with (B:= bang A0); subst; auto.
subst. inversion H21.
apply split_nil in H11. inversion H11. inversion H10. subst.
inversion H22.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(arrow T U)) in H24;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H24;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H27 in H24.  auto.
apply sub_trans with (B:= bang A0); subst; auto.

subst. inversion H25.
apply split_nil in H11. inversion H11. inversion H10. subst.
inversion H22. apply split_nil in H12.
inversion H12. subst.
apply unbox_arrow in H26;auto.
inversion H26. inversion H5.
inversion H8. inversion  H12. inversion H13.
inversion H28. inversion H29. subst. exists i0.
exists A1. exists B1. exists [].  split. left.  auto.
inversion H37. split;auto.
inversion H32;subst;[simpl|inversion H33].
exists i0.
exists A1. exists B1. exists []. split. right.  auto.
inversion H41. split;auto.

apply notqext_nottyped with (lt:=[]) (T:= bang A0) in H1;auto.
 inversion H1. contradict H23. auto.

inversion H10. subst. auto.

subst. inversion H10. inversion H15.
subst.
apply split_ident in H9. subst.
inversion H14.
apply unbox_arrow in H17;auto.
inversion H17. inversion H19.
inversion H20. inversion  H21. inversion H22.
inversion H23. subst.

exists i1.
exists A1. exists B1. exists LL2. split. left.  auto.
inversion H30. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
inversion H25;subst;[simpl|inversion H26].
exists i1.
exists A1. exists B1. exists LL2. split. right.  auto.
inversion H34. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.

apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0. auto. auto.
subst.  apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (bang(arrow T U))]) (T:= bang(arrow T U)) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= bang(arrow T U)) in H1;auto.
 inversion H1. contradict H4. auto. auto.

inversion H4. inversion H5. inversion H6.
inversion H7. inversion H8. inversion H10.
inversion H12.
destruct H9;
  [apply sub_circ_inv in H9|apply sub_bangcirc_inv in H9];
  auto;right; right; right; right; inversion H9;
    inversion H15; inversion H16; exists x3; exists x5; exists x4;
      rewrite H17; auto.
Qed.


Theorem UNBOX_LL: forall i IL LL A,
~(In (is_qexp (CON UNBOX)) IL)->
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON UNBOX) A))
 -> LL = [] /\ exists T U,
Subtyping (bang(arrow ( (circ T U)) (bang (arrow T U)))) A.
Proof.
intros. induction i.
inversion H1. lia.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7.  auto.

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
assert(i0+1+1= i);try lia. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto. auto.
subst. inversion H23.
inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
apply seq_mono_cor with (k:= i) in H26;try lia.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
subst. inversion H23. split.  auto.
exists T. exists U.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.


apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto. apply in_eq.
apply notqext_nottyped with (lt:=[]) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto.
subst.  auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
assert(i= i0+1+1);try lia.
rewrite <- H24 in H22.
inversion H16. subst. apply IHi in H22. auto.
inversion H16. subst. auto.
apply sub_trans with (B:=A1);auto.
inversion H16. split;auto.
exists T. exists U.
apply sub_trans with (B:=A1);auto.
subst. inversion H16. split. auto.
exists T. exists U.
apply sub_trans with (B:=A1);auto.

apply notqext_nottyped with (lt:=lL2) (T:=A1) in H;auto.
inversion H. subst. contradict H12. apply in_eq.
apply notqext_nottyped with (lt:=lL2) (T:=A1) in H;auto.
inversion H. subst. contradict H12. auto. auto.

subst. inversion H8. inversion H5.
apply split_nil in H11. inversion H11. subst.
inversion H16.  inversion H12.
inversion H18. subst.
inversion H23. apply split_nil in H7.
inversion H7. subst.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H20;auto.
assert(i= i2+1+1);try lia.
rewrite <- H3 in H20. apply IHi in H20. auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H19.
apply split_nil in H7.
inversion H7. subst. inversion H20.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
apply seq_mono_cor with (k:= i) in H22;try lia.
apply IHi in H22. auto.
apply sub_trans with (B:=bang A1);auto.

split. auto. exists T. exists U.
apply sub_trans with (B:=bang A1);auto.
apply notqext_nottyped with (lt:=[]) (T:=bang A1) in H;auto.
inversion H. subst. contradict H21. auto.
subst. inversion H8. split. auto.
exists T. exists U. auto.


apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.

apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. auto.
Qed.

Theorem sub_slet_inv: forall i IL LL a b A,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_ (typeof (Slet a b) A)) ->
 ~(In (is_qexp (Slet a b)) IL) ->
 (exists j B, j+1+1 <= i /\ Subtyping B A /\
(splitseq prog j IL LL [Conj (atom_ (typeof a B))  (atom_ (typeof b (bang one)))]
\/
splitseq prog j IL LL [Conj (atom_ (typeof a B))  (atom_ (typeof b ( one)))])) \/
(exists j, j+1 <= i /\ validT A /\
(splitseq prog j IL LL [Conj (atom_ (typeof a A))  (atom_ (typeof b (bang one)))]
\/
splitseq prog j IL LL [Conj (atom_ (typeof a A))  (atom_ (typeof b ( one)))]))
.
Proof.
intros. induction i.
inversion H0. lia.
subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A) in H;auto.
inversion H. contradict H2. auto.

inversion H0. inversion H4.
subst. inversion H8. inversion H15.
subst. apply split_ident in H7.
subst. inversion H13.
inversion H6. subst. inversion H16.
inversion H21. subst. apply split_ident in H10.
subst. inversion H20. inversion H9.
subst. inversion H23. inversion H28. subst.
apply split_ident in H17. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H27;auto.
assert(i0+1+1=i); try lia. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12.
left. exists x. exists x0. auto. inversion  H17.
split. lia. auto.
right. inversion H3.  inversion H12.
exists x. split. lia. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try lia.
apply IHi in H29. inversion H29. inversion H3.
inversion H12.
inversion H18.
left. exists x. exists x0. auto.
split. lia. auto.
right. inversion H3.  inversion H12.
exists x. split. lia. auto.
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i0. exists A2.
split. lia.
split. apply sub_trans with (B:=A1);auto.
right. auto. subst.
left. exists i0. exists A2.
split. lia.
split. apply sub_trans with (B:=A1);auto.
left. auto.
subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try lia. subst.
apply IHi in H22. inversion H22. inversion H3.
inversion H9.
left. exists x. exists x0. auto. inversion  H12.
split. lia. auto.
right. inversion H3.  inversion H9.
exists x. split. lia. auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i1. exists A1. split.
lia. split. auto. right. auto.
left. subst. exists i1. exists A1. split.
lia. split. auto. left. auto.
subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try lia. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6.
left. exists x. exists x0. auto. inversion  H10.
split. lia. auto.
right. inversion H3.  inversion H6.
exists x. split. lia. auto.
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try lia.
apply IHi in H22. inversion H22. inversion H25.
inversion H26.
left. exists x. exists x0. auto. inversion  H27.
split. lia. auto.
right. inversion H25.  inversion H26.
exists x. split. lia. auto.
 apply sub_trans with (B:=bang A1);auto.
left. subst. exists i2. exists (bang A1).
split. lia.
split. auto. inversion H8. subst.
 right. auto.
left. subst. exists i2. exists (bang A1).
split. lia.
split. auto. inversion H8. subst.
left. auto.
subst.
apply notqext_nottyped with (a:=Slet a b) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto.
subst. right. exists i0. split. lia.
 split. auto. right. auto.
subst. right. exists i0. split. lia. split. auto. left. auto.

subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Slet a b) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.


Theorem fun_typed: forall i IL LL f A,
Subtypecontext IL LL IL LL -> abstr f ->
seq_ i IL LL (atom_ (typeof (Fun f) A)) ->
 ~(In (is_qexp (Fun f)) IL) ->
(
 (exists j T T', j+1+1 <= i /\
validT (bang T) /\ validT T' /\
((Subtyping (arrow T T') A /\ splitseq prog j IL LL [(All (fun x : qexp =>
Imp (is_qexp x) (lImp (typeof x T) (atom_ (typeof (f x) T')))))])
\/ (Subtyping (arrow (bang T) T') A /\ splitseq prog j IL LL [(All (fun x : qexp =>
Imp (is_qexp x) (Imp (typeof x (bang T)) (atom_ (typeof (f x) T')))))])))

\/
 (exists j T T', j+1+1 <= i /\
validT (bang T) /\ validT T' /\
((Subtyping (bang(arrow T T')) A /\ splitseq prog j IL [] [(All (fun x : qexp =>
Imp (is_qexp x) (lImp (typeof x T) (atom_ (typeof (f x) T')))))])
\/ (Subtyping (bang(arrow (bang T) T')) A /\ splitseq prog j IL [] [(All (fun x : qexp =>
Imp (is_qexp x) (Imp (typeof x (bang T)) (atom_ (typeof (f x) T')))))])) )
\/

 (exists j T T', j+1 <= i /\
validT (bang T) /\ validT T' /\
((  A = arrow T T' /\ splitseq prog j IL LL [(All (fun x : qexp =>
Imp (is_qexp x) (lImp (typeof x T) (atom_ (typeof (f x) T')))))])
\/ (A= (arrow (bang T) T')  /\ splitseq prog j IL LL [(All (fun x : qexp =>
Imp (is_qexp x) (Imp (typeof x (bang T)) (atom_ (typeof (f x) T')))))])))

\/
 (exists j T T', j+1 <= i /\
validT (bang T) /\ validT T' /\
((A= bang((arrow T T')) /\ splitseq prog j IL [] [(All (fun x : qexp =>
Imp (is_qexp x) (lImp (typeof x T) (atom_ (typeof (f x) T')))))])
\/ (A= (bang(arrow (bang T) T'))  /\ splitseq prog j IL [] [(All (fun x : qexp =>
Imp (is_qexp x) (Imp (typeof x (bang T)) (atom_ (typeof (f x) T')))))]))))
.
Proof.
intros  i IL LL f A H h. intros.  induction i.
inversion H0. lia.
subst.
apply notqext_nottyped with (a:=Fun f) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Fun f) (T:=A) in H;auto.
inversion H. contradict H2. auto.

inversion H0. inversion H4.
subst. inversion H8. inversion H15.
subst. apply split_ident in H7.
subst. inversion H13.
inversion H6. subst. inversion H16.
inversion H21. subst. apply split_ident in H10.
subst. inversion H20. inversion H9.
subst. inversion H23. inversion H28. subst.
apply split_ident in H17. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H27;auto.
assert(i0+1+1=i); try lia. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17.
inversion H18.  inversion H25.
inversion H31.  destruct H33.
inversion H33.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.

inversion H3.
inversion H12. inversion H17. inversion H18.
inversion H24. inversion H30. inversion H32.
destruct H34. inversion H34.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25.
clear.  intros. lia.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.

inversion H12. inversion H17. inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33.  destruct H35. inversion H35.
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H30.
clear.  intros. lia.
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H30.
clear.  intros. lia.

inversion H17. inversion H18.
inversion H24.     inversion H25. inversion H31.
inversion H33.  destruct H35. inversion H35.
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H30.
clear.  intros. lia.
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H30.
clear.  intros. lia.

apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try lia.
apply IHi in H29. inversion H29.
inversion H3. inversion H12. inversion H18.
inversion H24. inversion H31.
inversion H33.  destruct H35.
inversion H35.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25 H2.
clear.  intros. lia.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25 H2.
clear.  intros. lia.

inversion H3.
inversion H12. inversion H18. inversion H24.
inversion H25.  inversion H32. inversion H34.
destruct H36. inversion H36.
 right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H31 H2.
clear.  intros. lia.
 right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H31 H2.
clear.  intros. lia.

inversion H12. inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33. inversion H35. destruct H37. inversion H37.
 right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2.
clear.  intros. lia.
 right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2.
clear.  intros. lia.

inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33. inversion H35. destruct H37. inversion H37.
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2.
clear.  intros. lia.
 right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2.
clear.  intros. lia.

apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
subst. left.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. apply sub_trans with (B:=A1);auto.
apply ss_general with (lL2:=lL0) (lL3:=[]).
apply split_ref. inversion H23.
inversion H31.  subst. apply split_ident in H17;auto.
subst. inversion H29. apply s_all. intros.
apply abstr_lam_simp with (e:=E) in h;
try unfold lambda; try rewrite H24;auto.
unfold ext_eq in h. assert(h28:=H28).
apply h in H28.  apply H25 in h28.
rewrite <- H28. auto. apply ss_init.
subst. left.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
right. split. apply sub_trans with (B:=A1);auto.
apply ss_general with (lL2:=lL0) (lL3:=[]).
apply split_ref. inversion H23.
inversion H31.  subst. apply split_ident in H17;auto.
subst. inversion H29. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x : qexp => E x) in h;
try unfold lambda; try rewrite H24;auto.
unfold ext_eq in h. assert(h28:=H28).
apply h in H28.  apply H25 in h28.
rewrite <- H28. auto.  apply ss_init.

subst. inversion H19.
subst. right. left.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. apply sub_trans with (B:=A1);auto.
 apply ss_general with (lL2:=[]) (lL3:=[]).
apply init. inversion H10.
inversion H31.  subst. apply split_ident in H17;auto.
subst. inversion H29. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x : qexp => E x) in h;
try unfold lambda; try rewrite H24;auto.
unfold ext_eq in h. assert(h28:=H28).
apply h in H28.  apply H25 in h28.
rewrite <- H28. auto.   apply ss_init.

subst.
apply notqext_nottyped with (a:=Fun f) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=Fun f) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try lia. subst.
apply IHi in H22. inversion H22. inversion H3.
inversion H9.  inversion H12. inversion H17.
inversion H24.  inversion H26.
destruct H28.
inversion H28.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H18.
clear.  intros. lia.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H18.
clear.  intros. lia.

inversion H3.
inversion H9. inversion H12. inversion H17.
inversion H18. inversion H25. inversion H27.
destruct H29. inversion H29.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.

inversion H9. inversion H12. inversion H17.
inversion H18.
inversion H24. inversion H26.
inversion H28.  destruct H30. inversion H30.
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25.
clear.  intros. lia.
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25.
clear.  intros. lia.

inversion H12. inversion H17.
inversion H18.     inversion H24. inversion H26.
inversion H28.  destruct H30. inversion H30.
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H25.
clear.  intros. lia.
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H25.
clear.  intros. lia.

apply sub_trans with (B:=A1);auto. auto.

subst. left.  exists i1. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. auto.
apply ss_general with (lL2:=lL2) (lL3:=[]).
apply split_ref. inversion H16.
inversion H24.  subst. apply split_ident in H10;auto.
subst. inversion H22. apply s_all. intros.
apply abstr_lam_simp with (e:=E) in h;
try unfold lambda; try rewrite H17;auto.
unfold ext_eq in h. assert(h21:=H21).
apply h in H21.  apply H18 in h21.
rewrite <- H21. auto. apply ss_init.
subst. left.  exists i1. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
right. split. auto.
apply ss_general with (lL2:=lL2) (lL3:=[]).
apply split_ref. inversion H16.
inversion H24.  subst. apply split_ident in H10;auto.
subst. inversion H22. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H17;auto.
unfold ext_eq in h. assert(h21:=H21).
apply h in H21.  apply H18 in h21.
rewrite <- H21. auto. apply ss_init.

subst. inversion H11.
subst. inversion H11.

subst.
apply notqext_nottyped with (a:=Fun f) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=Fun f) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.

subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try lia. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6.
inversion H10.  inversion H11. inversion H22.
inversion H25.
destruct H28.
inversion H28.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H17.
clear.  intros. lia.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H17.
clear.  intros. lia.

inversion H3.
inversion H6. inversion H10. inversion H11.
inversion H17. inversion H24. inversion H27.
destruct H30. inversion H30.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H22.
clear.  intros. lia.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H22.
clear.  intros. lia.

inversion H6. inversion H10. inversion H11.
inversion H17.
inversion H22. inversion H25.
inversion H28.  destruct H31. inversion H31.
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.

inversion H10. inversion H11.
inversion H17.     inversion H22. inversion H25.
inversion H28.  destruct H31. inversion H31.
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H24.
clear.  intros. lia.

apply sub_trans with (B:=bang A1);auto.

subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try lia.
apply IHi in H22. inversion H22. inversion H25.
inversion H26. inversion H27. inversion H29.
inversion H31. inversion H33. destruct H35.
inversion H35.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H10 H2 H30.
clear.  intros. lia.
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H10 H2 H30.
clear.  intros. lia.

inversion H25.
inversion H26. inversion H27. inversion H29.
inversion H30. inversion H32. inversion H34.
destruct H36. inversion  H36.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H31.
clear.  intros. lia.
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H31.
clear.  intros. lia.

inversion H26. inversion H27. inversion H29.
inversion H30.
inversion H31. inversion H33.
inversion H35.  destruct H37. inversion H37.
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32.
clear.  intros. lia.
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32.
clear.  intros. lia.

inversion H27. inversion H29.
inversion H30.     inversion H31. inversion H33.
inversion H35.  destruct H37. inversion H37.
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32.
clear.  intros. lia.
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32.
clear.  intros. lia.

apply sub_trans with (B:=bang A1);auto.

subst. right. left.  exists i2. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
right. split. auto.
apply ss_general with (lL2:=[]) (lL3:=[]).
apply split_ref. inversion H19.
 apply split_nil in H9. inversion H9. subst.
 inversion H20. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H24;auto.
unfold ext_eq in h. assert(h22:=H22).
apply h in H22.  apply H17 in h22.
rewrite <- H22. auto. apply ss_init.

subst. right. left.  exists i2. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. auto.
apply ss_general with (lL2:=[]) (lL3:=[]).
apply split_ref. inversion H19.
 apply split_nil in H9. inversion H9. subst.
 inversion H20. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H24;auto.
unfold ext_eq in h. assert(h22:=H22).
apply h in H22.  apply H17 in h22.
rewrite <- H22. auto. apply ss_init.

subst.
apply notqext_nottyped with (a:=Fun f) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto.

subst. right. right. left.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. auto.
apply ss_general with (lL2:=LL) (lL3:=[]).
apply split_ref. inversion H8.
inversion H17. subst.  apply split_ident in H7. subst.
 inversion H16. apply s_all. intros.
apply abstr_lam_simp with (e:=E) in h;
try unfold lambda; try rewrite H9;auto.
unfold ext_eq in h. assert(h14:=H14).
apply h in H14.  apply H13 in h14.
rewrite <- H14. auto. auto. apply ss_init.

subst. right. right. left.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
right. split. auto.
apply ss_general with (lL2:=LL) (lL3:=[]).
apply split_ref. inversion H8.
inversion H17. subst.  apply split_ident in H7. subst.
 inversion H16. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H9;auto.
unfold ext_eq in h. assert(h14:=H14).
apply h in H14.  apply H13 in h14.
rewrite <- H14. auto. auto. apply ss_init.

subst. right. right. right.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
right. split. auto.
apply ss_general with (lL2:=[]) (lL3:=[]).
apply init. inversion H5.
apply split_nil in H7. inversion H7. subst.
 inversion H16. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H9;auto.
unfold ext_eq in h. assert(h18:=H18).
apply h in H18.  apply H14 in h18.
rewrite <- H18. auto. auto. apply ss_init.


subst. right. right. right.  exists i0. exists T1. exists T2.
split. clear. lia. split. auto. split. auto.
left. split. auto.
apply ss_general with (lL2:=[]) (lL3:=[]).
apply init. inversion H5.
apply split_nil in H7. inversion H7. subst.
 inversion H16. apply s_all. intros.
apply abstr_lam_simp with (e:=fun x => E x) in h;
try unfold lambda; try rewrite H9;auto.
unfold ext_eq in h. assert(h18:=H18).
apply h in H18.  apply H14 in h18.
rewrite <- H18. auto. auto. apply ss_init.

subst.
apply notqext_nottyped with (a:=Fun f) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Fun f) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

Theorem let_typed: forall i IL LL b E A,
Subtypecontext IL LL IL LL ->
(forall x, proper x -> abstr (E x)) ->
abstr (fun x => lambda (E x)) ->
seq_ i IL LL (atom_ (typeof (Let E b) A)) ->
 ~(In (is_qexp  (Let E b)) IL) ->
exists j T1 T2,
validT (bang T1) /\ validT (bang T2) /\
 ((exists T3, j+1+1 <= i /\ Subtyping T3 A /\
(splitseq prog j IL LL [(All (fun x : qexp => (All( fun y:qexp =>
             Imp (is_qexp x) (Imp (is_qexp y)
             (lImp (typeof x T1) (lImp (typeof y T2) (atom_ (typeof (E x y) T3)))))))));
             atom_ (typeof b (tensor T1 T2))]
\/ splitseq prog j IL LL [(All (fun x : qexp => (All( fun y:qexp =>
             Imp (is_qexp x) (Imp (is_qexp y)
             (Imp (typeof x (bang T1)) (Imp (typeof y (bang T2)) (atom_ (typeof (E x y) T3)))))))));
             atom_ (typeof b (bang (tensor T1 T2)))]))
\/(j+1 <= i /\ (splitseq prog j IL LL [(All (fun x : qexp => (All( fun y:qexp =>
             Imp (is_qexp x) (Imp (is_qexp y)
             (lImp (typeof x T1) (lImp (typeof y T2) (atom_ (typeof (E x y) A)))))))));
             atom_ (typeof b (tensor T1 T2))]
\/ splitseq prog j IL LL [(All (fun x : qexp => (All( fun y:qexp =>
             Imp (is_qexp x) (Imp (is_qexp y)
             (Imp (typeof x (bang T1)) (Imp (typeof y (bang T2)) (atom_ (typeof (E x y) A)))))))));
             atom_ (typeof b (bang (tensor T1 T2)))]))).
Proof.
intros i IL LL b E A H. intros h h1. intros.  induction i.
inversion H0. lia.
subst.
apply notqext_nottyped with (a:=Let E b) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Let E b) (T:=A) in H;auto.
inversion H. contradict H2. auto.

inversion H0. inversion H4.
subst. inversion H8. inversion H15.
subst. apply split_ident in H7.
subst. inversion H13.
inversion H6. subst. inversion H16.
inversion H21. subst. apply split_ident in H10.
subst. inversion H20. inversion H9.
subst. inversion H23. inversion H28. subst.
apply split_ident in H17. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H27;auto.
assert(i0+1+1=i); try lia. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17.
inversion H24.  destruct H30.
inversion H30.
inversion H31. inversion H33.
destruct H35.
exists x.  exists x0. exists x1. repeat split;auto.
left. exists x2.
repeat split; auto.
revert H32.
clear.  intros. lia.
exists x.  exists x0. exists x1.
repeat split; auto. left.
exists x2.
repeat split; auto.
revert H32.
clear.  intros. lia.

inversion H30.
destruct H32.
exists x.  exists x0. exists x1. repeat split;auto.
right.
repeat split; auto.
revert H31.
clear.  intros. lia.
exists x.  exists x0. exists x1.
repeat split; auto. right.
repeat split; auto.
revert H31.
clear.  intros. lia.



apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try lia.
apply IHi in H29. inversion H29.
inversion H3. inversion H12. inversion H18.
inversion H25.  destruct H32.
inversion H32.
inversion H33. inversion H35.
destruct H37.
exists x.  exists x0. exists x1. repeat split;auto.
left. exists x2.
repeat split; auto.
revert H2 H34.
clear.  intros. lia.
exists x.  exists x0. exists x1.
repeat split; auto. left.
exists x2.
repeat split; auto.
revert H2 H34.
clear.  intros. lia.

inversion H32.
exists x.  exists x0. exists x1. repeat split;auto.
right.
repeat split; auto.
revert H2 H33.
clear.  intros. lia.

apply sub_trans with (B:= A2);auto.
apply sub_trans with (B:=A1);auto.
subst.   exists i0. exists T1. exists T2.
repeat split;auto. left. exists A2.
split.  clear. lia. split.
apply sub_trans with (B:=A1);auto.
left.
inversion H23.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
inversion H29. apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H24; auto.
apply H37 in H38. inversion H38.
apply s_all. intros.
unfold ext_eq in H24. assert(h44:=H44).
apply H24 in H44.  apply H43 in h44.
rewrite <- H44. auto.
subst.   exists i0. exists T1. exists T2.
repeat split;auto. left. exists A2.
split.  clear. lia. split.
apply sub_trans with (B:=A1);auto.
right.
inversion H23.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
inversion H29. apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H24; auto.
apply H37 in H38. inversion H38.
apply s_all. intros.
unfold ext_eq in H24. assert(h44:=H44).
apply H24 in H44.  apply H43 in h44.
rewrite <- H44. auto.

subst.
apply notqext_nottyped with (a:=Let E b) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=Let E b) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try lia. subst.
apply IHi in H22. inversion H22. inversion H3.
inversion H9.  inversion H12. inversion H18.
inversion H25.  inversion H26. inversion H27.
inversion H29.
destruct H31.
  exists x.  exists x0. exists x1.
repeat split; auto. left.
exists x2. split.  revert H28.
clear.  intros. lia.
split;  auto.
  exists x.  exists x0. exists x1.
repeat split; auto. left.
exists x2. split.  revert H28.
clear.  intros. lia.
split;  auto.

inversion H26.
destruct H28.
  exists x.  exists x0. exists x1.
repeat split; auto.  right
 . split.  revert H27.
clear.  intros. lia. auto.
  exists x.  exists x0. exists x1.
repeat split; auto. right
. split.  revert H27.
clear.  intros. lia. auto.

apply sub_trans with (B:=A1);auto.

subst.   exists i1. exists T1. exists T2.
repeat split;auto. left. exists A1.
split.  clear. lia. split. auto.
left.
inversion H16.
apply ss_general with (lL2:=lL0) (lL3:=lL3);auto.
inversion H22. apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H17; auto.
apply H30 in H31. inversion H31.
apply s_all. intros.
unfold ext_eq in H17. assert(h37:=H37).
apply H17 in H37.  apply H36 in h37.
rewrite <- H37. auto.


subst.   exists i1. exists T1. exists T2.
repeat split;auto. left. exists A1.
split.  clear. lia. split. auto.
right.
inversion H16.
apply ss_general with (lL2:=lL0) (lL3:=lL3);auto.
inversion H22. apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H17; auto.
apply H30 in H31. inversion H31.
apply s_all. intros.
unfold ext_eq in H17. assert(h37:=H37).
apply H17 in H37.  apply H36 in h37.
rewrite <- H37. auto.

subst.
apply notqext_nottyped with (a:=Let E b) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=Let E b) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.

subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. apply Subtyping_bang_inv in H29.
inversion H29. inversion H3.
subst. inversion H26.

subst. inversion H19. apply split_nil in H9.
inversion H8. inversion H9. subst.
inversion H20. apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try lia.
apply IHi in H22. inversion H22.
inversion H25.
inversion H26.  inversion H27.
inversion H30.
destruct H32. inversion H32.  inversion H33.
inversion H35.
exists x.  exists x0. exists x1.
repeat split; auto. left.
exists x2. split. revert H10 H34 H2.
clear.  intros. lia. split;auto.

inversion H32. exists x.  exists x0. exists x1.
repeat split; auto. right.
split. revert H10 H33 H2.
clear.  intros. lia. auto.

apply sub_trans with (B:=bang A1);auto.

subst.
subst.   exists i2. exists T1. exists T2.
repeat split;auto. left. exists (bang A1).
split.  clear. lia. split. auto.
left.
inversion H23. inversion H20. inversion H8.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H24; auto.
apply H30 in H36. inversion H36.
apply s_all. intros.
unfold ext_eq in H24. assert(h42:=H42).
apply H24 in H42.  apply H41 in h42.
rewrite <- H42. auto. rewrite H25. auto.

subst.
exists i2. exists T1. exists T2.
repeat split;auto. left. exists (bang A1).
split.  clear. lia. split. auto.
right.
inversion H23. inversion H20. inversion H8.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H24; auto.
apply H30 in H36. inversion H36.
apply s_all. intros.
unfold ext_eq in H24. assert(h42:=H42).
apply H24 in H42.  apply H41 in h42.
rewrite <- H42. auto. rewrite H25. auto.

subst.
apply notqext_nottyped with (a:=Let E b) (T:=bang A1) in H;auto.
inversion H. contradict H3. auto.

subst.
exists i0. exists T1. exists T2.
repeat split;auto. right.
split.  clear. lia.
left.
inversion H8. inversion H15.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H9; auto.
apply H23 in H24. inversion H24.
apply s_all. intros.
unfold ext_eq in H9. assert(h30:=H30).
apply H9 in H30.  apply H29 in h30.
rewrite <- H30. auto. rewrite H20. auto.


subst.
exists i0. exists T1. exists T2.
repeat split;auto. right.
split.  clear. lia.
right.
inversion H8. inversion H15.
apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
apply s_all. intros.
apply eq_ext_double  with (x1:=x) in H9; auto.
apply H23 in H24. inversion H24.
apply s_all. intros.
unfold ext_eq in H9. assert(h30:=H30).
apply H9 in H30.  apply H29 in h30.
rewrite <- H30. auto. rewrite H20. auto.

subst.
apply notqext_nottyped with (a:=Let E b) (T:=A) in H;auto.
inversion H. contradict H3. apply in_eq.

subst.
apply notqext_nottyped with (a:=Let E b) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

Theorem STAR_LL: forall i IL LL,
~(In (is_qexp (CON STAR)) IL)->
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON STAR) one))
 -> LL = [].
Proof.
intros. induction i.
inversion H1. lia.
apply notqext_nottyped with (lt:=LL) (T:=one) in H;auto.
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
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=one)in H27;auto.
assert(i0+1+1= i);try lia. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A0);auto. auto.
subst. inversion H23. auto. subst.
inversion H23. auto.
 subst.
inversion H23. auto.
apply notqext_nottyped with (lt:=lL0) (T:=A1) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
auto. auto. subst. inversion H16. auto.
subst. inversion H16. auto.
subst. inversion H16. auto.
apply notqext_nottyped with (lt:=lL2) (T:=A0) in H;auto.
inversion H. subst. contradict H12. apply in_eq.
auto. subst. inversion H8. auto.
subst. inversion H8. auto.
apply notqext_nottyped with (lt:=LL) (T:=one) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed.



Theorem STAR_LL2: forall i IL LL,
~(In (is_qexp (CON STAR)) IL)->
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_(typeof (CON STAR) (bang one)))
 -> LL = [].
Proof.
intros. induction i.
inversion H1. lia.
apply notqext_nottyped with (lt:=LL) (T:=bang one) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
auto.

inversion H1;auto. inversion H4. subst.
inversion H14. subst. inversion H11.
subst.  inversion H11.
subst. inversion H8. auto.
subst. inversion H8. auto.
apply notqext_nottyped with (lt:=LL) (T:=bang one) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed.

Theorem if_typed: forall i IL LL a1 a2 b A,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_ (typeof (If b a1 a2) A)) ->
 ~(In (is_qexp (If b a1 a2)) IL) ->
 (exists j B, j+1+1 <= i /\ Subtyping B A /\
splitseq prog j IL LL [Conj (atom_ (typeof b bool)) (And (atom_ (typeof a1 B)) (atom_(typeof a2 B)))])
\/ (exists j, j+1 <= i /\ validT A /\
splitseq prog j IL LL [Conj (atom_ (typeof b bool)) (And (atom_ (typeof a1 A)) (atom_(typeof a2 A)))]).
Proof.
intros. induction i.
inversion H0. lia.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H2. auto.

inversion H0. inversion H4.
subst. inversion H8. inversion H15.
subst. apply split_ident in H7.
subst. inversion H13.
inversion H6. subst. inversion H16.
inversion H21. subst. apply split_ident in H10.
subst. inversion H20. inversion H9.
subst. inversion H23. inversion H28. subst.
apply split_ident in H17. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H27;auto.
assert(i0+1+1=i); try lia. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12.
left. exists x. exists x0. auto. inversion  H17.
split. lia. auto.
right. inversion H3.  inversion H12.
exists x. split. lia. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try lia.
apply IHi in H29. inversion H29. inversion H3.
inversion H12.
inversion H18.
left. exists x. exists x0. auto.
split. lia. auto.
right. inversion H3.  inversion H12.
exists x. split. lia. auto.
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i0. exists A2.
split. lia.
split. apply sub_trans with (B:=A1);auto.
 auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try lia. subst.
apply IHi in H22. inversion H22. inversion H3.
inversion H9.
left. exists x. exists x0. auto. inversion  H12.
split. lia. auto.
right. inversion H3.  inversion H9.
exists x. split. lia. auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i1. exists A1. split.
lia. split. auto.  auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try lia. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6.
left. exists x. exists x0. auto. inversion  H10.
split. lia. auto.
right. inversion H3.  inversion H6.
exists x. split. lia. auto.
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try lia.
apply IHi in H22. inversion H22. inversion H25.
inversion H26.
left. exists x. exists x0. auto. inversion  H27.
split. lia. auto.
right. inversion H25.  inversion H26.
exists x. split. lia. auto.
 apply sub_trans with (B:=bang A1);auto.
left. subst. exists i2. exists (bang A1).
split. lia.
split. auto. inversion H8. subst.
 auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto.
subst. right. exists i0. split. lia.
 split. auto. auto.

subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

Theorem if_a1_a2_eq: forall i IL LL a1 a2 b A,
Subtypecontext IL LL IL LL ->
seq_ i IL LL (atom_ (typeof (If b a1 a2) A)) ->
 ~(In (is_qexp (If b a1 a2)) IL) ->
FQ a1 = FQ a2.

Proof.
intros. induction i.
inversion H0. lia.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H2. auto.

inversion H0. inversion H4.
subst. inversion H8. inversion H15.
subst. apply split_ident in H7.
subst. inversion H13.
inversion H6. subst. inversion H16.
inversion H21. subst. apply split_ident in H10.
subst. inversion H20. inversion H9.
subst. inversion H23. inversion H28. subst.
apply split_ident in H17. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=lL2) (B:=A) in H27;auto.
assert(i0+1+1=i); try lia. subst.
apply IHi in H27. inversion H27. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try lia.
apply IHi in H29. inversion H29. auto.
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
auto.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A2) in H;auto.
inversion H. contradict H18. subst.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A2) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H7.
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try lia. subst.
apply IHi in H22. inversion H22. auto.
apply sub_trans with (B:=A1);auto.
auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try lia. subst.
apply IHi in H20. inversion H20. auto.
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try lia.
apply IHi in H22. inversion H22.  auto.
 apply sub_trans with (B:=bang A1);auto.
auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto.
subst. auto.
subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=If b a1 a2) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

(* formerly testing4 *)
Theorem sub_one_inv: forall i IL a,
~(In (is_qexp (CON UNBOX)) IL)->
is_value a ->
Subtypecontext IL [] IL [] -> ~(In (is_qexp a) IL) ->
seq_ i IL [] (atom_(typeof a one))
 -> a = CON STAR.
Proof.
intros i IL a H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=[]) (T:=one) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.


assert (In (typeof (CON (Qvar x)) one) IL \/ In (typeof (CON (Qvar x)) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  one_bang_one in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  one_bang_one in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_one in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. auto. auto. destruct H3.
eapply  notqext_nottyped with (a:=CON (Qvar x)) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON (Qvar x)) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Circ t i0 a0) one) IL \/ In (typeof (Circ t i0 a0) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  one_bang_one in H17.
destruct H17; subst;  inversion H14.  inversion H11. assert(i1=i); try lia.
subst. apply split_nil  in H10.  inversion H10. subst. auto. subst.
assert(H16':=H16).
apply  one_bang_one in H16. destruct H16; subst. inversion H6.
rewrite H6 in *. inversion H8. subst.  inversion H16.
apply split_nil  in H12. inversion H12. subst.  inversion H16;auto.
inversion H20. inversion H23.  apply sub_not_bang in H34;auto.
inversion H34.
apply bang_one in H33. subst.   inversion H24. inversion H26.
apply  split_nil  in H14. inversion H14. subst. inversion H26.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H29;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H29;try lia.
rewrite <- H31 in H29. auto. auto. auto. destruct H5.
eapply  notqext_nottyped with (a:=Circ t i0 a0) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=Circ t i0 a0) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.

assert (In (typeof (CON TRUE) one) IL \/ In (typeof (CON TRUE) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  one_bang_one in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  one_bang_one in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_one in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. auto. auto. destruct H3.
eapply  notqext_nottyped with (a:=CON TRUE) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON TRUE) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.

assert (In (typeof (CON FALSE) one) IL \/ In (typeof (CON FALSE) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  one_bang_one in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  one_bang_one in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_one in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. auto. auto. destruct H3.
eapply  notqext_nottyped with (a:=CON FALSE) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON FALSE) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.

auto.


assert (In (typeof (CON (BOX T)) one) IL \/ In (typeof (CON (BOX T)) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  one_bang_one in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i1=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  one_bang_one in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.   inversion H33.
apply bang_one in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply bang_one in  H34.
inversion H34.   auto. apply one_bang_one in H17. destruct H17;inversion H17. auto.
destruct H4. eapply  notqext_nottyped with (a:=CON (BOX T)) (T:=one) in H0;auto.
inversion H0. contradict H5. auto.
eapply  notqext_nottyped with (a:=CON (BOX T)) (T:= bang one) in H0;auto.
inversion H0. contradict H5. auto.



assert (In (typeof (CON UNBOX) one) IL \/ In (typeof (CON UNBOX) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  one_bang_one in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  one_bang_one in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_one in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. apply bang_one in  H30.
inversion H30.   auto. apply one_bang_one in H13. destruct H13;inversion H13. auto.
destruct H3. eapply  notqext_nottyped with (a:=CON UNBOX) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON UNBOX) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (CON REV) one) IL \/ In (typeof (CON REV) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  one_bang_one in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  one_bang_one in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_one in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. apply bang_one in  H30.
inversion H30.   auto. apply one_bang_one in H13. destruct H13;inversion H13. auto.
destruct H3. eapply  notqext_nottyped with (a:=CON REV) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON REV) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Fun f) one) IL \/ In (typeof (Fun f) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  one_bang_one in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i0=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  one_bang_one in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.
   inversion H33.
apply bang_one in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. auto. auto.
destruct H4. eapply  notqext_nottyped with (a:=Fun f) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:= Fun f) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Prod v w) one) IL \/ In (typeof (Prod v w) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  one_bang_one in H17.
destruct H17; subst;  inversion H14.  inversion H11. assert(i0=i); try lia.
subst. apply split_nil  in H10.  inversion H10. subst. auto. subst.
assert(H16':=H16).
apply  one_bang_one in H16. destruct H16; subst. inversion H6.
rewrite H6 in *. inversion H8. subst.  inversion H16.
apply split_nil  in H12. inversion H12. subst.  inversion H16;auto.
inversion H20. inversion H23.  apply sub_not_bang in H34;auto.
   inversion H34.
apply bang_one in H33. subst.   inversion H24. inversion H26.
apply  split_nil  in H14. inversion H14. subst. inversion H26.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H29;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
rewrite <- H31 in H29. auto. auto. auto.
destruct H5. eapply  notqext_nottyped with (a:=Prod v w) (T:=one) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:= Prod v w) (T:= bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (App (CON UNBOX) v) one) IL \/ In (typeof (App (CON UNBOX) v) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  one_bang_one in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i0=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  one_bang_one in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.
   inversion H33.
apply bang_one in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= one) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto.
 subst. inversion H22. inversion H27. inversion H32.
apply split_nil in H28.  inversion H28. subst.
apply split_nil in H37.  inversion H37. subst.
apply unbox_arrow_one in H41;auto. inversion H41.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H13. auto. auto.
subst. inversion H10. inversion H14.
apply split_nil in H9.  inversion H9. subst.
apply split_nil in H19.  inversion H19. subst.
apply unbox_arrow_one2 in H23;auto. inversion H23.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H8. auto. auto. destruct H4.
apply notqext_nottyped with (T:=one) (lt:=[])in H1;auto.
inversion H1. contradict H5. auto.
apply notqext_nottyped with (T:=bang one) (lt:=[])in H1;auto.
inversion H1. contradict H5. auto.
Qed.

(* formerly testing4' *)
Theorem sub_bangone_inv: forall i IL a,
~(In (is_qexp (CON UNBOX)) IL)->
is_value a ->
Subtypecontext IL [] IL [] -> ~(In (is_qexp a) IL) ->
seq_ i IL [] (atom_(typeof a (bang one)))
 -> a = CON STAR.
Proof.
intros i IL a H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=[]) (T:= bang one) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.



assert (In (typeof (CON (Qvar x)) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_one in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. auto.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:=bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Circ t i0 a0) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14.
apply bang_one in H16.  subst. inversion H8.
apply split_nil  in H10. inversion H10. subst.  inversion H15.
assert(i=i2+1); try lia.
apply seq_mono_cor with (k:= i2 + 1 ) in H17;try lia.
rewrite <- H19 in H17. auto. auto.
apply  notqext_nottyped with (a:=Circ t i0 a0) (T:=bang one) in H0;auto.
inversion H0. contradict H6. auto.


assert (In (typeof (CON TRUE) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_one in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. auto.
apply  notqext_nottyped with (a:=CON TRUE) (T:=bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (CON FALSE) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_one in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. auto.
apply  notqext_nottyped with (a:=CON FALSE) (T:=bang one) in H0;auto.
inversion H0. contradict H4. auto.

auto.


assert (In (typeof (CON (BOX T)) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_one in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto. apply bang_one in  H17. inversion H17.
auto.
apply  notqext_nottyped with (a:=CON (BOX T)) (T:=bang one) in H0;auto.
inversion H0. contradict H5. auto.



assert (In (typeof (CON UNBOX) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_one in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. apply bang_one in  H13. inversion H13.
auto.
apply  notqext_nottyped with (a:=CON UNBOX) (T:=bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (CON REV) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_one in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. apply bang_one in  H13. inversion H13.
auto.
apply  notqext_nottyped with (a:=CON REV) (T:=bang one) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Fun f) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_one in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto. auto.
apply  notqext_nottyped with (a:=Fun f) (T:=bang one) in H0;auto.
inversion H0. contradict H5. auto.


assert (In (typeof (Prod v w) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14.
apply bang_one in H16.  subst. inversion H8.
apply split_nil  in H10. inversion H10. subst.  inversion H15.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H17;try lia.
rewrite <- H19 in H17. auto. auto.
apply  notqext_nottyped with (a:=Prod v w) (T:=bang one) in H0;auto.
inversion H0. contradict H6. auto.


assert (In (typeof (App (CON UNBOX) v) (bang one)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_one in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto.
subst. inversion H10. inversion H14.
apply split_nil in H9.  inversion H9. subst.
apply split_nil in H19.  inversion H19. subst.
apply unbox_arrow_one in H23;auto. inversion H23.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H8. auto. auto.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:=bang one) in H0;auto.
inversion H0.  contradict H5. auto.
Qed.

(* formerly testing5 *)
Theorem sub_bool_inv: forall i IL a,
~(In (is_qexp (CON UNBOX)) IL)->
is_value a ->
Subtypecontext IL [] IL [] -> ~(In (is_qexp a) IL) ->
seq_ i IL [] (atom_(typeof a bool))
 -> a = CON FALSE \/ a = CON TRUE.
Proof.
intros i IL a H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=[]) (T:=bool) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.

assert (In (typeof (CON (Qvar x)) bool) IL \/ In (typeof (CON (Qvar x)) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  bool_bang_bool in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  bool_bang_bool in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.
inversion H32.
apply bang_bool in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H27;auto.
assert (i = i3+1+1+1 );try lia.
apply seq_mono_cor with (k:= i3 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. auto. auto. destruct H3.
eapply  notqext_nottyped with (a:=(CON (Qvar x))) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=(CON (Qvar x))) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.

assert (In (typeof (Circ t i0 a0) bool) IL \/ In (typeof (Circ t i0 a0) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  bool_bang_bool in H17.
destruct H17; subst;  inversion H14.  inversion H11. assert(i1=i); try lia.
subst. apply split_nil  in H10.  inversion H10. subst. auto. subst.
assert(H16':=H16).
apply  bool_bang_bool in H16. destruct H16; subst. inversion H6.
rewrite H6 in *. inversion H8. subst.  inversion H16.
apply split_nil  in H12. inversion H12. subst.  inversion H16;auto.
inversion H20. inversion H23.  apply sub_not_bang in H34;auto.
inversion H34.
apply bang_bool in H33. subst.   inversion H24. inversion H26.
apply  split_nil  in H14. inversion H14. subst. inversion H26.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H29;auto.
assert (i = i1+1+1+1 );try lia.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H29;try lia.
rewrite <- H31 in H29. auto. auto. auto. destruct H5.
eapply  notqext_nottyped with (a:=Circ t i0 a0) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=Circ t i0 a0) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.


right. auto. left. auto.

assert (In (typeof (CON STAR) bool) IL \/ In (typeof (CON STAR) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  bool_bang_bool in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  bool_bang_bool in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_bool in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. auto. auto. destruct H3.
eapply  notqext_nottyped with (a:=CON STAR) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON STAR) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.

assert (In (typeof (CON (BOX T)) bool) IL \/ In (typeof (CON (BOX T)) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  bool_bang_bool in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i1=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  bool_bang_bool in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.   inversion H33.
apply bang_bool in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. apply bang_bool in  H34.
inversion H34.   auto. apply bool_bang_bool in H17. destruct H17;inversion H17. auto.
destruct H4. eapply  notqext_nottyped with (a:=CON (BOX T)) (T:=bool) in H0;auto.
inversion H0. contradict H5. auto.
eapply  notqext_nottyped with (a:=CON (BOX T)) (T:= bang bool) in H0;auto.
inversion H0. contradict H5. auto.



assert (In (typeof (CON UNBOX) bool) IL \/ In (typeof (CON UNBOX) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  bool_bang_bool in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  bool_bang_bool in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_bool in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. apply bang_bool in  H30.
inversion H30.   auto. apply bool_bang_bool in H13. destruct H13;inversion H13. auto.
destruct H3. eapply  notqext_nottyped with (a:=CON UNBOX) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON UNBOX) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (CON REV) bool) IL \/ In (typeof (CON REV) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  bool_bang_bool in H15.
destruct H15; subst;  inversion H12.  inversion H9. assert(i1=i); try lia.
subst. apply split_nil  in H8.  inversion H8. subst. auto. subst.
assert(H14':=H14).
apply  bool_bang_bool in H14. destruct H14; subst. inversion H4.
rewrite H4 in *. inversion H6. subst.  inversion H14.
apply split_nil  in H10. inversion H10. subst.  inversion H14;auto.
inversion H18. inversion H21.  apply sub_not_bang in H32;auto.   inversion H32.
apply bang_bool in H31. subst.   inversion H22. inversion H24.
apply  split_nil  in H12. inversion H12. subst. inversion H24.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H27;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H27;try lia.
rewrite <- H29 in H27. auto. apply bang_bool in  H30.
inversion H30.   auto. apply bool_bang_bool in H13. destruct H13;inversion H13. auto.
destruct H3. eapply  notqext_nottyped with (a:=CON REV) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:=CON REV) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Fun f) bool) IL \/ In (typeof (Fun f) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  bool_bang_bool in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i0=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  bool_bang_bool in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.
   inversion H33.
apply bang_bool in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto. auto. auto.
destruct H4. eapply  notqext_nottyped with (a:=Fun f) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:= Fun f) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Prod v w) bool) IL \/ In (typeof (Prod v w) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  bool_bang_bool in H17.
destruct H17; subst;  inversion H14.  inversion H11. assert(i0=i); try lia.
subst. apply split_nil  in H10.  inversion H10. subst. auto. subst.
assert(H16':=H16).
apply  bool_bang_bool in H16. destruct H16; subst. inversion H6.
rewrite H6 in *. inversion H8. subst.  inversion H16.
apply split_nil  in H12. inversion H12. subst.  inversion H16;auto.
inversion H20. inversion H23.  apply sub_not_bang in H34;auto.
   inversion H34.
apply bang_bool in H33. subst.   inversion H24. inversion H26.
apply  split_nil  in H14. inversion H14. subst. inversion H26.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H29;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
rewrite <- H31 in H29. auto. auto. auto.
destruct H5. eapply  notqext_nottyped with (a:=Prod v w) (T:=bool) in H0;auto.
inversion H0. contradict H4. auto.
eapply  notqext_nottyped with (a:= Prod v w) (T:= bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (App (CON UNBOX) v) bool) IL \/ In (typeof (App (CON UNBOX) v) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  bool_bang_bool in H16.
destruct H16; subst;  inversion H13.  inversion H10. assert(i0=i); try lia.
subst. apply split_nil  in H9.  inversion H9. subst. auto. subst.
assert(H15':=H15).
apply  bool_bang_bool in H15. destruct H15; subst. inversion H5.
rewrite H5 in *. inversion H7. subst.  inversion H15.
apply split_nil  in H11. inversion H11. subst.  inversion H15;auto.
inversion H19. inversion H22.  apply sub_not_bang in H33;auto.
   inversion H33.
apply bang_bool in H32. subst.   inversion H23. inversion H25.
apply  split_nil  in H13. inversion H13. subst. inversion H25.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bool) in H28;auto.
assert (i = i0+1+1+1 );try lia.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
rewrite <- H30 in H28. auto.
 subst. inversion H22. inversion H27. inversion H32.
apply split_nil in H28.  inversion H28. subst.
apply split_nil in H37.  inversion H37. subst.
apply unbox_arrow_bool in H41;auto. inversion H41.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H13. auto. auto.
subst. inversion H10. inversion H14.
apply split_nil in H9.  inversion H9. subst.
apply split_nil in H19.  inversion H19. subst.
apply unbox_arrow_bool2 in H23;auto. inversion H23.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H8. auto. auto. destruct H4.
apply notqext_nottyped with (T:=bool) (lt:=[])in H1;auto.
inversion H1. contradict H5. auto.
apply notqext_nottyped with (T:=bang bool) (lt:=[])in H1;auto.
inversion H1. contradict H5. auto.
Qed.

(* formerly testing5' *)
Theorem sub_bangbool_inv: forall i IL a,
~(In (is_qexp (CON UNBOX)) IL)->
is_value a ->
Subtypecontext IL [] IL [] -> ~(In (is_qexp a) IL) ->
seq_ i IL [] (atom_(typeof a (bang bool)))
 -> a = CON FALSE \/ a = CON TRUE.
Proof.
intros i IL a H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=[]) (T:= bang bool) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.


assert (In (typeof (CON (Qvar x)) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_bool in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. auto.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:=bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Circ t i0 a0) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14.
apply bang_bool in H16.  subst. inversion H8.
apply split_nil  in H10. inversion H10. subst.  inversion H15.
assert(i=i2+1); try lia.
apply seq_mono_cor with (k:= i2 + 1 ) in H17;try lia.
rewrite <- H19 in H17. auto. auto.
apply  notqext_nottyped with (a:=Circ t i0 a0) (T:=bang bool) in H0;auto.
inversion H0. contradict H6. auto.

right. auto. left. auto.

assert (In (typeof (CON STAR) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_bool in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. auto.
apply  notqext_nottyped with (a:=CON STAR) (T:=bang bool) in H0;auto.
inversion H0. contradict H4. auto.




assert (In (typeof (CON (BOX T)) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_bool in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto. apply bang_bool in  H17. inversion H17.
auto.
apply  notqext_nottyped with (a:=CON (BOX T)) (T:=bang bool) in H0;auto.
inversion H0. contradict H5. auto.



assert (In (typeof (CON UNBOX) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_bool in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. apply bang_bool in  H13. inversion H13.
auto.
apply  notqext_nottyped with (a:=CON UNBOX) (T:=bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (CON REV) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12.
apply bang_bool in H14.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H15;try lia.
rewrite <- H17 in H15. auto. apply bang_bool in  H13. inversion H13.
auto.
apply  notqext_nottyped with (a:=CON REV) (T:=bang bool) in H0;auto.
inversion H0. contradict H4. auto.


assert (In (typeof (Fun f) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_bool in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto. auto.
apply  notqext_nottyped with (a:=Fun f) (T:=bang bool) in H0;auto.
inversion H0. contradict H5. auto.


assert (In (typeof (Prod v w) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14.
apply bang_bool in H16.  subst. inversion H8.
apply split_nil  in H10. inversion H10. subst.  inversion H15.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H17;try lia.
rewrite <- H19 in H17. auto. auto.
apply  notqext_nottyped with (a:=Prod v w) (T:=bang bool) in H0;auto.
inversion H0. contradict H6. auto.


assert (In (typeof (App (CON UNBOX) v) (bang bool)) IL).
induction i. inversion H2.  lia. auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13.
apply bang_bool in H15.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
assert(i=i1+1); try lia.
apply seq_mono_cor with (k:= i1 + 1 ) in H16;try lia.
rewrite <- H18 in H16. auto.
subst. inversion H10. inversion H14.
apply split_nil in H9.  inversion H9. subst.
apply split_nil in H19.  inversion H19. subst.
apply unbox_arrow_bool in H23;auto. inversion H23.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H8. auto. auto.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:=bang bool) in H0;auto.
inversion H0.  contradict H5. auto.
Qed.

(* formerly testing7 *)
Theorem sub_tensor_inv: forall i IL LL a T U,
~(In (is_qexp (CON UNBOX)) IL)->
valid T -> valid U ->
is_value a ->
Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
seq_ i IL LL (atom_(typeof a (tensor T U)))
 -> exists v w, a = Prod v w.
Proof.
intros i IL LL a T U H100 H101 H102. intros. inversion H;subst.
inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= tensor T U) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.
inversion H2.   auto.  inversion H4. subst.  contradict H8.
subst. apply in_eq. subst. contradict H8. subst. apply in_eq.
subst. inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto. inversion H1.
clear H1.  contradict H3. auto.


assert (exists A, In (typeof (CON (Qvar x)) A) IL \/ In (typeof (CON (Qvar x)) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON (Qvar x)) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x0) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


Focus 2.

assert (exists A, In (typeof (CON TRUE) A) IL \/ In (typeof (CON TRUE) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON TRUE) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (Circ t i0 a0) A) IL \/ In (typeof (Circ t i0 a0) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H7. inversion H17.  subst.
 inversion H11. inversion H18. subst. apply split_ident in H10.
subst. inversion H16. inversion H9.  inversion H27.   subst.
inversion H19. inversion H26.  subst. apply  split_ident in H13.
subst. inversion H25.  inversion H12.  inversion H36. subst.
inversion H28. inversion H35. subst.  apply split_ident in H20.
subst.   assert (i = i1+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H34;auto.
rewrite <- H6  in H34. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H33. inversion H35. inversion H37. subst. inversion H13.
inversion H33.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H45;auto.
apply seq_mono_cor with (k:= i3 + 1 + 1 + 1) in H45;try lia.
assert(i=i3+1+1+1); try lia.
rewrite <- H6 in H45.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H38.
subst. apply notqext_nottyped with
 (lt:=[typeof (Circ t i0 a0) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H12. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H6. auto. auto. subst. inversion H24.
inversion H26. inversion H28.  subst. inversion H19. subst.
inversion H10. apply split_nil in H13.  inversion H13. subst.
inversion H24. assert(i=i1+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (Circ t i0 a0) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H9. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H6. auto. auto.
subst. inversion H14. inversion H16. inversion H18.
subst. inversion H8. apply split_nil in H10. inversion H10. subst.
inversion H15.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H29;auto.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H29;try lia.
 assert(i=i1+1+1+1); try lia. rewrite <- H6 in H29.  auto.
apply sub_trans with (B:= bang (tensor A2 A3)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H6.
subst.
inversion H11. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A2 A3)) in H1;auto.
 inversion H1. contradict H6. auto. subst.
apply SubAreVal in  H16. inversion H16. inversion H6.
subst. apply  notqext_nottyped with
(lt:=[typeof (Circ t i0 a0) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H6. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H6. auto. subst. auto.
 inversion H5. destruct H6;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H7. auto. contradict H8. auto.

assert (exists A, In (typeof (CON FALSE) A) IL \/ In (typeof (CON FALSE) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON FALSE) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

assert (exists A, In (typeof (CON STAR) A) IL \/ In (typeof (CON STAR) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON STAR) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (CON (BOX T0)) A) IL \/ In (typeof (CON (BOX T0)) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H26.   subst.
inversion H18. inversion H25.  subst. apply  split_ident in H12.
subst. inversion H24.  inversion H11.  inversion H35. subst.
inversion H27. inversion H34. subst.  apply split_ident in H19.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H33;auto.
rewrite <- H5  in H33. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H32. inversion H34. inversion H36. subst. inversion H12.
inversion H32.  apply split_nil in H19.  inversion H19. subst.
inversion H27. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H44;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H44;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H44.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H37.
inversion H33. inversion H37. inversion H36. inversion H40.
inversion H36. inversion H39. inversion H36.  inversion H41.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON (BOX T0)) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H11. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H5. auto. auto. subst. inversion H23.
inversion H25. inversion H27. subst.   inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H23. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H26;auto.
rewrite <- H30 in H26. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H28. inversion H27.  inversion H29. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON (BOX T0)) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. subst. inversion H15. inversion H8.
subst. inversion H7. apply split_nil in H12. inversion H12. subst.
inversion H19.
inversion H21.  inversion H24. apply Subtyping_bang_inv in H35.
inversion H35. inversion H36. subst. inversion H32. assert(H34':=H34).
apply Subtyping_bang_inv in H34. inversion H34.
inversion H35. inversion H36. subst. inversion H37. subst.
inversion H25. apply split_nil in H13. inversion H13. subst.
inversion H28. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H31;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H31;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H31.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H34'.
inversion H34'. inversion H13.
 apply Subtyping_bang_inv in H36.
inversion H36. inversion H37.  inversion H38. subst. inversion H39.
 inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H5. auto. subst. inversion H9.
inversion H14.  inversion H18. inversion  H17. inversion H21.
inversion  H17. inversion H20. inversion  H17. inversion H22.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON (BOX T0)) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H5. auto. subst. auto.
 inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.


assert (exists A, In (typeof (CON UNBOX) A) IL \/ In (typeof (CON UNBOX) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
inversion H32. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON UNBOX) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. inversion H23.  inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON UNBOX) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12.
 apply Subtyping_bang_inv in H32.
inversion H32. inversion H35.  inversion H36. subst. inversion H37.
 inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
inversion H13.  inversion H17.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON UNBOX) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

assert (exists A, In (typeof (CON REV) A) IL \/ In (typeof (CON REV) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H36.
inversion H32. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON REV) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H27. inversion H23.  inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON REV) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (tensor A1 A2)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12.
 apply Subtyping_bang_inv in H32.
inversion H32. inversion H35.  inversion H36. subst. inversion H37.
 inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A1 A2)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
inversion H13.  inversion H17.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON REV) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (Fun f) A) IL \/ In (typeof (Fun f) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H26.   subst.
inversion H18. inversion H25.  subst. apply  split_ident in H12.
subst. inversion H24.  inversion H11.  inversion H35. subst.
inversion H27. inversion H34. subst.  apply split_ident in H19.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H33;auto.
rewrite <- H5  in H33. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H32. inversion H34. inversion H36. subst. inversion H12.
inversion H32.  apply split_nil in H19.  inversion H19. subst.
inversion H27. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H44;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H44;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H44.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H37.
subst. apply notqext_nottyped with
 (lt:=[typeof (Fun f) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H11. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H5. auto. auto. subst. inversion H23.
inversion H25. inversion H27. subst.  inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H23. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H26;auto.
rewrite <- H30 in H26. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H28. subst.  apply notqext_nottyped with
 (lt:=[typeof (Fun f) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. inversion H15. inversion H17.
subst. inversion H7. apply split_nil in H9. inversion H9. subst.
inversion H14.
inversion H19.  inversion H22. apply Subtyping_bang_inv in H35.
inversion H35. inversion H36. subst. inversion H32. assert(H34':=H34).
apply Subtyping_bang_inv in H34. inversion H34.
inversion H35. inversion H36. inversion H37. subst.
inversion H25. apply split_nil in H11. inversion H11. subst.
inversion H26. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H28;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H28.  auto.
apply sub_trans with (B:= bang (tensor A2 A3)); subst; auto.
subst. apply SubAreVal in H34'.
inversion H34'. inversion H5.
subst.
inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(tensor A2 A3)) in H1;auto.
 inversion H1. contradict H5. auto. subst.
apply SubAreVal in  H15. inversion H15. inversion H5.
subst. apply  notqext_nottyped with
(lt:=[typeof (Fun f) (tensor T U)]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= tensor T U) in H1;auto.
 inversion H1. contradict H5. auto. subst. auto.
 inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.


exists v. exists w. auto.

assert (exists A, In (typeof (App (CON UNBOX) v) A) IL \/
In (typeof (App (CON UNBOX) v) A) LL).
induction i. inversion H2.  lia. exists (tensor T U). right. apply in_eq.
exists (tensor T U). left.   auto.
inversion H2. inversion H6. inversion H16.  subst.
 inversion H10. inversion H17. subst. apply split_ident in H9.
subst. inversion H15. inversion H8.  inversion H26.   subst.
inversion H18. inversion H25.  subst. apply  split_ident in H12.
subst. inversion H24.  inversion H11.  inversion H35. subst.
inversion H27. inversion H34. subst.  apply split_ident in H19.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= tensor T U) in H33;auto.
rewrite <- H5  in H33. auto.  apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. auto. subst.
inversion H32. inversion H34. inversion H36. subst. inversion H12.
inversion H33.  apply split_nil in H19.  inversion H19. subst.
inversion H32. subst. inversion H27. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H35;auto.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H35;try lia.
assert(i=i1+1+1+1); try lia.
rewrite <- H5 in H35.   auto.
apply sub_trans with (B:= tensor A3 A4);auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst. inversion H37.
subst.
inversion H27. inversion H33. subst.
apply split_ident in H19. subst. inversion H32.
apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_tensor2 in H34;auto.
inversion H34. inversion H39;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H41. auto. contradict H42.  auto.
auto.
subst. apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (tensor A3 A4)]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H11. apply in_eq.
 subst.
apply notqext_nottyped with (lt:=[]) (T:= tensor A3 A4) in H1;auto.
 inversion H1. contradict H5. auto.
auto.
subst. inversion H23.
inversion H25. inversion H27. subst.   inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H23. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H26;auto.
rewrite <- H30 in H26. auto.
apply sub_trans with (B:= tensor A1 A2);auto.
subst. inversion H9. apply split_nil in H12. inversion H12.
subst. inversion H23. inversion H18. subst.
assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H26;auto.
rewrite <- H5 in H26. auto.
apply sub_trans with (B:= tensor A1 A2);auto. subst.
inversion H18. inversion H24.
subst. inversion H23.
subst. apply split_ident in H12. subst.
apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_tensor2 in H27;auto.
inversion H27. inversion H12;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H22. auto. contradict H25.  auto.
auto.

subst.
  apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (tensor A1 A2)]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= tensor A1 A2) in H1;auto.
 inversion H1. contradict H5. auto. auto.
subst. inversion H13. inversion H15. inversion H17.
subst. inversion H7. apply split_nil in H9. inversion H9. subst.
inversion H14.
inversion H19.  inversion H22. apply Subtyping_bang_inv in H35.
inversion H35. inversion H36. subst. inversion H32. assert(H34':=H34).
apply Subtyping_bang_inv in H34. inversion H34.
inversion H35. inversion H36. inversion H37. subst.
inversion H25. apply split_nil in H11. inversion H11. subst.
inversion H26. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= tensor T U) in H28;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H28;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H5 in H28.  auto.
apply sub_trans with (B:= bang (tensor A2 A3)); subst; auto.
subst. apply SubAreVal in H34'.
inversion H34'. inversion H5. inversion H10.
subst. inversion H29. apply split_nil in H11.
inversion H11. subst.  inversion H26. apply split_nil  in H12.
inversion H12. subst.
apply unbox_arrow_tensor in H30;auto.
inversion H30. inversion H5.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto;
inversion H100. contradict H13. auto. inversion H8.
exists (bang (tensor A2 A3)). left. auto.
subst. inversion H18. subst. inversion H10.
inversion H15. subst. apply split_ident in H9. subst.
inversion H14. apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_tensor2 in H17;auto.
inversion H17. inversion H21;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
inversion H100. contradict H23. auto. contradict H24.  auto.
auto. subst. exists (tensor T U). right. apply in_eq.
subst. exists (tensor T U). left. auto.
inversion H4. destruct H5;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H6. auto. contradict H7. auto.
Qed.

(* formerly testing7' *)
Theorem sub_bangtensor_inv: forall i IL LL a T U,
~(In (is_qexp (CON UNBOX)) IL)->
is_value a ->
Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
seq_ i IL LL (atom_(typeof a (bang (tensor T U))))
 -> exists v w, a = Prod v w.
Proof.
intros i IL LL a T U H100. intros. inversion H;subst. inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= bang (tensor T U)) in H1;auto. inversion H1.
clear H1.  subst. contradict H8. apply in_eq.
apply notqext_nottyped with (lt:=LL) (T:= bang (tensor T U)) in H1;auto. inversion H1.
clear H1. contradict H7. auto.

assert (exists A, In (typeof (CON (Qvar x)) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON (Qvar x)) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON (Qvar x)) (T:= x0) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (Circ t i0 a0 ) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Circ t i0 a0 ) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H7. apply  Subtyping_bang_inv in H17.
inversion H17.  inversion H18.  subst.  inversion H14. assert(H16':=H16).
apply Subtyping_bang_inv in H16. inversion H16. inversion H17.
clear H16 H17. inversion H18. inversion H19.  subst. inversion H8.
apply split_nil  in H10. inversion H11. subst.  inversion H15.
inversion H17. subst. inversion H24. subst.
apply  Subtyping_bang_inv in H21. inversion H21.
inversion H6. subst. inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14.
inversion H14; clear H14. inversion H21. clear H21.
inversion H14. clear H14. inversion H26. subst.
clear H26. inversion H25. apply split_nil in H12.
inversion H12. subst. inversion H26. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H28;auto.
assert(i=i1+1+1+1); try lia.
apply seq_mono_cor with (k:= i1+1+1 + 1 ) in H28;try lia.
rewrite <- H6 in H28. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H6.
subst. inversion H10. inversion H6.
apply  notqext_nottyped with (a:=Circ t i0 a0 ) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H28. auto. subst.
subst. apply SubAreVal in H16'. inversion H16'. inversion H6.
 subst.
apply In_cntxt_ll with (a:= Circ t i0 a0) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H5.
apply  notqext_nottyped with (a:=Circ t i0 a0) (T:= x) in H0;auto.
inversion H0. contradict H7. auto.




assert (exists A, In (typeof (CON TRUE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON TRUE) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON TRUE) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON TRUE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON FALSE) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON FALSE) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON FALSE) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON FALSE) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON STAR) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst.
apply  notqext_nottyped with (a:=CON STAR) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
subst.
apply In_cntxt_ll with (a:=CON STAR) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON STAR) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.

assert (exists A, In (typeof (CON (BOX T0)) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON (BOX T0)) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13 . assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H23. subst.
apply  Subtyping_bang_inv in H20. inversion H20.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H20. clear H20.
inversion H13. clear H13. inversion H25. subst.
clear H25. inversion H24. apply split_nil in H11.
inversion H11. subst. inversion H25. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H27;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H27;try lia.
rewrite <- H5 in H27. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
subst. apply Subtyping_bang_inv in  H25. inversion H25.
inversion H5. inversion H8.  subst. inversion H13.
subst.
apply  notqext_nottyped with (a:=CON (BOX T0)) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H5. auto.
subst. apply SubAreVal in H15'. inversion H15'. inversion H5.
apply Subtyping_bang_inv in  H17. inversion H17.
inversion H18. inversion H19. subst. inversion H20.
subst.
apply In_cntxt_ll with (a:=CON (BOX T0)) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=CON (BOX T0)) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.


assert (exists A, In (typeof (CON UNBOX) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON UNBOX) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst. apply Subtyping_bang_inv in  H11. inversion H11.
inversion H4. inversion H12. subst. inversion H19.
subst.
apply  notqext_nottyped with (a:=CON UNBOX) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
apply Subtyping_bang_inv in  H13. inversion H13.
inversion H16. inversion H17. subst. inversion H18.
subst.
apply In_cntxt_ll with (a:=CON UNBOX) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON UNBOX) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (CON REV) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:=CON REV) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H5. apply  Subtyping_bang_inv in H15.
inversion H15.  inversion H16.  subst.  inversion H12. assert(H14':=H14).
apply Subtyping_bang_inv in H14. inversion H14. inversion H15.
clear H14 H15. inversion H16. inversion H17.  subst. inversion H6.
apply split_nil  in H8. inversion H8. subst.  inversion H13.
inversion H15. subst. inversion H22. subst.
apply  Subtyping_bang_inv in H19. inversion H19.
inversion H4. subst. inversion H10. assert(H12':=H12).
apply Subtyping_bang_inv in H12.
inversion H12; clear H12. inversion H19. clear H19.
inversion H12. clear H12. inversion H24. subst.
clear H24. inversion H23. apply split_nil in H10.
inversion H10. subst. inversion H24. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H26;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H26;try lia.
rewrite <- H4 in H26. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H12'. inversion H12'. inversion H4.
subst. apply Subtyping_bang_inv in  H11. inversion H11.
inversion H4. inversion H12. subst. inversion H19.
subst.
apply  notqext_nottyped with (a:=CON REV) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H4. auto.
subst. apply SubAreVal in H14'. inversion H14'. inversion H4.
apply Subtyping_bang_inv in  H13. inversion H13.
inversion H16. inversion H17. subst. inversion H18.
subst.
apply In_cntxt_ll with (a:=CON REV) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H3.
apply  notqext_nottyped with (a:=CON REV) (T:= x) in H0;auto.
inversion H0. contradict H5. auto.


assert (exists A, In (typeof (Fun f) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= Fun f) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13. assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H23. subst.
apply  Subtyping_bang_inv in H20. inversion H20.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H20. clear H20.
inversion H13. clear H13. inversion H25. subst.
clear H25. inversion H24. apply split_nil in H11.
inversion H11. subst. inversion H25. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H27;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H27;try lia.
rewrite <- H5 in H27. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
apply  notqext_nottyped with (a:=Fun f) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H5. auto. subst.
subst. apply SubAreVal in H15'. inversion H15'. inversion H5.
 subst.
apply In_cntxt_ll with (a:=Fun f) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=Fun f) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.


exists v. exists w. auto.


assert (exists A, In (typeof (App (CON UNBOX) v) A) IL).
induction i. inversion H2.  lia.
subst.
apply In_cntxt_ll with (a:= App (CON UNBOX) v) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. exists (bang (tensor T U)).  auto.
inversion H2. inversion H6. apply  Subtyping_bang_inv in H16.
inversion H16.  inversion H17.  subst.  inversion H13. assert(H15':=H15).
apply Subtyping_bang_inv in H15. inversion H15. inversion H16.
clear H15 H16. inversion H17. inversion H18.  subst. inversion H7.
apply split_nil  in H9. inversion H9. subst.  inversion H14.
inversion H16. subst. inversion H23. subst.
apply  Subtyping_bang_inv in H20. inversion H20.
inversion H5. subst. inversion H11. assert(H13':=H13).
apply Subtyping_bang_inv in H13.
inversion H13; clear H13. inversion H20. clear H20.
inversion H13. clear H13. inversion H25. subst.
clear H25. inversion H24. apply split_nil in H11.
inversion H11. subst. inversion H25. inversion H10. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= bang(tensor T U)) in H27;auto.
assert(i=i0+1+1+1); try lia.
apply seq_mono_cor with (k:= i0+1+1 + 1 ) in H27;try lia.
rewrite <- H5 in H27. auto.
 apply sub_trans with (B:= bang(tensor A1 A2)); auto.
subst. apply SubAreVal in H13'. inversion H13'. inversion H5.
subst. inversion H28.
apply split_nil in H11.  inversion H11. subst.
inversion H26.
apply split_nil in H12.  inversion H12. subst.
inversion H10. subst.
apply unbox_arrow_tensor in H30;auto. inversion H30. inversion H5.
eapply notqext_nottyped with (T:=x) (lt:=[])in H100;auto.
 inversion H100. contradict H13. auto. inversion H8.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:=bang (tensor A1 A2)) in H0;auto.
inversion H0. contradict H26. auto. subst.
apply SubAreVal in H15'. inversion H15'. inversion H5.
 subst.
inversion H10. inversion H15.  subst. inversion H14.
apply split_ident in H9. subst. apply subcntxt_splits with (ll1:=LL1)(ll2:=LL2) in H0;auto.
inversion H0.
apply unbox_arrow_tensor in H18;auto. inversion H18. inversion H9;
eapply notqext_nottyped with (T:=x) (lt:=LL1)in H100;auto;
 inversion H100. contradict H13. auto. contradict H17. auto. auto. subst.
apply In_cntxt_ll with (a:=App (CON UNBOX) v) (t:= bang (tensor T U)) in H0; auto.
inversion H0. apply in_eq. subst.  exists (bang (tensor T U)).
auto. inversion H4.
apply  notqext_nottyped with (a:=App (CON UNBOX) v) (T:= x) in H0;auto.
inversion H0. contradict H6. auto.
Qed.


(* formerly testing8 *)
Theorem sub_arrow_inv: forall i IL LL a T U,
~(In (is_qexp (CON UNBOX)) IL)->
validT T -> validT U -> (forall v, a = App (CON UNBOX) v ->
~In (is_qexp v) IL)->
 is_value a ->
Subtypecontext IL LL IL LL -> ~(In (is_qexp a) IL) ->
seq_ i IL LL (atom_(typeof a (arrow T U)))
 -> (exists f,  a = Fun f) \/ (exists T0, a = CON (BOX T0)) \/ (a=CON UNBOX)
\/ (a=CON REV) \/
(exists t i u, a = App (CON UNBOX) (Circ t i u)).
Proof.
intros i IL LL a T U H100 H101 H102 H103. intros. inversion H;subst.
inversion H2. inversion H4. subst. inversion H5.
inversion H13. inversion H17. apply split_nil in H7. inversion H7. subst.
inversion H19. contradict H1;auto. subst. inversion H5. apply split_nil in H7.
inversion H7. subst. inversion H12. inversion H16. inversion  H18. contradict H1;auto.
apply notqext_nottyped with (lt:=LL) (T:= arrow T U) in H1;auto. inversion H1.
clear H1.  contradict H7. auto.
inversion H2.   auto.  inversion H4. subst.  contradict H8.
subst. apply in_eq. subst. contradict H8. subst. apply in_eq.
subst. inversion H10. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto. inversion H1.
clear H1.  contradict H3. auto.


assert (exists A, In (typeof (CON (Qvar x)) A) IL \/ In (typeof (CON (Qvar x)) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON (Qvar x)) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (arrow A1 B1)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A1 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON (Qvar x)) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x0) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (Circ t i0 a0) A) IL \/ In (typeof (Circ t i0 a0) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H7. inversion H17.  subst.
 inversion H11. inversion H18. subst. apply split_ident in H10.
subst. inversion H16. inversion H9.  inversion H27.   subst.
inversion H19. inversion H26.  subst. apply  split_ident in H13.
subst. inversion H25.  inversion H12.  inversion H36. subst.
inversion H28. inversion H35. subst.  apply split_ident in H20.
subst.   assert (i = i1+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H34;auto.
rewrite <- H6  in H34. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H33. inversion H35. inversion H37. subst. inversion H13.
inversion H33.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H45;auto.
apply seq_mono_cor with (k:= i3 + 1 + 1 + 1) in H45;try lia.
assert(i=i3+1+1+1); try lia.
rewrite <- H6 in H45.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H38.
subst. apply notqext_nottyped with
 (lt:=[typeof (Circ t i0 a0) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H12. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H6. auto. auto. subst. inversion H24.
inversion H26. inversion H28.  subst. inversion H19. subst.
inversion H10. apply split_nil in H13.  inversion H13. subst.
inversion H24. assert(i=i1+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (Circ t i0 a0) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H9. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H6. auto. auto.
subst. inversion H14. inversion H16. inversion H18.
subst. inversion H8. apply split_nil in H10. inversion H10. subst.
inversion H15.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H29;auto.
apply seq_mono_cor with (k:= i1 + 1 + 1 + 1) in H29;try lia.
 assert(i=i1+1+1+1); try lia. rewrite <- H6 in H29.  auto.
apply sub_trans with (B:= bang (arrow A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H6.
subst.
inversion H11. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A2 B1)) in H1;auto.
 inversion H1. contradict H6. auto. subst.
apply SubAreVal in  H16. inversion H16. inversion H6.
subst. apply  notqext_nottyped with
(lt:=[typeof (Circ t i0 a0) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H6. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H6. auto. subst. auto.
 inversion H5. destruct H6;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H7. auto. contradict H8. auto.

assert (exists A, In (typeof (CON TRUE) A) IL \/ In (typeof (CON TRUE) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON TRUE) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (arrow A1 B1)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A1 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON TRUE) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (CON FALSE) A) IL \/ In (typeof (CON FALSE) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON FALSE) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (arrow A1 B1)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A1 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON FALSE) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.


assert (exists A, In (typeof (CON STAR) A) IL \/ In (typeof (CON STAR) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H5. inversion H15.  subst.
 inversion H9. inversion H16. subst. apply split_ident in H8.
subst. inversion H14. inversion H7.  inversion H25.   subst.
inversion H17. inversion H24.  subst. apply  split_ident in H11.
subst. inversion H23.  inversion H10.  inversion H34. subst.
inversion H26. inversion H33. subst.  apply split_ident in H18.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H32;auto.
rewrite <- H4  in H32. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H31. inversion H33. inversion H35. subst. inversion H11.
inversion H31.  apply split_nil in H18.  inversion H18. subst.
inversion H26. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H43;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H43;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H4 in H43.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H36.
subst. apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H10. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H4. auto. auto. subst. inversion H22.
inversion H24. inversion H26. subst.   inversion H17. subst.
inversion H8. apply split_nil in H11.  inversion H11. subst.
inversion H22. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H25;auto.
rewrite <- H29 in H25. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H27. subst.
 apply notqext_nottyped with
 (lt:=[typeof (CON STAR) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H7. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H4. auto. auto.
subst. inversion H12. subst. inversion H14. inversion H7.
subst. inversion H6. apply split_nil in H11. inversion H11. subst.
inversion H18.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H34.
inversion H34. inversion H35. subst. inversion H31. assert(H33':=H33).
apply Subtyping_bang_inv in H33. inversion H33.
inversion H34. inversion H35. subst. inversion H36. subst.
inversion H24. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H9. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H30;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H30;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H4 in H30.  auto.
apply sub_trans with (B:= bang (arrow A1 B1)); subst; auto.
subst. apply SubAreVal in H33'.
inversion H33'. inversion H12. inversion H9. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A1 B1)) in H1;auto.
 inversion H1. contradict H4. auto. subst. inversion H8.
subst. apply  notqext_nottyped with
(lt:=[typeof (CON STAR) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. auto. subst. auto.
 inversion H3. destruct H4;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H5. auto. contradict H6. auto.

right. left. exists T0. auto.
right. right. left. auto.
right. right. right. left. auto.
left. exists f. auto.


assert (exists A, In (typeof (Prod v w) A) IL \/ In (typeof (Prod v w) A) LL).
induction i. inversion H2.  lia. exists (arrow T U). right. apply in_eq.
exists (arrow T U). left.   auto.
inversion H2. inversion H7. inversion H17.  subst.
 inversion H11. inversion H18. subst. apply split_ident in H10.
subst. inversion H16. inversion H9.  inversion H27.   subst.
inversion H19. inversion H26.  subst. apply  split_ident in H13.
subst. inversion H25.  inversion H12.  inversion H36. subst.
inversion H28. inversion H35. subst.  apply split_ident in H20.
subst.   assert (i = i0+1+1);try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H34;auto.
rewrite <- H6  in H34. auto.  apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto. subst.
inversion H33. inversion H35. inversion H37. subst. inversion H13.
inversion H33.  apply split_nil in H20.  inversion H20. subst.
inversion H28. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H45;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H45;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H6 in H45.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H38.
subst. apply notqext_nottyped with
 (lt:=[typeof (Prod v w) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H12. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H6. auto. auto. subst. inversion H24.
inversion H26. inversion H28.  subst. inversion H19. subst.
inversion H10. apply split_nil in H13.  inversion H13. subst.
inversion H24. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H27;auto.
rewrite <- H31 in H27. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H29.
subst.  apply notqext_nottyped with
 (lt:=[typeof (Prod v w) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H9. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H6. auto. auto.
subst. inversion H14. inversion H16. inversion H18.
subst. inversion H8. apply split_nil in H10. inversion H10. subst.
inversion H15.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H6 in H29.  auto.
apply sub_trans with (B:= bang (arrow A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H6.
subst.
inversion H11. subst.
apply notqext_nottyped with (lt:=[]) (T:= bang(arrow A2 B1)) in H1;auto.
 inversion H1. contradict H6. auto. subst.
apply SubAreVal in  H16. inversion H16. inversion H6.
subst. apply  notqext_nottyped with
(lt:=[typeof (Prod v w) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H6. apply in_eq.
apply  notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H6. auto. subst. auto.
 inversion H5. destruct H6;
apply  notqext_nottyped with
(lt:=LL) (T:= x) in H1;auto;inversion H1.
  contradict H7. auto. contradict H8. auto.

assert(exists j LL' t u, (seq_ j IL LL' (atom_ (typeof v (circ t u)))
\/ seq_ j IL LL' (atom_ (typeof v (bang (circ t u)))))
 /\ valid t /\ valid u /\ Subtypecontext IL LL' IL LL').

induction i. inversion H2. lia.
subst. apply notqext_nottyped with (lt:=[typeof (App (CON UNBOX) v) (arrow T U)]) (T:= arrow T U) in H1;auto.
inversion H1. contradict H5. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
inversion H1. contradict H4. auto. inversion H2. inversion H6.
inversion H16. subst. inversion H10. inversion H17. subst.
apply split_ident in H9. subst.
inversion H15. inversion H8. inversion H26. subst.
inversion H18. inversion H25. subst. apply split_ident in H12.
subst. inversion H24.  inversion H11. inversion H35. subst.
inversion H27. inversion H34. subst.
apply split_ident in H19. subst.
 apply subtypecontext_subtyping with (IL':= IL) (LL':=lL2) (B:= arrow T U) in H33;auto.
assert(i=i0+1+1); try lia.
rewrite <- H5 in H33.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. auto.
subst.
inversion H32. inversion H34. inversion H36. subst. inversion H12.
inversion H32.  apply split_nil in H19.  inversion H19. subst.
inversion H27. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H44;auto.
apply seq_mono_cor with (k:= i2 + 1 + 1 + 1) in H44;try lia.
assert(i=i2+1+1+1); try lia.
rewrite <- H5 in H44.   auto.
apply sub_trans with (B:= arrow A2 B0);auto.
apply sub_trans with (B:= arrow A1 B1);auto. subst. inversion H37.
subst. inversion H27. inversion H33. subst. apply split_ident in H19.
inversion H32. apply unbox_arrow in H36;auto.
inversion H36. inversion H38.
inversion H39. inversion  H40. inversion H41.
inversion H42. subst. exists i1. exists LL2.
exists A0. exists B2. split. left.  auto.
inversion H49. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
inversion H44;subst;[simpl|inversion H45].
exists i1. exists LL2.
exists A0. exists B3. split. right.  auto.
inversion H53. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
subst.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0. auto. auto.


subst. apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (arrow A2 B0)]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H11. apply in_eq. subst.
apply notqext_nottyped with (lt:=[]) (T:= arrow A2 B0) in H1;auto.
 inversion H1. contradict H5. auto. auto. subst. inversion H23.
inversion H25. inversion H27.  subst. inversion H18. subst.
inversion H9. apply split_nil in H12.  inversion H12. subst.
inversion H23. assert(i=i0+1+1); try lia.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H26;auto.
rewrite <- H30 in H26. auto.
apply sub_trans with (B:= arrow A1 B1);auto.
subst. inversion H28.
subst. inversion H18. inversion H24.
subst. apply split_ident in H12. subst. inversion H23.
apply unbox_arrow in H25;auto.
inversion H25. inversion H28.
inversion H29. inversion  H30. inversion H31.
inversion H32. subst. exists i0. exists LL2.
exists A0. exists B0. split. left.  auto.
inversion H39. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
inversion H34;subst;[simpl|inversion H35].
exists i0. exists LL2.
exists A0. exists B2. split. right.  auto.
inversion H43. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
subst.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0. auto. auto.
subst.  apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (arrow A1 B1)]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H8. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow A1 B1) in H1;auto.
 inversion H1. contradict H5. auto. auto.

(*
 subst.
inversion H15.
inversion H20.  inversion H23. apply Subtyping_bang_inv in H36.
inversion H36. inversion H37. subst. inversion H33. assert(H35':=H35).
apply Subtyping_bang_inv in H35. inversion H35.
inversion H36. inversion H37. inversion H38. subst.
inversion H26. apply split_nil in H12. inversion H12. subst.
inversion H27. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H29;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H29;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H6 in H29.  auto.
apply sub_trans with (B:= bang (arrow A2 B1)); subst; auto.
subst. apply SubAreVal in H35'.
inversion H35'. inversion H6.
subst.
inversion H11.*) subst. inversion H13.
subst. inversion H10.  subst.
inversion H7.
apply split_nil in H9. inversion H9. subst.
inversion H14. inversion H17. inversion H20.
subst. inversion H25.
apply split_nil in H11. inversion H11. subst.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H22;auto.
 assert(i=i2+1+1); try lia. rewrite <- H5 in H22.  auto.
apply sub_trans with (B:= bang A0); subst; auto.
subst. inversion H21.
apply split_nil in H11. inversion H11. subst.
inversion H22.
apply subtypecontext_subtyping with (IL':= IL) (LL':=[]) (B:= arrow T U) in H24;auto.
apply seq_mono_cor with (k:= i0 + 1 + 1 + 1) in H24;try lia.
 assert(i=i0+1+1+1); try lia. rewrite <- H27 in H24.  auto.
apply sub_trans with (B:= bang A0); subst; auto.

subst. inversion H25.
apply split_nil in H11. inversion H11. subst.
inversion H22. apply split_nil in H12.
inversion H12. subst.
apply unbox_arrow in H26;auto.
inversion H26. inversion H5.
inversion H8. inversion  H13. inversion H19.
inversion H24. subst. exists i0. exists [].
exists A1. exists B1. split. left.  auto.
inversion H35. split;auto.
inversion H29;subst;[simpl|inversion H30].
exists i0. exists [].
exists A1. exists B1. split. right.  auto.
inversion H39. split;auto.

apply notqext_nottyped with (lt:=[]) (T:= bang A0) in H1;auto.
 inversion H1. contradict H23. auto.

subst. inversion H10. inversion H15.
subst.
apply split_ident in H9. subst.
inversion H14.
apply unbox_arrow in H17;auto.
inversion H17. inversion H19.
inversion H20. inversion  H21. inversion H22.
inversion H23. subst. exists i1. exists LL2.
exists A1. exists B1. split. left.  auto.
inversion H30. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.
inversion H25;subst;[simpl|inversion H26].
exists i1. exists LL2.
exists A1. exists B1. split. right.  auto.
inversion H34. split;auto. split;auto.
apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto. inversion H0.
auto.

apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H0;auto.
inversion H0. auto. auto.
subst.  apply notqext_nottyped with
 (lt:=[typeof (App (CON UNBOX) v) (arrow T U)]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H5. apply in_eq.
subst.  apply notqext_nottyped with (lt:=[]) (T:= arrow T U) in H1;auto.
 inversion H1. contradict H4. auto. auto.

inversion H4. inversion H5. inversion H6.
inversion H7. inversion H8. inversion H10.
inversion H12.
 destruct H9;[apply sub_circ_inv in H9|apply sub_bangcirc_inv in H9];auto ;
right; right; right; right; inversion H9;
inversion H15; inversion H16; exists x3; exists x5; exists x4;
rewrite H17; auto.
Qed.
