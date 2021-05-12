
(****************************************************************
   File: LSL.v                                                 
   Authors: Mohamed Yousri Mahmoud
   Date: Jun 2018
   Current Version: Coq V8.9
                                                                 
   An intuitionistic linear sequent calculus used as a specification
   logic, for use in two-level Hybrid.
  ***************************************************************)
Require Export Hybrid.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import FunInd.

Set Implicit Arguments.

(****************************************************************
  List Utilities (mainly for using lists as multisets) and
  Other General Lemmas
  ****************************************************************)

Section util.

Inductive split (T:Type) : list T -> list T -> list T -> Prop := 
|init: split [] [] []
|splitr1: forall l1 l2 l3 A, split l1 l2 l3 -> split (A::l1) (A::l2) l3
|splitr2: forall l1 l2 l3 A, split l1 l2 l3 -> split (A::l1) l2 (A::l3).

Theorem split_nil: forall T, forall (l1 l2:list T),
  split [] l1 l2 <-> l1 = [] /\ l2 = [].
Proof.
intros T l1 l2. apply iff_to_and. split; intros H. 
- inversion H. auto. 
- inversion H. subst. apply init. 
Qed.
  
Theorem split_ident_alt: forall T, forall (l1 l2 l3:list T),
  split l1 l2 l3 ->l3 = [] ->  l1 = l2.
Proof. 
intros T l1 l2 l3 H. induction H;auto. 
- intros H0. apply IHsplit in H0;subst;auto. 
- intros H0. inversion H0.
Qed.

Theorem split_ident: forall T, forall (l1 l2 l3:list T),
  split l1 l2 [] ->  l1 = l2.
Proof.
intros T l1 l2 l3 H. apply split_ident_alt in H;auto. 
Qed.

Theorem split_ref: forall T, forall (l:list T), split l l [].
Proof. intros T l. induction l;try apply init. apply splitr1. auto.
Qed.

Theorem split_rref: forall T, forall (l:list T), split l  [] l.
Proof. intros T l. induction l;try apply init. apply splitr2. auto.
Qed.

Theorem concat_split: forall T, forall (l l1 l2:list T), 
  l = l1++l2 -> split l l1 l2.
intro. induction l. 
- intros l1 l2 H. symmetry  in H. apply app_eq_nil in H.
  inversion H. subst. apply init. 
- intros l1 l2 H. destruct l1.
  + rewrite  app_nil_l in H. subst. apply split_rref.
  + rewrite <- app_comm_cons in H. inversion H. assert (H2':=H2). 
    apply IHl in H2. apply splitr1. rewrite <- H2'. auto.
Qed.

Lemma eq_dec_false : forall T, forall x: T, x<>x <-> False.
Proof.
intros T x; split; intros H.
- apply H; auto.
- destruct H.
Qed.

Definition disjoint {T:Type} (l1 l2:list T) : Prop :=
  (forall x:T, In x l1 -> ~(In x l2)) /\
  (forall x:T, In x l2 -> ~(In x l1)).

Lemma disjoint_app_r: forall (T:Type) (l1 l2 l3:list T),
    disjoint l1 (l2 ++ l3) <-> disjoint l1 l2 /\ disjoint l1 l3.
Proof.
  unfold disjoint.
  intros T l1 l2 l3; split; intros [H H0]; repeat split.
  - intros x H1 H2. apply H in H1; elim H1.  apply in_or_app; left; auto.
  - intros x H1 H2. apply H in H2; elim H2.  apply in_or_app; left; auto.
  - intros x H1 H2. apply H in H1; elim H1.  apply in_or_app; right; auto.
  - intros x H1 H2. apply H in H2; elim H2.  apply in_or_app; right; auto.
  - intros x H1 H2. elim H; clear H; intros H H3. elim H0; clear H0; intros H0 H4.
    specialize in_app_or with (1:=H2); intros [H5 | H5].
    + apply H3 in H5; elim H5; auto.
    + apply H0 in H5; auto.
  - intros x H1 H2. elim H; clear H; intros H H3. elim H0; clear H0; intros H0 H4.
    specialize in_app_or with (1:=H1); intros [H5 | H5].
    + apply H3 in H5; elim H5; auto.
    + apply H4 in H5; auto.
Qed.

Lemma disjoint_NoDup : forall (T:Type) (l1 l2:list T),
    NoDup (l1++l2) <-> (disjoint l1 l2 /\ NoDup l1 /\ NoDup l2).
Proof.
  intros T l1 l2; split.
  - generalize l2; clear l2.
    induction l2; simpl; auto.
    + rewrite -> app_nil_r; intro H.
      repeat split; auto; constructor.
    + intro H; specialize NoDup_remove with (1:=H); intros [H0 H1].
      apply IHl2 in H0. elim H0; clear H0; intros [H0 H2] [H3 H4].
      repeat split; auto.
      * intros x H5 H6. simpl in H6; elim H6; clear H6; intro H6; subst.
        { specialize NoDup_remove with (1:=H); intros [H6 H7]. elim H7.
          rewrite -> in_app_iff. left; auto. }
        { specialize H0 with (1:=H5); elim H0; auto. }
      * intros x H5 H6. simpl in H5; elim H5; clear H5; intro H5; subst.
        { specialize NoDup_remove with (1:=H); intros [H5 H7]. elim H7.
          rewrite -> in_app_iff. left; auto. }
        { specialize H0 with (1:=H6); elim H0; auto. }
      * constructor; auto. intro H5; elim H1.
        rewrite -> in_app_iff. right; auto.
  - generalize l1; clear l1. 
    induction l1; simpl; auto.
    + intros [H [H0 H1]]; auto.
    + intros [[H H0] [H1 H2]]. constructor.
      * intro H3. inversion H1; subst. rewrite -> in_app_iff in H3.
        elim H3; clear H3; intro H3.
        { elim H6; auto. }
        { specialize H0 with (1:=H3). simpl in H0. elim H0; left; auto. }
      * apply IHl1. inversion H1; subst.
        repeat split; auto.
        { intros x H3 H4. generalize (in_cons a x l1 H3); intro H7.
          apply H in H7; elim H7; auto. }
        { intros x H3 H4. apply H0 in H3. elim H3. apply in_cons; auto. }
Qed.

Variable T:Type.
Hypothesis eq_dec : forall x y : T, {x = y}+{x <> y}.

Theorem remove_In : 
  forall (l : list T) (x y: T),
  In x l -> y<>x -> In x (remove eq_dec y l).
Proof.
intros l x y H H0. induction l; auto. simpl remove. simpl In in H.
destruct H.
- (* x is head of list *)
  subst. destruct (eq_dec y x).
  rewrite <- e in H0. rewrite eq_dec_false in H0. 
  inversion H0.   apply in_eq.  
- (* x in tail of list *)
  destruct (eq_dec y a);auto. simpl.
  apply or_intror;auto.
Qed.

Fixpoint remove_one (l:list T) a :=
  match l with
    | [] => []
    | y::t =>  if eq_dec a y then t else y::(remove_one t a)
  end.

Theorem count_occ_remove_nin: forall l a A, a<>A ->
  count_occ eq_dec (remove_one l a) A = count_occ eq_dec l A.
Proof.
intros l a A H. induction l; simpl; auto.
destruct (eq_dec a a0) as [e | n]; destruct (eq_dec a0 A) as [e0 | n0]; auto.
- contradict H. subst. auto. 
- simpl. destruct (eq_dec a0 A) as [e1 | n1]; auto.
  contradict n1. auto.
- simpl. destruct (eq_dec a0 A) as [e1 | n1]; auto. contradict n0. auto.
Qed.

Theorem count_occ_remove_in: forall l a,
 count_occ eq_dec (remove_one l a) a = count_occ eq_dec l a -1.
Proof.
intros l a. induction l; simpl; auto.
destruct (eq_dec a a0) as [e | n].
- destruct (eq_dec a0 a). omega. contradict n. auto.
- simpl. destruct (eq_dec a a0).
  + contradict n. auto.
  + destruct (eq_dec a0 a); auto. contradict n. auto.
Qed.

Theorem count_occ_remove: forall l l' A,
  (forall a, count_occ eq_dec (A::l) a = count_occ eq_dec l' a) ->
  (forall a, count_occ eq_dec l a = count_occ eq_dec (remove_one l' A) a).
Proof.
intros l l' A H a. destruct l.
- destruct (eq_dec A a) as [e | n].
  + subst. rewrite count_occ_remove_in. rewrite <- H.
    simpl. destruct (eq_dec a a);omega. 
  + assert(h:=n).
    apply count_occ_remove_nin with (l:=l') in n.
    rewrite n, <- H. simpl.
    destruct (eq_dec A a); auto. contradict h. auto.
- destruct (eq_dec A a).
  + subst. rewrite count_occ_remove_in. rewrite <- H.
    simpl. destruct (eq_dec a a); try omega.
    contradict n. auto.
  + assert(h:=n).
    apply count_occ_remove_nin with (l:=l') in n.
    rewrite n, <- H. simpl.
    destruct (eq_dec A a); auto.
    contradict h. auto.
Qed.

Theorem remove_one_length: forall l a, In a l ->
  length l = S (length (remove_one l a)).
Proof.
intros l a H. induction l.
- inversion H.
- inversion H.
  + subst. simpl.
    destruct (eq_dec a a); auto. contradict n. auto.
  + apply IHl in H0. simpl.
    destruct (eq_dec a a0); auto.
Qed. 

Theorem count_occ_length: forall l l',
  (forall a, count_occ eq_dec l a = count_occ eq_dec l' a) ->
  length l  = length l'.
Proof.
intros l; induction l.
- intros l' H. simpl in *.
  symmetry in H. rewrite count_occ_inv_nil in H.
  subst. simpl. auto.
- intros l' H.
  assert (H0: forall a0 : T, count_occ eq_dec l a0 = 
                             count_occ eq_dec (remove_one l' a) a0).
  { intro a0. apply count_occ_remove with (a:=a0) in H. auto. }
  apply IHl in H0.
  assert (H1: In a l'). 
  { assert (H1: In a (a::l)); try apply in_eq.
    rewrite count_occ_In with (eq_dec:=eq_dec) in H1.
    rewrite H in H1. rewrite <- count_occ_In in H1. auto. }
  apply remove_one_length in H1.
  rewrite H1,<- H0. simpl. auto.
Qed.

Theorem split_insert:
  forall l l1 l2, split l l1 l2 ->
  forall LL A, l = remove_one LL A -> In A LL ->
  (exists l1', split LL l1' l2 /\ 
               (forall a, count_occ eq_dec l1' a =
                          if eq_dec a A then S(count_occ eq_dec l1 a)
                          else count_occ eq_dec l1 a)) 
   /\
  (exists l2', split LL l1 l2' /\ 
               (forall a, count_occ eq_dec l2' a =
                          if eq_dec a A then S(count_occ eq_dec l2 a)
                          else count_occ eq_dec l2 a)).
(* Proof to be cleaned up. *)
Proof.
intros l l1 l2 H. induction H;intros.
split. destruct LL. inversion H0. 
destruct LL.  inversion H0. 
subst. exists [A]. split. apply splitr1,init.
intros. simpl. destruct (eq_dec A a);
 destruct (eq_dec a A);auto; contradict n ;auto.
inversion H1. simpl in H. 
destruct (eq_dec A t);inversion H.

destruct LL. inversion H0. 
destruct LL.  inversion H0. 
subst. exists [A]. split. apply splitr2,init.
intros. simpl. destruct (eq_dec A a);
 destruct (eq_dec a A);auto; contradict n ;auto.
inversion H1. simpl in H. 
destruct (eq_dec A t);inversion H.
destruct LL. simpl in H0. inversion H0.
simpl in H0. destruct (eq_dec A0 t).
assert(In A (A::l1));try apply in_eq.
apply IHsplit in H2. inversion H2.
split. inversion H3. inversion H5.
subst. exists (t::x). split. apply splitr1.
auto. intros. specialize H7 with a.
destruct (eq_dec a A). simpl.
rewrite H7. destruct (eq_dec t a).
destruct (eq_dec A a). destruct (eq_dec a t).
auto. contradict n. auto. contradict n. auto.
destruct (eq_dec a t).
contradict n. auto. destruct (eq_dec A a). 
auto. contradict n1. auto.
destruct (eq_dec a t). simpl.
destruct (eq_dec A a). 
contradict n. auto.  destruct (eq_dec t a).
omega. contradict n1. auto.
simpl. rewrite H7. destruct (eq_dec t a).
contradict n0. auto.
destruct (eq_dec A a). contradict n. auto.
auto. 

exists (t::l3). subst. split. 
apply splitr2,splitr1. auto. 
intros. simpl. destruct (eq_dec t a); destruct (eq_dec a t);auto;
contradict n;auto. simpl.
destruct (eq_dec A A). auto. contradict n. auto.

inversion H0. inversion H1. 
contradict n. auto.
apply IHsplit in H2;auto. inversion H2.
split. inversion H5. inversion H7.
subst. exists (t::x). split. apply splitr1.
auto. intros. specialize H9 with a.
destruct (eq_dec a A0). simpl.
rewrite H9. destruct (eq_dec t a). auto.
auto. 
simpl. rewrite H9. destruct (eq_dec t a);
auto. 

inversion H6.  inversion H7. 
exists x. split;auto.  
apply splitr1. auto. 


destruct LL. simpl in H0. inversion H0.
simpl in H0. destruct (eq_dec A0 t).
assert(In A (A::l1));try apply in_eq.
apply IHsplit in H2. inversion H2.
split. exists (t::l2). subst. split. 
apply splitr1,splitr2. auto. 
intros. simpl. destruct (eq_dec t a); destruct (eq_dec a t);auto;
contradict n;auto.


inversion H4. inversion H5.
subst. exists (t::x). split. apply splitr2.
auto. intros. specialize H7 with a.
destruct (eq_dec a A). simpl.
rewrite H7. destruct (eq_dec t a).
destruct (eq_dec A a). destruct (eq_dec a t).
auto. contradict n. auto. contradict n. auto.
destruct (eq_dec a t).
contradict n. auto. destruct (eq_dec A a). 
auto. contradict n1. auto.
destruct (eq_dec a t). simpl.
destruct (eq_dec A a). 
contradict n. auto.  destruct (eq_dec t a).
omega. contradict n1. auto.
simpl. rewrite H7. destruct (eq_dec t a).
contradict n0. auto.
destruct (eq_dec A a). contradict n. auto.
auto. simpl.
destruct (eq_dec A A). auto. contradict n. auto.


inversion H0. inversion H1. 
contradict n. auto.
apply IHsplit in H2;auto. inversion H2.
split. inversion H5.  inversion H7. 
exists x. split;auto.  
apply splitr2. auto. 

inversion H6. inversion H7.
subst. exists (t::x). split. apply splitr2.
auto. intros. specialize H9 with a.
destruct (eq_dec a A0). simpl.
rewrite H9. destruct (eq_dec t a). auto.
auto. 
simpl. rewrite H9. destruct (eq_dec t a);
auto. 
Qed.

Theorem split_same:
  forall l l1 l2, split l l1 l2 ->
  forall l', (forall a, count_occ eq_dec l a = count_occ eq_dec l' a) ->
  exists l1' l2',
    split l' l1' l2' /\
    (forall a, count_occ eq_dec l1 a = count_occ eq_dec l1' a) /\
    (forall a, count_occ eq_dec l2 a = count_occ eq_dec l2' a).
(* Proof to be cleaned up. *)
Proof.
intros l l1 l2 H. induction H;intros.
simpl in H. symmetry in H. rewrite count_occ_inv_nil  in H.
rewrite H. exists [],[]. simpl. split;auto. apply init. 

assert(forall a : T, count_occ eq_dec l1 a = 
count_occ eq_dec (remove_one l' A) a).
intros. apply count_occ_remove with (a:=a) in H0. auto.
apply IHsplit in H1. inversion H1. inversion H2.
inversion H3. inversion H5. 
apply split_insert with (LL:=l') (A:=A) in H4;auto.
inversion H4. inversion H8. inversion H10.
exists x1,x0. split;auto.   
split. intros. simpl. specialize H12 with a.
destruct (eq_dec a A);rewrite H12.
destruct (eq_dec A a). rewrite H6. auto.
contradict n. auto. destruct (eq_dec A a).
contradict n. auto. rewrite H6. auto. auto.

assert(In A (A::l1));try apply in_eq.
rewrite count_occ_In  in H8.
rewrite H0,<- count_occ_In in H8. auto.


assert(forall a : T, count_occ eq_dec l1 a = 
count_occ eq_dec (remove_one l' A) a).
intros. apply count_occ_remove with (a:=a) in H0. auto.
apply IHsplit in H1. inversion H1. inversion H2.
inversion H3. inversion H5. 
apply split_insert with (LL:=l') (A:=A) in H4;auto.
inversion H4. inversion H9. inversion H10.
exists x,x1. split;auto.   
split. intros. rewrite H6. auto.
intros. simpl. specialize H12 with a.
destruct (eq_dec a A);rewrite H12.
destruct (eq_dec A a). rewrite H7. auto.
contradict n. auto. destruct (eq_dec A a).
contradict n. auto.  rewrite H7. auto.

assert(In A (A::l1));try apply in_eq.
rewrite count_occ_In  in H8.
rewrite H0,<- count_occ_In in H8. auto.
Qed.

Theorem in_split_or: forall  (l l1 l2:list T),
  split l l1 l2 -> forall a, In a l -> In a l1 \/ In a l2.
Proof.
intros l l1 l2 H. induction H; intros.
- inversion H. 
- inversion H0. 
  + subst. left. apply in_eq. 
  + apply IHsplit in H1. destruct H1.
    * left. apply in_cons. auto.
    * right. auto.
- inversion H0.
  + subst. right. apply in_eq. 
  + apply IHsplit in H1. destruct H1.
    * left. auto.
    * right. apply in_cons. auto.
Qed.

Theorem count_split: forall (l l1 l2:list T), split l l1 l2 ->
  forall a, count_occ eq_dec l a = 
            count_occ eq_dec l1 a + count_occ eq_dec l2 a.
Proof.
intros l l1 l2 H. induction H; intros;
simpl; auto; rewrite IHsplit; 
destruct (eq_dec A a); omega; auto.
Qed.

Theorem count_app: forall (l l1 l2:list T) (q:T),
  l = l1 ++ l2 -> 
  count_occ eq_dec l q = count_occ eq_dec l1 q + count_occ eq_dec l2 q.
Proof.
intro l. induction l; intros.
- symmetry in H. apply app_eq_nil in H. inversion H. subst.
  simpl. auto.
- destruct l1.
  + rewrite app_nil_l in H.
    rewrite <- H in *. simpl in *. auto.
  + inversion H. assert(h:=H2).
    apply IHl with (q:=q) in H2. simpl.
    destruct (eq_dec t q);rewrite <- h,H2; omega.
Qed.

Theorem split_identr_alt: forall (l1 l2 l3:list T), split l1 l2 l3 ->l2 = [] ->  l1 = l3.
Proof.
  intros l1 l2 l3 H. induction H;auto.
  - intros. inversion H0.
  - intros. apply IHsplit in H0;subst;auto.
Qed.

Theorem split_identr: forall (l1 l2 l3:list T), split l1 [] l2 ->  l1 = l2.
Proof.
  intros. apply split_identr_alt in H;auto. 
Qed.

Functional Scheme remove_one_ind := Induction for remove_one Sort Prop.

Theorem remove_one_in:
  forall il a b, In b il -> a<>b -> In b (remove_one il a).
Proof.
intros il a b H H0. functional induction remove_one il a.
- inversion H.
- inversion H; auto.
  contradict H0. auto.
- inversion H.
  + subst. apply in_eq.
  + apply in_cons;auto.
Qed.

Theorem remove_one_in2:
  forall il a b,  In b (remove_one il a) ->  In b il.
Proof.
intros il a b H. functional induction remove_one il a.
- inversion H.
- apply in_cons;auto.
- inversion H.
  + subst. apply in_eq.
  + apply in_cons;auto.
Qed.

Theorem split_identl_alt: forall (l1 l2 l3:list T),
    split l1 l2 l3 -> l2 = [] -> l1 = l3.
Proof.
  intros l1 l2 l3 H. induction H;auto.
  - intros.
    inversion H0.
  - intros.  apply IHsplit in H0;subst;auto. 
Qed.

Theorem split_identl: forall (l1 l2 l3:list T), split l1 [] l2 -> l1 = l2.
Proof.
  intros. apply split_identl_alt with (l2:=[]);auto. 
Qed.

Theorem in_split_l: forall l l1 l2 :list T,
split l l1 l2 -> forall a, In a l1 -> In a l.
Proof.
intros l l1 l2 H. induction H;intros. inversion H.
 inversion H0.  
subst. apply in_eq. apply in_cons, IHsplit;auto. 
 apply in_cons,IHsplit;auto.
Qed.

Theorem not_in_split: forall l l1 l2 :list T,
split l l1 l2 -> forall a, ~(In a l) -> ~ (In a l1) /\ ~(In a l2).
Proof.
intros l l1 l2 H. induction H;intros; split;auto;
 rewrite not_in_cons  in H0; inversion H0;
apply IHsplit in H2; inversion H2;  try rewrite not_in_cons; try split;auto.
Qed.

Theorem unique_in_split: forall l l1 l2: list T,
split l l1 l2 -> forall a, 
count_occ eq_dec l a = 1 ->
 (~ (In a l1) /\ (In a l2)) \/ ( (In a l1) /\ ~(In a l2)) . 
Proof.
intros l l1 l2 H. induction H;intros. simpl in H. omega.
destruct (eq_dec A a). 
subst. rewrite count_occ_cons_eq in  H0;auto.
inversion H0. rewrite <- count_occ_not_In in H2. 
apply not_in_split with (a:=a) in H;auto. inversion H.
right;split;auto. apply in_eq.
rewrite count_occ_cons_neq in  H0;auto. 
apply IHsplit in H0. destruct H0. inversion H0.
left;split;auto. contradict H1. inversion H1;auto.
contradict n. auto. inversion H0. right;split;auto.
apply in_cons;auto.


destruct (eq_dec A a). 
subst. rewrite count_occ_cons_eq in  H0;auto.
inversion H0. rewrite <- count_occ_not_In in H2. 
apply not_in_split with (a:=a) in H;auto. inversion H.
left;split;auto. apply in_eq.
rewrite count_occ_cons_neq in  H0;auto. 
apply IHsplit in H0. destruct H0. inversion H0. 
left;split;auto. apply in_cons;auto. 
inversion H0. right;split;auto.
contradict H2. inversion H2;auto.
contradict n. auto.
Qed.

Theorem in_split_r: forall l l1 l2 :list T,
split l l1 l2 -> forall a, In a l2 -> In a l.
intros l l1 l2 H. induction H;intros. inversion H.
 apply in_cons,IHsplit;auto. inversion H0.  
subst. apply in_eq. apply in_cons, IHsplit;auto. 
Qed.

Theorem nodup_concat: forall  l :list T,
NoDup l ->  forall l1 l2, l = l1++l2 -> NoDup l1 /\ NoDup l2.
intros l H. induction H. intros.
symmetry in H. apply app_eq_nil in H.
inversion H. subst; split;apply NoDup_nil.
intros.
destruct l1.
rewrite app_nil_l in H1. subst.
split; [apply NoDup_nil|apply NoDup_cons;auto].
inversion H1. assert(h:=H4).
apply IHNoDup  in H4. inversion H4.
split;auto. subst. rewrite in_app_iff in H.
apply not_or in H. inversion H. apply NoDup_cons;auto.
Qed.

Theorem nodup_in_app: forall l:list T, NoDup l  ->
forall a l1 l2, l = l1++l2 -> In a l -> 
(In a l1 /\ ~ In a l2) \/
(~In a l1 /\  In a l2).
intros l H. induction H. intros.
inversion H0. intros.
destruct l1.
rewrite app_nil_l in H1. subst.
right. split;auto.
inversion H1. assert(h:=H5).
destruct (eq_dec a x). subst.
rewrite in_app_iff in H.
apply not_or in H. inversion H.
left. split;auto. apply in_eq.
inversion H2. contradict n. auto.
apply IHNoDup  with (a:=a) in H5;auto. inversion H5.
inversion H6. left; split;auto.
apply in_cons. auto. 
inversion H6.
right;split;auto. 
contradict n. inversion n. subst. auto. contradict H7. auto.
Qed.

End util.

(* Make implicit the type argument to all new functions on lists. *)
Arguments remove_one {T} eq_dec l a.

Section lsl.

(****************************************************************
  The linear specification logic.
  ****************************************************************)
Variable atm : Set.
Variable con : Set.

(* Decidability of equality must be proven for each instantiation of atm *)
Hypothesis eq_dec : forall x y : atm, {x = y}+{x <> y}.

Inductive oo : Set :=
  | atom : atm -> oo
  | T : oo
  | Conj : oo -> oo -> oo          (* Multiplicative conjunction *)
  | And: oo -> oo -> oo            (* Additive conjunction *)
  | Imp : atm -> oo -> oo          (* intuitionistic implication *)
  | lImp : atm -> oo -> oo         (* linear implication *)
  | All : (expr con -> oo) -> oo
  | Some : (expr con -> oo) -> oo.

Variable prog : atm -> list oo -> list oo -> Prop.

Inductive seq : nat -> list atm -> list atm -> oo -> Prop  :=
  | s_bc :
      forall (i : nat) (A : atm) (IL LL: list atm) (lL iL : list oo) (b : oo),
      prog A iL lL -> splitseq i IL [] iL -> splitseq i IL LL lL -> seq (i+1) IL LL (atom A)
  | l_init :
      forall (i : nat) A  (IL : list atm),
       seq i IL [A]  (atom A)
  | i_init :
      forall (i : nat) A  (IL : list atm),
       In A IL -> seq i IL nil  (atom A)
  | s_tt : forall (i : nat) (IL : list atm) (LL : list atm),
         seq i IL LL  T
  | m_and :
      forall (i : nat) (B C : oo) (IL : list atm) (LL LL1 LL2 : list atm),
      split LL LL1 LL2 -> seq i IL LL1 B -> seq i IL LL2 C -> 
      seq (i+1) IL LL  (Conj B C)
  | a_and :
      forall (i : nat) (B C : oo) (IL : list atm) (LL : list atm) (QL : list atm),
      seq i IL LL  B -> seq i IL LL  C -> seq (i+1) IL (LL)  (And B C)
  
  | i_imp :
      forall (i : nat) (A : atm) (B : oo) (IL : list atm) (LL : list atm),
      seq i (A::IL) LL B -> seq (i+1) IL LL (Imp A B)
  | l_imp :
      forall (i : nat) (A : atm) (B : oo) (IL : list atm) (LL : list atm),
      seq i IL (A::LL) B -> seq (i+1) IL LL (lImp A B)
  | s_all :
      forall (i : nat) (B : expr con -> oo) (IL : list atm) (LL : list atm),
      (forall x : expr con, proper x -> seq i IL LL (B x)) -> seq (i+1) IL LL (All B)
with
splitseq : nat -> list atm -> list atm -> list oo -> Prop :=
| ss_init: forall i IL, splitseq i IL [] []
| ss_general: forall i IL lL1 lL2 lL3 G Gs, 
     split lL1 lL2 lL3 -> seq i IL lL2 G -> splitseq i IL lL3 Gs -> splitseq i IL lL1 (G::Gs).

Scheme seq_split_ind := Minimality  for seq Sort Prop
        with split_seq_ind := Minimality  for splitseq Sort Prop.  	 

(****************************************************************
  Intuitionistic Context Weakening and Contraction
  ****************************************************************)

Definition P0_splitseq_weaken (i : nat) (il: list atm) (ll: list atm)
           (b: list oo) : Prop :=
  forall il', (forall a : atm, In a il -> In a il') -> splitseq i il' ll b.

Definition P_seq_weaken (i : nat) (il: list atm) (ll: list atm)
           (b: oo) :Prop :=
  forall il',  (forall a : atm, In a il -> In a il') -> seq i il' ll b.


Theorem seq_weakening : forall (j : nat) (b :  oo) (il ll: list atm),
 seq j il ll b -> P_seq_weaken j il ll b.
Proof.
intros j b il ll H. 
apply seq_split_ind with (P0 := P0_splitseq_weaken);
unfold P0_splitseq_weaken,P_seq_weaken; auto.
- (* s_bc case *)
  intros i A IL LL lL iL b0 H0 H1 H2 H3 H4 il' H5.
  apply s_bc with (lL:=lL) (iL:=iL); auto. 
- (* l_init case *) 
  intros; apply l_init.
- (* i_init_case *)
  intros; apply i_init; auto.
- (* s_tt case *)
  intros; apply s_tt.
- (* m_and case *)
  intros i B C IL LL LL1 LL2 H0 H1 H2 H3 H4 il' H5.
  apply m_and with LL1 LL2; auto.
- (* a_and case *)
  intros; apply a_and; auto.
- (* i_imp case *)
  intros i A B IL LL H0 H1 il' H2. apply i_imp; auto.
  apply H1; auto.
  intros a H3.
  specialize in_inv with (1 := H3); intro H4.
  elim H4; clear H4; intro H4.
  + rewrite H4. apply in_eq; auto.
  + apply in_cons; apply H2; auto.
- (* l_imp case *)
  intros; apply l_imp;auto.
- (* s_all case *)
  intros; apply s_all;auto.
- (* ss_init_case *)
  intros; apply ss_init;auto.
- (* ss_general case *)
  intros i IL lL1 lL2 lL3 G Gs H0 H1 H2 H3 H4 il' H5.
  apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
Qed.

Theorem seq_weakening_cor :
  forall (i : nat) (b :  oo) (il il' ll: list atm),
    seq i il ll b -> (forall a : atm, In a il -> In a il') -> seq i il' ll b.
Proof.
intros i b il il' ll H H0.
assert (H1:= seq_weakening). unfold P_seq_weaken in H1.
apply H1 with (il:=il);auto.
Qed.

Theorem split_seq_weakening :
  forall (j : nat) (b :  list oo) (il ll: list atm),
  splitseq j il ll b -> P0_splitseq_weaken j il ll b.
Proof.
intros j b il ll H.
apply split_seq_ind with (P := P_seq_weaken); auto.
unfold P0_splitseq_weaken,P_seq_weaken.
- (* s_bc case *)
  intros i A IL LL lL iL b0 H0 H1 H2 H3 H4 il' H5.
  apply s_bc with (lL:=lL) (iL:=iL); auto. 
- (* l_init case *)
  unfold P_seq_weaken. intros. apply l_init. 
- (* i_init case *)
  unfold P_seq_weaken. intros. apply i_init. auto.
- (* s_tt case *)
  unfold P_seq_weaken. intros. apply s_tt.
- (* m_and case *)
  unfold P_seq_weaken. intros i B C IL LL LL1 LL2 H0 H1 H2 H3 H4 il' H5.
  apply m_and with LL1 LL2; auto.
- (* a_and case *)
  unfold P_seq_weaken. intros. apply a_and; auto.
- (* i_imp case *)
  unfold P_seq_weaken. intros i A B IL LL H0 H1 il' H2. apply i_imp; auto.
  apply H1; auto.
  intros a H3.
  specialize in_inv with (1 := H3); intro H4.
  elim H4; clear H4; intro H4.
  rewrite H4.
  apply in_eq; auto.
  apply in_cons; apply H2; auto.
- (* l_imp_case *)
  unfold P_seq_weaken. intros. apply l_imp;auto.
- (* s_all case *)
  unfold P_seq_weaken. intros. apply s_all;auto.
- (* ss_init_case *)
  unfold P0_splitseq_weaken. intros. apply ss_init;auto.
- (* ss_general case *)
  unfold P0_splitseq_weaken.
  intros i IL lL1 lL2 lL3 G Gs H0 H1 H2 H3 H4 il' H5. 
  apply ss_general with (lL2:=lL2) (lL3:=lL3);auto.
Qed.

Theorem seq_contraction: forall IL1 IL2 LL i b, 
  seq i (IL1++IL2) LL b -> (forall a, In a IL1 -> In a IL2) ->
  seq i IL2 LL b.
Proof.
intros IL1 IL2 LL i b H H0. 
apply seq_weakening_cor with(il:=IL1++IL2);auto.
intros a H1. apply in_app_or in H1. 
destruct H1; auto.
Qed. 

Theorem seq_contraction2: forall IL1 IL2  LL i b, 
  seq i (IL2++IL1) LL b -> (forall a, In a IL1 -> In a IL2) ->
  seq i IL2 LL b.
intros IL1 IL2 LL i b H H0. 
apply seq_weakening_cor with (il:=IL2++IL1);auto.
intros a H1. apply in_app_or in H1. 
destruct H1; auto.
Qed. 

(****************************************************************
  Height Weakening
  ****************************************************************)

Definition P_seq_mono (j : nat) (il: list atm) (ll: list atm) (b: oo) : Prop :=
 forall k, j < k -> seq k il ll b.

Definition P0_splitseq_mono (j : nat) (il: list atm) (ll: list atm) (b: list oo) :Prop :=
 forall k, j < k -> splitseq k il ll b.

Theorem seq_mono :
 forall (j : nat) (il ll: list atm) (b : oo),
    seq j il ll b -> P_seq_mono j il ll b.
Proof.
intros j il ll b H.
apply seq_split_ind with (P := P_seq_mono) (P0:=P0_splitseq_mono); auto;
  unfold P_seq_mono, P0_splitseq_mono;
  intros; try destruct k; try assert (S k = k + 1); try omega;
  try constructor; auto.  (* handles the init and tt cases *)
- (* s_bc case *)
  rewrite H6. apply s_bc with lL iL; auto.
  + apply H2; omega.
  + apply H4; omega.
- (* m_and case *)
  rewrite H6.
  apply m_and with LL1 LL2; auto.
  + apply H2; omega.
  + apply H4; omega. 
- (* a_and case *)
  rewrite H5.
  apply a_and; auto.
  + apply H1;omega. 
  + apply H3;omega.
- (* i_imp case *)
  rewrite H3.
  apply i_imp; auto. apply H1; omega. 
- (* l_imp case *)
  rewrite H3.
  apply l_imp; auto. apply H1; omega. 
- (* s_all case *)
  rewrite H3.
  apply s_all; auto. intros; apply H1; auto ;omega. 
- (* ss_general case *)
  apply ss_general with lL2 lL3; auto.
Qed.

Theorem splitseq_mono :
 forall (j : nat) (il ll: list atm) (b : list oo),
    splitseq j il ll b -> P0_splitseq_mono j il ll b.
Proof.
intros j il ll b H.
apply split_seq_ind with (P := P_seq_mono) (P0:=P0_splitseq_mono); auto;
  unfold P_seq_mono, P0_splitseq_mono;
  intros; try destruct k; try assert (S k = k + 1); try omega;
  try constructor; auto.  (* handles the init and tt cases *)
- (* s_bc case *)
  rewrite H6. apply s_bc with lL iL;auto.
  + apply H2; omega.
  + apply H4; omega. 
- (* m_and case *)
  rewrite H6.
  apply m_and with LL1 LL2; auto.
  + apply H2; omega. 
  + apply H4; omega.
- (* a_and case *)
  rewrite H5.
  apply a_and; auto. 
  + apply H1; omega.
  + apply H3; omega.
- (* i_imp case *)
  rewrite H3.
  apply i_imp; auto. apply H1; omega. 
- (* l_imp case *)
  rewrite H3.
  apply l_imp; auto. apply H1; omega. 
- (* s_all case *)
  rewrite H3.
  apply s_all;auto. intros; apply H1; auto; omega. 
- (* ss_general case *)
  apply ss_general with lL2 lL3; auto.
Qed.

Theorem seq_mono_cor :
 forall (j k : nat) (il ll: list atm) (b : oo),
 j <= k -> seq j il ll b -> seq k il ll b.
Proof.
intros j k il ll b H H0.
specialize le_lt_or_eq with (1 := H); intro H1.
elim H1; clear H1; intro H1.
apply seq_mono with j; auto.
rewrite <- H1; auto.
Qed.

Theorem splitseq_mono_cor :
 forall (j k : nat) (il ll: list atm) (b :list oo),
 j <= k -> splitseq j il ll b -> splitseq k il ll b.
Proof.
intros j k il ll b H H0.
specialize le_lt_or_eq with (1 := H); intro H1.
elim H1; clear H1; intro H1.
apply splitseq_mono with j; auto.
rewrite <- H1; auto.
Qed.

(***********************************************************************
  Admissibility of Cut for Atomic Formulas in the Intuitionistic Context
  **********************************************************************)

Definition P_seq_cut (i : nat)  (il: list atm) (ll: list atm) (b: oo) :Prop :=
  forall j a, In a il ->  seq j (remove eq_dec a il) [] (atom a) ->
  (seq (i+j) (remove eq_dec a il) ll b).

Definition P0_splitseq_cut (i : nat) (il: list atm) (ll: list atm) (b: list oo):=
  forall j a,  In a il  -> seq j (remove eq_dec a il) [] (atom a) ->
  splitseq (i+j) (remove eq_dec a il) ll b.

Lemma seq_cut_aux:
  forall (i :nat)(a:atm)(b:oo)(il ll:(list atm)),
  seq i il ll b ->  P_seq_cut i il ll  b.
Proof.
intros i a b il ll H.
apply seq_split_ind with (P0:=P0_splitseq_cut);
  unfold P_seq_cut, P0_splitseq_cut; intros;
  try replace (i0+1+j) with ((i0+j)+1); try omega; auto.
- (* s_bc case *)
  apply s_bc with (lL:=lL) (iL:=iL); auto.          
- (* l_init case *)
  constructor; auto.
- (* i_init case *)
  destruct (eq_dec a0 A).
  + subst. apply seq_mono_cor with j; try omega; auto.
  + constructor; auto. apply remove_In; auto.
- (* s_tt case *)
  constructor; auto.
- (* m_and case *)
  apply m_and with LL1 LL2; auto. 
- (* a_and case *)
  constructor; auto.
- (* i_imp case *)
  simpl remove in H1. specialize H1 with j a0. 
  destruct (eq_dec a0 A).
  + apply i_imp. apply seq_weakening_cor with (remove eq_dec a0 IL); auto. 
    * apply H1; auto.
      apply in_cons; auto.
    * intros; apply in_cons; auto. 
  + apply i_imp. apply H1.
    * apply in_cons; auto. 
    * apply seq_weakening_cor with (remove eq_dec a0 IL); auto.
      intros. apply in_cons; auto.
- (* l_imp case *)
  constructor; auto.
- (* s_all case *)
  constructor; auto.
- (* ss_init_case *)
  constructor; auto.
- (* ss_general case *)
  apply ss_general with lL2 lL3; auto. 
Qed.

(* Ltac test:= apply H1 with H1. *)

(****************************************************************
  Linear Context Exchange
  ****************************************************************)

Definition P0_splitseq_exchange
 (i : nat)  (il: list atm) (ll: list atm)  (b: list oo) :Prop :=
 forall ll',  (forall a, count_occ eq_dec ll a = count_occ eq_dec ll' a)
 -> splitseq i il ll' b.

Definition P_seq_exchange
 (i : nat)  (il: list atm) (ll: list atm)  (b: oo) :Prop :=
 forall ll',  (forall a, count_occ eq_dec ll a = count_occ eq_dec ll' a) 
 -> seq i il ll' b.

Theorem seq_exchange : forall (j : nat) (b :  oo) (il ll: list atm),
  seq j il ll b -> P_seq_exchange j il ll b.
Proof.
intros j b il ll H.
apply seq_split_ind with (P0 := P0_splitseq_exchange);
  unfold P0_splitseq_exchange,P_seq_exchange; intros; auto.
- (* s_bc case *)
  apply s_bc with (lL:=lL) (iL:=iL); auto. 
- (* l_init case *)
  assert(h:=H0).
  apply count_occ_length in H0. destruct ll'.
  + simpl in H0. omega. 
  + destruct ll'. 
    * assert(In A [A]);try apply in_eq.
      rewrite count_occ_In,h,<-count_occ_In in H1.
      inversion H1. 
      { subst. apply l_init. }
      { inversion H2. }
    * simpl in H0. omega.
- (* i_init case *)
  simpl in H1. symmetry in H1.
  rewrite count_occ_inv_nil in H1. subst.
  apply i_init; auto.
- (* s_tt case *)
  constructor.
- (* m_and case *)
  apply split_same with (eq_dec:=eq_dec) (l':=ll') in H0;auto.
  inversion H0. inversion H6.
  inversion H7. inversion H9. apply m_and with (LL1:=x) (LL2:=x0); auto.
- (* a_and case *)
  constructor; auto.
- (* i_imp case *)
  constructor; auto.
- (* l_imp case *)
  apply l_imp; auto. apply H1.
  simpl. intros. rewrite H2. auto.
- (* s_all case *)
  constructor; auto.
- (* ss_init case *)
  simpl in H0. symmetry in H0. rewrite count_occ_inv_nil in H0.
  rewrite H0. apply ss_init; auto.
- (* ss_general case *)
  apply split_same with (eq_dec:=eq_dec) (l':=ll') in H0;auto.
  inversion H0. inversion H6.
  inversion H7. inversion H9. 
  apply ss_general with (lL2:=x) (lL3:=x0); auto.
Qed.

Theorem splitseq_exchange :
 forall (j : nat) (il ll: list atm) (b : list oo),
    splitseq j il ll b -> P0_splitseq_exchange j il ll b.
Proof.
apply split_seq_ind with (P := P_seq_exchange);
  unfold P0_splitseq_exchange,P_seq_exchange; intros; auto.
- (* s_bc case *)
  apply s_bc with (lL:=lL) (iL:=iL); auto. 
- (* l_init_case *)
  intros. assert(h:=H).
  apply count_occ_length in H. destruct ll'.
  + simpl in H. omega. 
  + destruct ll'. 
    * assert(In A [A]);try apply in_eq.
      rewrite count_occ_In,h,<-count_occ_In in H0.
      inversion H0.
      { subst. apply l_init. }
      { inversion H1. }
    * simpl in H. omega. 
- (* i_init case *)
  simpl in H0. symmetry in H0.
  rewrite count_occ_inv_nil in H0. subst.
  apply i_init. auto.
- (* s_tt case *)
  constructor.
- (* m_and case *)
  apply split_same with (eq_dec:=eq_dec) (l':=ll') in H;auto.
  inversion H. inversion H5.
  inversion H6. inversion H8. apply m_and with (LL1:=x) (LL2:=x0); auto.
- (* a_and case *)
  constructor; auto.
- (* i_imp case *)
  constructor; auto.
- (* l_imp case *)
  apply l_imp;auto. apply H0.
  simpl. intros. rewrite H1. auto.
- (* s_all case *)
  constructor; auto.
- (* ss_init_case *)
  simpl in H. symmetry in H. rewrite count_occ_inv_nil in H.
  rewrite H.
  apply ss_init; auto.
- (* ss_general case *)
  apply split_same with (eq_dec:=eq_dec) (l':=ll') in H;auto.
  inversion H. inversion H5.
  inversion H6. inversion H8. 
  apply ss_general with (lL2:=x) (lL3:=x0); auto.
Qed.

Theorem seq_exchange_cor :
  forall ( i : nat) (b :  oo) (il ll' ll: list atm), seq i il ll b ->
  (forall a, count_occ eq_dec ll a = count_occ eq_dec ll' a) ->
  seq i il ll' b.
Proof.
intros.
assert (H1:= seq_exchange). unfold P_seq_exchange in H1.
apply H1 with (ll:=ll);auto.
Qed.

Theorem splitseq_exchange_cor :
  forall ( i : nat) (b :  list oo) (il ll' ll: list atm),
  splitseq i il ll b ->
  (forall a,count_occ eq_dec ll a = count_occ eq_dec ll' a) ->
  splitseq i il ll' b.
Proof.
intros.
assert (H1:= splitseq_exchange). unfold P0_splitseq_exchange in H1.
apply H1 with (ll:=ll);auto.
Qed.

(****************************************************************
  Admissibility of Cut for Atomic Formulas in the Linear Context
  ***************************************************************)

Definition P_seq_cut_linear
  (i : nat)  (il: list atm) (ll: list atm)  (b: oo) :Prop :=
  forall j a ll',   In a ll ->  seq j il ll' (atom a) ->
  seq (i+j) il (ll'++(remove_one eq_dec ll a)) b.

Definition P0_splitseq_cut_linear
  (i : nat) (il: list atm) (ll: list atm)  (b: list oo):=
  forall j a ll',  In a ll  -> seq j il ll' (atom a) ->
  splitseq (i+j) il (ll'++(remove_one eq_dec ll a)) b.

Lemma seq_cut_linear:
  forall (i :nat)(a:atm)(b:oo)(il ll:(list atm)),
  seq i il ll b ->  P_seq_cut_linear i il ll  b.
Proof.
intros i a b il ll H.
apply seq_split_ind with (P0:=P0_splitseq_cut_linear);
  unfold P_seq_cut_linear,P0_splitseq_cut_linear; intros; auto.
- (* s_bc case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega.
  apply s_bc with (lL:=lL) (iL:=iL);auto.
  apply splitseq_mono_cor with (j:=i0). omega. auto.          
- (* l_init case *)
  inversion H0.
  + subst. simpl. destruct (eq_dec a0 a0).
    * rewrite app_nil_r. apply seq_mono_cor with (j:=j); auto.
      omega.
    * contradict n. auto.
  + inversion H2.
- (* i_init case *)
  inversion H1.
- (* s_tt case *)
  apply s_tt. 
- (* m_and case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. assert(h':=H0). 
  apply in_split_or with (a:=a0) in H0;auto. destruct H0.
  + assert(h0:=H0).
    apply H2 with (j:=j) (ll':=ll') in H0;auto.
    apply seq_exchange_cor with (ll:=(ll'++ remove_one eq_dec LL1 a0)++ LL2).
    * apply m_and with (ll' ++ remove_one eq_dec LL1 a0) LL2;auto.
      { apply concat_split. auto. }
      { apply seq_mono_cor with (j:=i0);try omega. auto. }
    * intros.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec LL a0) 
              (l:=ll' ++ remove_one eq_dec LL a0);auto.
      rewrite count_app with (l1:=(ll' ++ remove_one eq_dec LL1 a0))
              (l2:=LL2) (l:=(ll' ++ remove_one eq_dec LL1 a0) ++ LL2);auto.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec LL1 a0) 
              (l:=ll' ++ remove_one eq_dec LL1 a0);auto.
      destruct (eq_dec a0 a1).
      { subst. repeat rewrite count_occ_remove_in.
        apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        rewrite h'. rewrite count_occ_In with (eq_dec:=eq_dec) in h0,  H5.
        omega. }
      { apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        repeat rewrite count_occ_remove_nin;auto. rewrite h'.  omega. }
  + assert(h0:=H0).
    apply H4 with (j:=j) (ll':=ll') in H0;auto.
    apply seq_exchange_cor with (ll:=LL1++(ll'++ remove_one eq_dec LL2 a0)).
    * apply m_and with LL1 (ll' ++ remove_one eq_dec LL2 a0) ;auto.
      { apply concat_split. auto. }
      { apply seq_mono_cor with (j:=i0);try omega. auto. }
    * intros.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec LL a0) 
              (l:=ll' ++ remove_one eq_dec LL a0);auto.
      rewrite count_app with (l2:=(ll' ++ remove_one eq_dec LL2 a0))
              (l1:=LL1) (l:=LL1++ll' ++ remove_one eq_dec LL2 a0);auto.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec LL2 a0) 
              (l:=ll' ++ remove_one eq_dec LL2 a0);auto.
      destruct (eq_dec a0 a1). 
      { subst. repeat rewrite count_occ_remove_in.
        apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        rewrite h'. rewrite count_occ_In with (eq_dec:=eq_dec) in h0, H5.
        omega. }
      { apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        repeat rewrite count_occ_remove_nin;auto. rewrite h'.  omega. }
- (* a_and case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. apply a_and;auto. 
- (* i_imp case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. 
  apply i_imp, H1;auto.
  apply seq_weakening_cor with ( il:=IL);auto.
  intros. apply in_cons. auto.
- (* l_imp case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. 
  apply l_imp.
  apply seq_exchange_cor with
    (ll:=ll' ++ remove_one eq_dec (A :: LL) a0);auto.
  + apply H1;auto. apply in_cons. auto.
  + intros. 
    rewrite count_app with (l1:=ll')
            (l2:=remove_one eq_dec (A :: LL) a0); auto.
    rewrite app_comm_cons, count_app with
            (l:=(A :: ll') ++ remove_one eq_dec LL a0)
            (l1:=A::ll') (l2:=remove_one eq_dec LL a0); auto.
    destruct (eq_dec a0 a1).
    * subst. repeat rewrite count_occ_remove_in.
      simpl. destruct (eq_dec A a1); auto.
      rewrite count_occ_In with (eq_dec:=eq_dec) in H2. omega.
    * repeat rewrite count_occ_remove_nin;auto. simpl.
      destruct (eq_dec A a1);omega.
- (* s_all case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. apply s_all;auto.
- (* ss_init case *)
  inversion H0.
- (* ss_general case *)
  assert(h':=H0). 
  apply in_split_or with (a:=a0) in H0;auto. destruct H0.
  + assert(h0:=H0).
    apply H2 with (j:=j) (ll':=ll') in H0;auto.
    apply splitseq_exchange_cor with
          (ll:=(ll'++ remove_one eq_dec lL2 a0)++ lL3).
    * apply ss_general with (ll' ++ remove_one eq_dec lL2 a0) lL3;auto.
      { apply concat_split. auto. }
      { apply splitseq_mono_cor with (j:=i0);try omega. auto. }
    * intros.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec lL1 a0) 
              (l:=ll' ++ remove_one eq_dec lL1 a0);auto.
      rewrite count_app with (l1:=(ll' ++ remove_one eq_dec lL2 a0))
              (l2:=lL3) (l:=(ll' ++ remove_one eq_dec lL2 a0) ++ lL3);auto.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec lL2 a0) 
              (l:=ll' ++ remove_one eq_dec lL2 a0);auto.
      destruct (eq_dec a0 a1). 
      { subst. repeat rewrite count_occ_remove_in.
        apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        rewrite h'. rewrite count_occ_In with (eq_dec:=eq_dec) in h0, H5.
        omega. }
      { apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        repeat rewrite count_occ_remove_nin;auto. rewrite h'.  omega. }
  + assert(h0:=H0).
    apply H4 with (j:=j) (ll':=ll') in H0;auto.
    apply splitseq_exchange_cor with
          (ll:=lL2++(ll'++ remove_one eq_dec lL3 a0)).
    * apply ss_general with lL2 (ll' ++ remove_one eq_dec lL3 a0) ;auto.
      { apply concat_split. auto. }
      { apply seq_mono_cor with (j:=i0);try omega. auto. }
    * intros.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec lL1 a0) 
              (l:=ll' ++ remove_one eq_dec lL1 a0);auto.
      rewrite count_app with (l2:=(ll' ++ remove_one eq_dec lL3 a0))
              (l1:=lL2) (l:=lL2++ll' ++ remove_one eq_dec lL3 a0);auto.
      rewrite count_app with (l1:=ll') (l2:=remove_one eq_dec lL3 a0) 
              (l:=ll' ++ remove_one eq_dec lL3 a0);auto.
      destruct (eq_dec a0 a1).
      { subst. repeat rewrite count_occ_remove_in.
        apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        rewrite h'. rewrite count_occ_In with (eq_dec:=eq_dec) in h0, H5.
        omega. }
      { apply count_split with (eq_dec:=eq_dec) (a:=a1) in h'.
        repeat rewrite count_occ_remove_nin;auto. rewrite h'. omega. }
Qed.

Theorem seq_cut_linear_cor:
  forall (i j:nat)(a:atm)(b:oo)(il ll ll':(list atm)),
  seq i il ll b ->   In a ll ->  seq j il ll' (atom a)  ->
  (seq (i+j) il (ll'++(remove_one eq_dec ll a))  b).
Proof.
intros. apply seq_cut_linear in H;auto.
Qed.

Definition P_seq_cut_one
  (i : nat)  (il: list atm) (ll: list atm)  (b: oo) :Prop :=
  forall j a, In a il -> seq j (remove_one eq_dec il a) [] (atom a) ->
  (seq (i+j) (remove_one eq_dec il a) ll b).

Definition P0_splitseq_cut_one
  (i : nat)  (il: list atm) (ll: list atm)  (b: list oo):=
  forall j a,  In a il  -> seq j (remove_one eq_dec il a) [] (atom a) ->
  splitseq (i+j) (remove_one eq_dec il a) ll b.

Lemma seq_cut_one_aux:
  forall (i :nat)(a:atm)(b:oo)(il ll:(list atm)),
  seq i il ll b ->  P_seq_cut_one i il ll  b.
Proof.
intros i a b il ll H.
apply seq_split_ind with (P0:=P0_splitseq_cut_one); auto; 
  unfold P_seq_cut_one,P0_splitseq_cut_one; intros.
- (* s_bc case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega.
  apply  s_bc with (lL:=lL) (iL:=iL);auto.          
- (* l_init case *)
  apply l_init.
- (* i_init case *)
  destruct (eq_dec a0 A).
  + subst. apply seq_mono_cor with j;try omega;auto.
  + apply i_init. apply remove_one_in;auto.
- (* s_tt case *)
  constructor.
- (* m_and case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. 
  apply m_and with LL1 LL2;auto. 
- (* a_and case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. constructor;auto. 
- (* i_imp case *)
  simpl remove_one in H1. specialize H1 with j a0. 
  replace (i0 +1+j) with ((i0+j)+1); try omega. destruct (eq_dec a0 A).  
  + apply i_imp. apply seq_weakening_cor with IL;auto. 
    * apply H1.
      { subst. apply in_eq. }
      { apply seq_weakening_cor with (remove_one eq_dec IL a0);auto.
        apply remove_one_in2. }
    * intros. destruct (eq_dec a1 A).
      { subst. apply in_eq. } 
      { subst. apply in_cons,remove_one_in;auto. }
  + apply i_imp. apply H1.
    * apply in_cons;auto. 
    * apply seq_weakening_cor with (remove_one eq_dec IL a0);auto.
      intros. apply in_cons;auto.
- (* l_limp case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. apply l_imp;auto.
- (* s_all case *)
  replace (i0 +1+j) with ((i0+j)+1); try omega. apply s_all;auto.
- (* ss_init case *)
  apply ss_init.
- (* ss_general case *)
  apply ss_general with lL2 lL3;auto.
Qed.

End lsl.
