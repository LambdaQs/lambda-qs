(****************************************************************
   File: ProgLemmas2.v
   Authors: Mohamend Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Lemmas about seq_ and prog, mainly inversion lemmas
   ***************************************************************)

Require Import ProgLemmas1.
Require Import PQAdequacy.
Require Import ProtoQuipperProg.
Require Import LSL.
Require Import ProtoQuipperSyntax.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Definition seq_ := ProgLemmas1.seq_.
Definition prog := ProgLemmas1.prog.


(*******************************)
(* Inversion Lemmas about seq_ *)
(*******************************)

Theorem fun_typed2: forall i IL LL f A,
    Subtypecontext IL LL IL LL -> abstr f -> 
    seq_ i IL LL (atom_ (typeof (Fun f) A)) ->
    ~(In (is_qexp (Fun f)) IL) ->  
    ((exists j T T', j+1+1 <= i /\ validT (bang T) /\ validT T' /\  
      ((Subtyping (arrow T T') A /\
        splitseq prog j IL LL
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (lImp (typeof x T)
                                    (atom_ (typeof (f x) T')))))])
       \/
       (Subtyping (arrow (bang T) T') A /\
        splitseq prog j IL LL
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (Imp (typeof x (bang T))
                                   (atom_ (typeof (f x) T')))))])))
     \/ 
     (exists j T T', j+1+1 <= i /\ validT (bang T) /\ validT T' /\  
      ((Subtyping (bang(arrow T T')) A /\ LL = [] /\
        splitseq prog j IL []
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (lImp (typeof x T)
                                    (atom_ (typeof (f x) T')))))])
       \/
       (Subtyping (bang(arrow (bang T) T')) A /\ LL=[] /\
        splitseq prog j IL []
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (Imp (typeof x (bang T))
                                   (atom_ (typeof (f x) T')))))])))
     \/
     (exists j T T', j+1 <= i /\ validT (bang T) /\ validT T' /\
      ((A = arrow T T' /\
        splitseq prog j IL LL
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (lImp (typeof x T)
                                    (atom_ (typeof (f x) T')))))])
       \/
       (A = (arrow (bang T) T') /\
        splitseq prog j IL LL
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (Imp (typeof x (bang T))
                                   (atom_ (typeof (f x) T')))))])))
     \/ 
     (exists j T T', j+1 <= i /\ validT (bang T) /\ validT T' /\
      ((A = bang((arrow T T')) /\ LL = [] /\
        splitseq prog j IL []
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (lImp (typeof x T)
                                    (atom_ (typeof (f x) T')))))])
       \/
       (A = (bang(arrow (bang T) T')) /\ LL=[] /\
        splitseq prog j IL []
                 [(All (fun x : qexp =>
                          Imp (is_qexp x)
                              (Imp (typeof x (bang T))
                                   (atom_ (typeof (f x) T')))))])))).
Proof.
intros  i IL LL f A H h. intros.  induction i.
inversion H0. omega. 
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
assert(i0+1+1=i); try omega. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17.
inversion H18.  inversion H25.
inversion H31.  destruct H33.
inversion H33. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega.

inversion H3.
inversion H12. inversion H17. inversion H18.
inversion H24. inversion H30. inversion H32.
destruct H34. inversion H34. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25. 
clear.  intros. omega. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega.

inversion H12. inversion H17. inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33.  destruct H35. inversion H35. 
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H30. 
clear.  intros. omega. 
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H30. 
clear.  intros. omega.

inversion H17. inversion H18.
inversion H24.     inversion H25. inversion H31.
inversion H33.  destruct H35. inversion H35. 
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H30. 
clear.  intros. omega. 
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H30. 
clear.  intros. omega.
 
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try omega.
apply IHi in H29. inversion H29. 
inversion H3. inversion H12. inversion H18.
inversion H24. inversion H31.
inversion H33.  destruct H35.
inversion H35. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25 H2. 
clear.  intros. omega. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25 H2. 
clear.  intros. omega.

inversion H3. 
inversion H12. inversion H18. inversion H24.
inversion H25.  inversion H32. inversion H34.
destruct H36. inversion H36. 
 right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H31 H2. 
clear.  intros. omega. 
 right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H31 H2. 
clear.  intros. omega.

inversion H12. inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33. inversion H35. destruct H37. inversion H37. 
 right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2. 
clear.  intros. omega. 
 right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2. 
clear.  intros. omega.

inversion H18.
inversion H24. inversion H25. inversion H31.
inversion H33. inversion H35. destruct H37. inversion H37. 
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2. 
clear.  intros. omega.
 right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H32 H2. 
clear.  intros. omega.

apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
subst. left.  exists i0. exists T1. exists T2.
split. clear. omega. split. auto. split. auto.
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
split. clear. omega. split. auto. split. auto.
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
split. clear. omega. split. auto. split. auto.
left. split. apply sub_trans with (B:=A1);auto.
split. inversion H23. auto. apply ss_general with (lL2:=[]) (lL3:=[]).
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
assert(i0+1+1=i);try omega. subst.
apply IHi in H22. inversion H22. inversion H3. 
inversion H9.  inversion H12. inversion H17.
inversion H24.  inversion H26.
destruct H28.
inversion H28. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H18. 
clear.  intros. omega. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H18. 
clear.  intros. omega.

inversion H3.
inversion H9. inversion H12. inversion H17.
inversion H18. inversion H25. inversion H27.
destruct H29. inversion H29. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega.

inversion H9. inversion H12. inversion H17.
inversion H18.
inversion H24. inversion H26.
inversion H28.  destruct H30. inversion H30. 
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25. 
clear.  intros. omega. 
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H25. 
clear.  intros. omega.

inversion H12. inversion H17.
inversion H18.     inversion H24. inversion H26.
inversion H28.  destruct H30. inversion H30. 
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H25. 
clear.  intros. omega. 
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H25. 
clear.  intros. omega.
 
apply sub_trans with (B:=A1);auto. auto.

subst. left.  exists i1. exists T1. exists T2.
split. clear. omega. split. auto. split. auto.
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
split. clear. omega. split. auto. split. auto.
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
assert(i2+1+1=i); try omega. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6.  
inversion H10.  inversion H11. inversion H22.
inversion H25. 
destruct H28.
inversion H28. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H17. 
clear.  intros. omega. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H17. 
clear.  intros. omega.

inversion H3.
inversion H6. inversion H10. inversion H11.
inversion H17. inversion H24. inversion H27.
destruct H30. inversion H30. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H22. 
clear.  intros. omega. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H22. 
clear.  intros. omega.

inversion H6. inversion H10. inversion H11.
inversion H17.
inversion H22. inversion H25.
inversion H28.  destruct H31. inversion H31. 
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega. 
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega.

inversion H10. inversion H11.
inversion H17.     inversion H22. inversion H25.
inversion H28.  destruct H31. inversion H31. 
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega. 
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H24. 
clear.  intros. omega.

apply sub_trans with (B:=bang A1);auto.

subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try omega.
apply IHi in H22. inversion H22. inversion H25. 
inversion H26. inversion H27. inversion H29.
inversion H31. inversion H33. destruct H35.
inversion H35. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H10 H2 H30. 
clear.  intros. omega. 
 left. exists x.  exists x0. exists x1.
repeat split; auto. revert H10 H2 H30. 
clear.  intros. omega.

inversion H25.
inversion H26. inversion H27. inversion H29.
inversion H30. inversion H32. inversion H34.
destruct H36. inversion  H36. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H31. 
clear.  intros. omega. 
right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H31. 
clear.  intros. omega.

inversion H26. inversion H27. inversion H29.
inversion H30.
inversion H31. inversion H33.
inversion H35.  destruct H37. inversion H37. 
right. right.  left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32. 
clear.  intros. omega. 
right. right. left. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32. 
clear.  intros. omega.

inversion H27. inversion H29.
inversion H30.     inversion H31. inversion H33.
inversion H35.  destruct H37. inversion H37. 
right. right.  right. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32. 
clear.  intros. omega. 
right. right. right. exists x.  exists x0. exists x1.
repeat split; auto. revert H2 H10 H32. 
clear.  intros. omega.

apply sub_trans with (B:=bang A1);auto.

subst. right. left.  exists i2. exists T1. exists T2.
split. clear. omega. split. auto. split. auto.
right. split. auto. split. inversion H8. auto.
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
split. clear. omega. split. auto. split. auto.
left. split. auto. split. inversion H8. auto.
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
split. clear. omega. split. auto. split. auto.
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
split. clear. omega. split. auto. split. auto.
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
split. clear. omega. split. auto. split. auto.
right. split. auto. split. inversion H8. auto.
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
split. clear. omega. split. auto. split. auto.
left. split. auto. split. inversion H8. auto.
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


Theorem True_LL: forall i IL LL, 
    ~(In (is_qexp (CON TRUE)) IL) ->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON TRUE) bool)) -> LL = [].
Proof.
intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=bool) in H;auto.
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
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=bool)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
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
apply notqext_nottyped with (lt:=LL) (T:=bool) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed. 


Theorem False_LL: forall i IL LL, 
    ~(In (is_qexp (CON FALSE)) IL)->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON FALSE) bool)) -> LL = [].
Proof.
intros. induction i.
inversion H1. omega.
apply notqext_nottyped with (lt:=LL) (T:=bool) in H;auto.
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
apply subtypecontext_subtyping with (LL':=lL2) (IL':=IL) (B:=bool)in H27;auto.
assert(i0+1+1= i);try omega. rewrite H3 in H27.
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
apply notqext_nottyped with (lt:=LL) (T:=bool) in H;auto.
inversion H. subst. contradict H7. apply in_eq.
Qed. 

Theorem app_typed: forall i IL LL e1 e2 A,
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_ (typeof (App e1 e2) A))->
    ~(In (is_qexp (App e1 e2)) IL) ->
    (exists j T' B, j+1+1 <= i /\ Subtyping B A /\ validT (arrow T' B) /\
     splitseq prog j IL LL
              [(Conj (atom_ (typeof e1 (arrow T' B))) (atom_ (typeof e2 T')))])
    \/
    (exists j T', j+1 <= i /\ validT (arrow T' A)/\   
     splitseq prog j IL LL
              [(Conj (atom_ (typeof e1 (arrow T' A))) (atom_ (typeof e2 T')))]).
Proof.
intros. induction i.
inversion H0. omega. 
subst. 
apply notqext_nottyped with (a:=App e1 e2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A) in H;auto.
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
assert(i0+1+1=i); try omega. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17. 
left. exists x. exists x0. exists x1. auto. inversion  H18.
split. omega. auto. 
right. inversion H3.  inversion H12.
exists x. exists x0. inversion H17.  split. omega. auto. 
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try omega.
apply IHi in H29. inversion H29. inversion H3.
inversion H12. 
inversion H18. inversion H24. 
left. exists x. exists x0. exists x1. auto. 
split. omega. auto. 
right. inversion H3.  inversion H12. inversion H18.
exists x. exists x0. split. omega. auto. 
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i0. exists T'. exists A2.
split. omega.
split. apply sub_trans with (B:=A1);auto. split.
 auto. auto. 
subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7. 
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try omega. subst.
apply IHi in H22. inversion H22. inversion H3. 
inversion H9. inversion H12.
left. exists x. exists x0. exists x1. auto. inversion  H17.
split. omega. auto. 
right. inversion H3.  inversion H9. inversion H12.
exists x. exists x0. split. omega. auto. 
apply sub_trans with (B:=A1);auto.
left. subst. exists i1. exists T'. exists A1. split. 
omega. split. auto.  auto.
subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try omega. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6. inversion H10.
left. exists x. exists x0. exists x1. auto. inversion  H11.
split. omega. auto. 
right. inversion H3.  inversion H6. inversion H10.
exists x. exists x0. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try omega.
apply IHi in H22. inversion H22. inversion H25. 
inversion H26.  inversion H27.
left. exists x. exists x0. exists x1. auto. inversion  H29.
split. omega. auto. 
right. inversion H25.  inversion H26. inversion H27.
exists x. exists x0. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
left. subst. exists i2. exists T'. exists (bang A1).
split. omega.
split. auto. split. auto. inversion H8. subst.
 auto.
subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto.
subst. right. exists i0. exists T'. split. omega. 
 split. auto. auto.

subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=App e1 e2) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

Theorem prod_typed: forall i IL LL e1 e2 A,
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_ (typeof (Prod e1 e2) A)) ->
    ~(In (is_qexp (Prod e1 e2)) IL) ->
    (exists j T T' B, j+1+1 <= i /\ Subtyping B A /\
     ((B = tensor T T' /\ validT (tensor T T') /\
       splitseq prog j IL LL [Conj (atom_ (typeof e1 T)) (atom_ (typeof e2 T'))])
      \/
      (B = bang (tensor T T') /\ validT (bang T) /\ validT (bang T')/\
       splitseq prog j IL LL
                [Conj (atom_ (typeof e1 (bang T))) (atom_ (typeof e2 (bang T')))])))
    \/         
    (exists j T T', j+1 <= i /\
     ((A = tensor T T' /\ validT (tensor T T') /\
       splitseq prog j IL LL [Conj (atom_ (typeof e1 T)) (atom_ (typeof e2 T'))])
      \/
      (A = bang (tensor T T') /\ validT (bang T) /\ validT (bang T') /\
       splitseq prog j IL LL
                [Conj (atom_ (typeof e1 (bang T))) (atom_ (typeof e2 (bang T')))]))).
Proof.
intros. induction i.
inversion H0. omega. 
subst. 
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A) in H;auto.
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
assert(i0+1+1=i); try omega. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17.
inversion H18.
left. exists x. exists x0. exists x1.
exists x2. inversion  H24.
split. omega. auto. 
right. inversion H3.  inversion H12.
inversion H17.
exists x. exists x0. exists x1. inversion H18.
split. omega. auto. 
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try omega.
apply IHi in H29. inversion H29. inversion H3.
inversion H12. 
inversion H18. inversion H24. 
left. exists x. exists x0. exists x1. exists x2. auto. 
split. omega. inversion H25. auto. 
right. inversion H3.  inversion H12.
inversion H18. inversion H24. 
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i0. 
exists T. exists T'. exists (tensor T T').
split. omega.
split. apply sub_trans with (B:=A1);auto.
left. auto. subst.
left. exists i0. exists T. exists T'. exists (bang(tensor T T')).  
split. omega.
split. apply sub_trans with (B:=A1);auto.
right. auto.
subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7. 
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try omega. subst.
apply IHi in H22. inversion H22. inversion H3. 
inversion H9.  inversion H12. inversion H17.
left. exists x. exists x0. exists x1. exists x2.
inversion  H18.
split. omega. auto. 
right. inversion H3.  inversion H9. inversion H12.
inversion H17.
exists x. exists x0. exists x1. split. omega. auto. 
apply sub_trans with (B:=A1);auto.
left. subst. exists i1. exists T. exists T'. exists (tensor T T').
split. 
omega. split. auto. left.  auto.
left. subst. exists i1. exists T. exists T'. exists (bang(tensor T T')).
split. 
omega. split. auto. right. auto.
subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try omega. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6. inversion H10. inversion H11.
inversion H17.
left. exists x. exists x0. exists x1. exists x2. 
split. omega. auto. 
right. inversion H3.  inversion H6. inversion H10. inversion H11.
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try omega.
apply IHi in H22. inversion H22. inversion H25. 
inversion H26. inversion H27. inversion H29.
inversion H30.
left. exists x. exists x0. exists x1. exists x2. 
split. omega. auto. 
right. inversion H25.  inversion H26. inversion H27.
inversion H29.
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
left. subst. exists i2. exists T. exists T'. exists (bang (tensor T T')).
split. omega.
split. auto. inversion H8. subst.
 right. auto.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto. subst.
subst. right. exists i0. exists T. exists T'. 
split. omega. left. auto. 
right. subst. exists i0.  exists T. exists T'. 
split. omega. right. auto.
subst.
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A) in H;auto.
inversion H.  contradict H3. apply in_eq. 
apply notqext_nottyped with (a:=Prod e1 e2) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.


Theorem sub_Circ_inv: forall i IL LL t a c A,
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_ (typeof (Circ t c a) A)) ->
    ~(In (is_qexp (Circ t c a)) IL) ->
    (exists j T T' B, j+1+1 <= i /\ Subtyping B A /\ validT (circ T T') /\ LL = [] /\
     splitseq prog j IL [] [And (toimp (FQ a) (atom_(typeof a T')))
                                ((toimp (FQ t) (atom_(typeof t T))))]
     /\
     ((B = circ T T') \/ (B = bang (circ T T'))))
    \/
    (exists j T T', j+1 <= i /\ validT (circ T T') /\ LL = [] /\
     splitseq prog j IL [] [And (toimp (FQ a) (atom_(typeof a T')))
                                ((toimp (FQ t) (atom_(typeof t T))))]
     /\
     ((A = circ T T') \/ (A = bang (circ T T')))).
Proof.
intros. induction i.
inversion H0. omega. 
subst. 
apply notqext_nottyped with (a:=Circ t c a) (T:=A) in H;auto.
inversion H. contradict H3.
apply in_eq. subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A) in H;auto.
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
assert(i0+1+1=i); try omega. subst.
apply IHi in H27. inversion H27.
inversion H3. inversion H12. inversion H17.
inversion H18.
left. exists x. exists x0. exists x1.
exists x2. inversion  H24.
split. omega. auto. 
right. inversion H3.  inversion H12.
inversion H17.
exists x. exists x0. exists x1. inversion H18.
split. omega. auto. 
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto. auto.
subst. inversion H10. apply split_nil in H17. inversion H17.
subst. inversion H26. inversion H23. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H29;auto.
apply seq_mono_cor with (k:= i) in H29; try omega.
apply IHi in H29. inversion H29. inversion H3.
inversion H12. 
inversion H18. inversion H24. 
left. exists x. exists x0. exists x1. exists x2. auto. 
split. omega. inversion H25. auto. 
right. inversion H3.  inversion H12.
inversion H18. inversion H24. 
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
left. subst. exists i0. 
exists T. exists U. exists (circ T U).
split. omega.
split. apply sub_trans with (B:=A1);auto.
repeat split;auto. inversion H23.  auto.  subst.
left. exists i0. exists T. exists U. exists (bang(circ T U)).  
split. omega.
split. apply sub_trans with (B:=A1);auto. repeat split;auto.
inversion H23. auto. 
subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A2) in H;auto.
inversion H. contradict H9.
apply in_eq. subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A2) in H;auto.
inversion H. contradict H2. auto. auto.
subst. inversion H7. 
apply split_nil in H10. inversion H10. subst.
inversion H19. inversion H16. subst.
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
assert(i0+1+1=i);try omega. subst.
apply IHi in H22. inversion H22. inversion H3. 
inversion H9.  inversion H12. inversion H17.
left. exists x. exists x0. exists x1. exists x2.
inversion  H18.
split. omega. auto. 
right. inversion H3.  inversion H9. inversion H12.
inversion H17.
exists x. exists x0. exists x1. split. omega. auto. 
apply sub_trans with (B:=A1);auto.
left. subst. exists i1. exists T. exists U. exists (circ T U).
split. 
omega. repeat split;auto. inversion H16. auto. 
left. subst. exists i1. exists T. exists U. exists (bang(circ T U)).
split. 
omega. repeat split; auto. inversion H16. auto.
subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A1) in H;auto.
inversion H. contradict H6.
apply in_eq. subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A1) in H;auto.
inversion H. contradict H3. auto. auto.
subst. inversion H5. apply split_nil in H7. inversion H7.
subst. inversion H12.
inversion H15. inversion H18.
subst. inversion H23. apply split_nil in H9.
inversion H8. inversion H9. subst. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H20;auto.
assert(i2+1+1=i); try omega. subst.
apply IHi in H20. inversion H20.
inversion H3.
inversion H6. inversion H10. inversion H11.
inversion H17.
left. exists x. exists x0. exists x1. exists x2. 
split. omega. auto. 
right. inversion H3.  inversion H6. inversion H10. inversion H11.
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. apply split_nil in H9.
inversion H9. inversion H8. subst. inversion H20. 
apply subtypecontext_subtyping with (IL':=IL) (LL':=[]) (B:=A) in H22;auto.
apply seq_mono_cor with (k:= i) in H22; try omega.
apply IHi in H22. inversion H22. inversion H25. 
inversion H26. inversion H27. inversion H29.
inversion H30.
left. exists x. exists x0. exists x1. exists x2. 
split. omega. auto. 
right. inversion H25.  inversion H26. inversion H27.
inversion H29.
exists x. exists x0. exists x1. split. omega. auto. 
 apply sub_trans with (B:=bang A1);auto.
left. subst. exists i2. exists T. exists U. exists (bang (circ T U)).
split. omega.
repeat split; auto. inversion H8. auto.
apply notqext_nottyped with (a:=Circ t c a) (T:=bang A1) in H;auto.
inversion H.  contradict H3. auto. subst.
subst. right. exists i0. exists T. exists U. 
split. omega. repeat split;auto. inversion H8.  auto. 
right. subst. exists i0.  exists T. exists U. 
split. omega. repeat split;auto. inversion H8.  auto.
subst.
apply notqext_nottyped with (a:=Circ t c a) (T:=A) in H;auto.
inversion H.  contradict H3. apply in_eq. 
apply notqext_nottyped with (a:=Circ t c a) (T:=A) in H;auto.
inversion H. contradict H2. auto.
Qed.

Theorem BOX_LL: forall i IL LL A T0, 
    ~(In (is_qexp (CON (BOX T0))) IL)->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON (BOX T0)) A)) ->
    LL = [] /\
    exists  U, Subtyping (bang(arrow (bang (arrow T0 U)) (bang (circ T0 U)))) A.
Proof.
intros. induction i.
inversion H1. omega.
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
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto. auto.
subst. inversion H23. 
inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
apply seq_mono_cor with (k:= i) in H26;try omega.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
subst. inversion H23. split.  auto.
exists U.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto.


apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. apply in_eq.
apply notqext_nottyped with (lt:=[]) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto.
subst.  auto. auto.
subst. inversion H7. 
apply split_nil in H10. inversion H10. subst.
inversion H19. 
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
assert(i= i0+1+1);try omega.
rewrite <- H24 in H22.
inversion H16. subst. apply IHi in H22. auto.
inversion H16. subst. auto.
apply sub_trans with (B:=A1);auto.
inversion H16. split;auto.
exists U.
apply sub_trans with (B:=A1);auto.
subst. inversion H16. split. auto.
exists U.
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
assert(i= i2+1+1);try omega.
rewrite <- H3 in H20. apply IHi in H20. auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. 
apply split_nil in H7.
inversion H7. subst. inversion H20.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
apply seq_mono_cor with (k:= i) in H22;try omega.
apply IHi in H22. auto.
apply sub_trans with (B:=bang A1);auto.

split. auto. exists U.
apply sub_trans with (B:=bang A1);auto.
apply notqext_nottyped with (lt:=[]) (T:=bang A1) in H;auto.
inversion H. subst. contradict H21. auto. 
subst. inversion H8. split. auto.
exists U. auto.


apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. apply in_eq.

apply notqext_nottyped with (lt:=LL) (T:=A) in H;auto.
inversion H. subst. contradict H7. auto. 
Qed. 


Theorem REV_LL: forall i IL LL A, 
    ~(In (is_qexp (CON REV)) IL)->
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_(typeof (CON REV) A)) ->
    LL = [] /\
    exists T U, Subtyping (bang(arrow ( (circ T U)) (bang (circ U T)))) A.
Proof.
intros. induction i.
inversion H1. omega.
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
assert(i0+1+1= i);try omega. rewrite H3 in H27.
apply IHi in H27. auto.
apply sub_trans with (B:=A1);auto.
apply sub_trans with (B:=A2);auto. auto.
subst. inversion H23. 
inversion H10. apply split_nil in H25.
inversion H25. subst. inversion H30.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H26;auto.
apply seq_mono_cor with (k:= i) in H26;try omega.
apply IHi in H26. auto.
apply sub_trans with (B:=A2);auto.
apply sub_trans with (B:=A1);auto.
subst. inversion H23. split.  auto.
exists T. exists U.
apply sub_trans with (B:=A2);auto.
auto.
apply sub_trans with (B:=A1);auto.


apply notqext_nottyped with (lt:=lL0) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto. auto. apply in_eq.
apply notqext_nottyped with (lt:=[]) (T:=A2) in H;auto.
inversion H. subst. contradict H18. auto.
subst.  auto. auto.
subst. inversion H7. 
apply split_nil in H10. inversion H10. subst.
inversion H19. 
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
assert(i= i0+1+1);try omega.
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
assert(i= i2+1+1);try omega.
rewrite <- H3 in H20. apply IHi in H20. auto.
apply sub_trans with (B:=bang A1);auto.
subst. inversion H19. 
apply split_nil in H7.
inversion H7. subst. inversion H20.
apply subtypecontext_subtyping with (LL':=[]) (IL':=IL) (B:=A)in H22;auto.
apply seq_mono_cor with (k:= i) in H22;try omega.
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


Theorem app_box_value: forall i IL LL v A T0,
    Subtypecontext IL LL IL LL -> 
    seq_ i IL LL (atom_ (typeof (App (CON (BOX T0)) v) A)) ->
    ~(In (is_qexp (App (CON (BOX T0)) v)) IL) -> 
    ((forall V, v = App (CON UNBOX) V -> ~In (is_qexp V) IL)) -> 
    ~In (is_qexp v) IL -> 
    ~In (is_qexp (CON UNBOX)) IL -> 
    ~In (is_qexp (CON (BOX T0))) IL -> 
    is_value v ->
    LL= [] /\
    (exists j  U A2, j+1+1 <= i /\ Subtyping (bang(circ T0 U)) A /\
                     seq_ j IL [] (atom_ (typeof v (bang A2))) /\ 
                     Subtyping (bang A2) (bang (arrow T0 U))).
Proof.
intros i IL LL v A T0 H H0 H1 H2 H97 H98 H99 H100. apply app_typed in H0;auto.
destruct H0. inversion H0.
inversion H3. inversion H4. inversion H5.
inversion H7. inversion H9.
inversion H11. inversion H19.
subst. apply split_ident in H14. subst.
inversion H18. apply BOX_LL in H20;auto.
inversion H20. inversion H23. inversion H24.
inversion H26. 
apply Subtyping_bang_inv in H32.
inversion H32. inversion H35. subst.
inversion H37. subst. 
assert(H21':=H21).
apply sub_bangarrow_inv in H21;auto. 
inversion H21. inversion H12.
subst. assert(h21:=H21'). inversion H21'. inversion H15.
subst. inversion H40 ;subst; inversion H36.
subst. inversion H30. split;auto.

apply split_identr in H14.
subst; auto. auto.
exists (i1+1). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H29. apply bArrow;auto.
subst. inversion H30. split;auto.
apply split_identr in H14.
subst; auto. auto.
exists (i1+1). exists x2.  exists (arrow (bang T1) B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H29. apply bArrow;auto.

subst. inversion H30. apply split_identr in H14.
subst.
split;auto.
exists (i1+1). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H13. apply bArrow;auto. auto.

apply subcntxt_splits   with (ll1:=[]) (ll2:=LL2) in H;auto.
inversion H. 
apply notqext_nottyped with (a:=Fun x) (T:=bang (arrow A1 B1)) in H29;auto.
inversion H29. subst. contradict H31. apply in_eq.

apply subcntxt_splits   with (ll1:=[]) (ll2:=[]) in H;auto.
inversion H.
apply notqext_nottyped with (a:=Fun x) (T:=bang (arrow A1 B1)) in H29;auto.
inversion H29. subst. contradict H31. auto.  apply split_identr in H14. subst.
apply init. auto.

destruct H12. subst.
inversion H12. clear H12. subst. 
assert(h21:=H21'). apply BOX_LL in H21';auto.
inversion H21'. subst.
apply split_identr in H14. subst. split. auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H12. apply bArrow;auto. auto.
apply split_identr in H14. rewrite <- H14.  auto. auto. 


destruct H12. subst. assert(h21:=H21'). apply UNBOX_LL in H21';auto.
inversion H21'. apply split_identr in H14. subst. split. auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H12. apply bArrow;auto. auto.
apply split_identr in H14. rewrite <- H14.  auto. auto.

destruct H12. subst. assert(h21:=H21'). apply REV_LL in H21';auto.
inversion H21'. apply split_identr in H14.  subst. split. auto. 
exists (i0). exists x2. exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H12. apply bArrow;auto. auto.
apply split_identr in H14. rewrite <- H14.  auto. auto.

inversion H12. inversion H13. inversion H15.
subst. assert(h21:=H21'). apply app_typed in H21'.
destruct H21'. inversion H22.
inversion H25. inversion H28.
inversion H29. inversion H31.
inversion H36. inversion H39.
inversion H47. subst. apply split_ident in  H42;auto.
subst. inversion H46.  apply UNBOX_LL in H48;auto.
inversion H48. 
apply sub_Circ_inv  in H49;auto.
destruct H49. assert(h51:=H51). clear H51.
inversion H49.
inversion H51. inversion H52.
inversion H53. inversion H54.
inversion H56. inversion H58.
inversion H60. subst. apply split_identr in H14. subst.
inversion H42. split;auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H40. apply bArrow;auto. auto.
assert(h51 :=H51 ). clear H51. inversion H49. 
inversion H51. inversion H52.
inversion H53. inversion H55.
inversion H57. apply split_identr in H14. subst.  inversion H42.
 split;auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. omega. split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H40. apply bArrow;auto. auto.
subst. simpl in H. auto. auto.
apply split_identr in H14. apply split_identr in H42. subst.
auto. auto. auto.
apply split_identr in H14. subst.
apply subcntxt_splits   with (ll1:=LL1) (ll2:=LL2) in H;auto.
inversion H. auto. auto.

assert(h24:=H24). clear H24. inversion H22.
inversion H24. inversion H25.
inversion H29. inversion H31.
inversion H43. subst. apply split_ident in  H38;auto.
subst. inversion H42.  apply UNBOX_LL in H44;auto.
inversion H44. 
apply sub_Circ_inv  in H45;auto.
destruct H45. inversion H45.
inversion H48. inversion H49.
inversion H50. inversion H51.
inversion H53. inversion H55.
inversion H57. subst. apply split_identr in H14. subst.
inversion H38. split;auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. omega.
split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H33. apply bArrow;auto.
auto.
 inversion H45. 
inversion H48. inversion H49.
inversion H50. inversion H52.
inversion H54.
apply split_identr in H14. subst.  inversion H38. split;auto. 
exists (i0). exists x2.  exists (arrow A1 B1).
split. inversion H5. revert H33. 
clear .  intro. omega.  split. apply sub_trans with (B:=x1); auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H37.
inversion H37. inversion H33. apply bArrow;auto.
subst. simpl in H. auto.
apply split_identr in H14. subst.
apply split_identr in H38. subst. auto. auto. auto.
apply split_identr in H14. subst.
apply subcntxt_splits   with (ll1:=LL1) (ll2:=LL2) in H;auto.
inversion H. auto.  auto.      
apply split_identr in H14. subst. auto. auto. auto.
apply SubAreVal in H16.
inversion H16. auto. 
apply SubAreVal in H37.
inversion H37. inversion H12. auto. 

subst. inversion H10.  inversion H21. 
auto. apply split_identr in H14. subst. auto. auto.
apply split_identr in H14. subst. auto. auto.
apply split_identr in H14. subst. auto. auto.

subst. apply SubAreVal in H24.
inversion H24. inversion H16. inversion H25.

apply subcntxt_splits with (ll1:=LL1) (ll2:=LL2) in H;auto. inversion H. auto.
auto.
inversion H0.
inversion H3. inversion H4. inversion H6.
inversion H8. inversion H16.
subst. apply split_ident in H11. subst.
inversion H15. apply BOX_LL in H17;auto.
inversion H17. 
inversion H20. 
inversion H21. inversion H23.
apply Subtyping_bang_inv in H29.
inversion H29. inversion H32. subst.
inversion H34. subst. 
assert(H18':=H18).
apply sub_bangarrow_inv in H18;auto. 
inversion H18. inversion H9.
subst. assert(h18:=H18'). inversion H18'. inversion H12.
subst. inversion H37;subst; inversion H33.
subst. inversion H27.  subst.
inversion H11.  split;auto.
exists (i1+1). exists x1.  exists (arrow A1 B1).
split. inversion H4. revert H5. 
clear .  intro. omega.  split. auto. 
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H22. apply bArrow;auto.
subst. inversion H27. subst.
inversion H11. split;auto.
exists (i1+1). exists x1. exists (arrow (bang T1) B1).
split. inversion H4. revert H5. 
clear .  intro. omega. split.  auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H22. apply bArrow;auto.

subst. inversion H27. subst.
inversion H11. split;auto.
exists (i1+1). exists x1. exists (arrow A1 B1).
split. omega. split. auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H22. apply bArrow;auto.

apply subcntxt_splits   with (ll1:=[]) (ll2:=LL2) in H;auto.
inversion H.
apply notqext_nottyped with (a:=Fun x) (T:=bang (arrow A1 B1)) in H26;auto.
inversion H26. subst. contradict H28. apply in_eq.

apply subcntxt_splits   with (ll1:=[]) (ll2:=[]) in H;auto.
inversion H.
apply notqext_nottyped with (a:=Fun x) (T:=bang (arrow A1 B1)) in H26;auto.
inversion H26. subst. contradict H28. auto. subst. auto.

destruct H9. inversion H9 as [h9].
clear H9. assert(H9:=h9). subst. assert(h18:=H18'). apply BOX_LL in H18';auto.
inversion H18'. subst. inversion H11. split. auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. omega. split. auto. 
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H19. apply bArrow;auto.
apply split_identr in H11. subst. auto.  auto.

destruct H9. subst. assert(h18:=H18'). apply UNBOX_LL in H18';auto.
inversion H18'. subst. inversion H11. split. auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. omega. split. auto. 
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H12. apply bArrow;auto.
apply split_identr in H11. subst. auto.  auto.

destruct H9. subst. assert(h18:=H18'). apply REV_LL in H18';auto.
inversion H18'. subst. inversion H11. split. auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. omega. split. auto. 
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H12. apply bArrow;auto.
apply split_identr in H11. subst. auto.  auto.

inversion H9. inversion H10. inversion H12.
subst. assert(h18:=H18'). apply app_typed in H18'.
destruct H18'. inversion H19.
inversion H22. inversion H25.
inversion H26. inversion H28.
inversion H33. inversion H36.
inversion H44. subst. apply split_ident in  H39;auto.
subst. inversion H43.  apply UNBOX_LL in H45;auto.
inversion H45. 
apply sub_Circ_inv  in H46;auto.
destruct H46. assert(h48:=H48). clear H48.
inversion H46.
inversion H48. inversion H49.
inversion H50. inversion H51.
inversion H53. inversion H55.
inversion H57. subst. inversion H39.
subst. inversion H11. split;auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. inversion H4. revert H38. 
clear .  intro. omega. split. auto. 
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H38.  apply bArrow;auto.
inversion H46.  inversion H49.
inversion H50. inversion H51.
inversion H53. inversion H55.  subst. inversion H39.
subst. inversion H11. split;auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. inversion H4. revert H38. 
clear .  intro. omega.
 split. auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H38. apply bArrow;auto.
subst. simpl in H. auto. subst.
apply split_identr in H39. apply split_identr in H11. subst.
auto. auto.  auto. 
apply subcntxt_splits   with (ll1:=LL1) (ll2:=LL2) in H;auto.
inversion H. auto. apply split_identr in H11. subst. auto. auto.


inversion H19.
inversion H22. inversion H25.
inversion H27. inversion H30.
inversion H41. subst. apply split_ident in  H36;auto.
subst. inversion H40.  apply UNBOX_LL in H42;auto.
inversion H42. 
apply sub_Circ_inv  in H43;auto.
destruct H43. inversion H43.
inversion H46.
inversion H47. inversion H48.
inversion H49. inversion H51.
inversion H53. inversion H55.  subst.
inversion H36. subst. inversion H11. subst. split;auto. 
exists (i0). exists x1.  exists (arrow A1 B1).
split. auto. split.  auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H33. apply bArrow;auto.
inversion H43.
 inversion H46.
inversion H47. inversion H48.
inversion H50. inversion H52. inversion H54.
subst. inversion H36. subst. inversion H11. subst. split;auto. 
exists (i0). exists x1. exists (arrow A1 B1).
split. auto. split. auto.
split. subst. auto. 
apply BangSub2;auto. apply SubAreVal in H34.
inversion H34. inversion H33. apply bArrow;auto.
subst. simpl in H. auto. apply split_identr in H36. apply split_identr in H11. subst.
auto. auto. auto.
apply subcntxt_splits   with (ll1:=LL1) (ll2:=LL2) in H;auto.
inversion H. auto.  apply split_identr in H11. subst. auto.                 
auto.
apply split_identr in H11. subst. auto. auto. auto.
apply SubAreVal in H13.
inversion H13. auto. 

apply SubAreVal in H14.
inversion H14.  auto. apply split_identr in H11. subst. auto. auto. 
subst. inversion H7. inversion H14.
apply subcntxt_splits   with (ll1:=LL1) (ll2:=LL2) in H;auto.
inversion H. auto. auto.
Qed.
