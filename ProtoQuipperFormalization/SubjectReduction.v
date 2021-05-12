(****************************************************************
   File: SubjectReduction.v
   Authors: Mohamend Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Subject Reduction (Type Soundness) for Proto Quipper
   ***************************************************************)
Require Import ProgLemmas3.
Require Import ProgLemmas2.
Require Import ProgLemmas1.
Require Import PQAdequacy.
Require Import ProtoQuipperProg.
Require Import LSL.
Require Import ProtoQuipperSyntax.
Require Import ProtoQuipperTypes.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Definition seq_ := ProgLemmas3.seq_.
Definition prog := ProgLemmas3.prog.
Definition unique_in_split := ProgLemmas3.unique_in_split.

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


Hypothesis  FQ_LET: forall i E b, abstr (fun x => lambda (E x)) ->  
         (forall x, proper x ->  abstr (E x)) ->
  FQ (Let E b) = set_union eq_dec (FQ (E (Var i) (Var i))) (FQ b).

Hypothesis  FQU_LET: forall i E b, abstr (fun x => lambda (E x)) ->  
         (forall x, proper x ->  abstr (E x)) ->
  FQU (Let E b) =  (FQU (E (Var i) (Var i))) ++  (FQU b).


Hint Resolve LSL.init LSL.splitr1 LSL.splitr2
              LSL.ss_init LSL.ss_general : hybrid.
Hint Resolve starq trueq falseq boxq unboxq revq lambdaq apq prodq letq
     sletq ifq Circq axc1 axc2 starl stari truel truei falsel falsei
     box unbox rev lambda1l lambda1i lambda2l lambda2i tap
     ttensorl ttensori tletl tleti tsletl tsleti tif tCricl
     tCrici subcnxt_i subcnxt_q subcnxt_iig subcnxt_llg subcnxt_lig: hybrid.

Theorem subject_reduction: forall i,
   forall IL  C C' a a',
       (forall V, In V (get_boxed a)  -> 
            ~ (exists i, V = (Var i) \/ V = (CON (Qvar i))))-> 
      NoDup (FQUC a') -> NoDup(FQU a')->  
     (forall t, In t IL -> (exists i, t = is_qexp (Var i) \/ t = is_qexp (CON (Qvar i)) \/
     exists T, t = typeof (Var i) T)) ->
      seq_ i IL [] (atom_ (reduct C a C' a')) ->
      exists j, forall LL1 LL2 A, Subtypecontext IL LL1 IL LL1 ->
                  Subtypecontext IL LL2 IL LL2 ->
                  common_ll a a' LL1 LL2 ->
                  (forall q, In q (FQ a') -> In (typeof q qubit) LL2)->
                  seq_ j IL LL1  (atom_ (typeof a A)) ->
                  exists k, seq_ k IL LL2 (atom_ (typeof a' A)).
Proof.
intros i. induction i.
+
  intros IL C C' a a' hnot1 hnot2 hnot3  hnot5 H.
  inversion H. 
  - clear - H0. omega. 
  - apply hnot5 in H3. inversion H3.
  inversion  H3. destruct H4. 
   * inversion H4.
   * destruct H4. 
     {inversion H4. } 
     {inversion H4.  inversion H6. }
   
+ intros IL C C' a a' hnot1 hnot2 hnot3  hnot5 H. assert(hnot4:=LL_FQ).
  inversion H;cycle 1. 
  - apply hnot5 in H3. inversion H3.
  inversion  H3. destruct H4.
   * inversion H4.
   * destruct H4. 
     {inversion H4. }
     {inversion H4.  inversion H6. }
  - inversion H2; subst.
    * inversion H3. apply split_nil in H5. 
      inversion H5. subst. 
      assert(i0=i);[clear - H0;  omega|..].
      subst. apply IHi  in H10 ;auto.
      ++ inversion H10.
         exists (x+1+1). intros LL1 LL2 A H4 H4' H4'' H4'''  H7.
         apply sub_slet_inv in H7. 
         -- destruct H7.
          ** inversion H7. inversion H8.
          inversion H9. inversion H16.
          destruct H18. 
           +++ inversion H18. inversion H26. subst.
            apply split_ident in H21;auto. subst.
            inversion H25. 
            apply seq_mono_cor with (k:= x) in H28;[..|clear - H12 H22;  omega].
            assert(H21':=H21).
            apply split_common_l with (ll2:=LL2) (a:=(Slet b0 a0))
            (a':=(Slet b0 a'0)) in H21;auto. 
             { inversion H21. inversion H29.
              apply H1 with (LL2:=x2)  (A:=bang one) in H28;auto.
               { inversion H28. exists (x3+x+1+1+1).
                apply s_bc with (iL:=[])
               (lL:=[Conj (atom_ (typeof b0 A)) (atom_ (typeof a'0 (bang one)))]);auto.
                 { apply tsleti. apply SubAreVal in H17. inversion H17. auto. }
                 { apply ss_init. }
                 { apply ss_general with (lL2:=LL2) (lL3:=[]).
                   { apply split_ref. }
                   { apply m_and with (LL1:=LL1) (LL2:=x2);auto.
                     { apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=A) in H27;auto. 
                       { apply seq_mono_cor with (j:= i0+1+1). clear - H12 H22;  omega. auto. }
                       { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                         inversion H4;auto. } }
                     { apply seq_mono_cor with (j:= x3). 
                       clear - H12 H22;  omega. auto. }}
                   { apply ss_init. }}}
               { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                 inversion H4;auto. }
               { apply subcntxt_splits with (ll1:=LL1) (ll2:=x2) in H4';auto.
                 inversion H4';auto. }
               { apply sub_a_comm with (a1:=a0) in H31.
                 { apply sub_a'_comml with (a'1:=a'0) in H31; auto.
                   { intros. assert(h4'':=H4'').
                     apply in_common_r with (q:=q) in H4''. 
                     { inversion H4''. simpl in H33.
                       apply set_union_elim in H33.
                       destruct H33;auto.  
                       apply unique_in_split with (a:=(typeof (CON (Qvar q)) 
                       qubit)) in H30;auto. 
                       destruct H30.
                        { inversion H30. apply  hnot4 with (q:=q) in H27;auto. 
                          { rewrite <- H27 in H35. contradict H35. auto. }
                          { inversion H30. intros.
                            apply ProgLemmas3.in_split_l with   
                            (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                            apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto. }
                          { intros. assert(h21:=H21').
                            apply ProgLemmas3.in_split_l with 
                            (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                            assert(h21':=h21). 
                            apply count_split with (eq_dec:=ProgLemmas1.eq_dec)
                            (a:=(typeof (CON (Qvar q0)) T)) in h21.
                            assert(t4'':=h4''). apply in_common_l_T with 
                            (q:=q0) (T:=T) in t4'';auto. subst.
                            apply in_common_l with (q:=q0) in h4'';auto. 
                            inversion h4''. subst. rewrite count_occ_In 
                            with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                            clear - H34 H37 H20 h21. omega. }
                          { inversion H29. apply subcntxt_splits with (ll1:= LL1)
                           (ll2:=x2) in H4';auto. inversion H4';auto. }}
                        { inversion H30. contradict H36. auto. }}
                     { apply ProgLemmas3.in_split_r with 
                       (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto. }}
                   { intros. simpl in H32. rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. auto. }} 
                 { intros. apply hnot4 with (q:=q) in H28;auto.
                   { rewrite H28. auto. }
                   { intros. apply ProgLemmas3.in_split_r with
                    (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto. }
                   { intros. assert(h21:=H21').
                     apply ProgLemmas3.in_split_r with 
                     (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                      assert(h21':=h21).
                      apply count_split with (eq_dec:=ProgLemmas1.eq_dec) 
                     (a:=(typeof (CON (Qvar q0)) T)) in h21.
                     assert(t4'':=H4''). apply in_common_l_T with (q:=q0)
                     (T:=T) in t4'';auto. subst. Optimize Proof.
                     apply in_common_l with (q:=q0) in H4'';auto.
                     inversion H4''. subst. rewrite count_occ_In with
                    (eq_dec:=ProgLemmas1.eq_dec) in H33. 
                    clear - H33  H20 h21. omega. } Optimize Proof.
                   { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto. }}
                 { intros. simpl in H32. 
                   rewrite set_union_iff in H32.
                   apply not_or in H32. inversion H32. auto. }} 
               { intros. simpl in H4'''. specialize H4''' with q.
                 rewrite  set_union_iff in H4'''.   
                 assert(In (typeof q qubit) LL2); auto. 
                 apply unique_in_split with (a:=(typeof q qubit)) in H30.
                 { destruct H30.   
                   { inversion H30. auto. }
                   { inversion H30. assert(h32:=H32).
                     apply fq_all_qvar in h32. inversion h32. 
                     subst. apply hnot4 with (q:=x3)  in H27;auto.
                     { rewrite <- H27 in H34. simpl in hnot3. 
                       rewrite NoDup_count_occ'  with 
                       (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                       specialize hnot3 with (CON (Qvar x3)). 
                        rewrite count_app with (l1:=FQU b0) (l2:=FQU a'0) 
                        in hnot3;auto.
                        assert(In (CON (Qvar x3)) (FQU b0 ++ FQU a'0)). 
                        rewrite in_app_iff, FQU_FQ. left. auto.
                        apply hnot3 in H19.
                        rewrite <- FQU_FQ, count_occ_In with 
                        (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H34.
                        clear - H34 H32 H19. omega. }
                     { intros. apply ProgLemmas3.in_split_l with 
                       (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                       apply in_common_l_T with (q:=q) (T:=T) in H4'';auto. }
                     { intros. assert(h21:=H21'). 
                       apply ProgLemmas3.in_split_l with 
                       (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                        assert(h21':=h21). apply count_split with 
                        (eq_dec:=ProgLemmas1.eq_dec) 
                        (a:=(typeof (CON (Qvar q)) T)) in h21. assert(t4'':=H4''). 
                        apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                        subst. apply in_common_l with (q:=q) in H4'';auto. 
                        inversion H4''. subst. rewrite count_occ_In 
                        with (eq_dec:=ProgLemmas1.eq_dec) in H19. 
                        clear - H22 h21 H19. omega. }
                     { inversion H29. apply subcntxt_splits with 
                       (ll1:= LL1) (ll2:=x2) in H4';auto.
                       inversion H4';auto. }}}
                 { apply fq_all_qvar in H32. inversion H32. subst.
                   apply in_common_r  with (q:=x3) in H4'';auto. 
                   inversion H4''. auto. }}}
             { intros. apply hnot4 with (q:=q) in H27;auto.   
               { rewrite <- H27 in H29. simpl. repeat rewrite set_union_iff.
                 split;left;auto. }
               { intros. apply ProgLemmas3.in_split_l with 
                 (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                 apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto. }
               { intros. assert(h21:=H21').
                 apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                 assert(h21':=h21). apply count_split with 
                 (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                 assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                 subst. apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                 subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
                 clear - h21 H30 H20. omega. }
               { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                 inversion H4;auto. }}
           +++ inversion H18. inversion H26. subst.
               apply split_ident in H21;auto. subst.
               inversion H25. apply seq_mono_cor with (k:= x) in H28;
               [..| clear - H12 H22; omega]. assert(H21':=H21).
               apply split_common_l with (ll2:=LL2) (a:=(Slet b0 a0))
               (a':=(Slet b0 a'0)) in H21;auto. 
               { inversion H21. inversion H29.
                 apply H1 with (LL2:=x2) (A:=one) in H28.
                 { inversion H28. exists (x3+x+1+1+1).
                   apply s_bc with (iL:=[])
                   (lL:=[Conj (atom_ (typeof b0 A)) (atom_ (typeof a'0 (one)))]);auto.
                   { apply tsletl. apply SubAreVal in H17. inversion H17. auto. }
                   { apply ss_init. }
                   { apply ss_general with (lL2:=LL2) (lL3:=[]).
                     { apply split_ref. }
                     { apply m_and with (LL2:=x2) (LL1:=LL1) ;auto. 
                       { apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1)
                        (B:=A) in H27;auto.
                        { apply seq_mono_cor with (j:= i0+1+1).
                          clear - H12 H22; omega.  auto. }
                        { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                          inversion H4;auto. } }
                       { apply seq_mono_cor with (j:= x3).  clear - H12 H22; omega. auto. } }
                       { apply ss_init. } } }
                 { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                   inversion H4;auto. }
                 { apply subcntxt_splits with (ll1:=LL1) (ll2:=x2) in H4';auto.
                   inversion H4';auto. }
                 { apply sub_a_comm with (a1:=a0) in H31.
                   { apply sub_a'_comml with (a'1:=a'0) in H31; auto.
                     { intros. assert(h4'':=H4''). apply in_common_r with (q:=q) in H4''. 
                       { inversion H4''. simpl in H33. apply set_union_elim in H33.
                         destruct H33;auto. apply unique_in_split with 
                         (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                         destruct H30.   
                         { inversion H30. apply  hnot4 with (q:=q) in H27;auto. 
                           { rewrite <- H27 in H35. contradict H35. auto. } 
                           { intros. apply ProgLemmas3.in_split_l with
                             (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                             apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto. }
                           { intros. assert(h21:=H21'). 
                             apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                             assert(h21':=h21).
                             apply count_split with (eq_dec:=ProgLemmas1.eq_dec) 
                             (a:=(typeof (CON (Qvar q0)) T)) in h21.
                             assert(t4'':=h4''). 
                             apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                             subst. apply in_common_l with (q:=q0) in h4'';auto. 
                             inversion h4''. subst. 
                             rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                             clear - h21 H20 H37; omega. } 
                           { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                             inversion H4;auto. } }
                         { inversion H30. contradict H36. auto. } } 
                       { apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto. } }
                     { intros. simpl in H32. rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. } } 
                   { intros. apply hnot4 with (q:=q) in H28;auto.
                     { rewrite H28. auto. }
                     { intros. apply ProgLemmas3.in_split_r with 
                       (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                       apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto. }
                     { intros. assert(h21:=H21').
                       apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T))
                       in H21';auto. assert(h21':=h21). apply count_split with 
                       (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                       assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                       subst. apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                       subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H33.
                       clear -h21 H20 H33; omega. }
                     { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                       inversion H4;auto. } }
                   { intros. simpl in H32. rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. auto. } } 
                 { intros. simpl in H4'''. specialize H4''' with q. 
                   rewrite  set_union_iff in H4'''. 
                   assert(In (typeof q qubit) LL2); auto. 
                   apply unique_in_split with (a:=(typeof q qubit)) in H30.
                   { destruct H30.
                     { inversion H30. auto. }
                     { inversion H30. assert(h32:=H32). apply fq_all_qvar in h32.
                       inversion h32. subst. apply hnot4 with (q:=x3) in H27;auto.
                       { rewrite <- H27 in H34. simpl in hnot3.  
                         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) 
                         in hnot3. specialize hnot3 with (CON (Qvar x3)). 
                         rewrite count_app with (l1:=FQU b0) (l2:=FQU a'0) in hnot3;auto.
                        assert(In (CON (Qvar x3)) (FQU b0 ++ FQU a'0));
                        [rewrite in_app_iff, FQU_FQ; left; auto|..].
                        apply hnot3 in H19.
                        rewrite <- FQU_FQ, count_occ_In with 
                        (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H34. omega. }
                     { intros. apply ProgLemmas3.in_split_l with 
                       (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                       apply in_common_l_T with (q:=q) (T:=T) in H4'';auto. }
                     { intros. assert(h21:=H21'). apply ProgLemmas3.in_split_l 
                       with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                       assert(h21':=h21). apply count_split with 
                       (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q)) T)) in h21.
                       assert(t4'':=H4''). apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                      subst. apply in_common_l with (q:=q) in H4'';auto. inversion H4''.
                      subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H19.
                      omega. }
                    { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                      inversion H4;auto. } } }
                   { apply fq_all_qvar in H32. inversion H32. subst.
                     apply in_common_r  with (q:=x3) in H4'';auto. inversion H4''. auto. } } }
               { Optimize Proof. intros. Optimize Proof.
                 apply hnot4 with (q:=q) in H27;auto.
                 { rewrite <- H27 in H29. simpl. repeat rewrite set_union_iff.
                   split;left;auto. }
                 { intros. apply ProgLemmas3.in_split_l with 
                  (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto. }
                 { intros. assert(h21:=H21').
                   apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T))
                   in H21';auto. assert(h21':=h21).
                   apply count_split with 
                   (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                   assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                   subst. apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                   subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
                   clear -h21 H30 H20;omega. }
                 { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                   inversion H4;auto. } } 
          ** inversion H7. inversion H8. inversion H12. inversion H17.
             +++ inversion H18. inversion H26. subst. apply split_ident in H21;auto. subst.
                 inversion H25. apply seq_mono_cor with (k:= x) in H28
                 ;[..|clear -H22 H12 H9; omega]. assert(H21':=H21).
                 apply split_common_l with (ll2:=LL2) (a:=(Slet b0 a0))
                 (a':=(Slet b0 a'0)) in H21;auto. 
                 { inversion H21. inversion H29. 
                   apply H1 with (A:=bang one) (LL2:=x1) in H28.
                   { inversion H28. exists (x2+x+1+1+1). apply s_bc with (iL:=[])
                     (lL:=[Conj (atom_ (typeof b0 A)) (atom_ (typeof a'0 (bang one)))]);auto.
                     { apply tsleti. auto. } 
                     { apply ss_init. }
                     { apply ss_general with (lL2:=LL2) (lL3:=[]).
                       { apply split_ref. }
                       { apply m_and with (LL1:=LL1) (LL2:=x1) ;auto.
                         { apply seq_mono_cor with (j:= i0) ;try omega. auto. }
                         { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                           inversion H4;auto. 
                           apply seq_mono_cor with (j:= x2) ;try omega. auto. } }
                       { apply ss_init. } } }
                   { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto. }
                   { apply subcntxt_splits with (ll1:=LL1) (ll2:=x1) in H4';auto.
                     inversion H4';auto. }
                   { apply sub_a_comm with (a1:=a0) in H31.
                     { apply sub_a'_comml with (a'1:=a'0) in H31;auto.
                       { intros. assert(h4'':=H4''). 
                         apply in_common_r with (q:=q) in H4''. 
                         { inversion H4''. simpl in H33. apply set_union_elim in H33.
                           destruct H33;auto. 
                           apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                           destruct H30.
                           { inversion H30. apply  hnot4 with (q:=q) in H27;auto. 
                             { rewrite <- H27 in H35. contradict H35. auto. }
                             { intros. apply ProgLemmas3.in_split_l with 
                              (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                              apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto. }
                             { intros. assert(h21:=H21').
                               apply ProgLemmas3.in_split_l with 
                               (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                               assert(h21':=h21).
                               apply count_split with 
                               (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                               assert(t4'':=h4''). 
                               apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                               subst. apply in_common_l with (q:=q0) in h4'';auto.
                               inversion h4''. subst. 
                               rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                               omega. }
                             { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                               inversion H4;auto. } }
                           { inversion H30. contradict H36. auto. } } 
                         { apply ProgLemmas3.in_split_r with 
                           (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto. } }
                       { intros. simpl in H32. rewrite set_union_iff in H32.
                         apply not_or in H32. inversion H32. auto. } }
                     { intros. apply hnot4 with (q:=q) in H28;auto.
                       { rewrite H28. auto. }
                       { intros. apply ProgLemmas3.in_split_r with
                         (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                         apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto. }
                       { intros. assert(h21:=H21').
                         apply ProgLemmas3.in_split_r with 
                         (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                         assert(h21':=h21). apply count_split with 
                         (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                         assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                         subst. apply in_common_l with (q:=q0) in H4'';auto.
                         inversion H4''. subst.
                         rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H33.
                          omega. }
                       { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                         inversion H4;auto. } }
                     { intros. simpl in H32. rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. } } 
                   { intros. simpl in H4'''. specialize H4''' with q.
                     rewrite  set_union_iff in H4'''.   
                     assert(In (typeof q qubit) LL2); auto. 
                     apply unique_in_split with (a:=(typeof q qubit)) in H30.
                     { destruct H30.
                       { inversion H30. auto. }
                       { inversion H30. assert(h32:=H32). apply fq_all_qvar in h32.
                         inversion h32. subst. apply hnot4 with (q:=x2) in H27;auto.
                         { rewrite <- H27 in H34. simpl in hnot3. 
                           rewrite NoDup_count_occ'  with 
                           (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                           specialize hnot3 with (CON (Qvar x2)). 
                           rewrite count_app with (l1:=FQU b0) (l2:=FQU a'0) in hnot3;auto.
                           assert(In (CON (Qvar x2))  (FQU b0 ++ FQU a'0)). 
                           rewrite in_app_iff, FQU_FQ. left. auto.
                           apply hnot3 in H19. 
                           rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H34.
                           omega. }
                         { intros. apply ProgLemmas3.in_split_l with 
                           (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                           apply in_common_l_T with (q:=q) (T:=T) in H4'';auto. }
                         { intros. assert(h21:=H21').
                           apply ProgLemmas3.in_split_l with 
                           (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                           assert(h21':=h21). apply count_split with 
                           (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q)) T)) in h21.
                           assert(t4'':=H4''). apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                           subst. apply in_common_l with (q:=q) in H4'';auto.
                           inversion H4''. subst. 
                           rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H19.
                           omega. }
                         { apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                           inversion H4;auto. } } }
                     { apply fq_all_qvar in H32. inversion H32. subst.
                       apply in_common_r  with (q:=x2) in H4'';auto. inversion H4''. auto. } } }
               { intros. apply hnot4 with (q:=q) in H27;auto.
                 rewrite <- H27 in H29. simpl. repeat rewrite set_union_iff.
                 split;left;auto.
                 intros.
                 apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                 apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                 intros. assert(h21:=H21').
                 apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                 assert(h21':=h21).
                 apply count_split with 
                 (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                 assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                 subst.
                 apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                 subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
                 omega. apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                 inversion H4;auto. } 
             +++   inversion H18. inversion H26. subst. apply split_ident in H21;auto.
                   subst. inversion H25.  assert(H21':=H21).
                   apply split_common_l with (ll2:=LL2) (a:=(Slet b0 a0))
                   (a':=(Slet b0 a'0)) in H21;auto. 
                   { inversion H21. inversion H29.
                     apply seq_mono_cor with (k:= x)  in H28;try omega.
                     apply H1 with (A:=one) (LL2:=x1) in H28.
                     inversion H28. exists (x2+x+1+1+1).
                     apply s_bc with (iL:=[])
                     (lL:=[Conj (atom_ (typeof b0 A)) (atom_ (typeof a'0 ( one)))]);auto.
                     apply tsletl. auto. 
                     apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                     apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x1);auto.
                     apply seq_mono_cor with (j:= i0) ;try omega. auto.
                     apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto.
                     apply seq_mono_cor with (j:= x2) ;try omega. auto.
                     apply ss_init.
                     apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto.
                     apply subcntxt_splits with (ll1:=LL1) (ll2:=x1) in H4';auto.
                     inversion H4';auto.
                     apply sub_a_comm with (a1:=a0) in H31.
                     apply sub_a'_comml with (a'1:=a'0) in H31. auto.
                     intros.
                     assert(h4'':=H4'').
                     apply in_common_r with (q:=q) in H4''. inversion H4''.
                     simpl in H33. apply set_union_elim in H33.
                     destruct H33;auto. 
                     apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                     destruct H30.   inversion H30. 
                     apply  hnot4 with (q:=q) in H27;auto. 
                     rewrite <- H27 in H35. contradict H35. auto.
                     intros.
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto.
                     intros.
                     assert(h21:=H21').
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     assert(h21':=h21).
                     apply count_split with 
                     (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                     assert(t4'':=h4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                     subst.
                     apply in_common_l with (q:=q0) in h4'';auto. inversion h4''.
                     subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                     omega.
                     apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto.
                     inversion H30.
                     contradict H36. auto. 
                     apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                     intros. simpl in H32. rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. auto. 
                     intros. apply hnot4 with (q:=q) in H28;auto.
                     rewrite H28. auto.
                     intros.
                     apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                     intros.
                     assert(h21:=H21').
                     apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     assert(h21':=h21).
                     apply count_split with 
                     (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                     assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                     subst.
                     apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                     subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H33.
                     omega.
                     apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto.
                     intros. simpl in H32. rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. auto. 
                     intros.
                     simpl in H4'''. specialize H4''' with q.
                     rewrite  set_union_iff in H4'''. 
                     assert(In (typeof q qubit) LL2); auto. 
                     apply unique_in_split with (a:=(typeof q qubit)) in H30.
                     destruct H30.   inversion H30. auto.
                     inversion H30. assert(h32:=H32). apply fq_all_qvar in h32. inversion h32. subst.
                     apply hnot4 with (q:=x2) in H27;auto.
                     rewrite <- H27 in H34. simpl in hnot3. 
                     rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                     specialize hnot3 with (CON (Qvar x2)). 
                     rewrite count_app with (l1:=FQU b0) (l2:=FQU a'0) in hnot3;auto.
                     assert(In (CON (Qvar x2)) (FQU b0 ++ FQU a'0)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H19.
                     rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H34.
                     omega.
                     intros.
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                     apply in_common_l_T with (q:=q) (T:=T) in H4'';auto.
                     intros.
                     assert(h21:=H21').
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                     assert(h21':=h21).
                     apply count_split with 
                     (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q)) T)) in h21.
                     assert(t4'':=H4''). apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                     subst.
                     apply in_common_l with (q:=q) in H4'';auto. inversion H4''.
                     subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H19.
                     omega.
                     apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto.
                     apply fq_all_qvar in H32. inversion H32. subst.
                     apply in_common_r  with (q:=x2) in H4'';auto. inversion H4''. auto. }
                   { intros.
                     apply hnot4 with (q:=q) in H27;auto.
                     rewrite <- H27 in H29. simpl. repeat rewrite set_union_iff.
                     split;left;auto.
                     intros.
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                     intros.
                     assert(h21:=H21').
                     apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                     assert(h21':=h21).
                     apply count_split with 
                     (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                     assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                     subst.
                     apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                     subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H30.
                     omega.
                     apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                     inversion H4;auto. } 
         -- auto.
         -- contradict H7. apply hnot5 in H7. inversion H7.
            destruct H8. inversion H8. destruct H8. inversion H8.
            inversion H8. inversion H9. 
      ++ simpl in hnot1. intros.  specialize hnot1 with V.
         rewrite in_app_iff in hnot1. apply hnot1. right. auto.
      ++ simpl in hnot2.
         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). 
         intros. rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
         specialize hnot2 with x. 
         rewrite count_app with (l1:=FQUC b0) (l2:=FQUC a'0) in hnot2;auto.
         assert(In x (FQUC b0 ++ FQUC a'0)). rewrite in_app_iff. right. auto.
         apply hnot2 in H4.  
         rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega.
      ++ simpl in hnot3. rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec).
         intros. rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
         specialize hnot3 with x.
         rewrite count_app with (l1:=FQU b0) (l2:=FQU a'0) in hnot3;auto.
         assert(In x (FQU b0 ++ FQU a'0)). rewrite in_app_iff. right. auto.
         apply hnot3 in H4.
         rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega. 
    * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
      apply sub_slet_inv in H4.
      ++ destruct H4.
         -- inversion H4. inversion H5.
            inversion H7. inversion H9.
            destruct H11.
            ** inversion H11.
               inversion H20. subst. apply split_ident in H15;auto. subst.
               inversion H19. exists (i0+1+1). apply STAR_LL2 in  H22. subst.
               +++ apply split_ident in H15;auto. subst. apply common_a_a in H1''.
                   { subst.
                     apply subtypecontext_subtyping with (IL':=IL) (LL':=LL2) (B:=A) in H21;auto. 
                     apply seq_mono_cor with (j:= i1+1+1) ;try omega. auto. } 
                   { simpl. intros.  split;auto. }
               +++ contradict H12. apply hnot5 in H12.
                   inversion H12. destruct H23. 
                   { inversion H23. }
                   { inversion H23. inversion H24. inversion H24. inversion H25. } 
               +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                   inversion H1;auto.
            ** inversion H11. inversion H20. subst. apply split_ident in H15;auto. subst.
               inversion H19. exists (i0+1+1). apply ProgLemmas1.STAR_LL in   H22.
               +++ subst. apply split_ident in H15;auto.
                   subst. apply common_a_a in H1''.
                   { subst.
                     apply subtypecontext_subtyping with (IL':=IL) (LL':=LL2) (B:=A) in H21;auto.  
                     apply seq_mono_cor with (j:= i1+1+1) ;try omega. auto. }
                   {  simpl. intros. split;auto. } 
               +++ contradict H12. apply hnot5 in H12.
                   inversion H12. destruct H23. 
                   { inversion H23. }
                   { inversion H23. inversion H24. inversion H24. inversion H25. }
               +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                      inversion H1;auto.
         -- inversion H4. inversion H5. inversion H8. 
            destruct H10. 
            ** inversion H10. inversion H19. subst. apply split_ident in H14;auto. subst.
               inversion H18. exists (i0+1+1). apply STAR_LL2 in  H21.
               +++ subst. apply split_ident in H14;auto. 
                   subst. apply common_a_a in H1''. 
                   { subst. apply seq_mono_cor with (j:= i1) ;try omega. auto. }
                   {  simpl. intros. split;auto. }  
               +++ contradict H12. apply hnot5 in H12.
                   inversion H12. destruct H22.
                   { inversion H22. }
                   { inversion H22. inversion H23. inversion H23. inversion H24. }
               +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                   inversion H1;auto.
            ** inversion H10. inversion H19. subst. apply split_ident in H14;auto. subst.
               inversion H18. exists (i0+1+1). apply ProgLemmas1.STAR_LL in    H21.
               +++ subst. apply split_ident in H14;auto. subst.  apply common_a_a in H1''.
                   { subst. apply seq_mono_cor with (j:= i1) ;try omega. auto. }
                   { simpl. intros. split;auto. }
               +++ contradict H12. apply hnot5 in H12.
                   inversion H12. destruct H22. 
                   { inversion H22. }
                   { inversion H22. inversion H23. inversion H23. inversion H24. }
               +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                   inversion H1;auto. 
      ++ auto.
      ++ contradict H4. apply hnot5 in H4. inversion H4.
         destruct H5. inversion H5. destruct H5. inversion H5.
         inversion H5. inversion H7. 
    * inversion H3. apply split_nil in H5. inversion H5. subst. 
      assert(i0=i);try omega. subst. apply IHi  in H10 ;auto.
      ++ inversion H10. exists (x+1+1). intros LL1 LL2 A H4 H4' H4'' H4''' H7.
         assert(H7':=H7).  apply if_a1_a2_eq in H7';auto.  
         -- apply if_typed in H7;auto. 
            ** destruct H7.
               +++ inversion H7. inversion H8.
                   inversion H9. inversion H16. inversion H18.
                   inversion H26. subst. apply split_ident in H21;auto. subst.
                   inversion H25. apply seq_mono_cor with (k:= x) in H27;try omega.
                   assert(H21':=H21). apply split_common_r with (ll2:=LL2) (a:=(If b0 a1 a2))
                   (a':=(If b' a1 a2)) in H21;auto.  
                   { inversion H21. inversion H29.
                     apply H1 with (A:=bool) (LL2:=x2)in H27.
                     inversion H27. exists (x3+x+1+1+1).
                     apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof b' bool))
                               (And (atom_ (typeof a1 A)) (atom_ (typeof a2 A)))]);auto.
                    apply tif. apply SubAreVal in H17. inversion H17.
                    auto. auto. apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x2) (LL2:=LL0);auto.
                    apply seq_mono_cor with (j:= x3) ;try omega. auto.
                    inversion H28. apply a_and;auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL0) (B:=A) in H38;auto. 
                    apply seq_mono_cor with (j:= i1+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL0) (B:=A) in H39;auto. 
                    apply seq_mono_cor with (j:= i1+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=x2) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=b0) in H31.
                    apply sub_a'_comml with (a'1:=b') in H31. auto.
                    intros.
                    assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H33. repeat rewrite set_union_iff in H33. 
                    rewrite H7' in H33. simpl in H33.
                    assert( (In (CON (Qvar q)) (FQ a2) \/
                          In (CON (Qvar q)) (FQ b') \/ In (CON (Qvar q)) (FQ a2)) <-> 
                    (In (CON (Qvar q)) (FQ a2) \/
                          In (CON (Qvar q)) (FQ b'))) as H33'. intuition.
                    rewrite H33' in H33. clear H33'.
                    destruct H33;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                    destruct H30.   inversion H30. 
                    contradict H35. auto. 
                    inversion H30. inversion H28.
                    apply  hnot4 with (q:=q) in H43;auto. 
                    rewrite <- H43 in H36. contradict H36. auto.
                    intros.
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto.
                    intros.
                    assert(h21:=H21').
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    assert(h21':=h21).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                    assert(t4'':=h4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q0) in h4'';auto. inversion h4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H44.
                    omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                    intros. simpl in H32. repeat rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. 
                     apply not_or in H34. inversion H34. auto. 
                    intros. apply hnot4 with (q:=q) in H27;auto.
                    rewrite H27. auto.
                    intros.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                    intros.
                    assert(h21:=H21').
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    assert(h21':=h21).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                    assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H33.
                    omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    intros. simpl in H32. repeat rewrite set_union_iff in H32.
                     apply not_or in H32. inversion H32. 
                     apply not_or in H34. inversion H34. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    repeat rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H30.
                    destruct H30.   
                    inversion H30. inversion H28. assert(h32:=H32).
                    apply fq_all_qvar in h32. inversion h32. subst.
                     apply hnot4 with (q:=x3) in H41;auto.
                    rewrite <- H41 in H35. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x3)). 
                    rewrite count_app with (l1:=FQU b') (l2:=FQU a1++ FQU a2) in hnot3;auto.
                    assert(In (CON (Qvar x3)) (FQU b' ++ FQU a1++ FQU a2)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H19.
                    rewrite count_app with (l:=FQU a1++ FQU a2) (l1:=FQU a1) (l2:= FQU a2) in H19;auto.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H35.
                     omega.
                    intros.
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                    apply in_common_l_T with (q:=q) (T:=T) in H4'';auto.
                    intros.
                    assert(h21:=H21').
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                    assert(h21':=h21).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q)) T)) in h21.
                    assert(t4'':=H4''). apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q) in H4'';auto. inversion H4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H19.
                    omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    inversion H30. auto.
                    apply fq_all_qvar in H32. inversion H32. subst.
                    apply in_common_r  with (q:=x3) in H4'';auto. inversion H4''. auto. }

                   { intros.
                    inversion H28. simpl. rewrite H7'.
                    apply hnot4 with (q:=q) in H36;auto.
                    rewrite <- H36 in H29. repeat rewrite set_union_iff.
                    split;left;auto.
                    intros.
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                    intros.
                    assert(h21:=H21').
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                    assert(h21':=h21).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                    assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                    omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. }
               +++ inversion H7. inversion H8. assert(H17:=H9).
                  inversion H12.
                  inversion H18.
                  inversion H26. subst. apply split_ident in H21;auto. subst.
                  inversion H25. 
                  apply seq_mono_cor with (k:= x) in H27;try omega.
                  assert(H21':=H21).
                  apply split_common_r with (ll2:=LL2) (a:=(If b0 a1 a2))
                  (a':=(If b' a1 a2)) in H21;auto. 
                  { inversion H21.
                    inversion H29.
                   apply H1 with (A:=bool) (LL2:=x1) in H27.
                   inversion H27. exists (x2+x+1+1+1).
                   apply s_bc with (iL:=[])
                   (lL:=[Conj (atom_ (typeof b' bool))
                             (And (atom_ (typeof a1 A)) (atom_ (typeof a2 A)))]);auto.
                   apply tif. auto. auto.
                   apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                   apply split_ref. apply m_and with (LL1:=x1) (LL2:=LL0);auto.
                   apply seq_mono_cor with (j:= x2) ;try omega. auto.
                   inversion H28. apply a_and;auto.
                   apply seq_mono_cor with (j:= i1) ;try omega. auto.
                   apply seq_mono_cor with (j:= i1) ;try omega. auto.
                   apply ss_init.
                   apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                   inversion H4;auto. auto.
                   apply subcntxt_splits with (ll1:=x1) (ll2:=LL0) in H4';auto.
                   inversion H4';auto.
                  apply sub_a_comm with (a1:=b0) in H31.
                  apply sub_a'_comml with (a'1:=b') in H31. auto.
                  intros. assert(h4'':=H4'').
                  apply in_common_r with (q:=q) in H4''. inversion H4''.
                  simpl in H33. repeat rewrite set_union_iff in H33. 
                  rewrite H7' in H33. simpl in H33.
                  assert( (In (CON (Qvar q)) (FQ a2) \/
                        In (CON (Qvar q)) (FQ b') \/ In (CON (Qvar q)) (FQ a2)) <-> 
                  (In (CON (Qvar q)) (FQ a2) \/
                        In (CON (Qvar q)) (FQ b'))) as H33'. intuition.
                  rewrite H33' in H33. clear H33'.
                  destruct H33;auto. 
                  apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                  destruct H30.   inversion H30. 
                  contradict H35. auto. 
                  inversion H30. inversion H28.
                  apply  hnot4 with (q:=q) in H43;auto. 
                  rewrite <- H43 in H36. contradict H36. auto.
                  intros.
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto.
                  intros.
                  assert(h21:=H21').
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  assert(h21':=h21).
                  apply count_split with 
                  (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                  assert(t4'':=h4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                  subst.
                  apply in_common_l with (q:=q0) in h4'';auto. inversion h4''.
                  subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H44.
                  omega.
                  apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                  inversion H4;auto.
                  apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                  intros. simpl in H32. repeat rewrite set_union_iff in H32.
                   apply not_or in H32. inversion H32. 
                   apply not_or in H34. inversion H34. auto. 
                  intros. apply hnot4 with (q:=q) in H27;auto.
                  rewrite H27. auto.
                  intros.
                  apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                  intros.
                  assert(h21:=H21').
                  apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  assert(h21':=h21).
                  apply count_split with 
                  (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                  assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                  subst.
                  apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                  subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H33.
                  omega.
                  apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                  inversion H4;auto.
                  intros. simpl in H32. repeat rewrite set_union_iff in H32.
                   apply not_or in H32. inversion H32. 
                   apply not_or in H34. inversion H34. auto. 
                  intros.
                  simpl in H4'''. specialize H4''' with q.
                  repeat rewrite  set_union_iff in H4'''. 
                  assert(In (typeof q qubit) LL2); auto. 
                  apply unique_in_split with (a:=(typeof q qubit)) in H30.
                  destruct H30.   
                  inversion H30. inversion H28. 
                  assert(h32:=H32). apply fq_all_qvar in h32. inversion h32.
                  subst.   apply hnot4 with (q:=x2) in H41;auto.
                  rewrite <- H41 in H35. simpl in hnot3. 
                  rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                  specialize hnot3 with (CON (Qvar x2)). 
                  rewrite count_app with (l1:=FQU b') (l2:=FQU a1++ FQU a2) in hnot3;auto.
                  assert(In (CON (Qvar x2)) (FQU b' ++ FQU a1++ FQU a2)). rewrite in_app_iff, FQU_FQ. left. auto.
                   apply hnot3 in H19.
                  rewrite count_app with (l:=FQU a1++ FQU a2) (l1:=FQU a1) (l2:= FQU a2) in H19;auto.
                  rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H35.
                   omega.
                  intros.
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                  apply in_common_l_T with (q:=q) (T:=T) in H4'';auto.
                  intros.
                  assert(h21:=H21').
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) T)) in H21';auto.
                  assert(h21':=h21).
                  apply count_split with 
                  (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q)) T)) in h21.
                  assert(t4'':=H4''). apply in_common_l_T with (q:=q) (T:=T) in t4'';auto.
                  subst.
                  apply in_common_l with (q:=q) in H4'';auto. inversion H4''.
                  subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H19.
                  omega.
                  apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                  inversion H4;auto.
                  inversion H30. auto.
                  apply fq_all_qvar in H32. inversion H32. subst.
                  apply in_common_r  with (q:=x2) in H4'';auto. inversion H4''. auto. }
                { intros. inversion H28. simpl. rewrite H7'.
                  apply hnot4 with (q:=q) in H36;auto.
                  rewrite <- H36 in H29. repeat rewrite set_union_iff.
                  split;left;auto. auto.
                  intros.
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                  intros.
                  assert(h21:=H21').
                  apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H21';auto.
                  assert(h21':=h21).
                  apply count_split with 
                  (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h21.
                  assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                  subst.
                  apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                  subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H37.
                  omega.
                  apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                  inversion H4;auto. } 
           ** contradict H7. apply hnot5 in H7.
              inversion H7. destruct H8. inversion H8.
              inversion H8. inversion H9. inversion H9. inversion H12.
        -- contradict H7. apply hnot5 in H7.
           inversion H7. destruct H8. inversion H8.
           inversion H8. inversion H9. inversion H9. inversion H12.
      ++ simpl in hnot1. intros.  specialize hnot1 with V.
         rewrite in_app_iff in hnot1. apply hnot1. left. auto.
      ++ simpl in hnot2.
         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
         specialize hnot2 with x.
         rewrite count_app with (l1:=FQUC b') (l2:=FQUC a1++FQUC a2) in hnot2;auto.
         assert(In x (FQUC b' ++ FQUC a1++FQUC a2)). rewrite in_app_iff. left. auto.
         apply hnot2 in H4.
         rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega. 
      ++ simpl in hnot3.
         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
         rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
         specialize hnot3 with x.
         rewrite count_app with (l1:=FQU b') (l2:=FQU a1++FQU a2) in hnot3;auto.
         assert(In x (FQU b' ++ FQU a1++FQU a2)). rewrite in_app_iff. left. auto.
         apply hnot3 in H4.
         rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega. 
  * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
    assert(h4:=H4).  apply if_a1_a2_eq in h4;auto. 
    ++ apply if_typed in H4. 
       -- destruct H4.
          ** inversion H4. inversion H5.
            inversion H7. inversion H9.
            inversion H11.
            inversion H20. subst. apply split_ident in H15;auto. subst.
            inversion H19. 
            exists (i0+1+1). apply True_LL in  H21. 
            +++ subst.
                apply  split_identr in H15;auto. subst. inversion H22.
                apply common_a_a in H1''. 
                { subst. apply subtypecontext_subtyping with (IL':=IL) (LL':=LL2) (B:=A) in H18;auto. 
                apply seq_mono_cor with (j:= i2+1+1) ;try omega. auto. }
                { simpl. rewrite h4. intros. 
                repeat rewrite set_union_iff. intuition. } 
            +++ contradict H12. apply hnot5 in H12.
                inversion H12. destruct H23. 
                { inversion H23. }
                { inversion H23. inversion H24. inversion H24. inversion H25. }
            +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                inversion H1;auto.
          ** inversion H4. inversion H5.
            inversion H8. 
            inversion H10.
            inversion H19. subst. apply split_ident in H14;auto. subst.
            inversion H18. 
            exists (i0+1+1). apply True_LL in  H20. 
            +++ subst.
              apply  split_identr in H14;auto. subst. inversion H21.
              apply common_a_a in H1''. 
              { subst.
              apply seq_mono_cor with (j:= i2) ;try omega. auto. }
              {  simpl. rewrite h4. intros. 
              repeat rewrite set_union_iff. intuition. }
            +++ contradict H12. apply hnot5 in H12.
              inversion H12. destruct H22. 
              { inversion H22. }
              { inversion H22. inversion H23. inversion H23. inversion H24. }
            +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
              inversion H1;auto. 
       -- auto. 
       -- contradict H1. apply hnot5 in H1. inversion H1.
          inversion H5; inversion H7; inversion H8. inversion H9.
    ++ contradict H1. apply hnot5 in H1. inversion H1.
       inversion H5; inversion H7; inversion H8. inversion H9.
  * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1''  H1''' H4.
    assert(h4:=H4).  apply if_a1_a2_eq in h4;auto. 
    ++ apply if_typed in H4. 
       -- destruct H4.
          ** inversion H4. inversion H5.
              inversion H7. inversion H9.
              inversion H11.
              inversion H20. subst. apply split_ident in H15;auto. subst.
              inversion H19. 
              exists (i0+1+1). apply False_LL in  H21. 
              +++ subst.
                  apply  split_identr in H15;auto. subst. inversion H22.
                  apply common_a_a in H1''. 
                  { subst.
                  apply subtypecontext_subtyping with (IL':=IL) (LL':=LL2) (B:=A) in H21;auto. 
                  apply seq_mono_cor with (j:= i2+1+1) ;try omega. auto. }
                  { simpl. rewrite h4. intros. 
                  repeat rewrite set_union_iff. intuition. }
              +++ contradict H12. apply hnot5 in H12.
                  inversion H12. destruct H23. 
                  { inversion H23. }
                  { inversion H23. inversion H24. inversion H24. inversion H25. }
              +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                  inversion H1;auto.
          ** inversion H4. inversion H5.
              inversion H8. 
              inversion H10.
              inversion H19. subst. apply split_ident in H14;auto. subst.
              inversion H18. 
              exists (i0+1+1). apply False_LL in  H20.
              +++ subst.
                  apply  split_identr in H14;auto. subst. inversion H21.
                  apply common_a_a in H1''. 
                  { subst.
                  apply seq_mono_cor with (j:= i2) ;try omega. auto. }
                  { simpl. rewrite h4. intros. 
                  repeat rewrite set_union_iff. intuition. }
              +++ contradict H12. apply hnot5 in H12.
                  inversion H12. destruct H22. 
                  { inversion H22. }
                  { inversion H22. inversion H23. inversion H23. inversion H24. }
              +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                  inversion H1;auto.
       -- auto.
       -- contradict H1. apply hnot5 in H1. inversion H1.
          inversion H5; inversion H7; inversion H8. inversion H9.
    ++ contradict H1. apply hnot5 in H1. inversion H1.
       inversion H5; inversion H7; inversion H8. inversion H9.
(*Neqvar Case*)
  * assert(circ15:=H15). assert(circ16:=H16). 
    assert(H13:=H11). clear H15 H16 H11.
    exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
    apply app_box_value in H4;auto.
    ++ inversion H4. subst. inversion H7. inversion H5.
       inversion H8. inversion H9. inversion H11.
       inversion H15. assert(h17:=H17).
        apply Subtyping_bang_inv in  H17.
        inversion H17. inversion H18.
        inversion H19. inversion H20.
        -- subst.
            inversion H12. 
            ** inversion H22.
                inversion H31. inversion H33. assert(h29:=H29). apply valid_sub_eq in H29;auto.
                subst. assert(h30:=H30). apply valid_sub_eq in H30;auto. subst.
                assert(h25:=H25). apply sub_valid_sub_eq in H25;auto. 
                rewrite <- H25 in *. assert(h1':=H1).
                 apply subcnxt_add with
                (fq:=(FQ (Spec (newqvar v) T))) in H1.
                apply spec_typing with (T:=T) (v:=newqvar v) (i:=x) in H1;auto.
                inversion H1. inversion H21. 
                apply seq_weakening_cor with 
                (il':= rev (toiqlist (FQ (Spec (newqvar v) T))) ++ IL) in H27.
                +++ apply seq_exchange_cor with 
                (eq_dec:=ProgLemmas1.eq_dec)
                (ll':= rev (toqlist (FQ (Spec (newqvar v) T)))) in H27.
                    { assert(rev (toqlist (FQ (Spec (newqvar v) T))) = rev (toqlist (FQ (Spec (newqvar v) T)))++[])
                      ; try rewrite app_nil_r;auto. rewrite H28 in H27. 
                      apply move_from_ll in H27.
                      inversion H1''; [..| simpl in H29; inversion H29].
                      assert(FQ v = []). 
                      rewrite  <- count_occ_inv_nil with (eq_dec:=ProtoQuipperSyntax.eq_dec).
                      intros. destruct (in_dec ProtoQuipperSyntax.eq_dec x1 (FQ v)).
                      assert(i1':=i1). apply fq_all_qvar in i1. inversion i1. subst.
                      apply  LL_FQ with (q:=x2)  in H16;auto. rewrite H16 in i1'. inversion i1'.
                      intros. inversion H25. intros.  
                      inversion H25. rewrite <- count_occ_not_In. auto.
                      exists (x+x0+length(FQ (App v (Spec (newqvar v) T)))
                      +length(FQ (App v (Spec (newqvar v) T)))+1+1+1+1+1+1+1+1).
                      apply s_bc with 
                      (iL:=[And (toimp (FQ (App v (Spec (newqvar v) T))) (atom_(typeof (App v (Spec (newqvar v) T)) B2)))
                      (toimp (FQ ((Spec (newqvar v) T) )) (atom_ (typeof (Spec (newqvar v) T) T)))])
                      (lL:=[]);auto. apply tCricl;auto. simpl.
                      rewrite H32. rewrite union_empty. auto.
                      apply nodup_fq.
                      apply Spec_quantum_data.
                      apply ss_general with (lL2:=[]) (lL3:=[]). apply init.
                      apply a_and. auto. Focus 2. apply seq_mono_cor with 
                      (j:=x0 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T)))). 
                      omega. simpl. rewrite H32. rewrite union_empty,rev_length. auto.
                      apply nodup_fq. assert(x + x0 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T))) + 1 + 1+1+1+1+1 = x + x0 + 1+1+1+1+1+ 1 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T))));try omega. 
                       rewrite H35. apply move_from_ll. apply fq_all_qvar.
                      apply s_bc with (iL:=[]) (lL:=[Conj (atom_(typeof v (arrow T B2)))
                       (atom_(typeof (Spec (newqvar v) T) T))]);auto.
                      apply tap. apply vArrow; apply valid_is_T;auto. apply ss_init.
                      apply ss_general with (lL2:=rev (toqlist (FQ (App v (Spec (newqvar v) T)))) ++ [])
                      (lL3:=[]). apply split_ref.  apply m_and with (LL1:=[]) 
                      (LL2:=rev (toqlist (FQ (App v (Spec (newqvar v) T)))) ++ []).
                      apply split_rref. apply seq_mono_cor with (j:=x+1+1). omega.
                      apply seq_weakening_cor with (il:=IL).
                      apply subtypecontext_subtyping with (A:= bang (arrow T B1))  (IL:=IL) (LL:=[]);auto. 
                      apply BangSub1. apply  ArrowSub;auto. apply bArrow.
                      apply valid_is_T;auto. apply SubAreVal in H26. inversion H26. auto.
                      intros. rewrite in_app_iff. right. auto.
                      inversion H21. simpl. rewrite H32.
                       rewrite union_empty,rev_toqlist,rev_toiqlist,rev_involutive.
                      apply seq_mono_cor with (j:=x0). omega.
                      rewrite app_nil_r. auto. apply nodup_fq. apply ss_init. apply ss_init.
                      apply ss_init.
                      apply fq_all_qvar. }
                      { intros.
                      rewrite <- rev_count. auto. }
                +++ intros.
                    rewrite in_app_iff  in * . destruct H28.
                    { left. apply in_rev in H28. auto. } 
                    {  right.  auto. }
            ** inversion H22.
               inversion H31. inversion H33. assert(h29:=H29). apply valid_sub_eq in H29;auto.
               subst. assert(h30:=H30). apply valid_sub_eq in H30;auto. subst.
               assert(h25:=H25). apply sub_valid_sub_eq in H25;auto. 
               rewrite <- H25 in *. assert(h1':=H1).
               apply subcnxt_add with (fq:=(FQ (Spec (newqvar v) T))) in H1.
               apply spec_typing with (T:=T) (v:=newqvar v) (i:=x) in H1;auto.
               inversion H1. inversion H21. 
               apply seq_weakening_cor with 
               (il':= rev (toiqlist (FQ (Spec (newqvar v) T))) ++ IL) in H27.
               +++ apply seq_exchange_cor with (eq_dec:=ProgLemmas1.eq_dec)
                   (ll':= rev (toqlist (FQ (Spec (newqvar v) T)))) in H27.
                   { assert(rev (toqlist (FQ (Spec (newqvar v) T))) = rev (toqlist (FQ (Spec (newqvar v) T)))++[])
                      ; try rewrite app_nil_r;auto. rewrite H28 in H27. 
                      apply move_from_ll in H27.
                      inversion H1''; [..| simpl in H29; inversion H29].
                      assert(FQ v = []). 
                      rewrite  <- count_occ_inv_nil with (eq_dec:=ProtoQuipperSyntax.eq_dec).
                      intros. destruct (in_dec ProtoQuipperSyntax.eq_dec x1 (FQ v)).
                      assert(i1':=i1). apply fq_all_qvar in i1. inversion i1. subst.
                      apply  LL_FQ with (q:=x2)  in H16;auto. rewrite H16 in i1'. inversion i1'.
                      intros. inversion H25. intros.  
                      inversion H25. rewrite <- count_occ_not_In. auto.
                      exists (x+x0+length(FQ (App v (Spec (newqvar v) T)))
                      +length(FQ (App v (Spec (newqvar v) T)))+1+1+1+1+1+1+1+1).
                      apply s_bc with 
                      (iL:=[And (toimp (FQ (App v (Spec (newqvar v) T))) (atom_(typeof (App v (Spec (newqvar v) T)) B2)))
                      (toimp (FQ ((Spec (newqvar v) T) )) (atom_ (typeof (Spec (newqvar v) T) T)))])
                      (lL:=[]);auto. apply tCrici;auto. 
                      simpl. rewrite H32. rewrite union_empty. auto. apply nodup_fq.
                      apply Spec_quantum_data. 
                      apply ss_general with (lL2:=[]) (lL3:=[]). apply init.
                      apply a_and. auto. Focus 2. apply seq_mono_cor with 
                      (j:=x0 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T)))). 
                      omega. simpl. rewrite H32. rewrite union_empty,rev_length. auto.
                      apply nodup_fq. assert(x + x0 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T))) + 1 + 1+1+1+1+1 = x + x0 + 1+1+1+1+1+ 1 + length (FQ (App v (Spec (newqvar v) T))) +
                         length (FQ (App v (Spec (newqvar v) T))));try omega. 
                       rewrite H35. apply move_from_ll. apply fq_all_qvar.
                      apply s_bc with (iL:=[]) (lL:=[Conj (atom_(typeof v (arrow T B2)))
                       (atom_(typeof (Spec (newqvar v) T) T))]);auto.
                      apply tap. apply vArrow; apply valid_is_T;auto. apply ss_init.
                      apply ss_general with (lL2:=rev (toqlist (FQ (App v (Spec (newqvar v) T)))) ++ [])
                      (lL3:=[]). apply split_ref.  apply m_and with (LL1:=[]) 
                      (LL2:=rev (toqlist (FQ (App v (Spec (newqvar v) T)))) ++ []).
                      apply split_rref. apply seq_mono_cor with (j:=x+1+1). omega.
                      apply seq_weakening_cor with (il:=IL).
                      apply subtypecontext_subtyping with (A:= bang (arrow T B1))  (IL:=IL) (LL:=[]);auto. 
                      apply BangSub1. apply  ArrowSub;auto. apply bArrow.
                      apply valid_is_T;auto. apply SubAreVal in H26. inversion H26. auto.
                      intros. rewrite in_app_iff. right. auto.
                      inversion H21. simpl. rewrite H32.
                       rewrite union_empty,rev_toqlist,rev_toiqlist,rev_involutive.
                      apply seq_mono_cor with (j:=x0). omega.
                      rewrite app_nil_r. auto. apply nodup_fq. apply ss_init. apply ss_init.
                      apply ss_init.
                      apply fq_all_qvar. }
                    { intros.
                      rewrite <- rev_count. auto. }
               +++ intros.
                   rewrite in_app_iff  in * . destruct H28.
                   { left. apply in_rev in H28. auto. } 
                   {   right.  auto. }
        -- subst.
           apply SubAreVal in h17. inversion h17. inversion H22.
    ++ intros. contradict H1. apply hnot5 in H1. 
       inversion H1. destruct H5.
       inversion H5. destruct H5.
       inversion H5. inversion H5. inversion H7.
    ++  intros.  subst. simpl in hnot1.  specialize hnot1 with V.
        assert(App (CON UNBOX) V = V \/ V=V \/ In V (get_boxed V)) as H2';auto.
        apply hnot1 in H2'.
        contradict H1. apply hnot5 in H1. inversion H1.
        destruct H5. inversion H5. subst.
        contradict H2'. exists x. left. auto.
        destruct H5. inversion H5. subst.
        contradict H2'. exists x. right. auto.
        inversion H5. inversion H7.


    ++ simpl in hnot1.  specialize hnot1 with v.
       assert(v=v \/ In v (get_boxed v)) as H2';auto. apply hnot1 in H2'.
       contradict H1. apply hnot5 in H1. inversion H1.
       destruct H5. inversion H5. subst.
       contradict H2'. exists x. left. auto.
       destruct H5. inversion H5. subst.
       contradict H2'. exists x. right. auto.
       inversion H5. inversion H7.

    ++ contradict H1.  apply hnot5 in H1.
       inversion H1. destruct H5.
       inversion H5. destruct H5.
       inversion H5. inversion H5. inversion H7.

   ++ contradict H1.  apply hnot5 in H1.
      inversion H1. destruct H5.
      inversion H5. destruct H5.
      inversion H5. inversion H5. inversion H7.

  * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4. apply app_typed in H4.
    ++ destruct H4.
       -- rexists. destruct_conj. 
          inversion H9. clear H9. inversion H21. subst.
          apply split_ident in H14;auto. subst.
          inversion H20. apply app_typed in H19.
          ** destruct H19.  
             +++ rexists. destruct_conj. 
                  inversion H26. inversion H33. subst. apply split_ident in H28. 
                  { subst.
                  inversion H32. apply UNBOX_LL in H27.
                  destruct_conj. rexists. subst.
                  apply sub_Circ_inv in H28. destruct H28.
                  rexists. destruct_conj.
                  subst. inversion H14. subst.
                  apply split_identr in H10. subst.  inversion H30.
                  clear H30.
                  subst. inversion H16. inversion H35.
                  inversion  H37. subst. inversion H23.
                  assert(Subtyping x5 A). 
                  apply sub_trans with (B:=x1);auto.
                  apply sub_trans with (B:=B3);auto.
                  inversion H27. clear H27. inversion H45.
                  apply sub_valid_sub_eq in H40;auto.
                  subst. assert(Subtyping x8 (circ x A)).
                  apply sub_trans with (B:=x3);auto.
                  destruct H28;subst;inversion H10. inversion H41.
                  inversion H43.
                  apply sub_valid_sub_eq in H36;auto.
                  apply sub_valid_sub_eq in H40;auto.
                  subst. inversion H25. inversion H50.
                  subst. apply split_nil in H29. subst.
                  inversion H29. subst. inversion H47. 
                  apply move_to_ll in H54;auto.
                  apply quantum_data_typed in H54;auto.
                  inversion H54. 
                  apply sub_valid_sub_eq in H59;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H40.
                  apply H40 in H1''. omega.
                  intros. rewrite count_occ_In in H36.
                  rewrite <- H27 in H36. rewrite <- count_occ_In in H36.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H53. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H58. rexists. destruct_conj.
                  inversion H58. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H59.
                  apply H59 in H58. auto.
                  intros. rewrite rev_toiqlist in H58.
                  apply in_app_or in H58. destruct H58;auto.
                  apply in_toiqlistg in H58. inversion H58.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  inversion H28.
                  inversion H29.
                  apply sub_valid_sub_eq in H50;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H25. inversion H50.
                  subst. apply split_nil in H36. 
                  inversion H36. subst. inversion H50. 
                  apply move_to_ll in H61;auto.
                  apply quantum_data_typed in H61;auto.
                  inversion H61. 
                  apply sub_valid_sub_eq in H59;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x2) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H43.
                  apply H43 in H1''. omega.
                  intros. rewrite count_occ_In  with (eq_dec:= ProgLemmas1.eq_dec) in H41.
                  rewrite <- H30 in H41. rewrite <- count_occ_In in H41.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i5. rexists. destruct_conj.
                  apply H1''' in H59. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H58. rexists. destruct_conj.
                  inversion H58. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H59.
                  apply H59 in H58. auto.
                  Optimize Proof.
                  intros. rewrite rev_toiqlist in H58.
                  apply in_app_or in H58. destruct H58;auto.
                  apply in_toiqlistg in H58. inversion H58.
                  exists x2. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  apply fq_all_qvar.
                  inversion  H37. subst. inversion H23.
                  inversion H29.
                  assert(Subtyping x5 A). 
                  apply sub_trans with (B:=x1);auto.
                  apply sub_trans with (B:=B3);auto.
                  inversion H27. clear H27. inversion H49.
                  apply sub_valid_sub_eq in H46;auto.
                  subst. assert(Subtyping x8 (circ x A)).
                  apply sub_trans with (B:=x3);auto.
                  destruct H28;subst;inversion H10. inversion H43.
                  inversion H46.
                  apply sub_valid_sub_eq in H39;auto.
                  apply sub_valid_sub_eq in H40;auto.
                  subst. inversion H25. inversion H47.
                  apply split_nil in H34. 
                  inversion H34. subst. 
                  apply move_to_ll in H62;auto.
                  apply quantum_data_typed in H62;auto.
                  inversion H62. 
                  apply sub_valid_sub_eq in H28;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H40.
                  apply H40 in H1''. omega.
                  intros. rewrite count_occ_In in H39.
                  rewrite <- H28 in H39. rewrite <- count_occ_In in H39.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i3. rexists. destruct_conj.
                  apply H1''' in H55. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H27. rexists. destruct_conj.
                  inversion H27. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H28.
                  apply H28 in H27. auto.
                  intros. rewrite rev_toiqlist in H27.
                  apply in_app_or in H27. destruct H27;auto.
                  apply in_toiqlistg in H27. inversion H27.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  inversion H28.
                  inversion H34.
                  apply sub_valid_sub_eq in H48;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H25. apply split_nil in H39. 
                  inversion H39. subst. inversion H48. 
                  apply move_to_ll in H56;auto.
                  apply quantum_data_typed in H56;auto.
                  inversion H56. 
                  apply sub_valid_sub_eq in H61;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x2) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H43.
                  apply H43 in H1''. omega.
                  intros. rewrite count_occ_In  with (eq_dec:= ProgLemmas1.eq_dec) in H40.
                  rewrite <- H27 in H40. rewrite <- count_occ_In in H40.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H46. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H60. rexists. destruct_conj.
                  inversion H60. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H61.
                  apply H61 in H60. auto.
                  intros. rewrite rev_toiqlist in H60.
                  apply in_app_or in H60. destruct H60;auto.
                  apply in_toiqlistg in H60. inversion H60.
                  exists x4. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  auto.
                  rexists. destruct_conj.
                  subst. inversion H14. subst.
                  apply split_identr in H10. subst.  inversion H30.
                  clear H30.
                  subst. inversion H15. inversion H34.
                  inversion  H36. subst. inversion H23.
                  assert(Subtyping x5 A). 
                  apply sub_trans with (B:=x1);auto.
                  apply sub_trans with (B:=B3);auto.
                  inversion H25. clear H25. inversion H44.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. assert(Subtyping x3 (circ x A)). auto.
                  destruct H27;subst;inversion H10. inversion H40.
                  inversion H42.
                  apply sub_valid_sub_eq in H35;auto.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. inversion H16. apply split_nil in H28. subst.
                  inversion H28. subst. inversion H46. 
                  apply move_to_ll in H52;auto.
                  apply quantum_data_typed in H52;auto.
                  inversion H52. 
                  apply sub_valid_sub_eq in H57;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H35.
                  apply H35 in H1''. omega.
                  intros. rewrite count_occ_In in H29.
                  rewrite <- H25 in H29. rewrite <- count_occ_In in H29.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H39. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H56. rexists. destruct_conj.
                  inversion H56. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H57.
                  apply H57 in H56. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  apply fq_all_qvar.
                  inversion H27.
                  inversion H28.
                  apply sub_valid_sub_eq in H46;auto.
                  apply sub_valid_sub_eq in H49;auto.
                  subst. inversion H16. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion  H36. subst. inversion H23.
                  inversion H28.
                  assert(Subtyping x5 A). 
                  apply sub_trans with (B:=x1);auto.
                  apply sub_trans with (B:=B3);auto.
                  inversion H25. clear H25. inversion H48.
                  apply sub_valid_sub_eq in H45;auto.
                  subst. assert(Subtyping x3 (circ x A)). auto.
                  destruct H27;subst;inversion H10.
                  inversion H42.
                  inversion H45.
                  apply sub_valid_sub_eq in H38;auto.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. inversion H16. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  inversion H27.
                  inversion H53.
                  inversion H50.
                  apply sub_valid_sub_eq in H46;auto.
                  apply sub_valid_sub_eq in H47;auto.
                  subst. inversion H16. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  apply fq_all_qvar.
                  auto.
                  apply split_identr in H14. subst.
                  apply subcntxt_splits with (ll1:=LL3) (ll2:=LL0) in H1;auto.
                  inversion H1. auto. auto.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
                  apply subcntxt_splits with (ll1:=lL0) (ll2:=LL0) in H1;auto.
                  inversion H1 as [Hl Hr]. 
                  apply subcntxt_splits with (ll1:=LL1) (ll2:=LL3) in Hl;auto.
                  inversion Hl. auto. } 
                  { auto. }
                  Optimize Proof.
              +++ rexists. destruct_conj. 
                  inversion H25. inversion H32. subst. apply split_ident in H27.  
                  { subst.
                  inversion H31. apply UNBOX_LL in H26.
                  destruct_conj. rexists. subst.
                  apply sub_Circ_inv in H27. destruct H27.
                  rexists. destruct_conj.
                  subst. inversion H14. subst.
                  apply split_identr in H10. subst.  inversion H29.
                  clear H29.
                  subst. inversion H16. inversion H34.
                  inversion  H36. subst. 
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=x1);auto.
                  inversion H26. clear H26. inversion H33.
                  apply sub_valid_sub_eq in H10;auto.
                  subst. assert(Subtyping x7 (circ x A)).
                  apply sub_trans with (B:=x3);auto.
                  destruct H27;subst;inversion H10. inversion H45.
                  inversion H43.
                  apply sub_valid_sub_eq in H38;auto.
                  apply sub_valid_sub_eq in H41;auto.
                  subst. inversion H24. inversion H46.
                  subst. apply split_nil in H28. subst.
                  inversion H28. subst. inversion H46. 
                  apply move_to_ll in H50;auto.
                  apply quantum_data_typed in H50;auto.
                  inversion H50. 
                  apply sub_valid_sub_eq in H55;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H41.
                  apply H41 in H1''. omega.
                  intros. rewrite count_occ_In in H38.
                  rewrite <- H27 in H38. rewrite <- count_occ_In in H38.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i5. rexists. destruct_conj.
                  apply H1''' in H55. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H54. rexists. destruct_conj.
                  inversion H54. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H55.
                  apply H55 in H54. auto.
                  intros. rewrite rev_toiqlist in H54.
                  apply in_app_or in H54. destruct H54;auto.
                  apply in_toiqlistg in H54. inversion H54.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion H27.
                  inversion H28.
                  apply sub_valid_sub_eq in H47;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H24. inversion H47.
                  subst. apply split_nil in H38. 
                  inversion H38. subst.  
                  apply move_to_ll in H58;auto.
                  apply quantum_data_typed in H58;auto.
                  inversion H58. 
                  apply sub_valid_sub_eq in H29;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x2) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H45.
                  apply H45 in H1''. omega.
                  intros. rewrite count_occ_In  with (eq_dec:= ProgLemmas1.eq_dec) in H43.
                  rewrite <- H29 in H43. rewrite <- count_occ_In in H43.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i3. rexists. destruct_conj.
                  apply H1''' in H51. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H26. rexists. destruct_conj.
                  inversion H26. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H29.
                  apply H29 in H26. auto.
                  intros. rewrite rev_toiqlist in H26.
                  apply in_app_or in H26. destruct H26;auto.
                  apply in_toiqlistg in H26. inversion H26.
                  exists x2. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar. auto.
                  Optimize Proof.
                  rexists. destruct_conj.
                  subst. inversion H14. subst.
                  apply split_identr in H10. subst.  inversion H29.
                  clear H29.
                  subst. inversion H15. inversion H33.
                  inversion  H35. subst. 
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=x1);auto.
                  inversion H24. clear H24. inversion H30.
                  apply sub_valid_sub_eq in H10;auto.
                  subst. assert(Subtyping x3 (circ x A)). auto.
                  destruct H26;subst;inversion H10. inversion H44.
                  inversion H42.
                  apply sub_valid_sub_eq in H37;auto.
                  apply sub_valid_sub_eq in H40;auto.
                  subst. inversion H16. apply split_nil in H27. subst.
                  inversion H27. subst. inversion H45. 
                  apply move_to_ll in H49;auto.
                  apply quantum_data_typed in H49;auto.
                  inversion H49. 
                  apply sub_valid_sub_eq in H54;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H37.
                  apply H37 in H1''. omega.
                  intros. rewrite count_occ_In in H28.
                  rewrite <- H24 in H28. rewrite <- count_occ_In in H28.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H40. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H53. rexists. destruct_conj.
                  inversion H53. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H54.
                  apply H54 in H53. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto. Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  inversion H26.
                  inversion H27.
                  apply sub_valid_sub_eq in H46;auto.
                  apply sub_valid_sub_eq in H45;auto.
                  subst. inversion H16. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H22;auto.
                  inversion H22 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto. Optimize Proof.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  apply fq_all_qvar. auto.
                  apply split_identr in H14. subst.
                  apply subcntxt_splits with (ll1:=LL3) (ll2:=LL0) in H1;auto.
                  inversion H1. auto. auto.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
                  apply subcntxt_splits with (ll1:=lL0) (ll2:=LL0) in H1;auto.
                  inversion H1 as [Hl Hr]. 
                  apply subcntxt_splits with (ll1:=LL1) (ll2:=LL3) in Hl;auto.
                  inversion Hl. auto. }
                  { auto. }
          ** apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
             inversion H1. auto. 
          ** contradict H1. apply hnot5 in H1.
             inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
             ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
             ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
       -- Optimize Proof. rexists. destruct_conj. 
          inversion H8. clear H8. inversion H20. subst.
          apply split_ident in H10;auto. subst.
          inversion H19. apply app_typed in H16.
          ** destruct H16.
             +++  rexists. destruct_conj. 
                  inversion H25. inversion H32. subst. apply split_ident in H27;auto. 
                  subst.
                  inversion H31. apply UNBOX_LL in H26.
                  { destruct_conj. rexists. subst.
                  apply sub_Circ_inv in H27. destruct H27.
                  rexists. destruct_conj.
                  subst. inversion H10. subst.
                  apply split_identr in H9. subst.  inversion H29.
                  clear H29.
                  subst. inversion H15. inversion H34.
                  inversion  H36. subst. inversion H22.
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=B3);auto.
                  inversion H26. clear H26. inversion H44.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. assert(Subtyping x7 (circ x A)).
                  apply sub_trans with (B:=x2);auto.
                  destruct H27;subst; inversion H9. inversion H40.
                  inversion H24.
                  apply sub_valid_sub_eq in H35;auto.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. apply split_nil in H54. 
                  inversion H54. subst. inversion H58. 
                  apply move_to_ll in H39;auto.
                  apply quantum_data_typed in H39;auto.
                  inversion H39. 
                  apply sub_valid_sub_eq in H52;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H29.
                  apply H29 in H1''. omega.
                  intros. rewrite count_occ_In in H28.
                  rewrite <- H26 in H28. rewrite <- count_occ_In in H28.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H35. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H49. rexists. destruct_conj.
                  inversion H49. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H52.
                  apply H52 in H49. auto. Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion H27.
                  inversion H28.
                  apply sub_valid_sub_eq in H49;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H24. apply split_nil in H35. 
                  inversion H35. subst. inversion H49. 
                  apply move_to_ll in H53;auto.
                  apply quantum_data_typed in H53;auto.
                  inversion H53. 
                  apply sub_valid_sub_eq in H58;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x1) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H40.
                  apply H40 in H1''. omega.
                  intros. rewrite count_occ_In  with (eq_dec:= ProgLemmas1.eq_dec) in H39.
                  rewrite <- H26 in H39. rewrite <- count_occ_In in H39.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H42. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H57. rexists. destruct_conj.
                  inversion H57. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H58.
                  apply H58 in H57. auto. Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x3. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  inversion  H36. subst. inversion H22.
                  inversion H28. 
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=B3);auto.
                  inversion H26. clear H26. inversion H48.
                  apply sub_valid_sub_eq in H45;auto.
                  subst. assert(Subtyping x7 (circ x A)).
                  apply sub_trans with (B:=x2);auto.
                  destruct H27;subst;inversion H9. inversion H42.
                  inversion H45.
                  apply sub_valid_sub_eq in H38;auto.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. inversion H24. inversion H46.
                  apply split_nil in H33. 
                  inversion H33. subst. 
                  apply move_to_ll in H61;auto.
                  apply quantum_data_typed in H61;auto.
                  inversion H61. 
                  apply sub_valid_sub_eq in H27;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H39.
                  apply H39 in H1''. omega.
                  intros. rewrite count_occ_In in H38.
                  rewrite <- H27 in H38. rewrite <- count_occ_In in H38.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i3. rexists. destruct_conj.
                  apply H1''' in H54. contradict n. subst. auto. Optimize Proof.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H26. rexists. destruct_conj.
                  inversion H26. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H27.
                  apply H27 in H26. auto.
                  intros. rewrite rev_toiqlist in H26.
                  apply in_app_or in H26. destruct H26;auto.
                  apply in_toiqlistg in H26. inversion H26.
                  exists x. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion H27.
                  inversion H33.
                  apply sub_valid_sub_eq in H47;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H24. apply split_nil in H38. 
                  inversion H38. subst. inversion H47. 
                  apply move_to_ll in H55;auto.
                  apply quantum_data_typed in H55;auto.
                  inversion H55. 
                  apply sub_valid_sub_eq in H60;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x1) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H42.
                  apply H42 in H1''. omega.
                  intros. rewrite count_occ_In  with (eq_dec:= ProgLemmas1.eq_dec) in H39.
                  rewrite <- H26 in H39. rewrite <- count_occ_In in H39.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H45. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H59. rexists. destruct_conj.
                  inversion H59. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H60.
                  apply H60 in H59. auto.
                  intros. rewrite rev_toiqlist in H59.
                  apply in_app_or in H59. destruct H59;auto.
                  apply in_toiqlistg in H59. inversion H59.
                  exists x3. right. left. auto.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto. apply fq_all_qvar.
                  auto. Optimize Proof.
                  rexists. destruct_conj.
                  subst. inversion H10. subst.
                  apply split_identr in H9. subst.  inversion H29.
                  clear H29.
                  subst. inversion H14. inversion H33.
                  inversion  H35. subst. inversion H22.
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=B3);auto.
                  inversion H24. clear H24. inversion H43.
                  apply sub_valid_sub_eq in H38;auto.
                  subst. assert(Subtyping x2 (circ x A)). auto.
                  destruct H26;subst;inversion H9. inversion H39.
                  inversion H39.
                  apply sub_valid_sub_eq in H34;auto.
                  apply sub_valid_sub_eq in H38;auto.
                  subst. inversion H15. apply split_nil in H27. subst.
                  inversion H27. subst. inversion H45. 
                  apply move_to_ll in H51;auto.
                  apply quantum_data_typed in H51;auto.
                  inversion H51. 
                  apply sub_valid_sub_eq in H56;auto.
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21.
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H34.
                  apply H34 in H1''. omega.
                  intros. rewrite count_occ_In in H28.
                  rewrite <- H24 in H28. rewrite <- count_occ_In in H28.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. rexists. destruct_conj.
                  apply H1''' in H38. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  apply intoqlist_infq in H55. rexists. destruct_conj.
                  inversion H55. auto.
                  rewrite app_nil_r,rev_toqlist. intros.
                  assert(NoDup (toqlist (rev (FQ u')))). apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H56.
                  apply H56 in H55. auto.

                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.

                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion H26.
                  inversion H27.
                  apply sub_valid_sub_eq in H45;auto.
                  apply sub_valid_sub_eq in H48;auto.
                  subst. inversion H15. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.

                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.

                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Heap.
                  apply fq_all_qvar.
                  Optimize Heap.
                  Optimize Proof.
                  Optimize Proof.
                  inversion  H35. subst. inversion H22.
                  inversion H27.
                  assert(Subtyping x4 A). 
                  apply sub_trans with (B:=B3);auto.
                  inversion H24. clear H24. inversion H47.
                  apply sub_valid_sub_eq in H44;auto.
                  subst. assert(Subtyping x2 (circ x A)). auto.
                  destruct H26;subst;inversion H9.
                  inversion H41.
                  inversion H44.
                  apply sub_valid_sub_eq in H37;auto.
                  apply sub_valid_sub_eq in H38;auto.
                  subst. inversion H15. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.

                  inversion H26.
                  inversion H52.
                  inversion H49.
                  apply sub_valid_sub_eq in H45;auto.
                  apply sub_valid_sub_eq in H46;auto.
                  subst. inversion H15. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar.
                  Optimize Proof.
                  auto.
                  apply split_identr in H10. subst.
                  apply subcntxt_splits with (ll1:=LL3) (ll2:=LL0) in H1;auto.
                  inversion H1. auto. auto.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
                  Optimize Heap.
                  Optimize Proof. }
                  { contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d. }
                  { apply subcntxt_splits with (ll1:=lL0) (ll2:=LL0) in H1;auto.
                  inversion H1 as [Hl Hr]. 
                  apply subcntxt_splits with (ll1:=LL1) (ll2:=LL3) in Hl;auto.
                  inversion Hl. auto. }
              +++ rexists. destruct_conj. 
                  inversion H24. inversion H31. subst. apply split_ident in H26;auto. 
                  subst.
                  inversion H30. apply UNBOX_LL in H25.
                  { destruct_conj. rexists. subst.
                  apply sub_Circ_inv in H26. destruct H26.
                  rexists. destruct_conj.
                  subst. inversion H10. subst.
                  apply split_identr in H9. subst.  inversion H28.
                  clear H28.
                  subst. inversion H15. inversion H33.
                  inversion  H35. subst. 
                  inversion H25. clear H25. inversion H28.
                  apply sub_valid_sub_eq in H43;auto.
                  subst. assert(Subtyping x6 (circ x A)).
                  apply sub_trans with (B:=x2);auto.
                  destruct H26;subst;inversion H9. inversion H43.
                  inversion H42.
                  apply sub_valid_sub_eq in H39;auto.
                  apply sub_valid_sub_eq in H40;auto.
                  subst. inversion H23. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  Optimize Proof.
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.

                  apply fq_all_qvar.
                  Optimize Proof.
                  inversion H26.
                  inversion H27.
                  apply sub_valid_sub_eq in H45;auto.
                  (*apply sub_valid_sub_eq in H40;auto.*)
                  subst. inversion H23. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x1) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x1 i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x5 e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  Optimize Proof.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x3. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  apply fq_all_qvar. auto.
                  rexists. destruct_conj.
                  subst. inversion H10. subst.
                  apply split_identr in H9. subst.  inversion H28.
                  clear H28.
                  subst. inversion H14. inversion H32.
                  inversion  H34. subst. 
                  inversion H23. clear H23. inversion H27.
                  apply sub_valid_sub_eq in H42;auto.
                  subst. assert(Subtyping x2 (circ x A)). auto.
                  destruct H25;subst;inversion H9. inversion H42.
                  inversion H41.
                  apply sub_valid_sub_eq in H38;auto.
                  apply sub_valid_sub_eq in H39;auto.
                  subst. inversion H15. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x1 i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  Optimize Heap.
                  Optimize Proof.
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x5 e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.
                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.
                  Optimize Proof.
                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.
                  Optimize Proof.
                  apply fq_all_qvar. auto.
                  Optimize Heap.
                  Optimize Proof.
                  inversion H25.
                  inversion H26.
                  apply sub_valid_sub_eq in H43;auto.
                  apply sub_valid_sub_eq in H44;auto.
                  subst. inversion H15. 
                  match goal with
                  [H:LSL.split [] _ _|-_] =>  apply split_nil in H;inversion H; subst
                  |_=>idtac end.
                  match goal with
                  [H: LSL.seq _ _ _ _ (And _ _)|-_] =>  
                  inversion H as  [ | | | | | i3 B C IL0 LL QL e1 e2| | | ];
                  apply move_to_ll in e1;auto; try apply quantum_data_typed in e1;auto;
                  try inversion e1 as [e_occ e_typer]; 
                  try apply  sub_valid_sub_eq in e_typer;auto
                  |_=>idtac end. 
                  subst. rewrite qtyper_bind with (b:=a');auto.
                  apply typed_quantum_data;auto.
                  apply quantum_data_bind in H17. inversion H17. auto.
                  intros. Optimize Proof.
                  apply quantum_data_typed in H21;auto.
                  inversion H21 as [H22_occ H22_typer].
                  destruct (in_dec ProgLemmas1.eq_dec q LL2).
                  assert(h1'':=H1'').
                  apply quantum_ll with (q:=q) in H1'';auto.
                  assert(hfq:=H1'').
                  apply intoqlist_infq in hfq. rexists. destruct_conj.
                  apply in_common_r with (q:=x) in h1'';auto.
                  inversion h1''. subst.
                  assert(NoDup (toqlist (FQ a'))). 
                  apply nodup_toqlist,nodup_fq2. 
                  match goal with 
                  |[H:NoDup (toqlist (FQ a'))|-_] => 
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in H;
                  apply H in H1''; try omega
                  |_=>idtac end.
                  intros  q0 e3. rewrite count_occ_In in e3.
                  rewrite <- H22_occ in e3. rewrite <- count_occ_In in e3.
                  simpl. auto. rewrite union_empty, <- rev_toqlist,<- in_rev.
                  auto. apply nodup_fq2. Optimize Proof.
                  destruct (in_dec ProgLemmas1.eq_dec q (toqlist (FQ a'))).
                  apply intoqlist_infq in i4. inversion_clear i4 as [x i4_conj].
                  inversion_clear i4_conj as [i4_l i4_r].
                  apply H1''' in i4_r. contradict n. subst. auto.
                  rewrite count_occ_not_In with (eq_dec:= ProgLemmas1.eq_dec) in n,n0.
                  omega. intros. 
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  intros. 
                  Optimize Proof.
                  apply in_common_l2 with (q:=q0) (T:= T) in H1'';auto. inversion H1''. auto.
                  rewrite app_nil_r,rev_toqlist. 
                  intros q0 T e3.
                  apply intoqlist_infq in e3. inversion_clear e3 as [x e3_conj].
                  inversion e3_conj as [e3_l e3_r].
                  inversion e3_l. auto.
                  rewrite app_nil_r,rev_toqlist. intros q T e3.
                  assert(NoDup (toqlist (rev (FQ u')))) as e4. apply nodup_toqlist. 
                  apply  nodup_rev,nodup_fq2.
                  rewrite NoDup_count_occ' with (decA:= ProgLemmas1.eq_dec) in e4.
                  apply e4 in e3. auto.

                  intros  t hs. rewrite rev_toiqlist in hs.
                  apply in_app_or in hs. destruct hs as[hs|hs];auto.
                  apply in_toiqlistg in hs. inversion hs.
                  exists x. right. left. auto.

                  rewrite rev_toqlist,rev_toiqlist,app_nil_r. 
                  apply  subcnxt_add;auto.
                  assert(LL0=LL0++[]);try rewrite app_nil_r;auto.
                  apply subcntxt_concats with (ll1:=LL0) (ll2:=[])in H1;auto.
                  inversion H1. auto.

                  apply fq_all_qvar. auto.

                  apply split_identr in H10. subst.
                  apply subcntxt_splits with (ll1:=LL3) (ll2:=LL0) in H1;auto.
                  inversion H1. auto. auto.
                  contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d. }
                  { contradict H1. apply hnot5 in H1.
                  inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
                  ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
                  ;try inversion d_disl; inversion d_disr as [j1 d];inversion d. }
                  { apply subcntxt_splits with (ll1:=lL0) (ll2:=LL0) in H1;auto.
                  inversion H1 as [Hl Hr]. 
                  apply subcntxt_splits with (ll1:=LL1) (ll2:=LL3) in Hl;auto.
                  inversion Hl. auto. } 
           ** auto.
              apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
              inversion H1. auto. 
           ** auto.
              contradict H1. apply hnot5 in H1.
              inversion_clear H1 as [j e_dis]; destruct e_dis as [e_disl|e_disr]
              ;try inversion e_disl; destruct e_disr  as [d_disl|d_disr]
              ;try inversion d_disl; inversion d_disr as [j1 d];inversion d.
     ++ auto.
     ++ auto. contradict H1.  apply hnot5 in H1.
        inversion H1. destruct H5.
        inversion H5. destruct H5.
        inversion H5. inversion H5. inversion H7. Optimize Proof.


(*REV Case*)
    * assert(cir15:=H15). clear H15.
      assert(cir16:=H16). clear H16.
      assert(H13:=H11). clear H11.
      exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
      apply app_typed in H4;auto.
      ++ destruct H4.
         -- inversion H4. inversion H5. inversion H7.
            inversion H8. inversion H10.
            inversion H12. inversion H16.
            inversion H24. subst.
            apply split_ident in H19;auto. subst.
            inversion H23. apply REV_LL in H25; auto.
            ** inversion H25. subst.
                apply split_identl in H19;auto. subst.
                apply sub_Circ_inv in H26. 
                +++ destruct H26.
                    { inversion H17. inversion H18.
                    inversion H19. inversion H20.
                    inversion H21. inversion H26.
                    inversion H29. inversion H31.
                    subst.
                    inversion H1'';[.. | simpl in H32; inversion H32]. 
                    subst. 
                    inversion H33. destruct H34.
                    inversion H32. apply split_nil in H37.
                    inversion H37. subst. inversion H41.
                    inversion H27. inversion H48. inversion H50.
                    apply sub_valid_sub_eq in H46;auto.
                    apply sub_valid_sub_eq in H47;auto. subst.
                    inversion H28. inversion H34. inversion H35.
                    inversion H38. inversion H49.
                     inversion H63. inversion H64.
                    apply sub_valid_sub_eq in H61;auto.
                    apply sub_valid_sub_eq in H62;auto. subst.
                    inversion H52. inversion H44.
                     inversion H59. inversion H61.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H56;auto. subst.
                    inversion H11.
                     inversion H55. inversion H60.
                    apply sub_valid_sub_eq in H47;auto.
                    apply sub_valid_sub_eq in H51;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                    apply a_and;auto.
                    apply ss_init.
                    inversion H44.
                    inversion H59. inversion H61.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H56;auto. subst.
                    inversion H11. inversion H46.
                     inversion H65. inversion H73.
                    apply sub_valid_sub_eq in H60;auto.
                    apply sub_valid_sub_eq in H62;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                    apply a_and;auto.
                    apply ss_init.
                    inversion H46.
                     inversion H65. inversion H73.
                    apply sub_valid_sub_eq in H60;auto.
                    apply sub_valid_sub_eq in H62;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCrici;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.

                    inversion H32. apply split_nil in H37.
                    inversion H37. subst. inversion H41.
                    inversion H27. inversion H45. inversion H54.
                    inversion H52.
                    apply sub_valid_sub_eq in H50;auto.
                    apply sub_valid_sub_eq in H51;auto. subst.
                    inversion H28. inversion H34. inversion H35.
                    inversion H38. inversion H50.
                     inversion H65. inversion H66.
                    apply sub_valid_sub_eq in H63;auto.
                    apply sub_valid_sub_eq in H64;auto. subst.
                    inversion H53. inversion H44.
                     inversion H59. inversion H63.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H56;auto. subst.
                    inversion H11. Optimize Proof.
                    inversion H55. inversion H60.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H51;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H44.
                    inversion H59. inversion H63.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H56;auto. subst.
                    inversion H11. inversion H48.
                     inversion H67. inversion H75.
                    apply sub_valid_sub_eq in H60;auto.
                    apply sub_valid_sub_eq in H64;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H48.
                     inversion H67. inversion H75.
                    apply sub_valid_sub_eq in H60;auto.
                    apply sub_valid_sub_eq in H64;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCrici;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H45. inversion H54.
                    inversion H52.
                    apply sub_valid_sub_eq in H50;auto.
                    apply sub_valid_sub_eq in H51;auto. subst.
                    inversion H28. inversion H34. inversion H35.
                    inversion H38. inversion H50.
                    inversion H56.
                     inversion H69. inversion H70.
                    apply sub_valid_sub_eq in H67;auto.
                    apply sub_valid_sub_eq in H68;auto. subst.
                    inversion H53. inversion H44.
                     inversion H65. inversion H63.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H60;auto. subst.
                    inversion H11.
                     inversion H55. inversion H64.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H51;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H44.
                    inversion H65. inversion H63.
                    apply sub_valid_sub_eq in H55;auto.
                    apply sub_valid_sub_eq in H60;auto. subst.
                    inversion H11. inversion H48.
                     inversion H67. inversion H75.
                    apply sub_valid_sub_eq in H66;auto.
                    apply sub_valid_sub_eq in H64;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H48.
                     inversion H67. inversion H75.
                    apply sub_valid_sub_eq in H66;auto.
                    apply sub_valid_sub_eq in H64;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                     (lL:=[]). auto. apply tCrici;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init. Optimize Proof. }
                    { inversion H17. inversion H18.
                    inversion H19. inversion H20.
                    inversion H22. inversion H27.
                    inversion H30. destruct H32.
                    subst. inversion H1'';[.. | simpl in H29; inversion H29].
                    subst. 
                    inversion H31. apply split_nil in H33.
                    inversion H33. subst. inversion H37.
                    inversion H28. inversion H41. inversion H42.
                    inversion H44. inversion H50. 
                     inversion H59. inversion H60.
                    apply sub_valid_sub_eq in H57;auto.
                    apply sub_valid_sub_eq in H58;auto. subst.
                    inversion H52. inversion H32.
                     inversion H48. inversion H51.
                    apply sub_valid_sub_eq in H46;auto.
                    apply sub_valid_sub_eq in H47;auto. subst.
                    inversion H11.
                     inversion H46. inversion H49.
                    apply sub_valid_sub_eq in H36;auto.
                    apply sub_valid_sub_eq in H43;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H32.
                    inversion H48. inversion H51.
                    apply sub_valid_sub_eq in H46;auto.
                    apply sub_valid_sub_eq in H47;auto. subst.
                    inversion H11. inversion H35.
                     inversion H54. inversion H58.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H53;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H35.
                     inversion H54. inversion H58.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H53;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCrici;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H31. apply split_nil in H35.
                    inversion H35. subst. inversion H39.
                    inversion H28. inversion H41. inversion H42.
                    inversion H44. inversion H50. inversion H54.
                    inversion H63. inversion H64.
                    inversion H1'';[..|  simpl in H73; inversion H73]. 
                    subst. 
                    apply sub_valid_sub_eq in H61;auto.
                    apply sub_valid_sub_eq in H62;auto. subst.
                    inversion H52. inversion H32.
                    inversion H48. inversion H51.
                     apply sub_valid_sub_eq in H46;auto.
                    apply sub_valid_sub_eq in H47;auto. subst.
                    inversion H11.
                     inversion H46. inversion H49. Optimize Proof.
                    apply sub_valid_sub_eq in H36;auto.
                    apply sub_valid_sub_eq in H43;auto. subst.
                    Optimize Proof.
                    exists (i2+1+1).
                    Optimize Proof.
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H32.
                    inversion H48. inversion H51.
                    apply sub_valid_sub_eq in H46;auto.
                    apply sub_valid_sub_eq in H47;auto. subst.
                    inversion H11. inversion H34.
                     inversion H56. inversion H60.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H53;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCricl;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init.
                    inversion H34.
                     inversion H56. inversion H60.
                    apply sub_valid_sub_eq in H49;auto.
                    apply sub_valid_sub_eq in H53;auto. subst.
                    exists (i2+1+1).
                    apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B0))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                     (lL:=[]). auto. apply tCrici;auto.
                    apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                     apply a_and;auto.
                    apply ss_init. }
                +++ auto. (*apply h1;auto. apply Circv;auto.*)
                +++ contradict H1.  apply hnot5 in H1.
                    inversion H1. destruct H17.
                    inversion H17. destruct H17.
                    inversion H17. inversion H17. inversion H18.
             ** contradict H1.  apply hnot5 in H1.
                inversion H1. destruct H27.
                inversion H27. destruct H27.
                inversion H27. inversion H27. inversion H28. 
             ** apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H1;auto.
                inversion H1. auto.
          -- inversion H4.
              inversion H5. inversion H7.
              inversion H9. inversion H11.
              inversion H20.
              inversion H21. subst.
              apply split_ident in H16;auto. subst.
              apply REV_LL in H28; auto.
              ** inversion H28. subst. apply split_identl in H24;auto. subst.
                  apply sub_Circ_inv in H29. 
                  +++ destruct H29.
                      { inversion H12. inversion H16.
                      inversion H17. inversion H18.
                      inversion H19. inversion H23.
                      inversion H25. inversion H27.
                      subst.
                      inversion H1'';[..|  simpl in H29; inversion H29]. 
                      subst. 
                      inversion H30. destruct H31.
                      inversion H29. apply split_nil in H34.
                      inversion H34. subst. inversion H38.
                      inversion H24. inversion H45. inversion H47.
                      apply sub_valid_sub_eq in H43;auto.
                      apply sub_valid_sub_eq in H44;auto. subst.
                      inversion H15. inversion H31. inversion H32.
                      inversion H35. inversion H46.
                       inversion H60. inversion H61.
                      apply sub_valid_sub_eq in H58;auto.
                      apply sub_valid_sub_eq in H59;auto. subst.
                      inversion H49. inversion H41.
                       inversion H56. inversion H58.
                      apply sub_valid_sub_eq in H52;auto.
                      apply sub_valid_sub_eq in H53;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                       (lL:=[]). auto. apply tCricl;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      inversion H41.
                      inversion H56. inversion H58.
                      apply sub_valid_sub_eq in H52;auto.
                      apply sub_valid_sub_eq in H53;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x0))))])
                       (lL:=[]). auto. apply tCrici;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init. Optimize Proof.
                      inversion H29. apply split_nil in H34.
                      inversion H34. subst. inversion H38.
                      inversion H15. inversion H41. inversion H42.
                      inversion H44. inversion H52. inversion H54.
                      inversion H61. inversion H63. 
                      apply sub_valid_sub_eq in H59;auto.
                      apply sub_valid_sub_eq in H60;auto. subst.
                      inversion  H50.
                      inversion H43. inversion H46.
                      apply sub_valid_sub_eq in H33;auto.
                      apply sub_valid_sub_eq in H35;auto. subst.
                      inversion H24. inversion H32.
                      inversion H60. inversion H62.
                      apply sub_valid_sub_eq in H56;auto.
                      apply sub_valid_sub_eq in H59;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t x1))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                       (lL:=[]). auto. apply tCricl;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      inversion H31.
                      inversion H49. inversion H51.
                      apply sub_valid_sub_eq in H46;auto.
                      apply sub_valid_sub_eq in H47;auto. subst.
                      inversion H24. inversion H35.
                       inversion H36. inversion H60. inversion H65.
                      apply sub_valid_sub_eq in H56;auto.
                      apply sub_valid_sub_eq in H59;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t x1))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                       (lL:=[]). auto. apply tCricl;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      subst. apply SubAreVal in H24.
                      inversion H24. inversion H35. 
                      inversion H54. 
                       inversion H61. inversion H63.
                      apply sub_valid_sub_eq in H59;auto.
                      apply sub_valid_sub_eq in H60;auto. subst.
                      inversion H50. subst. inversion H24.
                      inversion H32. inversion H58. inversion H59.
                      apply sub_valid_sub_eq in H56;auto.
                      apply sub_valid_sub_eq in H57;auto. subst.
                      inversion H43. inversion H46.
                      apply sub_valid_sub_eq in H33;auto.
                      apply sub_valid_sub_eq in H35;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t x1))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                       (lL:=[]). auto. apply tCrici;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      inversion H31.
                      inversion H49. inversion H51.
                      apply sub_valid_sub_eq in H46;auto.
                      apply sub_valid_sub_eq in H47;auto. subst.
                      inversion H24. inversion H35. inversion H36.
                      inversion H60. inversion H65.
                      apply sub_valid_sub_eq in H59;auto.
                      apply sub_valid_sub_eq in H56;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t x1))) ((toimp (FQ t') (atom_(typeof t' x4))))])
                       (lL:=[]). auto. apply tCrici;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      subst. inversion H32. }
                      { Optimize Proof. inversion H12. inversion H16.
                      inversion H17. inversion H18.
                      inversion H22. inversion H24.
                      inversion H26. destruct H29.
                      subst.
                      inversion H1'';[..|  simpl in H25; inversion H25]. 
                      subst. 
                      inversion H27. apply split_nil in H30.
                      inversion H30. subst. inversion H34.
                      inversion H15. inversion H38. inversion H39.
                      inversion H41. inversion H47. 
                       inversion H57. inversion H56.
                      apply sub_valid_sub_eq in H54;auto.
                      apply sub_valid_sub_eq in H55;auto. subst.
                      inversion H49. inversion H29.
                       inversion H45. inversion H48.
                      apply sub_valid_sub_eq in H43;auto.
                      apply sub_valid_sub_eq in H44;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x3))))])
                       (lL:=[]). auto. apply tCricl;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                      apply a_and;auto.
                      apply ss_init.
                      inversion H29.
                      inversion H45. inversion H48.
                      apply sub_valid_sub_eq in H43;auto.
                      apply sub_valid_sub_eq in H44;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x3))))])
                       (lL:=[]). auto. apply tCrici;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      inversion H27. apply split_nil in H32.
                      inversion H32. subst. inversion H36.
                      inversion H15. inversion H38. inversion H39.
                      inversion H41. inversion H47. inversion H51.
                      inversion H60. inversion H61.
                      inversion H1'' ;[..|  simpl in H70; inversion H70]. 
                      subst. Optimize Proof.
                      apply sub_valid_sub_eq in H58;auto.
                      apply sub_valid_sub_eq in H59;auto. subst.
                      inversion H49. inversion H29.
                      inversion H45. inversion H48.
                       apply sub_valid_sub_eq in H43;auto.
                      apply sub_valid_sub_eq in H44;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x3))))])
                       (lL:=[]). auto. apply tCricl;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init.
                      inversion H29.
                      inversion H45. inversion H48.
                      apply sub_valid_sub_eq in H43;auto.
                      apply sub_valid_sub_eq in H44;auto. subst.
                      exists (i1+1+1).
                      apply s_bc with (iL:=[And (toimp (FQ t) (atom_(typeof t B2))) ((toimp (FQ t') (atom_(typeof t' x3))))])
                       (lL:=[]). auto. apply tCrici;auto.
                      apply ss_general with (lL2:=[]) (lL3:=[]);auto.
                       apply a_and;auto.
                      apply ss_init. } 
                  +++ auto.
                  +++ contradict H1.  apply hnot5 in H1.
                      inversion H1. destruct H12.
                      inversion H12. destruct H12.
                      inversion H12. inversion H12. inversion H16.
               ** contradict H1.  apply hnot5 in H1.
                  inversion H1. destruct H12.
                  inversion H12. destruct H12.
                  inversion H12. inversion H12. inversion H15.
               ** apply subcntxt_splits with (ll1:=LL0) (ll2:=LL3)in H1.
                  inversion H1. auto. auto. 
         ++ contradict H1.  apply hnot5 in H1.
            inversion H1. destruct H5.
            inversion H5. destruct H5.
            inversion H5. inversion H5. inversion H7. Optimize Proof.  

(*FUN app value CASE*)
       * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
         assert(h4:=H4). apply app_typed in H4. 
         ++ destruct H4.
            -- inversion H4. inversion H5. inversion H7.
               inversion H8. inversion H10. inversion H12.
               inversion H17. inversion H25. subst. apply split_ident in H20;auto. subst.
               inversion H24. apply fun_typed2 in H26.
               ** destruct H26.
                  +++ inversion H26. inversion H28.
                      inversion H29. inversion H30. inversion H32.
                      inversion H34. destruct H36.
                      { inversion H36. inversion H38. inversion H46.
                      subst. apply split_ident in H41. subst. inversion H45.
                      assert(proper v);try apply value_proper;auto.
                      apply H23 in H39. inversion H39. inversion H44.
                      inversion H37. apply subtypecontext_subtyping with (B:=x3) (IL':=IL) (LL':=LL0) in H27;auto.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27.
                      apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=typeof v x3 :: lL0) in H52;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H52.
                      unfold P_seq_cut_one in H52. 
                      assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                      apply H52 with (j:=i1+1+1) in H60. simpl in H60.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_weakening_cor  with (il':=IL) in H60.
                      apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x3)
                      (ll':=LL0) (j:=i1+1+1) in H60. simpl in H60.
                      destruct ( ProgLemmas1.eq_dec (typeof v x3) (typeof v x3)).
                      apply seq_exchange_cor with (ll':=lL2) (eq_dec:=ProgLemmas1.eq_dec) in H60;auto.
                      assert(h60:=H60). apply common_eq in H1''. Focus 2. intros. split. 
                      intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in H60;auto. 
                      rewrite H60.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. apply split_ref. apply split_ref.
                      intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h60;auto. 
                      rewrite <- h60. auto. apply split_ref. apply split_ref.
                      rewrite <- H1''. 
                      exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      intros. rewrite count_app with (l:=LL0 ++ lL0) (l1:=LL0) (l2:=lL0) ;auto.
                      apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H20.
                      rewrite H20. omega. contradict n. auto. apply in_eq. auto. auto.
                       contradict n. auto. simpl.
                       destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                      contradict n. auto. auto. apply subcnxt_llg;auto.
                      apply sub_ref,bang_valid;auto. apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. apply sub_trans with (B:=x1);auto.
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. 
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto.  auto. }
                      { inversion H36. inversion H38. inversion H46.
                      subst. apply split_ident in H41. subst. inversion H45.
                      assert(proper v);try apply value_proper;auto.
                      apply H23 in H39. inversion H39. inversion H44.
                      inversion H37.
                      apply subtypecontext_subtyping with (B:=bang x3) (IL':=IL) (LL':=LL0) in H27;auto.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27. 
                      apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x3):: IL))  in H52.
                      apply subtypecontext_subtyping with (B:=A) (IL':=is_qexp v ::(typeof v (bang x3):: IL)) (LL':= lL0) in H52;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H52.
                      unfold P_seq_cut_one in H52. 
                      assert(In (is_qexp v) (is_qexp v::typeof v (bang x3)::IL));
                       try apply in_eq. Optimize Proof.
                      apply H52 with (j:=i1+1+1) in H60. simpl in H60.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      assert(h27':=H27). apply value_bang_emptyll in H27;auto. subst.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H60.
                      unfold P_seq_cut_one in H60. 
                      assert(In (typeof v (bang x3)) (typeof v (bang x3)::IL));
                       try apply in_eq. apply H60 with (j:=i1+1+1) in H18 . simpl in H18.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))).
                      apply split_ident in H20. subst.
                      assert(h18:=H18). 
                      apply common_eq in H1''.  Focus 2. intros. split. 
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite h18.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. apply split_ref. apply split_ref.
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite <- h18. auto. apply split_ref. apply split_ref. subst.
                      exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      auto. contradict n. auto. simpl.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))). auto.
                      contradict n. auto. apply (is_qexp (CON STAR)).
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. 
                      intros. simpl in hnot1. specialize hnot1 with V.
                      apply hnot1. rewrite in_app_iff. right. auto. 
                      contradict n. auto. 
                      simpl.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_weakening_cor  with (il:=IL). auto.
                      intros. apply in_cons. auto. contradict n. auto. auto.
                      apply subcnxt_iig;auto.
                      apply sub_ref;auto. exists x3. auto.
                       apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. apply sub_trans with (B:=x1);auto.
                      intros. inversion H60. subst.
                      apply in_cons,in_eq. inversion H61.
                      subst. apply in_eq.
                      apply in_cons,in_cons. auto.
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. 
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto.  auto. }
                  +++ Optimize Proof. inversion H26. 
                      { inversion H28.
                      inversion H29. inversion H30. inversion H31.
                      inversion H33. destruct H35.
                      inversion H36. inversion H37. inversion H39. inversion H41.
                      apply split_nil in H44. inversion H44. subst. 
                      apply split_identr in H20;auto.
                      subst.
                      inversion H48.
                      assert(proper v);try apply value_proper;auto.
                      apply H22 in H23. inversion H23. inversion H46.
                      inversion H38. apply subtypecontext_subtyping with (B:=x3) (IL':=IL) (LL':=LL0) in H27;auto.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27.
                      apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=[typeof v x3]) in H54;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H54.
                      unfold P_seq_cut_one in H54. 
                      assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                      apply H54 with (j:=i1+1+1) in H60. simpl in H60.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x3)
                      (ll':=LL0) (j:=i1+1+1) in H60. simpl in H60.
                      destruct ( ProgLemmas1.eq_dec (typeof v x3) (typeof v x3)).
                      apply seq_exchange_cor with (ll':=LL0) (eq_dec:=ProgLemmas1.eq_dec) in H60;auto.
                      assert(h60:=H60). 
                      apply common_eq in H1''. subst.
                       exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      intros. split. 
                      intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=LL0) (LL':=LL2)  (q:=x) in H60;auto. 
                      rewrite H60.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=LL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. apply split_ref. apply split_ref.
                      intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=LL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=LL0) (LL':=LL2)  (q:=x) in h60;auto. 
                      rewrite <- h60. auto. apply split_ref. apply split_ref.
                      rewrite app_nil_r. auto. 
                       contradict n. auto. apply in_eq. auto. 
                      contradict n. auto. simpl.  
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      auto. contradict n. auto.
                      auto. apply subcnxt_llg;auto.
                      apply sub_ref,bang_valid;auto. 
                      assert(LSL.split LL2 LL2 []); try apply split_ref.
                      apply subcntxt_splits with (il:=IL) in H60;auto.
                      inversion H60.  auto. inversion H57. apply sub_trans with (B:=x1);auto.
                      auto. inversion H57. auto. auto.

                      inversion H37. inversion H39. inversion H41.  inversion H48.
                      subst. apply split_identr in H20. apply split_nil in H44. subst. 
                      inversion H44.
                      assert(proper v);try apply value_proper;auto. 
                      apply H54 in H20. inversion H20. inversion H42.
                      inversion H38. inversion H55. apply subtypecontext_subtyping with (B:=bang x3) (IL':=IL) (LL':=LL0) in H27;auto.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27. 
                      apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x3):: IL))  in H51.
                      apply subtypecontext_subtyping with (B:=A) (IL':=is_qexp v ::(typeof v (bang x3):: IL)) (LL':= lL0) in H51;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H51.
                      unfold P_seq_cut_one in H51. 
                      assert(In (is_qexp v) (is_qexp v::typeof v (bang x3)::IL));
                       try apply in_eq.
                      apply H51 with (j:=i1+1+1) in H64. simpl in H64.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      assert(h27':=H27). apply value_bang_emptyll in H27;auto. subst.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H64.
                      unfold P_seq_cut_one in H64. 
                      assert(In (typeof v (bang x3)) (typeof v (bang x3)::IL));
                       try apply in_eq. apply H64 with (j:=i1+1+1) in H18 . simpl in H18.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))).
                      assert(h18:=H18). 
                      apply common_eq in H1''. Focus 2. intros. split. 
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                     (ll:=[]) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite h18.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=[]) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. 
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=[]) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=[]) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite <- h18. auto.   subst.
                      exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      contradict n. auto. simpl.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))). auto.
                      contradict n. auto. apply (is_qexp (CON STAR)). 
                      intros. simpl in hnot1. specialize hnot1 with V.
                      apply hnot1. rewrite in_app_iff. right. auto. 
                      contradict n. auto. 
                      simpl. Optimize Proof.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_weakening_cor  with (il:=IL). auto.
                      intros. apply in_cons. auto. contradict n. auto. auto.
                      apply subcnxt_iig;auto.
                      apply sub_ref;auto. exists x3. auto. subst.
                      assert(LSL.split LL2 LL2 []);try apply split_ref.
                       apply subcntxt_splits with (il:=IL) in H18;auto.
                      inversion H18.  auto. apply sub_trans with (B:=x1);auto.
                      intros. inversion H64. subst.
                      apply in_cons,in_eq. inversion H65.
                      subst. apply in_eq.
                      apply in_cons,in_cons. auto. auto. auto. }
                      { inversion H28.
                      inversion H29. inversion H30. inversion H31.
                      inversion H32. destruct H34.
                      inversion H35. inversion H37. inversion H38. inversion H40.
                      inversion H48. subst. apply split_ident in H43. subst. inversion H47.
                      assert(proper v);try apply value_proper;auto.
                      apply H23 in H41. inversion H41. inversion H46.
                       apply subtypecontext_subtyping with (B:=x3) (IL':=IL) (LL':=LL0) in H27;auto.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27.
                      apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=typeof v x3 :: lL0) in H54;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H54.
                      unfold P_seq_cut_one in H54. 
                      assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                      apply H54 with (j:=i1+1+1) in H56. simpl in H56.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_weakening_cor  with (il':=IL) in H56.
                      apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x3)
                      (ll':=LL0) (j:=i1+1+1) in H56. simpl in H56.
                      destruct ( ProgLemmas1.eq_dec (typeof v x3) (typeof v x3)).
                      apply seq_exchange_cor with (ll':=lL2) (eq_dec:=ProgLemmas1.eq_dec) in H56;auto.
                      assert(h56:=H56). 
                      apply common_eq in H1''. Focus 2. intros. split. 
                      intros. assert(h57:=H57). apply fq_all_qvar in H57. inversion H57. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h56;auto. 
                      rewrite h56.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. apply split_ref. apply split_ref.
                      intros. assert(h57:=H57). apply fq_all_qvar in H57. inversion H57. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL2) (LL':=LL2)  (q:=x) in h56;auto. 
                      rewrite <- h56. auto. apply split_ref. apply split_ref. subst.
                      exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      intros. rewrite count_app with (l:=LL0 ++ lL0) (l1:=LL0) (l2:=lL0) ;auto.
                      apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H20.
                      rewrite H20. omega. contradict n. auto. apply in_eq. auto. auto.
                       contradict n. auto. simpl.
                       destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                      contradict n. auto. auto. apply subcnxt_llg;auto.
                      apply sub_ref,bang_valid;auto. apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. inversion H39. subst. auto. apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. 
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto.  auto. inversion H39.
                      subst. apply sub_ref. apply bang_valid;auto. auto.

                      inversion H38. inversion H39. inversion H40. inversion H50.
                      subst. apply split_ident in H45. subst. inversion H49.
                      assert(proper v);try apply value_proper;auto.
                      apply H23 in H41. inversion H41. inversion H46.
                      assert(h27:=H27). apply hastype_isterm_subctx in h27. 
                      apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x3):: IL))  in H54.
                      apply subtypecontext_subtyping with (B:=A) (IL':=is_qexp v ::(typeof v (bang x3):: IL)) (LL':= lL0) in H54;auto.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H54.
                      unfold P_seq_cut_one in H54. 
                      assert(In (is_qexp v) (is_qexp v::typeof v (bang x3)::IL));
                       try apply in_eq.
                      apply H54 with (j:=i1+1+1) in H56. simpl in H56.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      assert(h27':=H27). apply value_bang_emptyll in H27;auto. subst.
                      apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H56.
                      unfold P_seq_cut_one in H56. 
                      assert(In (typeof v (bang x3)) (typeof v (bang x3)::IL));
                       try apply in_eq. apply H56 with (j:=i1+1+1) in H18 . simpl in H18.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))).
                      apply split_ident in H20. subst.
                      assert(h18:=H18). 
                      apply common_eq in H1''. Focus 2. intros. split. 
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite h18.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite <- h4. auto. apply split_ref. apply split_ref.
                      intros. assert(h19:=H19). apply fq_all_qvar in H19. inversion H19. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                      rewrite h4.  apply LL_FQ_ALT_L with 
                      (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                       (ll:=lL0) (LL':=LL2)  (q:=x) in h18;auto. 
                      rewrite <- h18. auto. apply split_ref. apply split_ref.  subst.
                      exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                      auto. contradict n. auto. simpl.
                      destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))). 
                      apply seq_mono_cor with (j:=i1);try omega.
                      auto.
                      contradict n. auto. apply (is_qexp (CON STAR)). 
                       apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto.
                      intros. 
                      Optimize Proof.
                      simpl in hnot1. specialize hnot1 with V.
                      apply hnot1. rewrite in_app_iff. right. auto. 
                      auto.
                      contradict n. auto. 
                      simpl.
                      destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                      apply seq_weakening_cor  with (il:=IL). 
                      apply seq_mono_cor with (j:=i1);try omega.
                      auto.
                      intros. apply in_cons. auto. contradict n. auto. auto.
                      apply subcnxt_iig;auto.
                      apply sub_ref;auto. exists x3. auto.
                       apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. 
                      intros. inversion H56. subst.
                      apply in_cons,in_eq. inversion H57.
                      subst. apply in_eq.
                      apply in_cons,in_cons. auto.
                      apply subcntxt_splits with (il:=IL) in H20;auto.
                      inversion H20.  auto. auto.
                      inversion H29. inversion H30. inversion H31.
                      inversion H32. inversion H34. inversion H36.
                      destruct H38. inversion H38. inversion H39. inversion H38.
                      inversion H39. }
                **  apply subcntxt_splits with (il:=IL) in H20;auto.
                    inversion H20.  auto. 
                **  auto. 
                **  contradict H1.  apply hnot5 in H1.
                    inversion H1. destruct H28.
                    inversion H28. destruct H28.
                    inversion H28. inversion H28. inversion H29.
             -- inversion H4. inversion H5. inversion H7.
                inversion H9. inversion H11. inversion H22. subst.
                apply split_ident in H17;auto. subst.
                inversion H21. apply fun_typed2 in H23.
                ** destruct H23.
                   +++  inversion H23. inversion H25.
                        inversion H26. inversion H27. inversion H29.
                        inversion H31. destruct H33.
                        { inversion H33. inversion H35. inversion H43.
                        subst. apply split_ident in H38. subst. inversion H42.
                        assert(proper v);try apply value_proper;auto.
                        apply H20 in H36. inversion H36. inversion H41.
                        inversion H34. apply subtypecontext_subtyping with (B:=x2) (IL':=IL) (LL':=LL0) in H24;auto.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24.
                        apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=typeof v x2 :: lL0) in H49;auto.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H49.
                        unfold P_seq_cut_one in H49. 
                        assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                        apply H49 with (j:=i1+1+1) in H57. simpl in H57.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_weakening_cor  with (il':=IL) in H57.
                        apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x2)
                        (ll':=LL0) (j:=i1+1+1) in H57. simpl in H57.
                        destruct ( ProgLemmas1.eq_dec (typeof v x2) (typeof v x2)).
                        apply seq_exchange_cor with (ll':=lL2) (eq_dec:=ProgLemmas1.eq_dec) in H57;auto.
                        assert(h57:=H57). 
                        apply common_eq in H1''. Focus 2. intros. split. 
                        intros. assert(h58:=H58). apply fq_all_qvar in H58. inversion H58. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h57;auto. 
                        rewrite h57.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. apply split_ref. apply split_ref.
                        intros. assert(h58:=H58). apply fq_all_qvar in H58. inversion H58. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h57;auto. 
                        rewrite <- h57. auto. apply split_ref. apply split_ref.   subst.
                        exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        intros. rewrite count_app with (l:=LL0 ++ lL0) (l1:=LL0) (l2:=lL0) ;auto.
                        apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H17.
                        rewrite H17. clear. omega. contradict n. auto. apply in_eq. auto. auto.
                         contradict n. auto. simpl.
                         destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                        contradict n. auto. auto. apply subcnxt_llg;auto.
                        apply sub_ref,bang_valid;auto. apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto.  auto. Optimize Proof. }
                        { inversion H33. inversion H35. inversion H43.
                        subst. apply split_ident in H38. subst. inversion H42.
                        assert(proper v);try apply value_proper;auto.
                        apply H20 in H36. inversion H36. inversion H41.
                        inversion H34. apply subtypecontext_subtyping with (B:=bang x2) (IL':=IL) (LL':=LL0) in H24;auto.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24. 
                        apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x2):: IL))  in H49.
                        apply subtypecontext_subtyping with (B:=A) (IL':=is_qexp v ::(typeof v (bang x2):: IL)) (LL':= lL0) in H49;auto.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H49.
                        unfold P_seq_cut_one in H49. 
                        assert(In (is_qexp v) (is_qexp v::typeof v (bang x2)::IL));
                         try apply in_eq.
                        apply H49 with (j:=i1+1+1) in H57. simpl in H57.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        assert(h24':=H24). apply value_bang_emptyll in H24;auto. subst.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H57.
                        unfold P_seq_cut_one in H57. 
                        assert(In (typeof v (bang x2)) (typeof v (bang x2)::IL));
                         try apply in_eq. apply H57 with (j:=i1+1+1) in H12 . simpl in H12.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))).
                        apply split_ident in H17. subst.
                        assert(h12:=H12). 
                        apply common_eq in H1''. Focus 2. intros. split. 
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite h12.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. apply split_ref. apply split_ref.
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite <- h12. auto. apply split_ref. apply split_ref.   subst.
                        exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        auto. contradict n. auto. simpl.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))). auto.
                        contradict n. auto. apply (is_qexp (CON STAR)). 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        intros. simpl in hnot1. specialize hnot1 with V.
                        apply hnot1. rewrite in_app_iff. right. auto. 
                        auto.
                        contradict n. auto. 
                        simpl.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_weakening_cor  with (il:=IL). auto.
                        intros. apply in_cons. auto. contradict n. auto. auto.
                        apply subcnxt_iig;auto.
                        apply sub_ref;auto. exists x2. auto.
                         apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        intros. inversion H57. subst.
                        apply in_cons,in_eq. inversion H58.
                        subst. apply in_eq.
                        apply in_cons,in_cons. auto.
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto.  auto. }
                    +++ Optimize Proof. inversion H23. 
                        { inversion H25.
                        inversion H26. inversion H27. inversion H28.
                        inversion H30. destruct H32.
                        inversion H33. inversion H34. inversion H36. inversion H38.
                        apply split_nil in H41. inversion H41. subst. apply split_identr in H17.
                        subst.
                        inversion H45.
                        assert(proper v);try apply value_proper;auto.
                        apply H19 in H20. inversion H20. inversion H43.
                        inversion H35. apply subtypecontext_subtyping with (B:=x2) (IL':=IL) (LL':=LL0) in H24;auto.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24.
                        apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=[typeof v x2]) in H51;auto.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H51.
                        unfold P_seq_cut_one in H51. 
                        assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                        apply H51 with (j:=i1+1+1) in H57. simpl in H57.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x2)
                        (ll':=LL0) (j:=i1+1+1) in H57. simpl in H57.
                        destruct ( ProgLemmas1.eq_dec (typeof v x2) (typeof v x2)).
                        apply seq_exchange_cor with (ll':=LL0) (eq_dec:=ProgLemmas1.eq_dec) in H57;auto.
                        assert(h57:=H57). 
                        apply common_eq in H1''. Focus 2. intros. split. 
                        intros. assert(h58:=H58). apply fq_all_qvar in H58. inversion H58. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=LL0) (LL':=LL2)  (q:=x) in h57;auto. 
                        rewrite h57.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=LL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. apply split_ref. apply split_ref.
                        intros. assert(h58:=H58). apply fq_all_qvar in H58. inversion H58. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=LL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=LL0) (LL':=LL2)  (q:=x) in h57;auto. 
                        rewrite <- h57. auto. apply split_ref. apply split_ref.   subst.
                        exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        rewrite app_nil_r. auto. 
                         contradict n. auto. apply in_eq. auto. 
                        contradict n. auto. simpl.  
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        auto. contradict n. auto.
                        auto. apply subcnxt_llg;auto.
                        apply sub_ref,bang_valid;auto. 
                        assert(LSL.split LL2 LL2 []); try apply split_ref.
                        apply subcntxt_splits with (il:=IL) in H57;auto.
                        inversion H57.  auto. inversion H54. auto. 
                        auto. inversion H54. auto. auto.
                        Optimize Proof. Optimize Heap.
                        inversion H34. inversion H36. inversion H38.  inversion H45.
                        subst. apply split_identr in H17. apply split_nil in H41. subst. 
                        inversion H41.
                        assert(proper v);try apply value_proper;auto. 
                        apply H51 in H17. inversion H17. inversion H39.
                        inversion H35. inversion H52. apply subtypecontext_subtyping with (B:=bang x2) (IL':=IL) (LL':=LL0) in H24;auto.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24. 
                        apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x2):: IL))  in H48.
                        apply subtypecontext_subtyping with (B:=A) (IL':=is_qexp v ::(typeof v (bang x2):: IL)) (LL':= lL0) in H48;auto.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H48.
                        unfold P_seq_cut_one in H48. 
                        assert(In (is_qexp v) (is_qexp v::typeof v (bang x2)::IL));
                         try apply in_eq.
                        apply H48 with (j:=i1+1+1) in H61. simpl in H61.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        assert(h24':=H24). apply value_bang_emptyll in H24;auto. subst.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H61.
                        unfold P_seq_cut_one in H61. 
                        assert(In (typeof v (bang x2)) (typeof v (bang x2)::IL));
                         try apply in_eq. apply H61 with (j:=i1+1+1) in H12 . simpl in H12.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))).
                        assert(h12:=H12). 
                        apply common_eq in H1''. Focus 2. intros. split. 
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=[]) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite h12.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=[]) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. 
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=[]) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=[]) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite <- h12. auto.   subst.
                        exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        contradict n. auto. simpl. Optimize Proof.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))). auto.
                        contradict n. auto. apply (is_qexp (CON STAR)). 
                        inversion H12.  auto. 
                        intros. simpl in hnot1. specialize hnot1 with V.
                        apply hnot1. rewrite in_app_iff. right. auto. 
                        auto. Optimize Proof.
                        contradict n. auto. 
                        simpl.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_weakening_cor  with (il:=IL). auto.
                        intros. apply in_cons. auto. contradict n. auto. auto.
                        apply subcnxt_iig;auto.
                        apply sub_ref;auto. exists x2. auto. subst.
                        assert(LSL.split LL2 LL2 []);try apply split_ref.
                         apply subcntxt_splits with (il:=IL) in H12;auto.
                        inversion H12.  auto. 
                        intros. inversion H61. subst.
                        apply in_cons,in_eq. inversion H62.
                        subst. apply in_eq.
                        apply in_cons,in_cons. auto. auto. auto. }
                        { Optimize Proof. inversion H25.
                        inversion H26. inversion H27. inversion H28.
                        inversion H29. destruct H31.
                        inversion H32. inversion H34. inversion H35. inversion H37.
                        inversion H45. subst. apply split_ident in H40. subst. inversion H44.
                        assert(proper v);try apply value_proper;auto.
                        apply H20 in H38. inversion H38. inversion H43.
                         apply subtypecontext_subtyping with (B:=x2) (IL':=IL) (LL':=LL0) in H24;auto.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24.
                        apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp v :: IL)) (LL':=typeof v x2 :: lL0) in H51;auto.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H51.
                        unfold P_seq_cut_one in H51. 
                        assert(In (is_qexp v) (is_qexp v::IL)); try apply in_eq.
                        apply H51 with (j:=i1+1+1) in H53. simpl in H53.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_weakening_cor  with (il':=IL) in H53.
                        apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x2)
                        (ll':=LL0) (j:=i1+1+1) in H53. simpl in H53.
                        destruct ( ProgLemmas1.eq_dec (typeof v x2) (typeof v x2)).
                        apply seq_exchange_cor with (ll':=lL2) (eq_dec:=ProgLemmas1.eq_dec) in H53;auto.
                        assert(h53:=H53). 
                        apply common_eq in H1''. Focus 2. intros. split. 
                        intros. assert(h54:=H54). apply fq_all_qvar in H54. inversion H54. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h53;auto. 
                        rewrite h53.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. apply split_ref. apply split_ref.
                        intros. assert(h54:=H54). apply fq_all_qvar in H54. inversion H54. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL2) (LL':=LL2)  (q:=x) in h53;auto. 
                        rewrite <- h53. auto. apply split_ref. apply split_ref.   subst.
                        exists (i4 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        intros. rewrite count_app with (l:=LL0 ++ lL0) (l1:=LL0) (l2:=lL0) ;auto.
                        apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H17.
                        rewrite H17. omega. contradict n. auto. apply in_eq. auto. auto.
                         contradict n. auto. simpl.
                         destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                        contradict n. auto. auto. apply subcnxt_llg;auto.
                        apply sub_ref,bang_valid;auto. 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. inversion H36. subst. apply sub_ref;auto.
                         apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto.   inversion H36.
                        subst. apply sub_ref. apply bang_valid;auto. auto.

                        inversion H35. inversion H36. inversion H37. inversion H47.
                        subst. apply split_ident in H42. subst. inversion H46.
                        assert(proper v);try apply value_proper;auto. Optimize Proof.
                        apply H20 in H38. inversion H38. inversion H43.
                        assert(h24:=H24). apply hastype_isterm_subctx in h24. 
                        apply seq_weakening_cor with (il':=is_qexp v ::(typeof v (bang x2):: IL))  in H51.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H51.
                        unfold P_seq_cut_one in H51. 
                        assert(In (is_qexp v) (is_qexp v::typeof v (bang x2)::IL));
                         try apply in_eq.
                        apply H51 with (j:=i1+1+1) in H53. simpl in H53.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        assert(h24':=H24). apply value_bang_emptyll in H24;auto. subst.
                        apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H53.
                        unfold P_seq_cut_one in H53. 
                        assert(In (typeof v (bang x2)) (typeof v (bang x2)::IL));
                         try apply in_eq. apply H53 with (j:=i1+1+1) in H12 . simpl in H12.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))).
                        apply split_ident in H17. subst.
                        assert(h12:=H12). 
                        apply common_eq in H1'';cycle 1. intros. split. 
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite h12.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite <- h4. auto. apply split_ref. apply split_ref.
                        intros. assert(h16:=H16). apply fq_all_qvar in H16. inversion H16. subst.
                        apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h4;auto. 
                        rewrite h4.  apply LL_FQ_ALT_L with 
                        (a:=(App (Fun E) v)) (a':=(E v)) (ll1:=[])
                         (ll:=lL0) (LL':=LL2)  (q:=x) in h12;auto. 
                        rewrite <- h12. auto. apply split_ref. apply split_ref.   subst.
                        exists (i4  + (i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                        auto. contradict n. auto. simpl.
                        destruct (ProgLemmas1.eq_dec (typeof v (bang x2)) (typeof v (bang x2))). 
                        apply seq_mono_cor with (j:=i1);try omega.
                        auto. Optimize Proof.
                        contradict n. auto. apply (is_qexp (CON STAR)). 
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto.
                        intros. simpl in hnot1. specialize hnot1 with V.
                        apply hnot1. rewrite in_app_iff. right. auto. 
                        auto.
                        contradict n. auto. 
                        simpl.
                        destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                        apply seq_weakening_cor  with (il:=IL). 
                        apply seq_mono_cor with (j:=i1);try omega.
                        auto.
                        intros. apply in_cons. auto. contradict n. auto. auto.
                        intros. inversion H53. subst.
                        apply in_cons,in_eq. inversion H54.
                        subst. apply in_eq.
                        apply in_cons,in_cons. auto.
                        apply subcntxt_splits with (il:=IL) in H17;auto.
                        inversion H17.  auto. auto. Optimize Proof.
                        inversion H26. inversion H27. inversion H28.
                        inversion H29. inversion H31. inversion H33.
                        destruct H35. inversion H35. inversion H36. inversion H35.
                        inversion H36. }
                  ** apply subcntxt_splits with (il:=IL) in H17;auto.
                     inversion H17.  auto. 
                  ** auto.
                  ** contradict H1.  apply hnot5 in H1.
                     inversion H1. destruct H25.
                     inversion H25. destruct H25.
                     inversion H25. inversion H25. inversion H26. 
               ++ auto. 
               ++ contradict H1.  apply hnot5 in H1.
                  inversion H1. destruct H5.
                  inversion H5. destruct H5.
                  inversion H5. inversion H5. inversion H7.
(* App case left *)
    * inversion H3. apply split_nil in H5;auto. 
      inversion H5. subst. assert(i0=i);try omega.
      subst. apply IHi  in H10 ;auto.
      ++ inversion H10. exists (x+1). intros LL1 LL2 A H4 H4' H4'' H4''' H7.
         apply app_typed in H7.
         -- destruct H7.
            ** inversion H7. inversion H8.
               inversion H9. inversion H12.
               inversion H17. inversion H19.
               inversion H21. inversion H29.
               subst. apply split_ident in H24;auto. subst.
               inversion H28. 
               apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=arrow x1 A) in H30;auto. 
               +++ apply seq_mono_cor with (k:= x) in H30;try omega.
                    assert(H24':=H24).
                    apply split_common_r with (ll2:=LL2) (a:=((App E1 E2)))
                    (a':=((App E1' E2))) in H24;auto. 
                    { inversion H24.
                    inversion H32.
                    apply H1 with (A:=arrow x1 A) (LL2:=x3) in H30.
                    inversion H30. exists (x4+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' (arrow x1 A))) (atom_ (typeof E2 x1))]);auto.
                    apply tap. inversion H20.
                    apply SubAreVal in H18. inversion H18. apply vArrow;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0);auto.
                    apply seq_mono_cor with (j:= x4) ;try omega. auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E1) in H34.
                    apply sub_a'_comml with (a'1:=E1') in H34. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H36. repeat rewrite set_union_iff in H36. 
                    destruct H36;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H33;auto.
                    destruct H33.   inversion H33. 
                    contradict H38. auto. 
                    inversion H33. 
                    apply  hnot4 with (q:=q) in H31;auto. 
                    rewrite <-  H31 in H39. contradict H39. auto.
                    intros.
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H24';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in h4'';auto.
                    intros.
                    assert(h24:=H24').
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q0)) T)) in H24';auto.
                    assert(h24':=h24).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h24.
                    assert(t4'':=h4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q0) in h4'';auto. inversion h4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H40.
                    omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. auto.

                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H33;auto.
                    intros. simpl in H35. repeat rewrite set_union_iff in H35.
                     apply not_or in H35. inversion H35. auto. 
                    intros. apply hnot4 with (q:=q) in H30;auto.
                    rewrite H30. auto.
                    intros.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H24';auto.
                    apply in_common_l_T with (q:=q0) (T:=T) in H4'';auto.
                    intros.
                    assert(h24:=H24').
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q0)) T)) in H24';auto.
                    assert(h24':=h24).
                    apply count_split with 
                    (eq_dec:=ProgLemmas1.eq_dec) (a:=(typeof (CON (Qvar q0)) T)) in h24.
                    assert(t4'':=H4''). apply in_common_l_T with (q:=q0) (T:=T) in t4'';auto.
                    subst.
                    apply in_common_l with (q:=q0) in H4'';auto. inversion H4''.
                    subst. rewrite count_occ_In with (eq_dec:=ProgLemmas1.eq_dec) in H36.
                    Optimize Proof. omega.
                    apply subcntxt_splits with (ll1:= LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. auto.
                    intros. simpl in H35. repeat rewrite set_union_iff in H35.
                     apply not_or in H35. inversion H35. auto. 
                    intros. simpl.
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    repeat rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H33.
                    destruct H33.   
                    inversion H33. assert(h35:=H35). apply fq_all_qvar in h35.
                    inversion h35. subst.
                     apply LL_FQ_ALT_R with 
                    (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL1) (ll:=lL2) (LL':=LL2)  (q:=x4) in H31;auto.
                    rewrite <- H31 in H38. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                    apply hnot3 in H22.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H38,H35.
                     omega.
                    inversion H33. auto.
                    apply fq_all_qvar in H35. inversion H35. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                     apply LL_FQ_ALT_R with 
                    (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H31;auto.
                    rewrite <- H31 in H32. repeat rewrite set_union_iff.
                    split;right;auto. }
                +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                +++ apply ArrowSub;auto.
                    apply sub_ref. inversion H20. auto.
             ** inversion H7. inversion H8.
                inversion H9. inversion H16.
                inversion H18. inversion H26.
                subst. apply split_ident in H21;auto. subst.
                inversion H25. 
                apply seq_mono_cor with (k:= x) in H27;try omega.
                assert(H21':=H21).
                apply split_common_r with (ll2:=LL2) (a:=((App E1 E2)))
                (a':=((App E1' E2))) in H21;auto. 
                +++ inversion H21.
                    inversion H29.
                    apply H1 with (A:=arrow x1 A) (LL2:= x2) in H27.
                    { inversion H27. exists (x3+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' (arrow x1 A))) (atom_ (typeof E2 x1))]);auto.
                    apply tap. auto. 
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x2) (LL2:=LL0) ;auto.
                    apply seq_mono_cor with (j:= x3) ;try omega. auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply ss_init. }
                    { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                      inversion H4;auto. }
                    { apply subcntxt_splits with (ll1:=x2) (ll2:=LL0) in H4';auto.
                      inversion H4';auto. }
                    { apply sub_a_comm with (a1:=E1) in H31.
                      apply sub_a'_comml with (a'1:=E1') in H31. auto.
                      intros. assert(h4'':=H4'').
                      apply in_common_r with (q:=q) in H4''. inversion H4''.
                      simpl in H33. repeat rewrite set_union_iff in H33. 
                      destruct H33;auto. 
                      apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                      destruct H30.   inversion H30. 
                      contradict H35. auto. 
                      inversion H30. 
                      apply LL_FQ_ALT_R with 
                      (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL1)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H28;auto.  
                      rewrite <-  H28 in H36. contradict H36. auto. Optimize Proof.
                      apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                      intros. simpl in H32. repeat rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. 
                      intros. apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto. 
                      rewrite H27. auto.
                      intros. simpl in H32. repeat rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. }
                      { intros.
                      simpl in H4'''. specialize H4''' with q.
                      repeat rewrite  set_union_iff in H4'''. 
                      assert(In (typeof q qubit) LL2); auto. 
                      apply unique_in_split with (a:=(typeof q qubit)) in H30.
                      destruct H30.   
                      inversion H30. assert(h32:=H32).
                      apply fq_all_qvar in h32. inversion h32. subst. 
                       apply LL_FQ_ALT_R with 
                      (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL1)
                       (ll:=lL2) (LL':=LL2)  (q:=x3) in H28;auto.
                      rewrite <- H28 in H35. simpl in hnot3. 
                      rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                      specialize hnot3 with (CON (Qvar x3)). 
                      rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                      assert(In (CON (Qvar x3)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                      apply hnot3 in H19.
                      rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H35,H32.
                       omega.
                      inversion H30. auto.
                      apply fq_all_qvar in H32. inversion H32. subst.
                      apply in_common_r  with (q:=x3) in H4'';auto. inversion H4''. auto. }
                  +++ intros. simpl.
                      apply LL_FQ_ALT_R with 
                      (a:=(App E1 E2)) (a':=(App E1' E2)) (ll1:=LL1)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H28;auto.
                      rewrite <- H28 in H29. repeat rewrite set_union_iff.
                      split;right;auto. 
               -- auto.
               -- contradict H4. apply hnot5 in H4. inversion H4. 
                  repeat match goal with
                  | [H: _ \/ _  |- _] => destruct H; [inversion H|..] 
                  |_ => idtac
                  end. inversion H8. inversion H9. Optimize Proof.
            ++ simpl in hnot1. intros.  specialize hnot1 with V. destruct E1;[..|
               rewrite in_app_iff in hnot1;apply hnot1;left; auto|auto];
               simpl in hnot1;simpl in H1; auto. Optimize Heap.   
            ++ simpl in hnot2.
               rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
               rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
               specialize hnot2 with x.
               rewrite count_app with (l1:=FQUC E1') (l2:=FQUC E2) in hnot2;auto.
               assert(In x (FQUC E1' ++ FQUC E2)). rewrite in_app_iff. left. auto.
               apply hnot2 in H4.
               rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
               omega. Optimize Proof.
            ++ simpl in hnot3.
               rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
               rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
               specialize hnot3 with x.
               rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
               assert(In x (FQU E1' ++ FQU E2)). rewrite in_app_iff. left. auto.
               apply hnot3 in H4.
               rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
               omega. 
(*App case right*)
    * inversion H3. apply split_nil in H5. 
      inversion H5. subst. 
      assert(i0=i);try omega.
      subst.
      apply IHi  in H10 ;auto.
      inversion H10.
      exists (x+1). intros LL1 LL2 A H4 H4' H4'' H4''' H7.
      apply app_typed in H7. 
      ++  destruct H7.
          -- inversion H7. inversion H8.
              inversion H9. inversion H12.
              inversion H17. inversion H19.
              inversion H21. inversion H29.
              subst. apply split_ident in H24;auto. subst.
              inversion H28. 
              apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=arrow x1 A) in H30;auto. 
              ** apply seq_mono_cor with (k:= x) in H31;try omega.
                 assert(H24':=H24).
                apply split_common_l with (ll2:=LL2) (a:=((App E1 E2)))
                (a':=((App E1 E2'))) in H24;auto. 
                 +++ inversion H24.
                      inversion H32.
                      apply H1 with (A:=x1) (LL2:=x3) in H31.
                      { inversion H31. exists (x4+x+1+1+1).
                      apply s_bc with (iL:=[])
                      (lL:=[Conj (atom_ (typeof E1 (arrow x1 A))) (atom_ (typeof E2' x1))]);auto.
                      apply tap. inversion H20.
                      apply SubAreVal in H18. inversion H18. apply vArrow;auto.
                      apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                      apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3);auto.
                      apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                      apply seq_mono_cor with (j:= x4) ;try omega. auto.
                      apply ss_init. }
                      { apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                      inversion H4;auto. }
                      { apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto. 
                        inversion H4';auto. }
                      { apply sub_a_comm with (a1:=E2) in H34.
                      apply sub_a'_comml with (a'1:=E2') in H34. auto.
                      intros. assert(h4'':=H4''). 
                      apply in_common_r with (q:=q) in H4''. inversion H4''.
                      Optimize Proof.
                      simpl in H36. repeat rewrite set_union_iff in H36. 
                      destruct H36;auto. 
                      apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H33;auto.
                      destruct H33.   inversion H33. 
                      apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.
                      rewrite <-  H30 in H38. contradict H38. auto.
                      inversion H33. contradict H39. auto.
                      apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H33;auto.
                      intros. simpl in H35. repeat rewrite set_union_iff in H35.
                       apply not_or in H35. inversion H35. auto. 
                      intros. apply LL_FQ_ALT_R with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL1)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H31;auto.
                      rewrite H31. auto.
                      intros. simpl in H35. repeat rewrite set_union_iff in H35.
                      apply not_or in H35. inversion H35. auto. }
                      { intros.
                      simpl in H4'''. specialize H4''' with q.
                      repeat rewrite  set_union_iff in H4'''. 
                      assert(In (typeof q qubit) LL2); auto. 
                      apply unique_in_split with (a:=(typeof q qubit)) in H33.
                      destruct H33.   
                      inversion H33. auto. inversion H33. 
                      assert(h35:=H35).  apply fq_all_qvar in h35. 
                      inversion h35. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=x4) in H30;auto. 
                      rewrite <- H30 in H37. simpl in hnot3. 
                      rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                      specialize hnot3 with (CON (Qvar x4)). 
                      rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                      assert(In (CON (Qvar x4)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                      apply hnot3 in H22.
                      rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H37,H35.
                       omega. Optimize Proof.
                      apply fq_all_qvar in H35. inversion H35. subst.
                      apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                  +++ intros. simpl. repeat rewrite set_union_iff .
                      apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto. 
                       rewrite <- H30 in H32. 
                      split;left;auto.
               ** auto.
                  apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                  inversion H4;auto.
               ** apply ArrowSub;auto.
                  apply sub_ref. inversion H20. auto.
           -- inversion H7. inversion H8.
              inversion H9. inversion H16.
              inversion H18. inversion H26.
              subst. apply split_ident in H21;auto. subst.
              inversion H25. 
              apply seq_mono_cor with (k:= x) in H28;try omega.
              assert(H21':=H21).
              apply split_common_l with (ll2:=LL2) (a:=((App E1 E2)))
              (a':=((App E1 E2'))) in H21;auto. 
              ** inversion H21.
                 inversion H29.
                  apply H1 with (A:=x1) (LL2:=x2) in H28.
                  +++ inversion H28. exists (x3+x+1+1+1).
                      apply s_bc with (iL:=[])
                      (lL:=[Conj (atom_ (typeof E1 (arrow x1 A))) (atom_ (typeof E2' x1))]);auto.
                      { apply tap. auto. } 
                      { apply ss_init. }
                      { apply ss_general with (lL2:=LL2) (lL3:=[]).
                      apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x2);auto.
                      apply seq_mono_cor with (j:= i0) ;try omega. auto.
                      apply seq_mono_cor with (j:= x3) ;try omega. auto.
                      apply ss_init. }
                  +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                      inversion H4;auto. 
                  +++ apply subcntxt_splits with (ll1:=LL1) (ll2:=x2) in H4';auto.
                      inversion H4';auto. 
                  +++ apply sub_a_comm with (a1:=E2) in H31.
                      { apply sub_a'_comml with (a'1:=E2') in H31. auto.
                      intros. assert(h4'':=H4'').
                      apply in_common_r with (q:=q) in H4''. inversion H4''.
                      simpl in H33. repeat rewrite set_union_iff in H33. 
                      destruct H33;auto. 
                      apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                      destruct H30.   inversion H30. 
                      apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto.  
                      rewrite <-  H27 in H35. contradict H35. auto.
                      inversion H30. contradict H36. auto.
                      apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H30;auto.
                      intros. simpl in H32. repeat rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. Optimize Proof. }
                      { intros.
                      apply LL_FQ_ALT_R with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL1)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H28;auto.  
                      rewrite H28. auto. }
                      { intros. simpl in H32. repeat rewrite set_union_iff in H32.
                       apply not_or in H32. inversion H32. auto. } 
                  +++ intros.
                      simpl in H4'''. specialize H4''' with q.
                      repeat rewrite  set_union_iff in H4'''. 
                      assert(In (typeof q qubit) LL2); auto. 
                      apply unique_in_split with (a:=(typeof q qubit)) in H30.
                      { destruct H30.   
                      inversion H30. auto. inversion H30.
                      assert(h32:=H32). 
                      apply fq_all_qvar in h32. inversion h32. subst.
                      apply LL_FQ_ALT_L with 
                      (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=x3) in H27;auto.  
                      rewrite <- H27 in H34. simpl in hnot3. 
                      rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                      specialize hnot3 with (CON (Qvar x3)). 
                      rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                      assert(In (CON (Qvar x3)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                      apply hnot3 in H19.
                      rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H34,H32.
                       omega. Optimize Proof. }
                      { apply fq_all_qvar in H32. inversion H32. subst.
                      apply in_common_r  with (q:=x3) in H4'';auto. inversion H4''. auto. }
               ** intros. simpl. repeat rewrite set_union_iff .
                  apply LL_FQ_ALT_L with 
                  (a:=(App E1 E2)) (a':=(App E1 E2')) (ll1:=LL0)
                       (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto.  
                  rewrite <- H27 in H29. 
                  split;left;auto.
          ++ auto.
          ++ contradict H4. apply hnot5 in H4. inversion H4. 
             repeat match goal with
             | [H: _ \/ _  |- _] => destruct H; [inversion H|..] 
             |_ => idtac
             end. inversion H8. inversion H9. Optimize Proof.
         ++  simpl in hnot1. intros.  specialize hnot1 with V. destruct E1; [..|
              rewrite in_app_iff in hnot1;apply hnot1;right; auto|auto];
              simpl in hnot1;simpl in H1; auto. destruct e;auto. apply hnot1,in_cons;auto.
              simpl in hnot1;simpl in H1; auto. Optimize Heap.

         ++ simpl in hnot2.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
            specialize hnot2 with x.
            rewrite count_app with (l1:=FQUC E1) (l2:=FQUC E2') in hnot2;auto.
            assert(In x (FQUC E1 ++ FQUC E2')). rewrite in_app_iff. right. auto.
            apply hnot2 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
            omega.
         ++ simpl in hnot3.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
            specialize hnot3 with x.
            rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
            assert(In x (FQU E1 ++ FQU E2')). rewrite in_app_iff. right. auto.
            apply hnot3 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
            omega. 
(*Prod Cse right*)
    * inversion H3. apply split_nil in H5. 
      inversion H5. subst. 
      assert(i0=i);try omega.
      subst.
      apply IHi  in H10 ;auto.
      ++ inversion H10.
         exists (x+1+1). intros LL1 LL2 A H4 H4'  H4'' H4''' H7.
         apply prod_typed in H7.
         -- destruct H7.
            ** inversion H7. inversion H8.
               inversion H9. inversion H12.
               inversion H16. inversion H18.
               destruct H20. 
               +++ inversion H20. inversion H22.
                   inversion H24. inversion H32. subst. apply split_ident in H27;auto. subst.
                    inversion H31. 
                    apply seq_mono_cor with (k:= x) in H33;try omega.
                    assert(H26':=H26).
                    apply split_common_l with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1 E2'))) in H26;auto. 
                    { inversion H26.
                    inversion H34.
                    apply H1 with (A:=x2) (LL2:=x3) in H33.
                    inversion H33. exists (x4+x+1+1+1). inversion H19.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1 B1)) (atom_ (typeof E2'  B2))]);auto.
                    apply ttensorl. apply SubAreVal in H40. inversion H40.
                    apply SubAreVal in H42. inversion H42. apply vTensor;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3);auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=B1) in H30;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=B2) in H37;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E2) in H36.
                    apply sub_a'_comml with (a'1:=E2') in H36. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H38. repeat rewrite set_union_iff in H38. 
                    destruct H38;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H35;auto.
                    destruct H35.   inversion H35. 
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.  
                    rewrite  H30 in H38. contradict H38. auto.
                    inversion H35. 
                    contradict H41. auto. 
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H35;auto.
                    intros. simpl in H37. repeat rewrite set_union_iff in H37.
                     apply not_or in H37. inversion H37. auto. 
                    intros.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H33;auto.  
                    rewrite H33. auto.
                    intros. simpl in H37. repeat rewrite set_union_iff in H37.
                     apply not_or in H37. inversion H37. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H35.
                    destruct H35;   inversion H35; auto.
                    assert(h37:=H37).
                    apply fq_all_qvar in h37. inversion h37. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H30;auto.  
                    rewrite <- H30 in H39. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H21.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H37,H39.
                     omega.
                    apply fq_all_qvar in H37. inversion H37. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.  
                    rewrite <- H30 in H34. repeat rewrite set_union_iff.
                    split;left;auto. } Optimize Proof.
                +++ inversion H20. inversion H22.
                    inversion H24. inversion H26.
                    inversion H34. subst. apply split_ident in H29;auto. subst.
                    inversion H33. 
                    apply seq_mono_cor with (k:= x) in H35;try omega.
                    assert(H28':=H28).
                    apply split_common_l with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1 E2'))) in H28;auto. 
                    { inversion H28.
                    inversion H36.
                    apply H1 with (A:=bang x2) (LL2:=x3) in H35.
                    inversion H35. exists (x4+x+1+1+1). inversion H19. inversion H41.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1 B1)) (atom_ (typeof E2'  B2))]);auto.
                    apply ttensorl. apply SubAreVal in H46. inversion H46.
                    apply SubAreVal in H48. inversion H48. apply vTensor;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3);auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=B1) in H32;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. apply BangSub1; auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=B2) in H39;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.  apply BangSub1; auto.
                    apply ss_init. inversion H41.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1 (bang B1))) (atom_ (typeof E2'  (bang B2)))]);auto.
                    apply ttensori. apply sub_not_bang  in H46;auto.
                    apply sub_not_bang in H48;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3);auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL1) (B:=bang B1) in H32;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. apply BangSub2; auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=bang B2) in H39;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.  apply BangSub2; auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E2) in H38.
                    apply sub_a'_comml with (a'1:=E2') in H38. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H40. repeat rewrite set_union_iff in H40. 
                    destruct H40;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H37;auto.
                    destruct H37.   inversion H37.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.   
                    rewrite  H32 in H40. contradict H40. auto.
                    inversion H37. 
                    contradict H43. auto. 
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H37;auto.
                    intros. simpl in H39. repeat rewrite set_union_iff in H39.
                     apply not_or in H39. inversion H39. auto. 
                    intros. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H35;auto.   
                    rewrite H35. auto.
                    intros. simpl in H39. repeat rewrite set_union_iff in H39.
                     apply not_or in H39. inversion H39. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H37.
                    destruct H37;   inversion H37; auto.
                    assert(h39:=H39).
                    apply fq_all_qvar in h39. inversion h39. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H32;auto.   
                    rewrite <- H32 in H41. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H21.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H39,H41.
                     omega.
                    apply fq_all_qvar in H39. inversion H39. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { Optimize Proof. intros. simpl.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.   
                    rewrite <- H32 in H36. repeat rewrite set_union_iff.
                    split;left;auto. }
             ** inversion H7. inversion H8.
                inversion H9. inversion H12.
                destruct H17. 
                +++ inversion H17. inversion H19.
                    inversion H21. inversion H29. subst. apply split_ident in H24;auto. subst.
                    inversion H28. 
                    apply seq_mono_cor with (k:= x) in H30;try omega.
                    assert(H23':=H23).
                    apply split_common_l with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1 E2'))) in H23;auto. 
                    { inversion H23.
                    inversion H31.
                    apply H1 with (A:=x2) (LL2:=x3) in H30.
                    inversion H30. exists (x4+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1 x1)) (atom_ (typeof E2'  x2))]);auto.
                    apply ttensorl. auto. 
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3);auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply seq_mono_cor with (j:= x4) ;try omega. auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E2) in H33.
                    apply sub_a'_comml with (a'1:=E2') in H33. auto.
                    intros. assert(h4'':=H4''). 
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H35. repeat rewrite set_union_iff in H35. 
                    destruct H35;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H32;auto.
                    destruct H32.   inversion H32. 
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto.   
                    rewrite  H27 in H35. contradict H35. auto.
                    inversion H32. 
                    contradict H38. auto. 
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H32;auto.
                    intros. simpl in H34. repeat rewrite set_union_iff in H34.
                     apply not_or in H34. inversion H34. auto. 
                    intros. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.   
                    rewrite H30. auto.
                    intros. simpl in H34. repeat rewrite set_union_iff in H34.
                     apply not_or in H34. inversion H34. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H32.
                    destruct H32;   inversion H32; auto.
                    assert(h34:=H34).
                    apply fq_all_qvar in h34. inversion h34. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H27;auto.   
                    rewrite <- H27 in H36. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                    Optimize Proof. assert(In (CON (Qvar x4)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H18.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H34,H36.
                     omega.
                    apply fq_all_qvar in H34. inversion H34. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto.   
                    rewrite <- H27 in H31. repeat rewrite set_union_iff.
                    split;left;auto.  }
                +++ inversion H17. inversion H19.
                    inversion H21. inversion H23.
                    inversion H31. subst. apply split_ident in H26;auto. subst.
                    inversion H30. 
                    apply seq_mono_cor with (k:= x) in H32;try omega.
                    assert(H25':=H25).
                    apply split_common_l with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1 E2'))) in H25;auto. 
                    { inversion H25.
                    inversion H33.
                    apply H1 with (A:=bang x2) (LL2:=x3) in H32.
                    inversion H32. exists (x4+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1 (bang x1))) (atom_ (typeof E2'  (bang x2)))]);auto.
                    apply ttensori. auto. auto. 
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=LL1) (LL2:=x3) ;auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply seq_mono_cor with (j:= x4) ;try omega. auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=x3) in H4';auto.
                    inversion H4';auto. auto.
                    apply sub_a_comm with (a1:=E2) in H35.
                    apply sub_a'_comml with (a'1:=E2') in H35. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H37. repeat rewrite set_union_iff in H37. 
                    destruct H37;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H34;auto.
                    destruct H34.   inversion H34.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H29;auto.    
                    rewrite  H29 in H37. contradict H37. auto.
                    inversion H34. 
                    contradict H40. auto. Optimize Proof.
                    apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H34;auto.
                    intros. simpl in H36. repeat rewrite set_union_iff in H36.
                     apply not_or in H36. inversion H36. auto. 
                    intros. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.   
                    rewrite H32. auto.
                    intros. simpl in H36. repeat rewrite set_union_iff in H36.
                     apply not_or in H36. inversion H36. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H34.
                    destruct H34;   inversion H34; auto.
                    assert(h36:=H36).
                    apply fq_all_qvar in h36. inversion h36. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H29;auto.   
                    rewrite <- H29 in H38. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1 ++ FQU E2')). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H18.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H36,H38.
                     omega.
                    apply fq_all_qvar in H36. inversion H36. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1 E2')) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H29;auto.   
                    rewrite <- H29 in H33. repeat rewrite set_union_iff.
                    split;left;auto. }
           -- auto.
           -- contradict H4. apply hnot5 in H4. inversion H4. 
              repeat match goal with
               | [H: _ \/ _  |- _] => destruct H; [inversion H|..] 
               |_ => idtac
              end. inversion H8. inversion H9.
        ++ simpl in hnot1. intros. specialize hnot1 with V;rewrite in_app_iff in hnot1;apply hnot1;right; auto.
        ++ Optimize Proof. simpl in hnot2.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
            specialize hnot2 with x.
            rewrite count_app with (l1:=FQUC E1) (l2:=FQUC E2') in hnot2;auto.
            assert(In x (FQUC E1 ++ FQUC E2')). rewrite in_app_iff. right. auto.
            apply hnot2 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
             omega. 
        ++  simpl in hnot3.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
            specialize hnot3 with x.
            rewrite count_app with (l1:=FQU E1) (l2:=FQU E2') in hnot3;auto.
            assert(In x (FQU E1 ++ FQU E2')). rewrite in_app_iff. right. auto.
            apply hnot3 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
             omega. Optimize Proof.
(*Prod case left*)
    * inversion H3. apply split_nil in H5. 
      inversion H5. subst.  
      assert(i0=i);try omega.
      subst. apply IHi  in H10 ;auto.
      ++ inversion H10. exists (x+1+1). intros LL1 LL2 A H4 H4'  H4'' H4''' H7.
         apply prod_typed in H7.
         -- destruct H7.
            ** inversion H7. inversion H8.
               inversion H9. inversion H12.
               inversion H16. inversion H18.
               destruct H20.
               +++ inversion H20. inversion H22.
                   inversion H24. inversion H32. subst. apply split_ident in H27;auto. subst.
                    inversion H31. 
                    apply seq_mono_cor with (k:= x) in H30;try omega.
                    assert(H26':=H26).
                    apply split_common_r with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1' E2))) in H26;auto. 
                    { inversion H26.
                    inversion H34.
                    apply H1 with (A:=x1) (LL2:=x3) in H30.
                    inversion H30. exists (x4+x+1+1+1). inversion H19.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' B1)) (atom_ (typeof E2  B2))]);auto.
                    apply ttensorl. apply SubAreVal in H40. inversion H40.
                    apply SubAreVal in H42. inversion H42. apply vTensor;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0) ;auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=B1) in H37;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL0) (B:=B2) in H33;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E1) in H36.
                    apply sub_a'_comml with (a'1:=E1') in H36. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H38. repeat rewrite set_union_iff in H38. 
                    destruct H38;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H35;auto.
                    destruct H35.   inversion H35. 
                    contradict H40. auto. 
                    inversion H35. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H33;auto.  
                    rewrite <-  H33 in H41. contradict H41. auto.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H35;auto.
                    intros. simpl in H37. repeat rewrite set_union_iff in H37.
                     apply not_or in H37. inversion H37. auto. 
                    intros. 
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.  
                    rewrite H30. auto.
                    intros. simpl in H37. repeat rewrite set_union_iff in H37.
                     apply not_or in H37. inversion H37. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H35.
                    destruct H35;   inversion H35; auto.
                    assert(h37:=H37).
                    apply fq_all_qvar in h37. inversion h37. subst.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H33;auto.  
                    rewrite <- H33 in H40. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H21.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H37,H40.
                     omega.
                    apply fq_all_qvar in H37. inversion H37. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { Optimize Proof. intros. simpl.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H33;auto.  
                    rewrite <- H33 in H34. repeat rewrite set_union_iff.
                    split;right;auto. }
                +++ inversion H20. inversion H22.
                    inversion H24. inversion H26.
                    inversion H34. subst. apply split_ident in H29;auto. subst.
                    inversion H33. 
                    apply seq_mono_cor with (k:= x) in H32;try omega.
                    assert(H28':=H28).
                    apply split_common_r with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1' E2))) in H28;auto. 
                    { inversion H28.
                    inversion H36.
                    apply H1 with (A:=bang x1) (LL2:=x3) in H32.
                    inversion H32. exists (x4+x+1+1+1). inversion H19. inversion H41.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' B1)) (atom_ (typeof E2  B2))]);auto.
                    apply ttensorl. apply SubAreVal in H46. inversion H46.
                    apply SubAreVal in H48. inversion H48. apply vTensor;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0);auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=B1) in H39;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto. apply BangSub1; auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL0) (B:=B2) in H35;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.  apply BangSub1; auto.
                    apply ss_init. inversion H41.
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' (bang B1))) (atom_ (typeof E2  (bang B2)))]);auto.
                    apply ttensori. apply sub_not_bang  in H46;auto.
                    apply sub_not_bang in H48;auto.
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0);auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=x3) (B:=bang B1) in H39;auto. 
                    apply seq_mono_cor with (j:= x4+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto. apply BangSub2; auto.
                    apply subtypecontext_subtyping with (IL':=IL) (LL':=LL0) (B:=bang B2) in H35;auto. 
                    apply seq_mono_cor with (j:= i0+1+1) ;try omega. auto.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.  apply BangSub2; auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. Optimize Proof.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E1) in H38.
                    apply sub_a'_comml with (a'1:=E1') in H38. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H40. repeat rewrite set_union_iff in H40. 
                    destruct H40;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H37;auto.
                    destruct H37.   inversion H37. 
                    contradict H42. auto. 
                    inversion H37. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H35;auto.  
                    rewrite <-  H35 in H43. contradict H43. auto.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H37;auto.
                    intros. simpl in H39. repeat rewrite set_union_iff in H39.
                     apply not_or in H39. inversion H39. auto. 
                    intros. 
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.  
                    rewrite H32. auto.
                    intros. simpl in H39. repeat rewrite set_union_iff in H39.
                     apply not_or in H39. inversion H39. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H37.
                    destruct H37;   inversion H37; auto.
                    assert(h39:=H39).
                    apply fq_all_qvar in h39. inversion h39. subst.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H35;auto.  
                    rewrite <- H35 in H42. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H21.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H39,H42.
                     omega.
                    apply fq_all_qvar in H39. inversion H39. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H35;auto.  
                    rewrite <- H35 in H36. repeat rewrite set_union_iff.
                    split;right;auto. }
             ** inversion H7. inversion H8.
                inversion H9. inversion H12.
                destruct H17.
                +++ inversion H17. inversion H19.
                    inversion H21. inversion H29. subst. apply split_ident in H24;auto. subst.
                    inversion H28. 
                    apply seq_mono_cor with (k:= x) in H27;try omega.
                    assert(H23':=H23).
                    apply split_common_r with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1' E2))) in H23;auto. 
                    { inversion H23.
                    inversion H31.
                    apply H1 with (A:=x1) (LL2:=x3) in H27.
                    inversion H27. exists (x4+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' x1)) (atom_ (typeof E2  x2))]);auto.
                    apply ttensorl. auto. 
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0);auto.
                    apply seq_mono_cor with (j:= x4) ;try omega. auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E1) in H33.
                    apply sub_a'_comml with (a'1:=E1') in H33. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H35. repeat rewrite set_union_iff in H35. 
                    destruct H35;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H32;auto.
                    destruct H32.   inversion H32. 
                    contradict H37. auto. 
                    inversion H32. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.  
                    rewrite <-  H30 in H38. contradict H38. auto.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H32;auto.
                    intros. simpl in H34. repeat rewrite set_union_iff in H34.
                     apply not_or in H34. inversion H34. auto. 
                    intros. 
                    apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H27;auto.  
                    rewrite H27. auto.
                    intros. simpl in H34. repeat rewrite set_union_iff in H34.
                     apply not_or in H34. inversion H34. auto.
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H32.
                    destruct H32;   inversion H32; auto.
                    assert(h34:=H34).
                    apply fq_all_qvar in h34. inversion h34. subst.
                     apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H30;auto.  
                    rewrite <- H30 in H37. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H18.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H34,H37.
                     omega. Optimize Proof.
                    apply fq_all_qvar in H34. inversion H34. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. } 
                    { intros. simpl.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H30;auto.  
                    rewrite <- H30 in H31. repeat rewrite set_union_iff.
                    split;right;auto. }
                +++ inversion H17. inversion H19.
                    inversion H21. inversion H23.
                    inversion H31. subst. apply split_ident in H26;auto. subst.
                    inversion H30. 
                    apply seq_mono_cor with (k:= x) in H29;try omega.
                    assert(H25':=H25).
                    apply split_common_r with (ll2:=LL2) (a:=((Prod E1 E2)))
                    (a':=((Prod E1' E2))) in H25;auto. 
                    { inversion H25.
                    inversion H33.
                    apply H1 with (A:=bang x1) (LL2:=x3) in H29.
                    inversion H29. exists (x4+x+1+1+1).
                    apply s_bc with (iL:=[])
                    (lL:=[Conj (atom_ (typeof E1' (bang x1))) (atom_ (typeof E2  (bang x2)))]);auto.
                    apply ttensori. auto. auto. 
                    apply ss_init. apply ss_general with (lL2:=LL2) (lL3:=[]).
                    apply split_ref. apply m_and with (LL1:=x3) (LL2:=LL0);auto.
                    apply seq_mono_cor with (j:= x4) ;try omega. auto.
                    apply seq_mono_cor with (j:= i0) ;try omega. auto.
                    apply ss_init.
                    apply subcntxt_splits with (ll1:=LL1) (ll2:=LL0) in H4;auto.
                    inversion H4;auto. auto.
                    apply subcntxt_splits with (ll1:=x3) (ll2:=LL0) in H4';auto.
                    inversion H4';auto.
                    apply sub_a_comm with (a1:=E1) in H35.
                    apply sub_a'_comml with (a'1:=E1') in H35. auto.
                    intros. assert(h4'':=H4'').
                    apply in_common_r with (q:=q) in H4''. inversion H4''.
                    simpl in H37. repeat rewrite set_union_iff in H37. 
                    destruct H37;auto. 
                    apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H34;auto.
                    destruct H34.   inversion H34. 
                    contradict H29. auto. 
                    inversion H34. 
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.  
                    rewrite <-  H32 in H40. contradict H40. auto. Optimize Proof.
                    apply ProgLemmas3.in_split_l with (a:=(typeof (CON (Qvar q)) qubit)) in H34;auto.
                    intros. simpl in H36. repeat rewrite set_union_iff in H36.
                     apply not_or in H36. inversion H36. auto. 
                    intros. apply LL_FQ_ALT_L with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL0)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H29;auto.  
                    rewrite H29. auto.
                    intros. simpl in H36. repeat rewrite set_union_iff in H36.
                     apply not_or in H36. inversion H36. auto. 
                    intros.
                    simpl in H4'''. specialize H4''' with q.
                    rewrite  set_union_iff in H4'''. 
                    assert(In (typeof q qubit) LL2); auto. 
                    apply unique_in_split with (a:=(typeof q qubit)) in H34.
                    destruct H34;   inversion H34; auto.
                    assert(h36:=H36).
                    apply fq_all_qvar in h36. inversion h36. subst.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=x4) in H32;auto.  
                    rewrite <- H32 in H39. simpl in hnot3. 
                    rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                    specialize hnot3 with (CON (Qvar x4)). 
                    rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
                    assert(In (CON (Qvar x4)) (FQU E1' ++ FQU E2)). rewrite in_app_iff, FQU_FQ. left. auto.
                     apply hnot3 in H18.
                    rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H36,H39.
                     omega.
                    apply fq_all_qvar in H36. inversion H36. subst.
                    apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                    { intros. simpl.
                    apply LL_FQ_ALT_R with 
                    (a:=(Prod E1 E2)) (a':=(Prod E1' E2)) (ll1:=LL1)
                     (ll:=lL2) (LL':=LL2)  (q:=q) in H32;auto.  
                    rewrite <- H32 in H33. repeat rewrite set_union_iff.
                    split;right;auto. } 
            -- auto.
            -- contradict H4. apply hnot5 in H4. inversion H4. 
               repeat match goal with
               | [H: _ \/ _  |- _] => destruct H; [inversion H|..] 
               |_ => idtac
               end. inversion H8. inversion H9.
         ++ simpl in hnot1. intros. specialize hnot1 with V;rewrite in_app_iff in hnot1;apply hnot1;left; auto.
         ++ simpl in hnot2.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
            specialize hnot2 with x.
            rewrite count_app with (l1:=FQUC E1') (l2:=FQUC E2) in hnot2;auto.
            assert(In x (FQUC E1' ++ FQUC E2)). rewrite in_app_iff. left. auto.
            apply hnot2 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
             omega. 
         ++ simpl in hnot3.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
            rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
            specialize hnot3 with x.
            rewrite count_app with (l1:=FQU E1') (l2:=FQU E2) in hnot3;auto.
            assert(In x (FQU E1' ++ FQU E2)). rewrite in_app_iff. left. auto.
            apply hnot3 in H4.
            rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
            omega. Optimize Proof.
(*let case not val*) 
    * inversion H3. apply split_nil in H5. 
      inversion H5. subst. 
      assert(i0=i);try omega.
      subst.
      apply IHi  in H10 ;auto.
      inversion H10.
      exists (x+1). intros LL1 LL2 A H4 H4' H4'' H4''' H7.
      apply let_typed in H7;auto. 
      ++ inversion H7. inversion H8.
        inversion H9. inversion H14.
        inversion H19. destruct H21.
        -- inversion H21. inversion H22. inversion H24.
            destruct H26. 
            ** Optimize Proof. inversion H26. inversion H34.
                inversion H42. subst. apply split_ident in H37;auto. subst.
                apply seq_mono_cor with (k:= x) in H41;try omega.
                assert(H29':=H29).
                apply split_common_l with (ll2:=LL2) (a:=((Let E b0)))
                (a':=(((Let E b')))) in H29;auto. 
                +++ inversion H29.
                    inversion H27.
                    apply H1 with (A:=tensor x1 x2) (LL2:=x4) in H41;auto.
                    { inversion H41. exists (x5+x+1+1+1+1+1+1+1).
                      apply s_bc with (iL:=[])
                      (lL:=[(All (fun x : qexp => (All( fun y:qexp =>
                                   Imp (is_qexp x) (Imp (is_qexp y) 
                                   (lImp (typeof x x1) (lImp (typeof y x2) (atom_ (typeof (E x y) A)))))))));
                                   atom_ (typeof b' (tensor x1 x2))]);auto.
                      apply tletl;auto. apply ss_init.
                      apply ss_general with (lL2:=lL2) (lL3:=x4);auto.
                      apply s_all;auto. intros. apply s_all;auto.
                      intros. inversion H33. apply H40 in  H32.
                      inversion H32. apply H47 in H35. inversion H35.
                      inversion H52. inversion H58. inversion H64.
                      apply i_imp;auto. apply i_imp;auto. apply l_imp;auto.
                      apply l_imp;auto.
                      apply subtypecontext_subtyping with (IL':=is_qexp x7 :: is_qexp x6 ::IL) 
                      (LL':=typeof x7 x2 :: typeof x6 x1 ::lL2) (B:=A) in H70;auto. 
                      apply seq_mono_cor with (j:= i5+1+1).
                       intros. omega. auto. apply subcnxt_llg;auto.
                      apply sub_ref;auto. apply bang_valid; auto.
                      apply subcnxt_llg;auto.
                      apply sub_ref;auto. apply bang_valid; auto. 
                      subst.
                      apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                      inversion H4;auto.
                      apply ss_general with (lL2:=x4) (lL3:=[]);auto.
                      apply split_ref.
                      apply seq_mono_cor with (j:= x5);auto.
                      clear. omega. apply ss_init. }
                      { subst.
                      apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                      inversion H4;auto. }
                      { apply subcntxt_splits with (ll1:= lL2) (ll2:=x4) in H4';auto.
                      inversion H4';auto. Optimize Heap. }
                      { apply sub_a_comm with (a1:=b0) in H30.
                      apply sub_a'_comml with (a'1:=b') in H30. auto.
                      intros. assert(h4'':=H4'').
                      apply in_common_r with (q:=q) in H4''. inversion H4''.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      rewrite FQ_LET with (i:=0) in H32;auto.
                      inversion H33. assert(h36:=H36). apply H43 in H36.
                      inversion H36. apply H48 in h36. inversion h36.
                      clear H48 H43 H36 h36. inversion H53; clear H53.
                      inversion H56;clear H56. inversion H61;clear H61.
                      simpl in H32. repeat rewrite set_union_iff in H32. 
                      destruct H32;auto. 
                      apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H28;auto.
                      destruct H28.   inversion H28.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                      (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=q) in H66;auto. 
                      rewrite  H66 in H32. inversion H32. inversion H69.
                      inversion  H69. inversion H70. contradict H61. auto.
                      repeat apply common_g;auto. contradict H1.
                      inversion H1. inversion H69.
                      contradict H1.
                      inversion H1. inversion H69.
                       clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. left. auto. apply hnot5 in H1;auto.
                      repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto.
                      inversion H28. 
                      contradict H68. auto. Optimize Proof.
                      apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H28;auto.
                      intros. 
                      simpl in H31. repeat rewrite set_union_iff in H31.
                       apply not_or in H31. inversion H31. auto. 
                      intros. apply LL_FQ_ALT_R with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL2)
                       (ll:= LL1) (LL':= LL2) (q:=q) in H41;auto. 
                      rewrite H41. auto.
                      intros. 
                      simpl in H31. repeat rewrite set_union_iff in H31.
                       apply not_or in H31. inversion H31. auto. }
                      { intros.
                      simpl in H4'''. specialize H4''' with q.
                      rewrite  set_union_iff in H4'''. 
                      assert(In (typeof q qubit) LL2); auto. 
                      apply unique_in_split with (a:=(typeof q qubit)) in H28.
                      destruct H28;   inversion H28; auto.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      inversion H33. assert(h37:=H37). apply H44 in H37.
                      inversion H37. apply H49 in h37. inversion h37.
                      clear H49 H44 H37 h37. inversion H54; clear H54.
                      inversion H57;clear H57. inversion H62;clear H62.
                      assert(h31:=H31). apply fq_all_qvar in h31. inversion h31. subst.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                      (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=x5) in H67;auto. 
                      apply in_cons with (a:=typeof (Var 0) x1) in H35.
                      apply in_cons with (a:=typeof (Var 0) x2) in H35.
                      rewrite  <- H67 in H35. 
                      rewrite FQU_LET with (i:=0) in hnot3;auto.
                      simpl in hnot3. 
                      rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                      specialize hnot3 with (CON (Qvar x5)). 
                      rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                      assert(In (CON (Qvar x5))
                     (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                       apply hnot3 in H37.
                      rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H35,H31.
                      omega.
                      repeat apply common_g;auto. contradict H1.
                      inversion H1. inversion H37.
                      contradict H1.
                      inversion H1. inversion H37.
                       clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. left. auto. apply hnot5 in H1;auto.
                      repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto.
                      Optimize Proof. apply fq_all_qvar in H31. inversion H31. subst.
                      apply in_common_r  with (q:=x5) in H4'';auto. inversion H4''. auto. }
                  +++ intros.  repeat rewrite FQ_LET with (i:=0);auto. simpl.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      inversion H33. assert(h28:=H28). apply H36 in H28.
                      inversion H28. apply H43 in h28. inversion h28.
                      clear H36 H43 H28 h28. inversion H48; clear H48.
                      inversion H51;clear H51. inversion H56;clear H56.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                      (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=q) in H61;auto. 
                      { apply in_cons with (a:=typeof (Var 0) x1) in H27.
                      apply in_cons with (a:=typeof (Var 0) x2) in H27.
                      rewrite <- H61 in H27. repeat rewrite set_union_iff.
                      split;left;auto. } 
                      { repeat apply common_g;auto. contradict H1.
                      inversion H1. inversion H56.
                      contradict H1.
                      inversion H1. inversion H56. }
                      { clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. left. auto. apply hnot5 in H1;auto. }
                      { repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto. }
              ** inversion H26. inversion H34.
                 inversion H42. subst. apply split_ident in H37;auto. subst.
                 apply seq_mono_cor with (k:= x) in H41;try omega.
                 assert(H29':=H29).
                 apply split_common_l with (ll2:=LL2) (a:=((Let E b0)))
                      (a':=(((Let E b')))) in H29;auto. 
                 +++  inversion H29.
                      inversion H27.
                      apply H1 with (A:=bang (tensor x1 x2)) (LL2:=x4) in H41.
                      { inversion H41. exists (x5+x+1+1+1+1+1+1+1).
                      apply s_bc with (iL:=[])
                      (lL:=[(All (fun x : qexp => (All( fun y:qexp =>
                                   Imp (is_qexp x) (Imp (is_qexp y) 
                                   (Imp (typeof x (bang x1)) (Imp (typeof y (bang x2)) (atom_ (typeof (E x y) A)))))))));
                                   atom_ (typeof b' (bang(tensor x1 x2)))]);auto.
                      apply tleti;auto. apply ss_init.
                      apply ss_general with (lL2:=lL2) (lL3:=x4);auto.
                      apply s_all;auto. intros. apply s_all;auto.
                      intros. inversion H33. apply H40 in  H32.
                      inversion H32. apply H47 in H35. inversion H35.
                      inversion H52. inversion H58. inversion H64.
                      repeat apply i_imp;auto. 
                      apply seq_weakening_cor with (il':= is_qexp x7:: typeof x7 (bang x2)::
                      is_qexp x6:: typeof x6 (bang x1)::IL) in H70.
                      apply subtypecontext_subtyping with (IL':=is_qexp x7:: typeof x7 (bang x2)::
                      is_qexp x6:: typeof x6 (bang x1)::IL) 
                      (LL':=lL2) (B:=A) in H70;auto. 
                      apply seq_weakening_cor with (il:= is_qexp x7:: typeof x7 (bang x2)::
                      is_qexp x6:: typeof x6 (bang x1)::IL).
                      apply seq_mono_cor with (j:= i5+1+1).
                       intros. omega. auto. 
                      intros.  inversion H72. subst. 
                      apply in_cons,in_cons, in_eq. 
                      inversion H73. subst. 
                      apply in_eq.
                      inversion H74. subst. 
                      repeat apply in_cons,in_cons, in_cons; apply in_eq. 
                      inversion H75. subst. 
                      apply in_cons,in_eq. 
                      repeat apply in_cons. auto.
                      apply subcnxt_iig;auto.
                      apply sub_ref;auto. exists x2. auto. 
                      apply subcnxt_iig;auto.
                      apply sub_ref;auto. exists x1. auto. 
                      subst.
                      apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                      inversion H4;auto.
                      intros.  inversion H72. subst. 
                      apply in_cons, in_eq. 
                      inversion H73. subst. 
                      apply in_cons,in_cons, in_cons,in_eq. 
                      inversion H74. subst. 
                      apply in_eq. 
                      inversion H75. subst. 
                      apply in_cons,in_cons,in_eq. 
                      apply in_cons,in_cons, in_cons,in_cons. auto.
                      apply ss_general with (lL2:=x4) (lL3:=[]);auto.
                      apply split_ref.
                      apply seq_mono_cor with (j:= x5);auto.
                      clear. omega. apply ss_init. }
                      { subst.
                      apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                      inversion H4;auto. }
                      { apply subcntxt_splits with (ll1:= lL2) (ll2:=x4) in H4';auto.
                      inversion H4';auto. }
                      { apply sub_a_comm with (a1:=b0) in H30.
                      apply sub_a'_comml with (a'1:=b') in H30. auto.
                      intros. assert(h4'':=H4'').
                      apply in_common_r with (q:=q) in H4''. inversion H4''.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      rewrite FQ_LET with (i:=0) in H32;auto.
                      inversion H33. assert(h36:=H36). apply H43 in H36.
                      inversion H36. apply H48 in h36. inversion h36.
                      clear H48 H43 H36 h36. inversion H53; clear H53.
                      inversion H56;clear H56. inversion H61;clear H61.
                      simpl in H32. repeat rewrite set_union_iff in H32. 
                      destruct H32;auto. 
                      apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H28;auto.
                      destruct H28.   inversion H28.
                      apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                      is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H66.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:= LL1) 
                      (LL':=LL2) (q:=q) in H66;auto. 
                      rewrite  H66 in H32.  contradict H61. auto.
                       clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. right. right. exists (bang x2). auto. 
                       inversion H1. exists 0. left. auto.
                      inversion H2. exists 0. right. right. exists (bang x1). auto. 
                      apply hnot5 in H3;auto.
                      repeat apply subcnxt_iig;auto. 
                      apply sub_ref;auto.  exists x2. auto.
                      apply sub_ref;auto.  exists x1. auto.
                      intros.  inversion H69. subst. 
                      apply in_cons, in_eq. 
                      inversion H70. subst. 
                      apply in_cons,in_cons, in_cons, in_eq. 
                      inversion H71. subst. 
                         apply in_eq. 
                      inversion H72. subst. 
                      apply in_eq. 
                      repeat apply in_cons. auto.
                      inversion H28. 
                      contradict H68. auto.
                      apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H28;auto.
                      intros. 
                      simpl in H31. repeat rewrite set_union_iff in H31.
                       apply not_or in H31. inversion H31. auto. 
                      intros. apply LL_FQ_ALT_R with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL2)
                       (ll:= LL1) (LL':= LL2) (q:=q) in H41;auto. 
                      rewrite H41. auto.
                      intros. 
                      simpl in H31. repeat rewrite set_union_iff in H31.
                       apply not_or in H31. inversion H31. auto. }
                      { intros.
                      simpl in H4'''. specialize H4''' with q.
                      rewrite  set_union_iff in H4'''. 
                      assert(In (typeof q qubit) LL2); auto. 
                      apply unique_in_split with (a:=(typeof q qubit)) in H28.
                      destruct H28;   inversion H28; auto.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      inversion H33. assert(h37:=H37). apply H44 in H37.
                      inversion H37. apply H49 in h37. inversion h37.
                      clear H49 H44 H37 h37. inversion H54; clear H54.
                      inversion H57;clear H57. inversion H62;clear H62.
                      assert(h31:=H31). apply fq_all_qvar in h31. inversion h31. subst.
                      apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                      is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H67.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:= LL1) 
                      (LL':= LL2) (q:=x5) in H67;auto. 
                      rewrite  <- H67 in H35. 
                      rewrite FQU_LET with (i:=0) in hnot3;auto.
                      simpl in hnot3. 
                      rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                      specialize hnot3 with (CON (Qvar x5)). 
                      rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                      assert(In (CON (Qvar x5))
                       (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                       apply hnot3 in H37.
                      rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H35,H31.
                       omega.
                       clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. right. right. exists (bang x2). auto. 
                       inversion H1. exists 0. left. auto.
                      inversion H2. exists 0. right. right. exists (bang x1). auto. 
                      apply hnot5 in H3;auto.
                      repeat apply subcnxt_iig;auto. 
                      apply sub_ref;auto.  exists x2. auto.
                      apply sub_ref;auto.  exists x1. auto.
                      intros.  inversion H37. subst. 
                      apply in_cons, in_eq. 
                      inversion H38. subst. 
                      apply in_cons,in_cons, in_cons, in_eq. 
                      inversion H39. subst. 
                         apply in_eq. 
                      inversion H40. subst. 
                      apply in_eq. 
                      repeat apply in_cons. auto.
                      apply fq_all_qvar in H31. inversion H31. subst.
                      apply in_common_r  with (q:=x5) in H4'';auto. inversion H4''. auto. }
                  +++ intros.  repeat rewrite FQ_LET with (i:=0);auto. simpl.
                      assert(proper (Var 0)). apply proper_VAR;auto.
                      inversion H33. assert(h28:=H28). apply H36 in H28.
                      inversion H28. apply H43 in h28. inversion h28.
                      clear H36 H43 H28 h28. inversion H48; clear H48.
                      inversion H51;clear H51. inversion H56;clear H56.
                      apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                      is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H61.
                      apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                       (ll:= LL1) 
                      (LL':= LL2) (q:=q) in H61;auto. 
                      rewrite <- H61 in H27. repeat rewrite set_union_iff.
                      split;left;auto. 
                       clear - hnot5. intros. inversion H. exists 0. left. auto.
                      inversion H0. exists 0. right. right. exists (bang x2). auto. 
                       inversion H1. exists 0. left. auto.
                      inversion H2. exists 0. right. right. exists (bang x1). auto. 
                      apply hnot5 in H3;auto.
                      repeat apply subcnxt_iig;auto. 
                      apply sub_ref;auto.  exists x2. auto.
                      apply sub_ref;auto.  exists x1. auto.
                      intros.  inversion H56. subst. 
                      apply in_cons, in_eq. 
                      inversion H63. subst. 
                      apply in_cons,in_cons, in_cons, in_eq. 
                      inversion H64. subst. 
                         apply in_eq. 
                      inversion H65. subst. 
                      apply in_eq. 
                      repeat apply in_cons. auto.
              -- inversion H21. destruct H23.
                  ** inversion H23. inversion H31.
                     inversion H39. subst. apply split_ident in H34;auto. subst.
                     apply seq_mono_cor with (k:= x) in H38;try omega.
                     assert(H26':=H26).
                     apply split_common_l with (ll2:=LL2) (a:=((Let E b0)))
                     (a':=(((Let E b')))) in H26;auto. 
                     +++  inversion H26.
                          inversion H24.
                          apply H1 with (A:=tensor x1 x2)  (LL2:=x3) in H38.
                          { inversion H38. exists (x4+x+1+1+1+1+1+1+1).
                          apply s_bc with (iL:=[])
                          (lL:=[(All (fun x : qexp => (All( fun y:qexp =>
                                       Imp (is_qexp x) (Imp (is_qexp y) 
                                       (lImp (typeof x x1) (lImp (typeof y x2) (atom_ (typeof (E x y) A)))))))));
                                       atom_ (typeof b' (tensor x1 x2))]);auto.
                          apply tletl;auto. apply ss_init.
                          apply ss_general with (lL2:=lL2) (lL3:=x3);auto.
                          apply s_all;auto. intros. apply s_all;auto.
                          intros. inversion H30. apply H37 in  H29.
                          inversion H29. apply H44 in H32. inversion H32.
                          inversion H49. inversion H55. inversion H61.
                          apply i_imp;auto. apply i_imp;auto. apply l_imp;auto.
                          apply l_imp;auto.
                          apply seq_mono_cor with (j:= i5). intros. omega. auto.
                          apply ss_general with (lL2:=x3) (lL3:=[]);auto.
                          apply split_ref.
                          apply seq_mono_cor with (j:= x4);auto.
                          clear. omega. apply ss_init. }
                          { subst.
                          apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                          inversion H4;auto. }
                          { apply subcntxt_splits with (ll1:= lL2) (ll2:=x3) in H4';auto.
                          inversion H4';auto. }
                          { apply sub_a_comm with (a1:=b0) in H27.
                          apply sub_a'_comml with (a'1:=b') in H27. auto.
                          intros. assert(h4'':=H4'').
                          apply in_common_r with (q:=q) in H4''. inversion H4''.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          rewrite FQ_LET with (i:=0) in H29;auto.
                          inversion H30. assert(h33:=H33). apply H40 in H33.
                          inversion H33. apply H45 in h33. inversion h33.
                          clear H45 H40 H33 h33. inversion H50; clear H50.
                          inversion H53;clear H53. inversion H58;clear H58.
                          simpl in H29. repeat rewrite set_union_iff in H29. 
                          destruct H29;auto. 
                          apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H25;auto.
                          destruct H25.   inversion H25.
                          (*apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                          is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H66.
                          assert(h8:=H31). 
                          apply fq_all_qvar in h31. inversion h31. subst.*)
                          apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                          (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=q) in H63;auto. 
                          rewrite   H63 in H29. contradict H58. inversion H29;
                          inversion H58. inversion H66.   auto. 
                          rewrite FQU_LET with (i:=0) in hnot3;auto.
                          simpl in hnot3. 
                          rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                          specialize hnot3 with (CON (Qvar q)). 
                          rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                          assert(In (CON (Qvar q))
                           (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                          repeat apply common_g;auto. contradict H1.
                          inversion H1. inversion H67.
                          contradict H1.
                          inversion H1. inversion H67.
                           clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. left. auto. apply hnot5 in H1;auto.
                          repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto.
                          inversion H25. 
                          contradict H65. auto.
                          apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H25;auto.
                          intros. 
                          simpl in H28. repeat rewrite set_union_iff in H28.
                           apply not_or in H28. inversion H28. auto. 
                          intros. apply LL_FQ_ALT_R with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL2)
                           (ll:= LL1) (LL':= LL2) (q:=q) in H38;auto. 
                          rewrite H38. auto.
                          intros. 
                          simpl in H28. repeat rewrite set_union_iff in H28.
                           apply not_or in H28. inversion H28. auto. }
                          { intros.
                          simpl in H4'''. specialize H4''' with q.
                          rewrite  set_union_iff in H4'''. 
                          assert(In (typeof q qubit) LL2); auto. 
                          apply unique_in_split with (a:=(typeof q qubit)) in H25.
                          destruct H25;   inversion H25; auto.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          inversion H30. assert(h34:=H34). apply H41 in H34.
                          inversion H34. apply H46 in h34. inversion h34.
                          clear H46 H41 H34 h34. inversion H51; clear H51.
                          inversion H54;clear H54. inversion H59;clear H59.
                          assert(h28:=H28). apply fq_all_qvar in h28. inversion h28. subst.
                          apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                          (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=x4) in H64;auto. 
                          apply in_cons with (a:=typeof (Var 0) x1) in H32.
                          apply in_cons with (a:=typeof (Var 0) x2) in H32.
                          rewrite  <- H64 in H32. 
                          rewrite FQU_LET with (i:=0) in hnot3;auto.
                          simpl in hnot3. 
                          rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                          specialize hnot3 with (CON (Qvar x4)). 
                          rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                          assert(In (CON (Qvar x4))
                           (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                           apply hnot3 in H34.
                          rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H28.
                           omega.
                          repeat apply common_g;auto. contradict H1.
                          inversion H1. inversion H34.
                          contradict H1.
                          inversion H1. inversion H34.
                           clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. left. auto. apply hnot5 in H1;auto.
                          repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto.
                          apply fq_all_qvar in H28. inversion H28. subst.
                          apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                      +++ intros.  repeat rewrite FQ_LET with (i:=0);auto. simpl.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          inversion H30. assert(h25:=H25). apply H33 in H25.
                          inversion H25. apply H40 in h25. inversion h25.
                          clear H33 H40 H25 h25. inversion H45; clear H45.
                          inversion H48;clear H48. inversion H53;clear H53.
                          apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL1) 
                          (LL':=typeof (Var 0) x2 :: typeof (Var 0) x1 :: LL2) (q:=q) in H58;auto. 
                          { apply in_cons with (a:=typeof (Var 0) x1) in H24.
                          apply in_cons with (a:=typeof (Var 0) x2) in H24.
                          rewrite <- H58 in H24. repeat rewrite set_union_iff.
                          split;left;auto. } 
                          { repeat apply common_g;auto. contradict H1.
                          inversion H1. inversion H53.
                          contradict H1.
                          inversion H1. inversion H53. }
                          { clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. left. auto. apply hnot5 in H1;auto. }
                          { repeat apply subcnxt_llg;auto;apply sub_ref,bang_valid;auto. }
                   ** inversion H23. inversion H31.
                      inversion H39. subst. apply split_ident in H34;auto. subst.
                      apply seq_mono_cor with (k:= x) in H38;try omega.
                      assert(H26':=H26).
                      apply split_common_l with (ll2:=LL2) (a:=((Let E b0)))
                      (a':=(((Let E b')))) in H26;auto. 
                      +++ inversion H26.
                          inversion H24.
                          apply H1 with (A:=bang(tensor x1 x2))  (LL2:=x3) in H38.
                          { inversion H38. exists (x4+x+1+1+1+1+1+1+1).
                          apply s_bc with (iL:=[])
                          (lL:=[(All (fun x : qexp => (All( fun y:qexp =>
                                       Imp (is_qexp x) (Imp (is_qexp y) 
                                       (Imp (typeof x (bang x1)) (Imp (typeof y (bang x2)) (atom_ (typeof (E x y) A)))))))));
                                       atom_ (typeof b' (bang (tensor x1 x2)))]);auto.
                          apply tleti;auto. apply ss_init.
                          apply ss_general with (lL2:=lL2) (lL3:=x3);auto.
                          apply s_all;auto. intros. apply s_all;auto.
                          intros. inversion H30. apply H37 in  H29.
                          inversion H29. apply H44 in H32. inversion H32.
                          inversion H49. inversion H55. inversion H61.
                          repeat apply i_imp;auto. 
                          apply seq_mono_cor with (j:= i5). intros. omega. auto.
                          apply ss_general with (lL2:=x3) (lL3:=[]);auto.
                          apply split_ref.
                          apply seq_mono_cor with (j:= x4);auto.
                          clear. omega. apply ss_init. }
                          { subst.
                          apply subcntxt_splits with (ll1:= lL2) (ll2:=lL4) in H4;auto.
                          inversion H4;auto. }
                          { apply subcntxt_splits with (ll1:= lL2) (ll2:=x3) in H4';auto.
                          inversion H4';auto. }
                          { apply sub_a_comm with (a1:=b0) in H27.
                          apply sub_a'_comml with (a'1:=b') in H27. auto.
                          intros. assert(h4'':=H4'').
                          apply in_common_r with (q:=q) in H4''. inversion H4''.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          rewrite FQ_LET with (i:=0) in H29;auto.
                          inversion H30. assert(h33:=H33). apply H40 in H33.
                          inversion H33. apply H45 in h33. inversion h33.
                          clear H45 H40 H33 h33. inversion H50; clear H50.
                          inversion H53;clear H53. inversion H58;clear H58.
                          simpl in H29. repeat rewrite set_union_iff in H29. 
                          destruct H29;auto. 
                          apply unique_in_split with (a:=(typeof (CON (Qvar q)) qubit)) in H25;auto.
                          destruct H25.   inversion H25.
                          apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                          is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H63.
                          apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:= LL1) 
                          (LL':= LL2) (q:=q) in H63;auto. 
                          rewrite   H63 in H29. contradict H58. auto. (*inversion H29;
                          inversion H58. inversion H66.   auto. *)
                          rewrite FQU_LET with (i:=0) in hnot3;auto.
                          simpl in hnot3. 
                          rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                          specialize hnot3 with (CON (Qvar q)). 
                          rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                          assert(In (CON (Qvar q))
                           (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                          repeat apply common_g;auto. 
                           clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. right. right. exists (bang x2). auto.
                          inversion H1. exists 0. left. auto. inversion H2. 
                          exists 0. right. right. exists (bang x1). auto.
                            apply hnot5 in H3;auto.
                          repeat apply subcnxt_iig;auto. 
                          apply sub_ref;auto.  exists x2. auto.
                          apply sub_ref;auto.  exists x1. auto.
                          intros.  inversion H66. subst. 
                          apply in_cons, in_eq. 
                          inversion H67. subst. 
                          apply in_cons,in_cons, in_cons, in_eq. 
                          inversion H68. subst. 
                             apply in_eq. 
                          inversion H69. subst. 
                          apply in_eq. 
                          repeat apply in_cons. auto.
                          inversion H25. 
                          contradict H65. auto.
                          apply ProgLemmas3.in_split_r with (a:=(typeof (CON (Qvar q)) qubit)) in H25;auto.
                          intros. 
                          simpl in H28. repeat rewrite set_union_iff in H28.
                           apply not_or in H28. inversion H28. auto. 
                          intros. apply LL_FQ_ALT_R with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL2)
                           (ll:= LL1) (LL':= LL2) (q:=q) in H38;auto. 
                          rewrite H38. auto.
                          intros. 
                          simpl in H28. repeat rewrite set_union_iff in H28.
                           apply not_or in H28. inversion H28. auto. }
                          { intros.
                          simpl in H4'''. specialize H4''' with q.
                          rewrite  set_union_iff in H4'''. 
                          assert(In (typeof q qubit) LL2); auto. 
                          apply unique_in_split with (a:=(typeof q qubit)) in H25.
                          destruct H25;   inversion H25; auto.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          inversion H30. assert(h34:=H34). apply H41 in H34.
                          inversion H34. apply H46 in h34. inversion h34.
                          clear H46 H41 H34 h34. inversion H51; clear H51.
                          inversion H54;clear H54. inversion H59;clear H59.
                          assert(h28:=H28). apply fq_all_qvar in h28. inversion h28. subst.
                          apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                          is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H64.
                          apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:= LL1) 
                          (LL':= LL2) (q:=x4) in H64;auto. 
                          rewrite  <- H64 in H32. 
                          rewrite FQU_LET with (i:=0) in hnot3;auto.
                          simpl in hnot3. 
                          rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot3.
                          specialize hnot3 with (CON (Qvar x4)). 
                          rewrite count_app with (l1:=FQU (E (Var 0) (Var 0))) (l2:=FQU b') in hnot3;auto.
                          assert(In (CON (Qvar x4))
                           (FQU (E (Var 0) (Var 0)) ++ FQU b')). rewrite in_app_iff, FQU_FQ. left. auto.
                           apply hnot3 in H34.
                          rewrite <- FQU_FQ, count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H32,H28.
                           omega. 
                          clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. right. right. exists (bang x2). auto.
                          inversion H1. exists 0. left. auto. inversion H2. 
                          exists 0. right. right. exists (bang x1). auto.
                            apply hnot5 in H3;auto.
                          repeat apply subcnxt_iig;auto. 
                          apply sub_ref;auto.  exists x2. auto.
                          apply sub_ref;auto.  exists x1. auto.
                          intros.  inversion H34. subst. 
                          apply in_cons, in_eq. 
                          inversion H35. subst. 
                          apply in_cons,in_cons, in_cons, in_eq. 
                          inversion H36. subst. 
                             apply in_eq. 
                          inversion H37. subst. 
                          apply in_eq. repeat apply in_cons. auto.
                          apply fq_all_qvar in H28. inversion H28. subst.
                          apply in_common_r  with (q:=x4) in H4'';auto. inversion H4''. auto. }
                      +++ intros.  repeat rewrite FQ_LET with (i:=0);auto. simpl.
                          assert(proper (Var 0)). apply proper_VAR;auto.
                          inversion H30. assert(h25:=H25). apply H33 in H25.
                          inversion H25. apply H40 in h25. inversion h25.
                          clear H33 H40 H25 h25. inversion H45; clear H45.
                          inversion H48;clear H48. inversion H53;clear H53.
                          apply seq_weakening_cor with (il':= is_qexp (Var 0):: typeof (Var 0) (bang x2)::
                          is_qexp (Var 0):: typeof (Var 0) (bang x1)::IL) in H58.
                          { apply  LL_FQ_ALT_L with  (a:=(Let E b0)) (a':=(Let E b')) (ll1:=lL4)
                           (ll:= LL1) 
                          (LL':=LL2) (q:=q) in H58;auto. 
                          rewrite <- H58 in H24. repeat rewrite set_union_iff.
                          split;left;auto. 
                          clear - hnot5. intros. inversion H. exists 0. left. auto.
                          inversion H0. exists 0. right. right. exists (bang x2). auto.
                          inversion H1. exists 0. left. auto. inversion H2. 
                          exists 0. right. right. exists (bang x1). auto.
                            apply hnot5 in H3;auto.
                          repeat apply subcnxt_iig;auto. 
                          apply sub_ref;auto.  exists x2. auto.
                          apply sub_ref;auto.  exists x1. auto. }
                          { intros.  inversion H53. subst. 
                          apply in_cons, in_eq. 
                          inversion H60. subst. 
                          apply in_cons,in_cons, in_cons, in_eq. 
                          inversion H61. subst. 
                             apply in_eq. 
                          inversion H62. subst. 
                          apply in_eq. repeat apply in_cons. auto. }
     ++ contradict H7. apply hnot5 in H7. inversion H7.
         destruct H8. inversion H8. destruct H8. inversion H8.
         inversion H8. inversion H9.
     ++ simpl in hnot1. intros. 
        specialize hnot1 with V;rewrite in_app_iff in hnot1.
        apply hnot1;right; auto.
     ++ simpl in hnot2.
        rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
        rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
        specialize hnot2 with x.
        rewrite count_app with (l1:=FQUC (lbind 0 (fun x : expr Econ => lambda (E x))))
         (l2:=FQUC b') in hnot2;auto.
        assert(In x (FQUC (lbind 0 (fun x : expr Econ => lambda (E x))) ++ FQUC b')). 
        rewrite in_app_iff. right. auto.
        apply hnot2 in H4.
        rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega.
     ++ apply FQUC_FQU. 
        simpl in hnot2.
        rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
        rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
        specialize hnot2 with x.
        rewrite count_app with (l1:=FQUC (lbind 0 (fun x : expr Econ => lambda (E x))))
         (l2:=FQUC b') in hnot2;auto.
        assert(In x (FQUC (lbind 0 (fun x : expr Econ => lambda (E x)))
         ++ FQUC b')). rewrite in_app_iff. right. auto.
        apply hnot2 in H4.
        rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
         omega.
(*let case value*)
    * exists (i0+1+1). intros LL1 LL2 A H1 H1' H1'' H1''' H4.
      assert(h4:=H4). apply let_typed in H4.
      ++ inversion H4. inversion H5. inversion H7.
         inversion H8. inversion H10. destruct H14. 
         -- inversion H14. inversion H18. inversion H20.
            destruct H22.
            ** inversion H22. inversion H30.
               inversion H38. subst. apply split_ident in H33;auto. 
               subst. clear H4 H5 H7 H8 H10 H14 H18 H20 H38.
               apply prod_typed in H37.
               +++ destruct H37.
                   { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    inversion H10. inversion H18. destruct H23.
                    inversion  H23.  inversion H26.  inversion H28.
                    inversion H38. subst. apply split_ident in H33. subst.
                    inversion H37. 
                    clear H4 H5 H7 H8 H10 H18 H23  H26 H28 H38 H37.
                    inversion H29.
                    assert(proper v);try apply value_proper;auto.
                    apply H10 in H18. inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H38 in H40. inversion H40. inversion H45.
                    inversion H51. inversion H57. inversion H20.
                    apply subtypecontext_subtyping with (B:=x0) (IL':=IL) (LL':=LL0) in H36;auto.
                    assert(h36:=H36). apply hastype_isterm_subctx in h36.
                    apply subtypecontext_subtyping with (B:=x1) (IL':=IL) (LL':=LL3) in H39;auto.
                    assert(h39:=H39). apply hastype_isterm_subctx in h39.
                    apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp u :: is_qexp v :: IL)) (LL':=typeof u x1 :: typeof v x0 :: lL2) in H63;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                    unfold P_seq_cut_one in H63. 
                    assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)); try apply in_eq.
                    apply H63 with (j:=i1+1+1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (is_qexp v) (is_qexp v :: IL)); try apply in_eq.
                    apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x1)
                    (ll':=LL3) (j:=i1+1+1) in H72. simpl in H72.
                    destruct ( ProgLemmas1.eq_dec (typeof u x1) (typeof u x1)).
                    apply seq_exchange_cor with (ll':=typeof v x0 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x0)
                    (ll':=LL0) (j:=i1+1+1) in H72. simpl in H72.
                    destruct ( ProgLemmas1.eq_dec (typeof v x0) (typeof v x0)).
                    apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                    assert(h72:=H72). 
                    apply common_eq in H1''. Focus 2. intros. split. 
                    intros. assert(h73:=H73). apply fq_all_qvar in H73. inversion H73. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h72;auto. 
                    rewrite h72.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h73:=H73). apply fq_all_qvar in H73. inversion H73. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h72;auto. 
                    rewrite <- h72. auto. apply split_ref. apply split_ref.  subst.
                    exists (i7 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                    intros. 
                    rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H25.
                    rewrite H25. 
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H32.
                    rewrite H32.
                    rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                    clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                    assert(forall l (a:atm), a::l = [a]++l);auto. 
                    rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                    rewrite count_app  with (l:=LL3 ++ [typeof v x0] ++ lL2) (l1:=LL3) (l2:=[typeof v x0] ++ lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x0] ++ lL2) (l1:=[typeof v x0]) 
                    (l2:= lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x0] ++ LL3 ++  lL2) (l1:=[typeof v x0] ) (l2:=LL3 ++ lL2) ;auto.
                    rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                    (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                    apply in_eq. auto. contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                    contradict n. auto. auto. contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                    apply seq_weakening_cor with (il:=IL);auto.
                    intros. apply in_cons.
                    auto.
                    contradict n. auto. auto.
                    repeat apply subcnxt_llg;auto.
                    apply SubAreVal in H20. inversion H20. inversion H72.
                    apply sub_ref. auto.
                    apply SubAreVal in H20. inversion H20. inversion H72.
                    apply sub_ref. auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H32;auto.
                    inversion H32.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H32;auto.
                    inversion H32.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H32;auto.
                    inversion H32.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H32;auto.
                    inversion H32.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.  auto. 
                    inversion  H23.  inversion H26.  inversion H28. clear H26 H28. 
                    inversion H32. inversion H38.
                    subst. apply split_ident in H33. subst.
                    inversion H37. 
                    clear H4 H5 H7 H8 H10 H18 H23  H38 H37.
                    inversion H29.
                    assert(proper v);try apply value_proper;auto.
                    apply H10 in H18. clear H4 H10 . inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H38 in H40. inversion H40. inversion H45.
                    inversion H51. inversion H57. inversion H20.
                    apply subtypecontext_subtyping with (B:=x0) (IL':=IL) (LL':=LL0) in H36;auto.
                    assert(h36:=H36). apply hastype_isterm_subctx in h36.
                    apply subtypecontext_subtyping with (B:=x1) (IL':=IL) (LL':=LL3) in H39;auto.
                    assert(h39:=H39). apply hastype_isterm_subctx in h39.
                    apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp u :: is_qexp v :: IL)) (LL':=typeof u x1 :: typeof v x0 :: lL2) in H63;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                    unfold P_seq_cut_one in H63. 
                    assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)) as H71; try apply in_eq.
                    apply H63 with (j:=i1+1+1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (is_qexp v) (is_qexp v :: IL)) as H72; try apply in_eq.
                    apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x1)
                    (ll':=LL3) (j:=i1+1+1) in H72. simpl in H72.
                    destruct ( ProgLemmas1.eq_dec (typeof u x1) (typeof u x1)).
                    apply seq_exchange_cor with (ll':=typeof v x0 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x0)
                    (ll':=LL0) (j:=i1+1+1) in H72. simpl in H72.
                    destruct ( ProgLemmas1.eq_dec (typeof v x0) (typeof v x0)).
                    apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                    assert(h72:=H72). 
                    apply common_eq in H1''. Focus 2. intros. split. 
                    intros. assert(h69:=H69). apply fq_all_qvar in H69. inversion H69. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h72;auto. 
                    rewrite h72.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h69:=H69). apply fq_all_qvar in H69. inversion H69. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x6) in h72;auto. 
                    rewrite <- h72. auto. apply split_ref. apply split_ref.  subst.
                    exists (i7 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                    intros. rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H25.
                    rewrite H25. 
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H28.
                    rewrite H28.
                    rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                    clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                    assert(forall l (a:atm), a::l = [a]++l) as H73;auto. 
                    rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                    rewrite count_app  with (l:=LL3 ++ [typeof v x0] ++ lL2) (l1:=LL3) (l2:=[typeof v x0] ++ lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x0] ++ lL2) (l1:=[typeof v x0]) 
                    (l2:= lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x0] ++ LL3 ++  lL2) (l1:=[typeof v x0] ) (l2:=LL3 ++ lL2) ;auto.
                    rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                    (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                    apply in_eq. auto. contradict n. auto.
                    simpl. 
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                    contradict n. auto. auto. contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                    apply seq_weakening_cor with (il:=IL);auto.
                    intros. apply in_cons.
                    auto.
                    contradict n. auto. auto.
                    repeat apply subcnxt_llg;auto.
                    apply SubAreVal in H66. inversion H66. inversion H70.
                    apply sub_ref. auto.
                    apply SubAreVal in H66. inversion H66. inversion H70.
                    apply sub_ref. auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    inversion H66. apply BangSub1;auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.  auto. 
                    inversion H66. apply BangSub1;auto. auto. }
                    { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    destruct H14.
                    inversion  H14.  inversion H18. inversion H20.  inversion H27.
                    inversion H37. subst. apply split_ident in H32. subst.
                    inversion H36. 
                    clear H4 H5 H7 H8 H14 H18 H20  H27 H37 H33 H36.
                    inversion H29.
                    assert(h34:=H34). apply hastype_isterm_subctx in h34.
                    assert(h35:=H35). apply hastype_isterm_subctx in h35.
                    assert(proper v);try apply value_proper;auto.
                    apply H14 in H18. inversion H18.
                    assert(proper u) as H40;try apply value_proper;auto.
                    apply H37 in H40. inversion H40. inversion H43.
                    inversion H49. inversion H55. 
                    apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp u :: is_qexp v :: IL)) (LL':=typeof u x5 :: typeof v x4 :: lL2) in H61;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H61.
                    unfold P_seq_cut_one in H61. 
                    assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)); try apply in_eq.
                    apply H61 with (j:=i1) in H63. simpl in H63.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                    unfold P_seq_cut_one in H63. 
                    assert(In (is_qexp v) (is_qexp v :: IL)); try apply in_eq.
                    apply H63 with (j:=i1) in H64. simpl in H64.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x5)
                    (ll':=LL3) (j:=i1) in H64. simpl in H64.
                    destruct ( ProgLemmas1.eq_dec (typeof u x5) (typeof u x5)).
                    apply seq_exchange_cor with (ll':=typeof v x4 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H64;auto.
                    apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x4)
                    (ll':=LL0) (j:=i1) in H64. simpl in H64.
                    destruct ( ProgLemmas1.eq_dec (typeof v x4) (typeof v x4)).
                    apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H64;auto.
                    assert(h64:=H64). 
                    apply common_eq in H1''.  Focus 2. intros. split. 
                    intros. assert(h65:=H65). apply fq_all_qvar in H65. inversion H65. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x0) in h64;auto. 
                    rewrite h64.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x0) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h65:=H65). apply fq_all_qvar in H65. inversion H65. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x0) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=LL1) (LL':=LL2)  (q:=x0) in h64;auto. 
                    rewrite <- h64. auto. apply split_ref. apply split_ref. subst.
                    exists (i7 + 1 + 1 + (i1 ) + (i1 )+(i1 ) + (i1 )). auto.
                    intros. rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H25.
                    rewrite H25. 
                    apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H28.
                    rewrite H28.
                    rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                    clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                    assert(forall l (a:atm) , a::l = [a]++l) as H73;auto. 
                    rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                    rewrite count_app  with (l:=LL3 ++ [typeof v x4] ++ lL2) (l1:=LL3) (l2:=[typeof v x4] ++ lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x4] ++ lL2) (l1:=[typeof v x4]) 
                    (l2:= lL2) ;auto.
                    rewrite count_app  with (l:=[typeof v x4] ++ LL3 ++  lL2) (l1:=[typeof v x4] ) (l2:=LL3 ++ lL2) ;auto.
                    rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                    (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                    apply in_eq. auto. contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                    contradict n. auto. auto. contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                    apply seq_weakening_cor with (il:=IL);auto.
                    intros. apply in_cons.
                    auto.
                    contradict n. auto. auto.
                    repeat apply subcnxt_llg;auto. inversion H23.
                    apply sub_ref. auto.
                    inversion H23. apply sub_ref. auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                    apply subcntxt_splits with (il:=IL) in H28;auto.
                    inversion H28.  auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto. auto.
                    inversion  H14. inversion H18. }
                +++ apply subcntxt_splits with (il:=IL) in H25;auto.
                    inversion H25.  auto.
                +++ contradict H1.  apply hnot5 in H1.
                    inversion H1. destruct H4.
                    inversion H4. destruct H4.
                    inversion H4. inversion H4. inversion H5. 
             ** inversion H22. inversion H30.
                inversion H38. subst. apply split_ident in H33;auto. 
                subst. 
                clear H4 H5 H7 H8 H10 H14 H18 H20 H38.
                apply prod_typed in H37.
                +++ destruct H37.
                    { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    inversion H10. inversion H18. destruct H23.
                    inversion  H23. subst. inversion H20.
                    inversion H23.  inversion H26.  inversion H28.
                    clear H26 H28. 
                    inversion H32. inversion H38.
                    subst. apply split_ident in H33. subst.
                    inversion H37. 
                    clear H4 H5 H7 H8 H10 H18 H23  H38 H37.
                    inversion H29.
                    assert(proper v);try apply value_proper;auto.
                    apply H10 in H18. clear H4 H10 . inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H38 in H40. inversion H40. inversion H45.
                    inversion H51. inversion H57. inversion H20.
                    inversion H66.
                    assert(h36':=H36). apply value_bang_emptyll in h36';auto.
                    assert(h39':=H39). apply  value_bang_emptyll in h39';auto. subst.
                     inversion  H28. subst. apply split_ident in H25. subst.
                    apply subtypecontext_subtyping with (B:=bang x0) (IL':=IL) (LL':=[]) in H36;auto.
                    assert(h36:=H36). apply hastype_isterm_subctx in h36.
                    apply subtypecontext_subtyping with (B:=bang x1) (IL':=IL) (LL':=[]) in H39;auto.
                    assert(h39:=H39). apply hastype_isterm_subctx in h39.
                    apply seq_weakening_cor with (il':=is_qexp u :: typeof u (bang x1) ::is_qexp v :: typeof v (bang x0) :: IL) in H63;auto.
                    apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp u :: typeof u (bang x1) ::is_qexp v :: typeof v (bang x0) :: IL)) (LL':= lL2) in H63;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                    unfold P_seq_cut_one in H63. 
                    assert(In (is_qexp u) (is_qexp u  :: typeof u (bang x1) :: is_qexp v :: typeof v (bang x0)  :: IL)) as H71; try apply in_eq.
                    apply H63 with (j:=i1+1+1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (typeof u (bang x1)) (typeof u (bang x1) :: is_qexp v :: typeof v (bang x0)  ::IL)) as H72; try apply in_eq.
                    apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (typeof u (bang x1)) (typeof u (bang x1))).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H72.
                    unfold P_seq_cut_one in H72. 
                    assert(In (is_qexp v) (is_qexp v :: typeof v (bang x0)  :: IL)) as H73; try apply in_eq.
                    apply H72 with (j:=i1+1+1) in H73. simpl in H73.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H73.
                    unfold P_seq_cut_one in H73. 
                    assert(In (typeof v (bang x0)) (typeof v (bang x0)  ::IL)) as H74; try apply in_eq.
                    apply H73 with (j:=i1+1+1) in H74. simpl in H74.
                    destruct (ProgLemmas1.eq_dec (typeof v (bang x0)) (typeof v (bang x0))).
                    assert(h74:=H74). 
                    apply common_eq in H1''.  Focus 2. intros. split. 
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite h74.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite <- h74. auto. apply split_ref. apply split_ref.  subst.
                    exists (i7 + 1 + 1 + (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                    contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (typeof v (bang x0)) (typeof v (bang x0))).
                    auto. contradict n. auto. apply (is_qexp (CON  TRUE)). contradict n.
                    auto. simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                     simpl.
                     destruct (ProgLemmas1.eq_dec (typeof u (bang x1)) (typeof u (bang x1))). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)).
                     repeat apply subcnxt_iig;auto.
                    apply sub_ref. auto. exists x1. auto.
                    apply sub_ref. auto. exists x0. auto.
                    intros. inversion H4. subst. apply in_cons,in_eq.
                    inversion H5. subst. apply in_cons,in_cons,in_cons,in_eq.
                    inversion H7. subst. apply in_eq.
                    inversion H8. subst. apply in_cons,in_cons,in_eq.
                    repeat apply in_cons. auto. assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto. inversion H67. apply BangSub2. auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    inversion H67. apply BangSub2. auto. auto. auto.
                    auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto. inversion H25.
                    apply subcntxt_splits with (il:=IL) in H28;auto. inversion H28.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. right. auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto. inversion H25.
                    apply subcntxt_splits with (il:=IL) in H28;auto. inversion H28.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. left. auto. auto. }
                    { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    destruct H14.
                    inversion  H14.  inversion H18. inversion H14.
                    inversion H18. subst.
                     inversion H20.  inversion H24.
                    inversion H27. inversion H37. subst. apply split_ident in H32. subst.
                    inversion H36.
                    clear H4 H5 H7 H8 H14 H18 H20  H24 H27 H37 H36.
                    inversion H29.
                    assert(proper v);try apply value_proper;auto.
                    apply H14 in H18.  inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H37 in H40. inversion H40. inversion H45.
                    inversion H51. inversion H57. 
                    inversion H36.
                    assert(h38':=H38). apply value_bang_emptyll in h38';auto.
                    assert(h39':=H39). apply value_bang_emptyll in h39';auto. subst.
                     inversion  H32. subst. apply split_ident in H25. subst.
                    assert(h38:=H38). apply hastype_isterm_subctx in h38.
                    assert(h39:=H39). apply hastype_isterm_subctx in h39.
                    apply seq_weakening_cor with (il':=is_qexp u :: typeof u (bang x5) ::is_qexp v :: typeof v (bang x4) :: IL) in H63;auto.
                    apply subtypecontext_subtyping with (B:=A) (IL':=(is_qexp u :: typeof u (bang x5) ::is_qexp v :: typeof v (bang x4) :: IL)) (LL':= lL2) in H63;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                    unfold P_seq_cut_one in H63. 
                    assert(In (is_qexp u) (is_qexp u  :: typeof u (bang x5) :: is_qexp v :: typeof v (bang x4)  :: IL)) as H71; try apply in_eq.
                    apply H63 with (j:=i1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (typeof u (bang x5)) (typeof u (bang x5) :: is_qexp v :: typeof v (bang x4)  ::IL)) as H72; try apply in_eq.
                    apply H71 with (j:=i1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (typeof u (bang x5)) (typeof u (bang x5))).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H72.
                    unfold P_seq_cut_one in H72. 
                    assert(In (is_qexp v) (is_qexp v :: typeof v (bang x4)  :: IL)) as H73; try apply in_eq.
                    apply H72 with (j:=i1) in H73. simpl in H73.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H73.
                    unfold P_seq_cut_one in H73. 
                    assert(In (typeof v (bang x4)) (typeof v (bang x4)  ::IL)) as H74; try apply in_eq.
                    apply H73 with (j:=i1) in H74. simpl in H74.
                    destruct (ProgLemmas1.eq_dec (typeof v (bang x4)) (typeof v (bang x4))).
                    assert(h74:=H74). 
                    apply common_eq in H1''.  Focus 2. intros. split. 
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite h74.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite <- h74. auto. apply split_ref. apply split_ref.  subst.
                    exists (i7 +1+1+ (i1 ) + (i1 )+(i1 ) + (i1 )). auto.
                    contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (typeof v (bang x4)) (typeof v (bang x4))).
                    auto. contradict n. auto. apply (is_qexp (CON  TRUE)). contradict n.
                    auto. simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                     simpl.
                     destruct (ProgLemmas1.eq_dec (typeof u (bang x5)) (typeof u (bang x5))). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)).
                     repeat apply subcnxt_iig;auto.
                    apply sub_ref. auto. exists x5. auto.
                    apply sub_ref. auto. exists x4. auto.
                    intros. inversion H4. subst. apply in_cons,in_eq.
                    inversion H5. subst. apply in_cons,in_cons,in_cons,in_eq.
                    inversion H7. subst. apply in_eq.
                    inversion H8. subst. apply in_cons,in_cons,in_eq.
                    repeat apply in_cons. auto. assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto. auto. 
                    apply subcntxt_splits with (il:=IL) in H25;auto. inversion H25.
                    apply subcntxt_splits with (il:=IL) in H32;auto. inversion H32.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. right. auto.
                    apply subcntxt_splits with (il:=IL) in H25;auto. inversion H25.
                    apply subcntxt_splits with (il:=IL) in H32;auto. inversion H32.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. left. auto. auto. }
                +++ apply subcntxt_splits with (il:=IL) in H25;auto. inversion H25.
                    auto.
                +++ contradict H1.  apply hnot5 in H1.
                    inversion H1. destruct H4.
                    inversion H4. destruct H4.
                    inversion H4. inversion H4. inversion H5. 
        -- inversion H14 as [H18 H22]. assert (H19:=H18).
           destruct H22 as [H22|H22]. 
           ** inversion H22. inversion H28.
              inversion H36. subst. apply split_ident in H31;auto. 
              subst. 
              clear H4 H5 H7 H8 H10 H14 H18 H28 H36.
              apply prod_typed in H35.
              +++ destruct H35.
                  { inversion H4.
                  inversion H5. inversion H7. inversion H8.
                  inversion H10. inversion H18. destruct H21.
                  inversion  H21.  inversion H25.  inversion H28.
                  inversion H36. subst. apply split_ident in H31. subst.
                  inversion H35. assert(h23:=H23).
                  clear H4 H5 H7 H8 H10 H18 H23  H21 H25 H36 H28.
                  inversion H27.
                  assert(proper v);try apply value_proper;auto.
                  apply H10 in H18. inversion H18.
                  assert(proper u);try apply value_proper;auto.
                  apply H36 in H38. inversion H38. inversion H43.
                  inversion H49. inversion H55. inversion H20.
                  apply subtypecontext_subtyping with (B:=x0) (IL':=IL) (LL':=LL0) in H34;auto.
                  assert(h34:=H34). apply hastype_isterm_subctx in h34.
                  apply subtypecontext_subtyping with (B:=x1) (IL':=IL) (LL':=LL3) in H37;auto.
                  assert(h37:=H37). apply hastype_isterm_subctx in h37.
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H61.
                  unfold P_seq_cut_one in H61. 
                  assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)) as H71; try apply in_eq.
                  apply H61 with (j:=i1+1+1) in H71. simpl in H71.
                  destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                  unfold P_seq_cut_one in H71. 
                  assert(In (is_qexp v) (is_qexp v :: IL)) as H72; try apply in_eq.
                  apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                  destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x1)
                  (ll':=LL3) (j:=i1+1+1) in H72. simpl in H72.
                  destruct ( ProgLemmas1.eq_dec (typeof u x1) (typeof u x1)).
                  apply seq_exchange_cor with (ll':=typeof v x0 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x0)
                  (ll':=LL0) (j:=i1+1+1) in H72. simpl in H72.
                  destruct ( ProgLemmas1.eq_dec (typeof v x0) (typeof v x0)).
                  apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                  assert(h72:=H72). 
                  apply common_eq in H1''. Focus 2. intros. split. 
                  intros. assert(h69:=H69). apply fq_all_qvar in H69. inversion H69. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h72;auto. 
                  rewrite h72.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h4;auto. 
                  rewrite <- h4. auto. apply split_ref. apply split_ref.
                  intros. assert(h69:=H69). apply fq_all_qvar in H69. inversion H69. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h4;auto. 
                  rewrite h4.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h72;auto. 
                  rewrite <- h72. auto. apply split_ref. apply split_ref.   subst.
                  exists (i7 + (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                  intros. rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in h23.
                  rewrite h23. 
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H30.
                  rewrite H30.
                  rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                  clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                  assert(forall l (a:atm), a::l = [a]++l) as H73;auto. 
                  rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                  rewrite count_app  with (l:=LL3 ++ [typeof v x0] ++ lL2) (l1:=LL3) (l2:=[typeof v x0] ++ lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x0] ++ lL2) (l1:=[typeof v x0]) 
                  (l2:= lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x0] ++ LL3 ++  lL2) (l1:=[typeof v x0] ) (l2:=LL3 ++ lL2) ;auto.
                  rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                  (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                  apply in_eq. auto. contradict n. auto.
                  simpl.
                   destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                  contradict n. auto. auto. contradict n. auto.
                  simpl.
                   destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                  apply seq_weakening_cor with (il:=IL);auto.
                  intros. apply in_cons.
                  auto.
                  contradict n. auto. auto.
                  repeat apply subcnxt_llg;auto.
                  apply subcntxt_splits with (il:=IL) in H30;auto.
                  inversion H30.  auto.
                  apply subcntxt_splits with (il:=IL) in h23;auto.
                  inversion h23.  auto.
                  apply subcntxt_splits with (il:=IL) in H30;auto.
                  inversion H30.  auto.
                  apply subcntxt_splits with (il:=IL) in h23;auto.
                  inversion h23.  auto.
                  apply subcntxt_splits with (il:=IL) in H30;auto.
                  inversion H30.  auto.
                  apply subcntxt_splits with (il:=IL) in h23;auto.
                  inversion h23.  auto.
                  apply subcntxt_splits with (il:=IL) in H30;auto.
                  inversion H30.  auto.
                  apply subcntxt_splits with (il:=IL) in h23;auto.
                  inversion h23.  auto.
                  auto. 
                  inversion  H21.  inversion H25.  inversion H28. clear H25 H28. 
                  inversion H30. inversion H36.
                  subst. apply split_ident in H31. subst.
                  inversion H35. 
                  clear H4 H5 H7 H8 H10 H18 H21  H36 H35.
                  inversion H27.
                  assert(proper v);try apply value_proper;auto.
                  apply H10 in H18. clear H4 H10 . inversion H18.
                  assert(proper u);try apply value_proper;auto.
                  apply H36 in H38. inversion H38. inversion H43.
                  inversion H49. inversion H55. 
                  apply subtypecontext_subtyping with (B:=x0) (IL':=IL) (LL':=LL0) in H34;auto.
                  assert(h34:=H34). apply hastype_isterm_subctx in h34.
                  apply subtypecontext_subtyping with (B:=x1) (IL':=IL) (LL':=LL3) in H37;auto.
                  assert(h37:=H37). apply hastype_isterm_subctx in h37.
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H61.
                  unfold P_seq_cut_one in H61. 
                  assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)) as H71; try apply in_eq.
                  apply H61 with (j:=i1+1+1) in H71. simpl in H71.
                  destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                  unfold P_seq_cut_one in H71. 
                  assert(In (is_qexp v) (is_qexp v :: IL)) as H72; try apply in_eq.
                  apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                  destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x1)
                  (ll':=LL3) (j:=i1+1+1) in H72. simpl in H72.
                  destruct ( ProgLemmas1.eq_dec (typeof u x1) (typeof u x1)).
                  apply seq_exchange_cor with (ll':=typeof v x0 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x0)
                  (ll':=LL0) (j:=i1+1+1) in H72. simpl in H72.
                  destruct ( ProgLemmas1.eq_dec (typeof v x0) (typeof v x0)).
                  apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H72;auto.
                  assert(h72:=H72). 
                  apply common_eq in H1''. Focus 2. intros. split. 
                  intros. assert(h63:=H63). apply fq_all_qvar in H63. inversion H63. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h72;auto. 
                  rewrite h72.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h4;auto. 
                  rewrite <- h4. auto. apply split_ref. apply split_ref.
                  intros. assert(h63':=H63). apply fq_all_qvar in H63. inversion H63. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h4;auto. 
                  rewrite h4.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x5) in h72;auto. 
                  rewrite <- h72. auto. apply split_ref. apply split_ref.  subst.
                  exists (i7  + (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                  intros. rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H23.
                  rewrite H23. 
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H28.
                  rewrite H28.
                  rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                  clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                  assert(forall l (a:atm), a::l = [a]++l) as H73;auto. 
                  rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                  rewrite count_app  with (l:=LL3 ++ [typeof v x0] ++ lL2) (l1:=LL3) (l2:=[typeof v x0] ++ lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x0] ++ lL2) (l1:=[typeof v x0]) 
                  (l2:= lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x0] ++ LL3 ++  lL2) (l1:=[typeof v x0] ) (l2:=LL3 ++ lL2) ;auto.
                  rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                  (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                  apply in_eq. auto. contradict n. auto.
                  simpl. 
                   destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                  contradict n. auto. auto. contradict n. auto.
                  simpl.
                   destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                  apply seq_weakening_cor with (il:=IL);auto.
                  intros. apply in_cons.
                  auto.
                  contradict n. auto. auto.
                  repeat apply subcnxt_llg;auto.
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.
                  inversion H20. inversion H64. apply BangSub1;auto.
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.  auto. 
                  inversion H20. inversion H64. apply BangSub1;auto. auto. }
                  { inversion H4.
                  inversion H5. inversion H7. inversion H8.
                  destruct H14.
                  inversion  H14.  inversion H18. inversion H20.  inversion H26.
                  inversion H35. subst. apply split_ident in H30. subst.
                  inversion H34. 
                  clear H4 H5 H7 H8 H14 H18 H20  H26 H35 H30 H34.
                  inversion H27.
                  assert(h32:=H32). apply hastype_isterm_subctx in h32.
                  assert(h33:=H33). apply hastype_isterm_subctx in h33.
                  assert(proper v);try apply value_proper;auto.
                  apply H14 in H18. inversion H18.
                  assert(proper u) as H40;try apply value_proper;auto.
                  apply H35 in H40. inversion H40. inversion H41.
                  inversion H47. inversion H53. 
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H59.
                  unfold P_seq_cut_one in H59. 
                  assert(In (is_qexp u) (is_qexp u :: is_qexp v :: IL)) as H63; try apply in_eq.
                  apply H59 with (j:=i1) in H63. simpl in H63.
                  destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                  apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H63.
                  unfold P_seq_cut_one in H63. 
                  assert(In (is_qexp v) (is_qexp v :: IL)) as H64; try apply in_eq.
                  apply H63 with (j:=i1) in H64. simpl in H64.
                  destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof u x4)
                  (ll':=LL3) (j:=i1) in H64. simpl in H64.
                  destruct ( ProgLemmas1.eq_dec (typeof u x4) (typeof u x4)).
                  apply seq_exchange_cor with (ll':=typeof v x3 :: LL3 ++  lL2) (eq_dec:=ProgLemmas1.eq_dec) in H64;auto.
                  apply seq_cut_linear_cor with (eq_dec:=ProgLemmas1.eq_dec) (a:=typeof v x3)
                  (ll':=LL0) (j:=i1) in H64. simpl in H64.
                  destruct ( ProgLemmas1.eq_dec (typeof v x3) (typeof v x3)).
                  apply seq_exchange_cor with (ll':=LL1) (eq_dec:=ProgLemmas1.eq_dec) in H64;auto.
                  assert(h64:=H64). 
                  apply common_eq in H1''. Focus 2. intros. split. 
                  intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x0) in h64;auto. 
                  rewrite h64.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x0) in h4;auto. 
                  rewrite <- h4. auto. apply split_ref. apply split_ref.
                  intros. assert(h61:=H61). apply fq_all_qvar in H61. inversion H61. subst.
                  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x0) in h4;auto. 
                  rewrite h4.  apply LL_FQ_ALT_L with 
                  (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                   (ll:=LL1) (LL':=LL2)  (q:=x0) in h64;auto. 
                  rewrite <- h64. auto. apply split_ref. apply split_ref.  subst.
                  exists (i7 +  (i1 ) + (i1 )+(i1 ) + (i1 )). auto.
                  intros. rewrite count_app with (l:=LL0 ++ LL3 ++lL2) (l1:=LL0++LL3) (l2:=lL2) ;auto.
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H23.
                  rewrite H23. 
                  apply count_split with (eq_dec:=ProgLemmas1.eq_dec) (a:=a) in H28.
                  rewrite H28.
                  rewrite count_app with (l:=LL0 ++ LL3) (l1:=LL0) (l2:=LL3) ;auto.
                  clear. omega. apply app_assoc. contradict n. auto. apply in_eq. auto. 
                  assert(forall l (a:atm) , a::l = [a]++l) as H73;auto. 
                  rewrite H73. rewrite H73 with (l:=LL3++lL2). intros.  
                  rewrite count_app  with (l:=LL3 ++ [typeof v x3] ++ lL2) (l1:=LL3) (l2:=[typeof v x3] ++ lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x3] ++ lL2) (l1:=[typeof v x3]) 
                  (l2:= lL2) ;auto.
                  rewrite count_app  with (l:=[typeof v x3] ++ LL3 ++  lL2) (l1:=[typeof v x3] ) (l2:=LL3 ++ lL2) ;auto.
                  rewrite count_app  with (l:=LL3 ++ lL2) (l1:=LL3) 
                  (l2:= lL2) ;auto. clear. omega. contradict n. auto.
                  apply in_eq. auto. contradict n. auto.
                  simpl.
                   destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto.
                  contradict n. auto. auto. contradict n. auto.
                  simpl.
                   destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). 
                  apply seq_weakening_cor with (il:=IL);auto.
                  intros. apply in_cons.
                  auto.
                  contradict n. auto. auto.
                  repeat apply subcnxt_llg;auto. 
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.
                  apply subcntxt_splits with (il:=IL) in H28;auto.
                  inversion H28.  auto.
                  apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto. auto.
                  inversion  H14. inversion H18. }
              +++ apply subcntxt_splits with (il:=IL) in H23;auto.
                  inversion H23.  auto.
              +++ contradict H1.  apply hnot5 in H1.
                  inversion H1. destruct H4.
                  inversion H4. destruct H4.
                  inversion H4. inversion H4. inversion H5. 
           ** inversion H22. inversion H28.
              inversion H36. subst. apply split_ident in H31;auto. 
              subst. 
              clear H4 H5 H7 H8 H10 H14 H18 H22 H28 H36.
              apply prod_typed in H35. 
              +++ destruct H35.
                  { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    inversion H10. inversion H18. destruct H21.
                    inversion  H21. subst. inversion H20.
                    inversion H21.  inversion H24.  inversion H26.
                    clear H26 H24. 
                    inversion H29. inversion H35.
                    subst. apply split_ident in H30. subst.
                    inversion H34. 
                    clear H4 H5 H7 H8 H10 H18 H21  H35 H34.
                    inversion H27.
                    assert(proper v);try apply value_proper;auto.
                    apply H10 in H18. clear H4 H10 . inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H35 in H37. inversion H37. inversion H42.
                    inversion H48. inversion H54. inversion H20.
                    inversion H63.
                    assert(h33':=H33). apply value_bang_emptyll in h33';auto.
                    assert(h36':=H36). apply  value_bang_emptyll in h36';auto. subst.
                     inversion  H26. subst. apply split_ident in H23. subst.
                    apply subtypecontext_subtyping with (B:=bang x0) (IL':=IL) (LL':=[]) in H33;auto.
                    assert(h33:=H33). apply hastype_isterm_subctx in h33.
                    apply subtypecontext_subtyping with (B:=bang x1) (IL':=IL) (LL':=[]) in H36;auto.
                    assert(h36:=H36). apply hastype_isterm_subctx in h36.
                    apply seq_weakening_cor with (il':=is_qexp u :: typeof u (bang x1) ::is_qexp v :: typeof v (bang x0) :: IL) in H60;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H60.
                    unfold P_seq_cut_one in H60. 
                    assert(In (is_qexp u) (is_qexp u  :: typeof u (bang x1) :: is_qexp v :: typeof v (bang x0)  :: IL)) as H71; try apply in_eq.
                    apply H60 with (j:=i1+1+1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (typeof u (bang x1)) (typeof u (bang x1) :: is_qexp v :: typeof v (bang x0)  ::IL)) as H72; try apply in_eq.
                    apply H71 with (j:=i1+1+1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (typeof u (bang x1)) (typeof u (bang x1))).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H72.
                    unfold P_seq_cut_one in H72. 
                    assert(In (is_qexp v) (is_qexp v :: typeof v (bang x0)  :: IL)) as H73; try apply in_eq.
                    apply H72 with (j:=i1+1+1) in H73. simpl in H73.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H73.
                    unfold P_seq_cut_one in H73. 
                    assert(In (typeof v (bang x0)) (typeof v (bang x0)  ::IL)) as H74; try apply in_eq.
                    apply H73 with (j:=i1+1+1) in H74. simpl in H74.
                    destruct (ProgLemmas1.eq_dec (typeof v (bang x0)) (typeof v (bang x0))).
                    assert(h74:=H74). 
                    apply common_eq in H1''.  Focus 2. intros. split. 
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite h74.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite <- h74. auto. apply split_ref. apply split_ref.  subst.
                    exists (i7 +  (i1 + 1 + 1) + (i1 + 1 + 1)+(i1 + 1 + 1) + (i1 + 1 + 1)). auto.
                    contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (typeof v (bang x0)) (typeof v (bang x0))).
                    auto. contradict n. auto. apply (is_qexp (CON  TRUE)). contradict n.
                    auto. simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                     simpl.
                     destruct (ProgLemmas1.eq_dec (typeof u (bang x1)) (typeof u (bang x1))). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)).
                     repeat apply subcnxt_iig;auto.
                    intros. inversion H4. subst. apply in_cons,in_eq.
                    inversion H5. subst. apply in_cons,in_cons,in_cons,in_eq.
                    inversion H7. subst. apply in_eq.
                    inversion H8. subst. apply in_cons,in_cons,in_eq.
                    repeat apply in_cons. auto. assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto. inversion H64. apply BangSub2. auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    inversion H64. apply BangSub2. auto. auto. auto.
                    auto.
                    apply subcntxt_splits with (il:=IL) in H23;auto. inversion H23.
                    apply subcntxt_splits with (il:=IL) in H26;auto. inversion H26.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. right. auto.
                    apply subcntxt_splits with (il:=IL) in H23;auto. inversion H23.
                    apply subcntxt_splits with (il:=IL) in H26;auto. inversion H26.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. left. auto. auto. }
                    { inversion H4.
                    inversion H5. inversion H7. inversion H8.
                    destruct H14.
                    inversion  H14.  inversion H18. inversion H14.
                    inversion H18. subst.
                     inversion H20.  inversion H22.
                    inversion H25. inversion H34. subst. apply split_ident in H29. subst.
                    inversion H33.
                    clear H4 H5 H7 H8 H14 H18 H20  H22 H25 H34 H33.
                    inversion H27.
                    assert(proper v);try apply value_proper;auto.
                    apply H14 in H18.  inversion H18.
                    assert(proper u);try apply value_proper;auto.
                    apply H34 in H37. inversion H37. inversion H42.
                    inversion H48. inversion H54. 
                    assert(h35':=H35). apply value_bang_emptyll in h35';auto.
                    assert(h36':=H36). apply value_bang_emptyll in h36';auto. subst.
                     inversion  H29. subst. apply split_ident in H23. subst.
                    assert(h35:=H35). apply hastype_isterm_subctx in h35.
                    assert(h36:=H36). apply hastype_isterm_subctx in h36.
                    apply seq_weakening_cor with (il':=is_qexp u :: typeof u (bang x4) ::is_qexp v :: typeof v (bang x3) :: IL) in H60;auto.
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H60.
                    unfold P_seq_cut_one in H60. 
                    assert(In (is_qexp u) (is_qexp u  :: typeof u (bang x4) :: is_qexp v :: typeof v (bang x3)  :: IL)) as H71; try apply in_eq.
                    apply H60 with (j:=i1) in H71. simpl in H71.
                    destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H71.
                    unfold P_seq_cut_one in H71. 
                    assert(In (typeof u (bang x4)) (typeof u (bang x4) :: is_qexp v :: typeof v (bang x3)  ::IL)) as H72; try apply in_eq.
                    apply H71 with (j:=i1) in H72. simpl in H72.
                    destruct (ProgLemmas1.eq_dec (typeof u (bang x4)) (typeof u (bang x4))).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H72.
                    unfold P_seq_cut_one in H72. 
                    assert(In (is_qexp v) (is_qexp v :: typeof v (bang x3)  :: IL)) as H73; try apply in_eq.
                    apply H72 with (j:=i1) in H73. simpl in H73.
                    destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)).
                    apply seq_cut_one_aux with (eq_dec:=ProgLemmas1.eq_dec) in H73.
                    unfold P_seq_cut_one in H73. 
                    assert(In (typeof v (bang x3)) (typeof v (bang x3)  ::IL)) as H74; try apply in_eq.
                    apply H73 with (j:=i1) in H74. simpl in H74.
                    destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))).
                    assert(h74:=H74). 
                    apply common_eq in H1''.  Focus 2. intros. split. 
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite h74.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite <- h4. auto. apply split_ref. apply split_ref.
                    intros. assert(h4':=H4). apply fq_all_qvar in H4. inversion H4. subst.
                    apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h4;auto. 
                    rewrite h4.  apply LL_FQ_ALT_L with 
                    (a:=(Let E (Prod v u))) (a':=(E v u)) (ll1:=[])
                     (ll:=lL2) (LL':=LL2)  (q:=x) in h74;auto. 
                    rewrite <- h74. auto. apply split_ref. apply split_ref. subst.
                    exists (i7 + (i1 ) + (i1 )+(i1 ) + (i1 )). auto.
                    contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (typeof v (bang x3)) (typeof v (bang x3))).
                    auto. contradict n. auto. apply (is_qexp (CON  TRUE)). contradict n.
                    auto. simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp v) (is_qexp v)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                     simpl.
                     destruct (ProgLemmas1.eq_dec (typeof u (bang x4)) (typeof u (bang x4))). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)). contradict n. auto.
                    simpl.
                     destruct (ProgLemmas1.eq_dec (is_qexp u) (is_qexp u)). auto. 
                    apply seq_weakening_cor with (il:=IL);auto. intros. repeat apply in_cons.
                    auto. contradict n. auto.
                     apply (is_qexp (CON  TRUE)).
                     repeat apply subcnxt_iig;auto.
                    intros. inversion H4. subst. apply in_cons,in_eq.
                    inversion H5. subst. apply in_cons,in_cons,in_cons,in_eq.
                    inversion H7. subst. apply in_eq.
                    inversion H8. subst. apply in_cons,in_cons,in_eq.
                    repeat apply in_cons. auto. assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto.
                    assert(LSL.split lL2 lL2[]);
                     try apply split_ref.
                    apply subcntxt_splits with (il:=IL) in H4. inversion H4.
                    auto. auto. auto. auto.
                    apply subcntxt_splits with (il:=IL) in H23;auto. inversion H23.
                    apply subcntxt_splits with (il:=IL) in H29;auto. inversion H29.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. right. auto.
                    apply subcntxt_splits with (il:=IL) in H23;auto. inversion H23.
                    apply subcntxt_splits with (il:=IL) in H29;auto. inversion H29.
                    auto.
                    intros. simpl in hnot1. specialize hnot1 with V.
                    apply hnot1. rewrite in_app_iff. right. auto. 
                    rewrite in_app_iff. left. auto. auto. }
                +++ apply subcntxt_splits with (il:=IL) in H23. inversion H23.
                    auto. auto.
                +++ contradict H1.  apply hnot5 in H1.
                    inversion H1. destruct H4.
                    inversion H4. destruct H4.
                    inversion H4. inversion H4. inversion H5. 
      ++ auto.
      ++ auto.
      ++ auto.
      ++ contradict H1.  apply hnot5 in H1.
         inversion H1. destruct H5.
         inversion H5. destruct H5.
         inversion H5. inversion H5. inversion H7.
(* circuit case *)
    * assert(circ16:=H16). clear H16.
      assert(circ17:=H17). clear H17.
      assert(H13:=H11). clear H11.
      assert(H14:=H12). clear H12.
      inversion H3. apply split_nil in H5. 
      inversion H5. subst. 
      assert(i0=i);try omega.
      assert(Hfq:=fq_common_ll a0 a'0).
      rexists. destruct_conj.
      subst.
      apply seq_weakening_cor with 
      (il':= List.rev (toiqlist (x))++ List.rev (toiqlist (x0))++IL ) in H10.
      ++ assert(h10:=H10). apply IHi  in H10 ;auto.
         -- inversion H10.
            exists (x1+1+1). assert(h4:=H4). assert(h7:=H7). clear H4 H7.
            intros LL1 LL2 A H4 H4' H4'' H4''' H7.
            apply sub_Circ_inv in H7. 
            ** destruct H7.
               +++ rexists. destruct_conj.
                    subst. inversion H18. inversion H26.
                    apply split_nil in H21. 
                    inversion H21. subst. inversion H25.  assert(h27:=H27). apply toimp_ilength in h27.
                    { apply move_to_ll in H27. 
                    apply seq_mono_cor with (k:= x1) in H27.
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (x))++ List.rev (toiqlist (x0))++IL ) in H27;auto.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (x))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H27;auto.
                    destruct H20. subst. inversion H5. subst.
                    apply H1 with (A:=x4)  (LL2:=(rev (toqlist (x0)) ++ []))in H27;auto.
                    inversion H27.
                    inversion H29. apply sub_valid_sub_eq  in H20;auto.
                    inversion H23. apply sub_valid_sub_eq  in H22;auto. subst.
                    exists (x1+x2+length (rev (toiqlist (FQ a0)))+length (FQ a0) + length (FQ a0)+length (FQ a'0) + length (FQ a'0)+1+1+1+1).
                    inversion H4'';[..|simpl in H19; inversion H19].
                    apply s_bc with (iL:=[And (toimp (FQ a'0) (atom_(typeof a'0 B2))) ((toimp (FQ t) (atom_(typeof t x3))))])
                    (lL:=[]);auto. apply tCricl;auto. 
                    apply ss_general with (lL2:=[]) (lL3:=[]).
                    apply split_ref. apply a_and;auto. 
                    assert(h17:=H17).  
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (FQ a0))++ List.rev (toiqlist (FQ a'0))++IL ) in H17;auto.
                    apply  IL_FQ_REPLACE in H17.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (FQ a'0))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H17;auto.
                    apply move_from_ll in H17. 
                    apply seq_mono_cor with (j:= x2  +length (rev (toiqlist (FQ a0)))+ length (FQ a'0) + length (FQ a'0)). 
                    omega. auto. 
                    apply fq_all_qvar.  
                    intros.
                    apply count_occ_toqlist with (q:=a1) in h7. 
                    repeat rewrite count_app_alt,count_occ_nil,<-rev_count.
                    rewrite h7. auto.
                    intros. rewrite <- in_rev in H22. apply in_toiqlistg in H22.
                    auto.
                    intros.
                    repeat rewrite in_app_iff. 
                    repeat rewrite in_app_iff in H22.
                    destruct H22.
                    apply count_occ_toiqlist with (q:=a1) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  h4, <- count_occ_In in H22.
                    repeat rewrite in_app_iff. left. rewrite <- in_rev. auto.
                    destruct H22.
                    apply count_occ_toiqlist with (q:=a1) in h7.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    h7, <- count_occ_In in H22.
                    right. left. rewrite <- in_rev. auto.
                    right. right. auto.
                    apply seq_mono_cor with (j:=i0);try omega. auto. 
                    apply ss_init.  apply ss_init.
                    repeat rewrite rev_toiqlist,rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    auto.
                    repeat rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    rewrite rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    auto.
                    repeat rewrite app_nil_r.
                    apply rev_common_ll;auto. 
                    intros.
                    assert(h17:=H17). apply fq_all_qvar in H17. inversion H17.
                    subst. rewrite app_nil_r, <- in_rev.
                    apply infq_intoqlist. rewrite count_occ_In in h17. rewrite <-  h7 in h17.
                    rewrite <- count_occ_In in h17. auto.
                    subst. inversion H5. inversion H19. subst.
                    apply H1 with (A:=x4)  (LL2:=(rev (toqlist (x0)) ++ []))in H27;auto.
                    inversion H27.
                    inversion H32. apply sub_valid_sub_eq  in H30;auto.
                    inversion H34. apply sub_valid_sub_eq  in H29;auto. subst.
                    exists (x1+x2+length (rev (toiqlist (FQ a0)))+length (FQ a0) + length (FQ a0)+length (FQ a'0) + length (FQ a'0)+1+1+1+1).
                    inversion H4'';[..|simpl in H22; inversion H22].
                    apply s_bc with (iL:=[And (toimp (FQ a'0) (atom_(typeof a'0 B2))) ((toimp (FQ t) (atom_(typeof t x3))))])
                    (lL:=[]);auto. apply tCricl;auto. 
                    apply ss_general with (lL2:=[]) (lL3:=[]).
                    apply split_ref. apply a_and;auto. 
                    assert(h17:=H17).  
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (FQ a0))++ List.rev (toiqlist (FQ a'0))++IL ) in H17;auto.
                    apply  IL_FQ_REPLACE in H17.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (FQ a'0))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H17;auto.
                    apply move_from_ll in H17. 
                    apply seq_mono_cor with (j:= x2 +length (rev (toiqlist (FQ a0))) + length (FQ a'0) + length (FQ a'0)). 
                    omega. auto. 
                    apply fq_all_qvar.
                    Optimize Proof.  
                    intros.
                    Optimize Proof.
                    apply count_occ_toqlist with (q:=a1) in h7. 
                    repeat rewrite count_app_alt,count_occ_nil,<-rev_count.
                    rewrite h7. auto.
                    intros. rewrite <- in_rev in H29. apply in_toiqlistg in H29.
                    auto.
                    intros.
                    repeat rewrite in_app_iff. 
                    repeat rewrite in_app_iff in H29.
                    destruct H29.
                    apply count_occ_toiqlist with (q:=a1) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  h4, <- count_occ_In in H29.
                    repeat rewrite in_app_iff. left. rewrite <- in_rev. auto.
                    destruct H29.
                    apply count_occ_toiqlist with (q:=a1) in h7.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    h7, <- count_occ_In in H29.
                    right. left. rewrite <- in_rev. auto.
                    right. right. auto.
                    apply seq_mono_cor with (j:=i0);try omega. auto. 
                    apply ss_init.  apply ss_init.
                    repeat rewrite rev_toiqlist,rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    auto.
                    repeat rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    rewrite rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    auto.
                    repeat rewrite app_nil_r.
                    apply rev_common_ll;auto. 
                    intros.
                    assert(h17:=H17). apply fq_all_qvar in H17. inversion H17.
                    subst. rewrite app_nil_r, <- in_rev.
                    apply infq_intoqlist. rewrite count_occ_In in h17. rewrite <-  h7 in h17.
                    rewrite <- count_occ_In in h17. auto.
                    inversion H19. subst.
                    apply H1 with (A:=x4)  (LL2:=(rev (toqlist (x0)) ++ []))in H27;auto.
                    inversion H27.
                    inversion H32. apply sub_valid_sub_eq  in H30;auto.
                    inversion H34. apply sub_valid_sub_eq  in H29;auto. subst.
                    exists (x1+x2+length (rev (toiqlist (FQ a0)))+length (FQ a0) + length (FQ a0)+length (FQ a'0) + length (FQ a'0)+1+1+1+1).
                    inversion H4'';[..|simpl in H22; inversion H22].
                    apply s_bc with (iL:=[And (toimp (FQ a'0) (atom_(typeof a'0 B2))) ((toimp (FQ t) (atom_(typeof t x3))))])
                    (lL:=[]);auto. apply tCrici;auto. 
                    apply ss_general with (lL2:=[]) (lL3:=[]).
                    apply split_ref. apply a_and;auto. 
                    assert(h17:=H17).  
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (FQ a0))++ List.rev (toiqlist (FQ a'0))++IL ) in H17;auto.
                    apply  IL_FQ_REPLACE in H17.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (FQ a'0))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H17;auto.
                    apply move_from_ll in H17. 
                    apply seq_mono_cor with (j:= x2 + length (rev (toiqlist (FQ a0))) + length (FQ a'0) + length (FQ a'0)). 
                    omega. auto. 
                    apply fq_all_qvar.
                    intros.
                    apply count_occ_toqlist with (q:=a1) in h7. 
                    repeat rewrite count_app_alt,count_occ_nil,<-rev_count.
                    rewrite h7. auto.
                    intros. rewrite <- in_rev in H29. apply in_toiqlistg in H29.
                    auto.
                    intros.
                    repeat rewrite in_app_iff. 
                    repeat rewrite in_app_iff in H29.
                    destruct H29.
                    apply count_occ_toiqlist with (q:=a1) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  h4, <- count_occ_In in H29.
                    repeat rewrite in_app_iff. left. rewrite <- in_rev. auto.
                    destruct H29.
                    apply count_occ_toiqlist with (q:=a1) in h7.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    h7, <- count_occ_In in H29.
                    right. left. rewrite <- in_rev. auto.
                    right. right. auto.
                    apply seq_mono_cor with (j:=i0);try omega. auto. 
                    apply ss_init.  apply ss_init.
                    repeat rewrite rev_toiqlist,rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    auto.
                    repeat rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    rewrite rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    auto.
                    repeat rewrite app_nil_r.
                    apply rev_common_ll;auto. 
                    intros.
                    assert(h17:=H17). apply fq_all_qvar in H17. inversion H17.
                    subst. rewrite app_nil_r, <- in_rev.
                    apply infq_intoqlist. rewrite count_occ_In in h17. rewrite <-  h7 in h17.
                    rewrite <- count_occ_In in h17. auto.
                    intros. repeat rewrite count_app_alt,count_occ_nil,<-rev_count. 
                    apply count_occ_toqlist with (q:=a) in h4.
                    rewrite  h4. auto.
                    intro. repeat rewrite in_app_iff. intro.
                    destruct H29. left.
                    apply count_occ_toiqlist with (q:=a) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    <-  h4, <- count_occ_In in H29. rewrite <- in_rev. auto.
                    right. right. auto.
                    omega.
                    apply fq_all_qvar. }
                    { apply fq_all_qvar. }
                +++ rexists. destruct_conj.
                    subst. inversion H17. inversion H25.
                    apply split_nil in H20. 
                    inversion H20. subst. inversion H24.  assert(h26:=H26). apply toimp_ilength in h26.
                    { apply move_to_ll in H26. 
                    apply seq_mono_cor with (k:= x1) in H26.
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (x))++ List.rev (toiqlist (x0))++IL ) in H26;auto.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (x))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H26;auto.
                    destruct H19. subst. 
                    apply H1 with (A:=x4)  (LL2:=(rev (toqlist (x0)) ++ []))in H26;auto.
                    inversion H26.
                    exists (x1+x2+length (rev (toiqlist (FQ a0)))+length (FQ a0) + length (FQ a0)+length (FQ a'0) + length (FQ a'0)+1+1+1+1).
                    inversion H4'';[..|simpl in H18; inversion H18].
                    apply s_bc with (iL:=[And (toimp (FQ a'0) (atom_(typeof a'0 x4))) ((toimp (FQ t) (atom_(typeof t x3))))])
                    (lL:=[]);auto. apply tCricl;auto. 
                    apply ss_general with (lL2:=[]) (lL3:=[]).
                    apply split_ref. apply a_and;auto. 
                    assert(h16:=H16).  
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (FQ a0))++ List.rev (toiqlist (FQ a'0))++IL ) in H16;auto.
                    apply  IL_FQ_REPLACE in H16.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (FQ a'0))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H16;auto.
                    apply move_from_ll in H16. 
                    apply seq_mono_cor with (j:= x2 + length (rev (toiqlist (FQ a0))) + length (FQ a'0) + length (FQ a'0)). 
                    omega. auto. 
                    apply fq_all_qvar.  
                    intros.
                    apply count_occ_toqlist with (q:=a1) in h7. 
                    repeat rewrite count_app_alt,count_occ_nil,<-rev_count.
                    rewrite h7. auto.
                    intros. rewrite <- in_rev in H21. apply in_toiqlistg in H21.
                    auto.
                    intros.
                    repeat rewrite in_app_iff. 
                    repeat rewrite in_app_iff in H21.
                    destruct H21.
                    apply count_occ_toiqlist with (q:=a1) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  h4, <- count_occ_In in H21.
                    repeat rewrite in_app_iff. left. rewrite <- in_rev. auto.
                    destruct H21.
                    apply count_occ_toiqlist with (q:=a1) in h7.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    h7, <- count_occ_In in H21.
                    right. left. rewrite <- in_rev. auto.
                    right. right. auto.
                    apply seq_mono_cor with (j:=i0);try omega. auto. 
                    apply ss_init.  apply ss_init.
                    repeat rewrite rev_toiqlist,rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    auto.
                    repeat rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    rewrite rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    auto.
                    repeat rewrite app_nil_r.
                    apply rev_common_ll;auto. 
                    intros.
                    assert(h16:=H16). apply fq_all_qvar in H16. inversion H16.
                    subst. rewrite app_nil_r, <- in_rev.
                    apply infq_intoqlist. rewrite count_occ_In in h16. rewrite <-  h7 in h16.
                    rewrite <- count_occ_In in h16. auto.
                    subst. 
                    apply H1 with (A:=x4)  (LL2:=(rev (toqlist (x0)) ++ []))in H26;auto.
                    inversion H26.
                    exists (x1+x2+length (rev (toiqlist (FQ a0)))+length (FQ a0) + length (FQ a0)+length (FQ a'0) + length (FQ a'0)+1+1+1+1).
                    inversion H4'';[..|simpl in H18; inversion H18].
                    apply s_bc with (iL:=[And (toimp (FQ a'0) (atom_(typeof a'0 x4))) ((toimp (FQ t) (atom_(typeof t x3))))])
                    (lL:=[]);auto. apply tCrici;auto. 
                    apply ss_general with (lL2:=[]) (lL3:=[]).
                    apply split_ref. apply a_and;auto. 
                    assert(h16:=H16).  
                    apply seq_weakening_cor with 
                    (il':= List.rev (toiqlist (FQ a0))++ List.rev (toiqlist (FQ a'0))++IL ) in H16;auto.
                    apply  IL_FQ_REPLACE in H16.
                    apply seq_exchange_cor with 
                    (ll':= List.rev (toqlist (FQ a'0))++[] ) (eq_dec:=ProgLemmas1.eq_dec) in H16;auto.
                    apply move_from_ll in H16. 
                    apply seq_mono_cor with (j:= x2 +length (rev (toiqlist (FQ a0))) + length (FQ a'0) + length (FQ a'0)). 
                    omega. auto. 
                    apply fq_all_qvar.  
                    intros.
                    apply count_occ_toqlist with (q:=a1) in h7. 
                    repeat rewrite count_app_alt,count_occ_nil,<-rev_count.
                    rewrite h7. auto.
                    intros. rewrite <- in_rev in H21. apply in_toiqlistg in H21.
                    auto.
                    intros.
                    repeat rewrite in_app_iff. 
                    repeat rewrite in_app_iff in H21.
                    destruct H21.
                    apply count_occ_toiqlist with (q:=a1) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  h4, <- count_occ_In in H21.
                    repeat rewrite in_app_iff. left. rewrite <- in_rev. auto.
                    destruct H21.
                    apply count_occ_toiqlist with (q:=a1) in h7.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    h7, <- count_occ_In in H21.
                    right. left. rewrite <- in_rev. auto.
                    right. right. auto.
                    apply seq_mono_cor with (j:=i0);try omega. auto. 
                    apply ss_init.  apply ss_init.
                    repeat rewrite rev_toiqlist,rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    auto.
                    repeat rewrite rev_toiqlist.
                    apply subcnxt_add2.
                    rewrite rev_toqlist,app_nil_r.
                    apply subcnxt_add.
                    auto.
                    repeat rewrite app_nil_r.
                    apply rev_common_ll;auto. 
                    intros.
                    assert(h16:=H16). apply fq_all_qvar in H16. inversion H16.
                    subst. rewrite app_nil_r, <- in_rev.
                    apply infq_intoqlist. rewrite count_occ_In in h16. rewrite <-  h7 in h16.
                    rewrite <- count_occ_In in h16. auto.
                    intros. repeat rewrite count_app_alt,count_occ_nil,<-rev_count. 
                    apply count_occ_toqlist with (q:=a) in h4.
                    rewrite  h4. auto.
                    intro. repeat rewrite in_app_iff. intro.
                    destruct H28. left.
                    apply count_occ_toiqlist with (q:=a) in h4.
                    rewrite <- in_rev,count_occ_In with (eq_dec:=ProgLemmas1.eq_dec),  
                    <-  h4, <- count_occ_In in H28. rewrite <- in_rev. auto.
                    right. right. auto.
                    omega.
                    apply fq_all_qvar. } 
                    { apply fq_all_qvar. } 
              ** auto. 
              ** contradict H4.
                 apply hnot5 in H4. inversion H4. destruct H5. 
                 inversion H5. destruct H5. inversion H5.
                 inversion H5. inversion H16.
           -- simpl in hnot1. intros. 
              specialize hnot1 with V;rewrite in_app_iff in hnot1.
              apply hnot1;right; auto.
           -- simpl in hnot2.
              rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
              rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
              specialize hnot2 with x1.
              rewrite count_app with (l1:=FQUC t) (l2:=FQUC a'0) in hnot2;auto.
              assert(In x1 (FQUC t ++ FQUC a'0)). rewrite in_app_iff. right. auto.
              apply hnot2 in H5.
              rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
               omega.
           -- apply FQUC_FQU. 
              simpl in hnot2.
              rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec). intros.
              rewrite NoDup_count_occ'  with (decA:=ProtoQuipperSyntax.eq_dec) in hnot2.
              specialize hnot2 with x1.
              rewrite count_app with (l1:=FQUC t) (l2:=FQUC a'0) in hnot2;auto.
              assert(In x1 (FQUC t ++ FQUC a'0)). rewrite in_app_iff. right. auto.
              apply hnot2 in H5.
              rewrite count_occ_In with (eq_dec:=ProtoQuipperSyntax.eq_dec) in H1.
               omega.
           -- intros. 
              apply in_app_or in H1. destruct H1.
              rewrite rev_toiqlist in H1.  
              apply in_toiqlistg in H1.  inversion H1.
              exists x1. right. left. auto. 
              apply in_app_or in H1. destruct H1.
              rewrite rev_toiqlist in H1.
              apply in_toiqlistg in H1.  inversion H1.
              exists x1. right. left. auto.
              apply   hnot5. auto. 
        ++ intros. apply in_or_app. right. apply in_or_app. right. auto.
Qed.
