(****************************************************************
   File: PQAdequacy.v
   Authors: Amy Felty and Mohamed Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Internal Adequacy of the representation of Proto Quipper typing
   rules (part of the definition of prog).
  ***************************************************************)

Require Export ProtoQuipperProg.
Import ListNotations.

Section Adeq.

Set Implicit Arguments.

Variable circIn: Econ -> set qexp.
Variable circOut: Econ -> set qexp.
Variable circApp: Econ -> Econ -> Econ .
Variable circNew: list qexp -> nat.
Variable circRev: nat -> nat.

Definition atm := ProtoQuipperProg.atm.
Definition Econ := ProtoQuipperSyntax.Econ.
Definition oo_ := ProtoQuipperProg.oo_.
Definition prog := ProtoQuipperProg.prog circIn circOut circApp circNew circRev.
(* Definition splitseq := @LSL.splitseq atm Econ prog. *)
Definition seq_ := ProtoQuipperProg.seq_ circIn circOut circApp circNew circRev.
Definition splitseq_ := ProtoQuipperProg.splitseq_ circIn circOut circApp circNew circRev.

Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold seq_ : hybrid.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold seq_ : hybrid.
Hint Resolve init splitr1 splitr2 ss_init ss_general : hybrid.
Hint Resolve  starq trueq falseq boxq unboxq revq qvar lambdaq apq prodq letq
              sletq ifq Circq axc1 axc2 starl stari truel truei falsel falsei
              box unbox rev lambda1l lambda1i lambda2l lambda2i tap
              ttensorl ttensori tletl tleti tsletl tsleti tif tCricl tCrici :
              hybrid.


(*************************)
(* Lemmas about Contexts *)
(*************************)

Lemma qexp_strengthen_weaken :
   forall (i:nat) (M:qexp) (Phi1 Phi2:list atm),
   (forall (M:qexp), In (is_qexp M) Phi1 ->  In (is_qexp M) Phi2) ->
   seq_ i Phi1 [] (atom_ (is_qexp M)) ->
   seq_ i Phi2 [] (atom_ (is_qexp M)).
Proof.
intro i.
generalize
  (lt_wf_ind i
     (fun i:nat =>
      forall (M:qexp) (Phi1 Phi2:list atm),
      (forall (M:qexp), In (is_qexp M) Phi1 ->  In (is_qexp M) Phi2) ->
      seq_ i Phi1 [] (atom_ (is_qexp M)) ->
      seq_ i Phi2 [] (atom_ (is_qexp M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M Phi1 Phi2 h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* Qvar to REV cases *)
  + unfold seq_; apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + (* Fun case *)
    inversion H1; subst; clear H1.
    inversion H8; subst; clear H8.
    inversion H3; subst; clear H3.
    apply s_bc with
        []
        [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply s_all; auto.
    intros x h2.
    specialize (H6 x h2).
    inversion H6; subst; clear H6.
    apply i_imp; auto.
    apply h with (is_qexp x::Phi1); auto; try lia.
    (* proof of extended context inv *)
    intro T; generalize (h1 T); simpl; tauto.
  + (* App case *)
    inversion H1; subst; clear H1.
    inversion H7; subst; clear H7.
    inversion H2; subst; clear H2.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H6).
    specialize h' with (1:=hi) (2:=h1) (3:=H9).
    unfold seq_,atom_;
      apply s_bc with [] [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply a_and; auto.
  + (* Prod case *)
    inversion H1; subst; clear H1.
    inversion H7; subst; clear H7.
    inversion H2; subst; clear H2.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H6).
    specialize h' with (1:=hi) (2:=h1) (3:=H9).
    unfold seq_,atom_;
      apply s_bc with [] [And (atom_ (is_qexp E1)) (atom_ (is_qexp E2))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply a_and; auto.
  + (* Let case *)
    inversion H1; subst; clear H1.
    inversion H4; subst; clear H4.
    inversion H9; subst; clear H9.
    apply s_bc with
        []
        [(All (fun x : qexp =>
                 (All (fun y:qexp =>
                         Imp (is_qexp x)
                             (Imp (is_qexp y) (atom_ (is_qexp (E x y))))))));
         (atom_ (is_qexp b0))]; auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    * apply s_all; auto.
      intros x h2.
      specialize (H6 x h2).
      inversion H6; subst; clear H6.
      apply s_all; auto.
      intros y h3.
      specialize (H7 y h3).
      inversion H7; subst; clear H7.
      inversion H6; subst; clear H6.
      apply i_imp; auto.
      apply i_imp; auto.
      apply h with (is_qexp y::is_qexp x::Phi1); auto; try lia.
      intro T; generalize (h1 T); simpl; tauto.
    * apply ss_general with [] []; auto with hybrid.
      { inversion H10. inversion H11.  subst. 
        apply split_ident in H1;auto. subst.
        apply h with Phi1; auto with hybrid; try lia. }
      { apply ss_init. }
  + (* Slet case *)
    inversion H1; subst; clear H1.
    inversion H7; subst; clear H7.
    inversion H2; subst; clear H2.
    assert (hi:i<i+1+1); try lia.
    generalize h; intro h'.
    specialize h with (1:=hi) (2:=h1) (3:=H6).
    specialize h' with (1:=hi) (2:=h1) (3:=H9).
    unfold seq_,atom_;
      apply s_bc with [] [And (atom_ (is_qexp E)) (atom_ (is_qexp b0))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply a_and; auto.
  + (* If case *)
    inversion H1; subst; clear H1.
    inversion H7; subst; clear H7.
    inversion H9; subst; clear H9.
    inversion H2; subst; clear H2.
    apply s_bc with
        []
        [And (atom_ (is_qexp b0))
             (And (atom_ (is_qexp a1))
                  (atom_(is_qexp a2)))]; auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply a_and; auto with hybrid.
    apply h with Phi1; auto; try lia.
    apply a_and; auto with hybrid.
    * apply h with Phi1; auto; try lia.
    * apply h with Phi1; auto; try lia.
  + (* Circ case *)
    inversion H1; subst; clear H1.
    inversion H3; subst; clear H3.
    apply s_bc with [] [toimpexp (FQ a) (atom_ (is_qexp a))]; auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    * assert(H8':=H8).
      apply toimpexp_ilength in H8'.
      { apply move_to_il in H8;auto.
        { apply h with (Phi2:= List.rev (toiqlist (FQ a)) ++ Phi2) in H8;
            auto.
          { apply move_from_il in H8;auto.
            { assert (H: length (FQ a) <= i0 ->
                         i0 - length (FQ a) + length (FQ a) = i0); try lia.
              rewrite <- H;auto. }
            { apply fq_all_qvar. }}
          { lia. }
          { intros. apply in_app_iff in H. destruct H.
            { apply in_or_app. left;auto. }
            { apply in_or_app. right;auto. }}}
        { apply fq_all_qvar. }}
      { apply fq_all_qvar. }
    * apply ss_init.
- (* context case *)
  specialize h1 with (M:=M).
  generalize (h1 H2); clear h1 H2.
  case Phi2.
  simpl; tauto.
  intros a l h1.
  apply i_init; auto with hybrid.
Qed.

Hint Resolve qexp_strengthen_weaken : hybrid.

(***************************)
(* Internal Adequacy Lemma *)
(***************************)

Lemma hastype_isterm_subctx :
   forall (i:nat) (M:qexp) (T:qtp) (it lt:list atm),
   Subtypecontext it lt it lt->
   seq_ i it lt (atom_ (typeof M T)) ->
   seq_ i it [] (atom_ (is_qexp M)).
Proof.
intro i.
generalize
  (lt_wf_ind i
     (fun i:nat =>
       forall (M:qexp) (T:qtp) ( it lt:list atm),
       Subtypecontext it lt it lt ->
       seq_ i it lt (atom_ (typeof M T)) ->
       seq_ i it [] (atom_ (is_qexp M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M T  it lt h0 h1.
inversion h1; subst; clear h1.
- (* s_bc case *)
  inversion H0; subst; clear H0.
  + (* axc1 case *)
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    generalize seq_mono; unfold Psinglell; intro h2.
    apply h2 with i0; try lia; auto.
  + (* axc2 case *)
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    inversion H8; subst; clear H8.
    generalize seq_mono; unfold Psinglell; intro h2.
    apply h2 with i; try lia; auto.
    (* cases starl, stari, truel, truei, falsel, falsei, box, unbox, rev *)
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + apply s_bc with [] []; auto with hybrid.
  + (* lambda1l case *)
    inversion H5; subst; clear H5.
    inversion H11; subst; clear H11.
    specialize split_ident with (1:=[]) (2:=H2); intro; subst.
    inversion H10; subst; clear H10.
    apply s_bc with
        [] [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply s_all; auto.
    intros x h1.
    specialize (H7 x h1).
    inversion H7; subst; clear H7.
    inversion H9; subst; clear H9.
    apply i_imp; auto.
    apply h with T2  (typeof x T1 :: lL2);
      eauto with hybrid; try lia.
    * apply subcnxt_llg;auto.  
      apply sub_ref,bang_valid;auto.
    * generalize seq_mono; unfold Psinglell; intro h2.
      apply h2 with i; try lia; auto with hybrid.
  + (* lambda1i case *)
    inversion H5; subst; clear H5.
    inversion H11; subst; clear H11.
    specialize split_ident with (1:=[]) (2:=H2); intro; subst.
    inversion H10; subst; clear H10.
    apply s_bc with
        [] [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply s_all; auto.
    intros x h1.
    specialize (H7 x h1).
    inversion H7; subst; clear H7.
    inversion H9; subst; clear H9.
    apply i_imp; auto. apply qexp_strengthen_weaken with (is_qexp x::typeof x (bang T1)::it).
    * intros. inversion H.
      { inversion H0. subst. apply in_eq. }
      { inversion H0.
        { inversion H5. }
        { apply in_cons;auto. }}
    * apply h with T2  lL2;
        eauto with hybrid; try lia.
      { apply subcnxt_iig;auto.  
        { apply sub_ref;auto. }
        { exists T1. auto. }}
      { generalize seq_mono; unfold Psinglell; intro h2.
        apply h2 with i; try lia; auto with hybrid.
        apply seq_weakening_cor with (typeof x (bang T1) :: is_qexp x :: it);auto.
        intros. inversion H.
        { subst. apply in_cons, in_eq;auto. }
        { inversion H0.
          { subst. apply in_eq. }
          { apply in_cons,in_cons;auto. }}}
  + (* lambda2i case *)
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    inversion H10; subst; clear H10.
    apply s_bc with
        [] [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply s_all; auto.
    intros x h1.
    specialize (H5 x h1).
    inversion H5; subst; clear H5.
    inversion H6; subst; clear H6.
    apply i_imp; auto.
    apply qexp_strengthen_weaken with (is_qexp x::typeof x (bang T1)::it).
    * intros. inversion H.
      { inversion H0. subst. apply in_eq. }
      { inversion H0.
        { inversion H1. }
        { apply in_cons;auto. }}
    * apply h with T2  [];
        eauto with hybrid; try lia.
      { apply subcnxt_iig;auto.  
        { apply sub_ref;auto. }
        { exists T1. auto. }}
      { generalize seq_mono; unfold Psinglell; intro h2.
        apply h2 with i; try lia; auto with hybrid.
        apply seq_weakening_cor with (typeof x (bang T1) :: is_qexp x :: it);auto.
        intros. inversion H.
        { subst. apply in_cons, in_eq;auto. }
        { inversion H0.
          { subst. apply in_eq. }
          { apply in_cons,in_cons;auto. }}}
  + (* lambda2l case *)
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11.
    inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    inversion H10; subst; clear H10.
    apply s_bc with
        [] [(All (fun x : qexp => Imp (is_qexp x) (atom_ (is_qexp (E x)))))];
      auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    apply s_all; auto.
    intros x h1.
    specialize (H5 x h1).
    inversion H5; subst; clear H5.
    inversion H6; subst; clear H6.
    apply i_imp; auto.
    apply h with T2  [typeof x T1]; eauto with hybrid; try lia.
    * apply subcnxt_llg;auto.  
      apply sub_ref,bang_valid;auto.
    *  generalize seq_mono; unfold Psinglell; intro h2.
      apply h2 with i ; try lia ; auto with hybrid.
  + (* tap case *)
    inversion H5. inversion H9. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H8. symmetry in H4. 
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2.
    apply  s_bc with 
        [] [And (atom_(is_qexp E1)) (atom_(is_qexp E2))];auto.
    * apply apq.
    * apply ss_general with [] [];auto.
      { apply init. }
      { apply a_and;auto.
        { apply h with (arrow T' T)  LL1;auto.
          lia. }
        { apply h with T' LL2;auto. lia. }}
      { apply ss_init. }
    * apply ss_init.
  + (* tensorl case *)
    inversion H5. inversion H9. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H8. symmetry in H4. 
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2. 
    apply  s_bc with 
        [] [And (atom_(is_qexp E1)) (atom_(is_qexp E2))];auto with hybrid.
    apply ss_general with [] [];auto with hybrid.
    apply a_and;auto with hybrid.
    * apply h with T0 LL1; auto; lia.
    *  apply h with T' LL2; auto; lia.
  + (* tensori case *)
    inversion H5. inversion H10. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H9. symmetry in H6. 
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2. 
    apply  s_bc with 
        [] [And (atom_(is_qexp E1)) (atom_(is_qexp E2))];auto with hybrid.
    apply ss_general with [] [];auto with hybrid. 
    apply a_and;auto with hybrid.
    * apply h with (bang T0) LL1;auto; lia.
    * apply h with (bang T') LL2;auto; lia.
  + (* tletl case *)  
    inversion H5.
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2. 
    inversion H11. 
    apply  s_bc with 
        [] [(All (fun x : qexp =>
                    (All (fun y:qexp => 
                            Imp (is_qexp x)
                                (Imp (is_qexp y)
                                     (atom_ (is_qexp (E x y))))))));
            (atom_ (is_qexp b0))];auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    * apply s_all. intros. assert(H20':=H20). apply H19 in H20.
      inversion H20. apply s_all. intros. assert(H26':=H26). 
      apply H25 in H26. inversion H26. inversion H31. 
      inversion H37.  inversion H43. repeat apply i_imp.
      apply h with T (typeof x0 T2 :: typeof x T1 :: lL2);auto with hybrid; try lia.
      { repeat apply cons_l_cr;auto.
        repeat apply subcnxt_llg;auto with hybrid.
        { apply sub_ref,bang_valid;auto. }
        { apply sub_ref,bang_valid;auto. }}
      { apply seq_mono_cor with i6;auto; lia. }
    * inversion H12. inversion H27. subst. apply split_ident in H22; auto.
      subst. apply ss_general with [] [];auto with hybrid.
      apply h with (tensor T1 T2) (lL4); auto; lia. 
  + (* tleti case *)
    inversion H5.
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2. 
    inversion H11. 
    apply s_bc with 
        [] [(All (fun x : qexp =>
                    (All (fun y:qexp => 
                            Imp (is_qexp x)
                                (Imp (is_qexp y)
                                     (atom_ (is_qexp (E x y))))))));
            (atom_ (is_qexp b0))];auto with hybrid.
    apply ss_general with [] []; auto with hybrid.
    * apply s_all.  intros. assert(H20':=H20). apply H19 in H20.
      inversion H20. apply s_all. intros. assert(H26':=H26). 
      apply H25 in H26. inversion H26. inversion H31. 
      inversion H37.  inversion H43. repeat apply i_imp.
      apply qexp_strengthen_weaken with
          (is_qexp x0::typeof x0 (bang T2)::is_qexp x::typeof x (bang T1)::it).
      { intros. inversion H51.
        { inversion H52. subst. apply in_eq. }
        { inversion H52.
          { inversion H53. }
          { inversion H53.
            { inversion H54. subst. apply in_cons,in_eq. }
            { inversion H54.
              { inversion H55. }
              { apply in_cons,in_cons;auto. }}}}}
      { apply h with T (lL2);auto; try lia.
        { repeat apply cons_i_cr;auto with hybrid.
          repeat apply subcnxt_iig;auto with hybrid.
          { apply sub_ref;auto with hybrid. }
          { exists T2; auto. }
          { apply sub_ref;auto with hybrid. }
          { exists T1; auto. }}
        { apply seq_mono_cor with i6;auto; try lia.
          apply seq_weakening with
              (typeof x0 (bang T2)::typeof x (bang T1)::is_qexp x0::is_qexp x::it);
            auto with hybrid.
          intros. inversion H51.
          { subst. apply in_cons,in_eq. }
          { inversion H52.
            { subst. apply in_cons,in_cons,in_cons,in_eq. }
            { inversion H53.
              { subst. apply in_eq. }
              { inversion H54.
                { subst. apply in_cons,in_cons,in_eq. }
                { repeat apply in_cons; auto. }}}}}}
    * inversion H12. inversion H27. subst. apply split_ident in H22; auto.
      subst. apply ss_general with [] [];auto with hybrid.
      apply h with (bang (tensor T1 T2)) (lL4);auto; try lia.
  + (* tsletl case *)
    inversion H5. inversion H9. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H8.  
    apply subcntxt_splits with (il:=it) in H2;auto.
    inversion H2.
    apply  s_bc with 
        [] [And (atom_(is_qexp E)) (atom_(is_qexp b0))];auto with hybrid.
    apply ss_general with [] [];auto with hybrid. 
    apply a_and;auto with hybrid.
    { apply h with T LL1;auto; lia. }
    { apply h with one LL2;auto; lia. }
  +  (* tsleti case *)
    inversion H5. inversion H9. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H8. 
    apply subcntxt_splits with (il:=it) in H2;auto. inversion H2.
    apply s_bc with 
        [] [And (atom_(is_qexp E)) (atom_(is_qexp b0))];auto with hybrid.
    apply ss_general with [] [];auto with hybrid. 
    apply a_and;auto with hybrid.
    * apply h with T LL1;auto; lia.
    * apply h with (bang one) LL2;auto; lia.
  + (* tif case *)
    inversion H5. inversion H10. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H9. 
    apply subcntxt_splits with (il:=it) in H2;auto. inversion H2.
    apply  s_bc with 
        [] [And (atom_ (is_qexp b0))
                (And (atom_ (is_qexp a1)) (atom_(is_qexp a2)))];
      auto with hybrid.
    apply ss_general with [] [];auto with hybrid. 
    apply a_and;auto.
    * apply h with bool  LL1;auto; lia. 
    * inversion H12. apply a_and;auto.
      { apply h with T LL2;auto; lia. }
      { apply h with T LL2;auto; lia. }
  + (* tcircl case *)
    inversion H1. inversion H12. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H11. 
    apply  s_bc with [] [toimpexp (FQ a) (atom_(is_qexp a))];auto with hybrid.
    assert(H10':=H10). apply toimp_ilength in H10';auto.
    * apply move_to_ll in H10.
      { apply ss_general with [] [];auto with hybrid.
        { apply h with (T:=U) in H10;auto with hybrid; try lia.
          { apply move_from_il in H10;auto.
            { apply seq_mono_cor with (k:=i+1) in H10;auto.
              assert (H':length (FQ a) + length (FQ a) <= i -> 
                         i - length (FQ a) - length (FQ a) + length (FQ a) <= i+1);
                lia. }
            { apply fq_all_qvar; lia. }}
          { rewrite rev_toqlist,rev_toiqlist,app_nil_r. apply subcnxt_add;auto.
            inversion H5. subst. auto. }}
        { apply ss_init. }}
      { apply fq_all_qvar. }
    * apply fq_all_qvar.
  + (* tCrici case *)
    inversion H1. inversion H12. subst. 
    apply split_ident_alt in H2; auto. subst.
    inversion H11. 
    apply s_bc with [] [toimpexp (FQ a) (atom_(is_qexp a))];auto with hybrid.
    assert(H10':=H10). apply toimp_ilength in H10';auto.
    * apply move_to_ll in H10.
      { apply ss_general with [] [];auto with hybrid.
        { apply h with (T:=U) in H10;auto with hybrid; try lia.
          { apply move_from_il in H10;auto.
            { apply seq_mono_cor with (k:=i+1) in H10;auto.
              assert (H':length (FQ a) + length (FQ a) <= i -> 
                           i - length (FQ a) - length (FQ a) +  length (FQ a) <=i+1);
                lia. }
            { apply fq_all_qvar; lia. }}
          { rewrite rev_toqlist,rev_toiqlist,app_nil_r. apply subcnxt_add;auto.
            inversion H5. subst. auto. }}
        { apply ss_init. }}
      { apply fq_all_qvar. }
    * apply fq_all_qvar.
- (* l_init case case *)
  apply i_init. 
  apply memb_il  with (T:=T) (M:=M) (ll:=[typeof M T]) in h0; try tauto.
  apply in_eq.
- (* l_init case case *)
  apply i_init.  
  apply memb_il_il with (il':=it) (ll:=[]) (ll':=[]) in H3; try tauto.
Qed.

(*************************)
(* Other Adequacy Lemmas *)
(*************************)

(* Any term satisfying the quantum_data predicate is well-formed. *)
Theorem quantumdata_qexp: forall t, quantum_data t -> 
  exists j, seq_ j (toiqlist (FQ t)) [] (atom_ (is_qexp t)).
Proof.
intros t H. induction H.
- simpl. exists 0. apply i_init.
  apply in_eq.
- simpl.  exists (0+1).
  apply s_bc with (lL:=[]) (iL:=[]);auto.
  + apply (atom_(is_qexp (CON STAR))).
  + apply starq.
  + apply ss_init. 
  + apply ss_init.
-  inversion IHquantum_data1.
   inversion IHquantum_data2. exists (x+x0+1+1).
   apply s_bc with (lL:=[])
     (iL:=[And (atom_(is_qexp a)) (atom_(is_qexp b))]); auto.
   + apply (atom_(is_qexp (CON STAR))).
   + apply prodq.
   + apply ss_general with (lL2:=[]) (lL3:=[]);auto.
     * apply init. 
     * apply a_and; auto.
       { apply [is_qexp (CON STAR)]. }
       { apply seq_mono_cor with (j:= x); try lia.
         apply seq_weakening_cor with (il:=toiqlist (FQ a));auto.
         apply toiqlist_union. simpl.
         intros.  apply set_union_intro1. unfold set_In. auto. }
       { apply seq_mono_cor with (j:= x0);try lia.
         apply seq_weakening_cor with (il:=toiqlist (FQ b));auto.
         apply toiqlist_union. simpl.
         intros.  apply set_union_intro2. unfold set_In. auto. }
     * apply ss_init. 
   + apply ss_init.
Qed.

End Adeq.

