(****************************************************************
   File: ProtoQuipperTypes.v                                                 
   Authors: Mohamed Yousri Mahmoud
   Date: June 2018
   Current Version: Coq V8.9
                                                                 
   Types of ProtoQuipper, a quantum lambda calculus programming
   language, and a subtyping relation.
  ***************************************************************)

Require Import Coq.Program.Basics.
Require Import Coq.Lists.ListSet.
Require Import List.
Require Import Coq.Program.Equality.
Require Export Div2.
Require Export EqNat.
Require Export Le.
Require Export Lt.
Require Export Plus.
Require Export Gt.
Require Export BoolEq.
Require Export Decidable.
Require Export Omega.
Require Import Datatypes.
Require Import Logic.


Inductive qtp:Type :=
qubit:qtp
|one:qtp
|bool:qtp
|tensor:qtp->qtp->qtp
|arrow: qtp -> qtp -> qtp
|circ: qtp -> qtp -> qtp
|bang: qtp -> qtp.


Inductive valid :qtp -> Prop :=
Qubit: valid qubit
|One : valid one 
|Tensor: forall A1 A2, valid A1 -> valid A2 ->
  valid (tensor A1 A2).
 

Inductive validT: qtp-> Prop :=
vQubit: validT qubit
|bQubit: validT (bang qubit)
|vOne:  validT one 
|bOne: validT (bang one)
|vBool: validT bool 
|bBool:  validT (bang bool)
|vTensor: forall A B, validT A -> validT B ->  validT (tensor A B) 
|bTensor: forall A B, validT A -> validT B -> validT (bang(tensor A B)) 
|vArrow: forall A B, validT A -> validT B -> validT (arrow A B) 
|bArrow: forall A B, validT A -> validT B -> validT (bang (arrow A B)) 
|vCirc: forall A B, valid A -> valid B -> validT (circ A B)
|bCirc: forall A B, valid A -> valid B -> validT (bang (circ A B)).


Theorem valid_is_T: forall A, valid A -> validT A.
Proof.
intros. dependent induction H;[ apply vQubit| apply vOne | apply vTensor]; auto.
Qed. 

Theorem bang_valid: forall A, validT (bang A) -> validT A.
Proof.
intros. dependent induction H;[ apply vQubit| apply vOne| apply vBool|
apply vTensor| apply vArrow| apply vCirc] ;auto.
Qed.

Inductive Subtyping: qtp -> qtp -> Prop :=
QubitSub: Subtyping qubit qubit
|OneSub: Subtyping  one one 
|BoolSub: Subtyping bool bool
|TensorSub: forall A1 A2 B1 B2,
   Subtyping A1 B1 -> Subtyping  A2  B2 ->
    Subtyping (tensor A1 A2) (tensor B1 B2)
|ArrowSub: forall A1 A2 B1 B2,
   Subtyping A2 A1 ->  Subtyping B1 B2 ->
    Subtyping (arrow A1 B1) (arrow A2 B2)
|CircSub: forall A1 A2 B1 B2, 
   Subtyping A2 A1 -> Subtyping B1 B2 ->
   validT (circ A1 B1) ->  validT (circ A2 B2)->
   Subtyping (circ A1 B1) (circ A2 B2)
|BangSub1:  forall A B, Subtyping A B ->
  validT (bang A) ->
  Subtyping (bang A)  B
|BangSub2:  forall A B, Subtyping A B ->
  validT (bang A)  ->
  Subtyping (bang A) (bang B).


Theorem SubAreVal: forall A B, Subtyping A B -> validT A /\ validT B.
intros.  dependent induction H; split;[ > try apply vQubit ..];
[> try apply vOne ..];[> try apply vBool..];
[> try apply vTensor..];[> try apply vArrow..];[> try apply vCirc..];
[> try inversion IHSubtyping1; try inversion IHSubtyping2..];auto;
[> try inversion H1; try inversion H2 ..];auto; 
inversion IHSubtyping; auto. inversion IHSubtyping. destruct B; [ apply bQubit| apply bOne|
apply bBool| apply bTensor| apply bArrow|
apply bCirc|..]; [inversion H2..|auto];auto.
inversion H;   try rewrite <- H7 in H0;
inversion H0.
Qed.


 
Theorem Subtyping_Prop1_qubit: forall B, Subtyping qubit B -> B = qubit.
Proof.
intros.  
dependent  induction H. reflexivity. 
Qed.

Theorem Subtyping_Prop1_one: forall B, Subtyping  one B -> B = one.
Proof.
intros.  
dependent  induction H. reflexivity.
Qed.

Theorem Subtyping_bang_one: forall B, Subtyping  (bang one) B -> B = one
\/ B = bang one.
Proof.
intros.  
dependent  induction H; apply Subtyping_Prop1_one in H
 ; [left|right; rewrite H] ;auto.
Qed.


Theorem Subtyping_Prop1_bool: forall B, Subtyping  bool B -> B = bool.
Proof.
intros.  
dependent  induction H. reflexivity. 
Qed.


Theorem Subtyping_bang_bool: forall B, Subtyping  (bang bool) B -> B = bool
\/ B = bang bool.
Proof.
intros.  
dependent  induction H; apply Subtyping_Prop1_bool in H
 ; [left|right; rewrite H] ;auto.
Qed.

Theorem sub_ref: forall A, validT A -> Subtyping A A.
Proof.
intros. induction A. apply QubitSub.
apply OneSub. apply BoolSub. apply TensorSub;  auto; inversion H; auto.
apply ArrowSub;  auto; inversion H; auto. apply CircSub;auto; inversion H;
 apply valid_is_T in H2 ; apply valid_is_T in H3; auto.  apply BangSub2. 
apply bang_valid in H. auto. auto.
Qed.


Theorem Subtyping_arrow_inv:
forall A1 A2 B, Subtyping  (arrow A1 A2) B ->
 exists B1 B2, B = arrow B1 B2
/\ Subtyping B1 A1 /\ Subtyping  A2 B2.
Proof.
intros. dependent induction H. exists A3,B2. auto.
Qed.

Theorem Subtyping_circ_inv:
forall A1 A2 B, Subtyping (circ A1 A2) B ->
 exists B1 B2, B = circ B1 B2
/\ Subtyping  B1 A1 /\ Subtyping  A2 B2.
Proof.
intros. dependent induction H. exists A3,B2. auto.
Qed.

Theorem Subtyping_tensor_inv:
forall A1 A2 B, Subtyping (tensor A1 A2) B -> 
exists B1 B2, B = tensor B1 B2
/\ Subtyping A1 B1 /\ Subtyping A2 B2.
Proof.
intros. dependent induction H. exists B1,B2.  auto. 
Qed.


Theorem Subtyping_bang_inv:
forall A B1, Subtyping A (bang B1) -> exists A1, A = (bang A1)
/\ Subtyping A1 B1.
Proof.
intros. dependent induction H. inversion H;subst;inversion H0. 
exists A. split;auto. 
Qed.


Theorem  Prop2_14: forall A, validT (bang A) -> Subtyping (bang A) A.
Proof.
intros. apply  BangSub1. apply sub_ref. apply bang_valid. auto.
auto. 
Qed.


Definition P1 (A:qtp) (B:qtp)  :Prop :=
valid A ->  valid B -> A =B.

Theorem valid_sub_eq_alt: forall A B,  Subtyping A B ->  P1 A B.
Proof.
intros A B H. apply Subtyping_ind; unfold P1;auto;intros.
inversion H4. inversion H5. apply H1 in H8;auto. apply H3 in H9;auto. 
rewrite H8,H9. auto. inversion H4. inversion H6. 
inversion H3. inversion H3.
Qed.

Theorem valid_sub_eq: forall A B, valid A ->  valid B ->
   Subtyping A B -> A =B.
Proof.
intros. assert (H2:=valid_sub_eq_alt).
unfold P1 in H2. apply H2; auto.
Qed.


Definition P (A:qtp) (B:qtp)  :Prop :=
forall C, (Subtyping B C -> Subtyping A C)
/\ (Subtyping C A-> Subtyping C B).



Theorem sub_trans_alt:
forall A B, Subtyping A B -> P A B.
Proof. intros. apply Subtyping_ind; unfold P;auto. 
intros. split; intros;
inversion H4;[apply TensorSub..|auto] ;
[apply H1 with (C:=B0) in H7|apply H3 with (C:=B3) in H9|
apply H1 with (C:=A0) in H8|apply H3 with (C:=A3) in H9|..]; auto.
inversion H5;subst;[apply BangSub1|inversion H6];auto.
apply TensorSub. apply H1 with (C:=A3) in H12. auto.
apply H3 with (C:=A4) in H13. auto.

intros. split; intros;
inversion H4;[apply ArrowSub..|auto] ;
[apply H1 with (C:=A3) in H7|apply H3 with (C:=B3) in H9|
apply H1 with (C:=A0) in H8|apply H3 with (C:=B0) in H9|..]; auto.
inversion H5;subst;[apply BangSub1|inversion H6];auto.
apply ArrowSub. apply H1 with (C:=A3) in H12. auto.
apply H3 with (C:=B3) in H13. auto.


intros. split; intros;
inversion H6;[apply CircSub;auto..|auto] ;
[apply H1 with (C:=A3) in H9|apply H3 with (C:=B3) in H10|
apply H1 with (C:=A0) in H9|apply H3 with (C:=B0) in H10|..]; auto.
inversion H7;subst;[apply BangSub1|inversion H8];auto.
apply CircSub;auto. apply H1 with (C:=A3) in H13. auto.
apply H3 with (C:=B3) in H14. auto.



intros. split. intros. apply BangSub1. 
apply H1 with (C:=C) in H3. auto. auto.
intros. assert (H3':=H3). apply  Subtyping_bang_inv in H3. inversion H3.
inversion H4. apply  H1 with (C:=x) in H6.
apply BangSub1 in H6. rewrite H5. auto. rewrite H5 in H3'. 
apply SubAreVal in H3'. inversion H3'. auto.
intros. split. intros. inversion H3. apply H1 in H5.
apply BangSub1;auto.
apply H1 in H5. apply BangSub2;auto.
intros. assert (H3':=H3). apply  Subtyping_bang_inv in H3. inversion H3.
inversion H4. apply  H1 with (C:=x) in H6. apply BangSub2 in H6. rewrite H5. 
auto. rewrite H5 in H3'. apply SubAreVal in H3'. inversion H3'. auto.
Qed.


Theorem sub_trans:
forall A B C, Subtyping A B -> Subtyping B C -> Subtyping A C.
Proof.
intros A B C H. apply sub_trans_alt in H. unfold P in H.  apply H with (C:= C).
Qed.

Theorem sub_bang_ornot: forall A B, Subtyping A B -> 
  validT(bang A) \/ exists C, A = bang C.
Proof.
intros. induction H;[left..|right|right]; [apply bQubit| apply bOne|
 apply bBool | apply bTensor; apply SubAreVal in H;apply SubAreVal in H0;inversion 
H;inversion H0;auto| apply bArrow; apply SubAreVal in H;apply SubAreVal in H0;inversion 
H;inversion H0;auto| apply bCirc; inversion H1;inversion H2;auto| exists A| 
exists A]; auto.
Qed.

Theorem sub_not_bang:forall A B, Subtyping A B -> 
  validT(bang A) -> validT(bang B).
Proof.
intros. inversion H0;subst. apply Subtyping_Prop1_qubit in H. subst. 
apply bQubit.
apply Subtyping_Prop1_one in H. subst. apply bOne.
apply Subtyping_Prop1_bool in H. subst. apply bBool.
apply Subtyping_tensor_inv in H. inversion H. inversion H1. inversion H4. subst.
apply bTensor;
inversion H4; inversion H6; 
[apply SubAreVal in H8; inversion H8|
apply SubAreVal in H9; inversion H9];auto.
apply Subtyping_arrow_inv in H. inversion H. inversion H1. inversion H4. subst. 
apply bArrow;inversion H4; inversion H6; [
apply SubAreVal in H8; inversion H8| 
apply SubAreVal in H9; inversion H9];auto.
assert(H':=H). apply Subtyping_circ_inv in H. inversion H. inversion H1. inversion H4. subst. 
apply bCirc;apply SubAreVal in H'; inversion H'; inversion H7;auto.
Qed.

Theorem isval_bang_val: forall A, validT(bang A) -> validT A.
Proof.
intros. inversion H. apply vQubit. apply vOne.
apply vBool. apply vTensor;auto. apply vArrow;auto.
apply vCirc;auto.
Qed.

Theorem one_bang_one: forall A, Subtyping A one -> A = one \/ A = bang one.
Proof.
intros. inversion H;auto. inversion H0;subst; inversion H1. right.
auto.
Qed. 

Theorem bang_one: forall A, Subtyping (bang A) (bang one) -> A = one.
Proof.
intros. inversion H;auto. apply Subtyping_bang_inv in H1.
inversion H1. inversion H4. subst. inversion H2. apply one_bang_one in H2.
destruct H2;auto. subst. inversion H3.
Qed. 

Theorem bool_bang_bool: forall A, Subtyping A bool -> A = bool 
\/ A = bang bool.
Proof.
intros. inversion H;auto. inversion H0;subst; inversion H1. right.
auto.
Qed. 

Theorem bang_bool: forall A, Subtyping (bang A) (bang bool) -> A = bool.
Proof.
intros. inversion H;auto. apply Subtyping_bang_inv in H1.
inversion H1. inversion H4. subst. inversion H2. apply bool_bang_bool in H2.
destruct H2;auto. subst. inversion H3.
Qed. 

Theorem sub_valid_sub_valid: forall A, valid A -> forall B,Subtyping A B ->
valid B. 
Proof.
intros A H. induction H;intros. inversion H.
apply Qubit. inversion H.
apply One. inversion H1. apply Tensor. apply IHvalid1 with (B:=B1).
auto. apply IHvalid2 with (B:=B2).
auto. 
Qed.

Theorem sub_valid_sub_eq: forall A, valid A -> forall B,Subtyping A B ->
A=B. 
Proof.
intros A H. induction H;intros. inversion H. auto.
inversion H. auto.
inversion H1.  apply IHvalid1 with (B:=B1) in H4.
apply IHvalid2 with (B:=B2) in H6. subst.
auto. 
Qed.

Theorem qubit_bang_qubit: forall A, Subtyping A qubit -> A = qubit 
\/ A = bang qubit.
Proof.
intros. inversion H;auto. inversion H0;subst; inversion H1. right.
auto.
Qed. 

Theorem subtyp_valid: forall  v, valid v -> forall a b, Subtyping a v
-> Subtyping a b -> Subtyping b v.
Proof.
intros v H. induction H; intros. apply qubit_bang_qubit in H.
destruct H;  subst.  
apply Subtyping_Prop1_qubit in H0.
subst. apply QubitSub.
inversion H0;
apply Subtyping_Prop1_qubit in H1;
subst; try apply BangSub1; try apply QubitSub; apply bQubit.

apply one_bang_one in H.
destruct H;  subst.  
apply Subtyping_Prop1_one in H0.
subst. apply OneSub.
inversion H0;
apply Subtyping_Prop1_one in H1;
subst; try apply BangSub1; try apply OneSub; apply bOne.

inversion H1.  subst.  inversion H2.
subst. apply TensorSub. apply IHvalid1 with (b:=B1) in H6;auto.
apply IHvalid2 with (b:=B2) in H7;auto.
inversion H3;[..|subst;inversion H4].
subst. inversion H2. inversion H6.
subst. apply TensorSub.
apply IHvalid1 with (b:=B1) in H13;auto.
apply IHvalid2 with (b:=B2) in H15;auto.
inversion H6. subst. apply BangSub1. apply TensorSub.
apply IHvalid1 with (b:=B1) in H13;auto.
apply IHvalid2 with (b:=B2) in H15;auto.
apply SubAreVal in H2. inversion H2. auto.
Qed.

