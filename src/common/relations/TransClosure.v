(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                       LMF, CNRS & Université Paris-Saclay                       *)
(**                                                                                 *)
(**                        Copyright 2016-2022 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments. 

Require Import Relations.

Inductive trans_clos (A : Type) (R : relation A) : relation A:=
  | t_step : forall x y, R x y -> trans_clos R x y
  | t_trans : forall x y z, R x y -> trans_clos R y z -> trans_clos R x z.

Inductive trans_clos_alt (A : Type) (R : relation A) : relation A:=
  | t_step_alt : forall x y, R x y -> trans_clos_alt R x y
  | t_trans_lat : forall x y z, trans_clos_alt R x y -> R y z -> trans_clos_alt R x z.

Lemma trans_clos_is_trans :
  forall A  (R : relation A) a b c, trans_clos R a b -> trans_clos R b c -> trans_clos R a c.
Proof.
intros A R a b c Hab; revert c; induction Hab as [a b Hab | a b c Hab Hbc].
intros c Hbc; apply t_trans with b; trivial.
intros d Hcd; apply t_trans with b; trivial.
apply IHHbc; trivial.
Qed.

Lemma trans_clos_is_idem :
  forall A  (R : relation A) a b, trans_clos (trans_clos R) a b -> trans_clos R a b.
Proof.
intros A R a b Hab; induction Hab as [a b Hab | a b c Hab Hbc]; trivial.
apply trans_clos_is_trans with b; trivial.
Qed.

Lemma trans_clos_incl :
  forall A (R1 R2 : relation A), inclusion _ R1 R2 -> inclusion _ (trans_clos R1) (trans_clos R2).
Proof.
intros A R1 R2 R1_in_R2 a b H; induction H as [a' b' H | a' b' c' H1 H2].
apply t_step; apply R1_in_R2; trivial.
apply t_trans with b'; trivial.
apply R1_in_R2; trivial.
Qed.

Lemma trans_clos_incl_of :
  forall A B (f : A -> B) (R1 : relation A) (R2 : relation B), 
  (forall a1 a2, R1 a1 a2 -> R2 (f a1) (f a2)) -> 
	forall a1 a2, trans_clos R1 a1 a2 ->  trans_clos R2 (f a1) (f a2).
Proof.
intros A B f R1 R2 R1_in_R2 a b H; induction H as [a' b' H | a' b' c' H1 H2].
apply t_step; apply R1_in_R2; trivial.
apply t_trans with (f b'); trivial.
apply R1_in_R2; trivial.
Qed.

Lemma trans_clos_alt_is_trans :
  forall A  (R : relation A) a b c, 
  trans_clos_alt R a b -> trans_clos_alt R b c -> trans_clos_alt R a c.
Proof.
intros A R a b c Hab Hbc; revert a Hab.
induction Hbc as [b c Hbc | b c d Hbc Hcd]; intros a Hab.
right with b; trivial.
right with c; trivial.
apply Hcd; trivial.
Qed.

Lemma trans_clos_trans_clos_alt : 
  forall A (R : relation A) x y, trans_clos R x y <-> trans_clos_alt R x y.
Proof.
intros A R; split; intro H; induction H.
left; assumption.
apply trans_clos_alt_is_trans with y; trivial.
left; assumption.
left; assumption.
apply trans_clos_is_trans with y; trivial.
left; assumption.
Qed.

Lemma transp_trans_clos :
  forall A (R : relation A) x y, transp _ (trans_clos R) x y <-> trans_clos (transp _ R) x y.
Proof.
intros A R x y; split; intro H; induction H as [a1 a2 H1 | a1 a2 a3 H1 H2].
left; assumption.
apply trans_clos_is_trans with a2; [ | left]; assumption.
left; assumption.
apply trans_clos_is_trans with a2; [ | left]; assumption.
Qed.

Lemma acc_trans :
 forall A (R : relation A) a, Acc R a -> Acc (trans_clos R) a.
Proof.
intros A R a Acc_R_a.
induction Acc_R_a as [a Acc_R_a IH].
apply Acc_intro.
intros b b_Rp_a; induction b_Rp_a.
apply IH; trivial.
apply Acc_inv with y.
apply IHb_Rp_a; trivial.
apply t_step; trivial.
Qed.

Lemma wf_trans :
  forall A (R : relation A) , well_founded R -> well_founded (trans_clos R).
Proof.
unfold well_founded; intros A R WR.
intro; apply acc_trans; apply WR; trivial.
Qed.

