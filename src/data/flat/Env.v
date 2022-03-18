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

Require Import List Bool Arith NArith.
Require Import BasicTacs BasicFacts Bool3 ListFacts ListSort ListPermut
        OrderedSet Partition FiniteSet FiniteBag FiniteCollection Join.

Require Export FTuples.
Require Export FTerms.
Require Export ATerms.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Inductive group_by : Type :=
  | Group_By : list (aggterm T) -> group_by
  | Group_Fine.

Definition env_slice := (Fset.set (A T) * group_by * list (tuple T))%type.
Definition env := (list env_slice).

Definition env_t (env : env) t := (labels T t, Group_Fine, t :: nil) :: env. 

Definition env_g (env : env) g s := 
  (match quicksort (OTuple T) s with 
   | nil => Fset.empty _ 
   | t :: _ => labels T t 
   end, g, s) :: env.

Lemma env_t_env_g : forall env t, env_t env t = env_g env Group_Fine (t :: nil).
Proof.
intros env t; apply refl_equal.
Qed.

Definition equiv_env_slice (e1 e2 : (Fset.set (A T) * group_by * (list (tuple T)))) := 
  match e1, e2 with
    | (sa1, g1, x1), (sa2, g2, x2) => 
      sa1 =S= sa2 /\ g1 = g2 /\ x1 =PE= x2
  end.

Definition equiv_env e1 e2 := Forall2 equiv_env_slice e1 e2.

Lemma equiv_env_refl : forall e, equiv_env e e.
Proof.
intro e; unfold equiv_env; induction e as [ | [[sa g] l] e]; simpl; trivial.
constructor 2; [simpl; repeat split | apply IHe].
- apply Fset.equal_refl.
- apply Oeset.permut_refl.
Qed.

Lemma equiv_env_sym :
  forall e1 e2, equiv_env e1 e2 <-> equiv_env e2 e1.
Proof.
assert (H : forall e1 e2, equiv_env e1 e2 -> equiv_env e2 e1).
{
  intro e1; induction e1 as [ | s1 e1]; intros [ | s2 e2].
  - exact (fun h => h).
  - intro H; inversion H.
  - intro H; inversion H.
  - intro H; simpl in H.
    inversion H; subst.
    simpl in H.
    constructor 2; [ | apply IHe1; assumption].
    destruct s1 as [[sa1 g1] l1]; destruct s2 as [[sa2 g2] l2]; simpl in H3; simpl.
    destruct H3 as [K1 [K2 K3]].
    split; [rewrite <- (Fset.equal_eq_1 _ _ _ _ K1); apply Fset.equal_refl | ].
    split; [apply sym_eq; assumption | ].
    apply Oeset.permut_sym; apply K3.
}
intros e1 e2; split; apply H.
Qed.

Definition weak_equiv_env_slice (e1 e2 : (Fset.set (A T) * group_by * (list (tuple T)))) := 
  match e1, e2 with
    | (sa1, g1, x1), (sa2, g2, x2) => sa1 =S= sa2 /\ g1 = g2
  end.

Definition weak_equiv_env e1 e2 := Forall2 weak_equiv_env_slice e1 e2.

Lemma weak_equiv_env_sym :
  forall e1 e2, weak_equiv_env e1 e2 <-> weak_equiv_env e2 e1.
Proof.
intro e1; induction e1 as [ | [[sa1 g1] x1] e1]; intro e2; simpl; split.
- intro H; inversion H; constructor 1.
- intro H; inversion H; constructor 1.
- destruct e2 as [ | [[sa2 g2] x2] e2]; intro H; inversion H; subst.
  constructor 2; [ | rewrite <- IHe1; assumption].
  simpl in H3; simpl; destruct H3 as [H3 H3']; split; [ | apply sym_eq; assumption].
  rewrite (Fset.equal_eq_2 _ _ _ _ H3); apply Fset.equal_refl.
- destruct e2 as [ | [[sa2 g2] x2] e2]; intro H; inversion H; subst.
  constructor 2; [ | rewrite IHe1; assumption].
  simpl in H3; destruct H3 as [H3 K3]; subst; simpl; repeat split.
  unfold weak_equiv_env in H; inversion H; subst; simpl in H3.
  rewrite (Fset.equal_eq_2 _ _ _ _ H3); apply Fset.equal_refl.
Qed.

Lemma equiv_env_weak_equiv_env :
  forall e1 e2, equiv_env e1 e2 -> weak_equiv_env e1 e2.
Proof.
intro e1; induction e1 as [ | [[sa1 g1] l1] e1]; intros [ | [[sa2 g2] l2] e2]; 
  intro He; inversion He; subst.
- constructor 1.
- constructor 2; [ | apply IHe1; trivial].
  unfold weak_equiv_env_slice; unfold equiv_env_slice in H2.
  split; [apply (proj1 H2) | apply (proj1 (proj2 H2))].
Qed.

Lemma env_slice_eq_1 :
  forall x1 x2, Oeset.compare (OLTuple T) x1 x2 = Eq ->
   match quicksort (OTuple T) x1 with
   | nil => emptysetS
   | t0 :: _ => labels T t0
   end =S=
   match quicksort (OTuple T) x2 with
   | nil => emptysetS
   | t0 :: _ => labels T t0
   end.
Proof.
intros l1 l2 Hl; unfold OLTuple, OLA in Hl; simpl in Hl.
unfold compare_OLA in Hl.
set (q1 := quicksort (OTuple T) l1) in *.
set (q2 := quicksort (OTuple T) l2) in *.
destruct q1 as [ | x1 q1]; destruct q2 as [ | x2 q2]; try discriminate Hl.
- apply Fset.equal_refl.
- simpl in Hl.
  case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in Hl; try discriminate Hl.
  rewrite tuple_eq in Hx; apply (proj1 Hx).
Qed.

Lemma env_t_eq_1 :
  forall e1 e2 x, equiv_env e1 e2 -> equiv_env (env_t e1 x) (env_t e2 x).
Proof.
intros e1 e2 x He.
constructor 2; [ | apply He].
simpl; repeat split.
- apply Fset.equal_refl.
- apply Oeset.permut_refl.
Qed.

Lemma env_t_eq_2 :
  forall e x1 x2, x1 =t= x2 ->  equiv_env (env_t e x1) (env_t e x2).
Proof.
intros e x1 x2 Hx.
constructor 2.
- simpl; repeat split.
  + rewrite tuple_eq in Hx; apply (proj1 Hx).
  + simpl; apply compare_list_t; unfold compare_OLA; simpl.
    rewrite Hx; apply refl_equal.
- apply equiv_env_refl.
Qed.

Lemma env_t_eq :
  forall e1 e2 x1 x2, equiv_env e1 e2 -> x1 =t= x2 -> equiv_env (env_t e1 x1) (env_t e2 x2).
Proof.
intros e1 e2 x1 x2 He Hx.
constructor 2; [ | apply He].
simpl; repeat split.
- rewrite tuple_eq in Hx; apply (proj1 Hx).
- simpl; apply compare_list_t; unfold compare_OLA; simpl.
  rewrite Hx; apply refl_equal.
Qed.

Lemma env_g_eq_1 :
  forall e1 e2 g x, equiv_env e1 e2 -> equiv_env (env_g e1 g x) (env_g e2 g x).
Proof.
intros e1 e2 g x He.
constructor 2; [ | apply He].
simpl; repeat split.
- apply Fset.equal_refl.
- apply Oeset.permut_refl.
Qed.

Lemma env_g_eq_2 :
  forall e g x1 x2, x1 =PE= x2 ->  equiv_env (env_g e g x1) (env_g e g x2).
Proof.
intros e g x1 x2 Hx.
constructor 2.
- simpl; repeat split.
  + apply env_slice_eq_1; simpl; rewrite <- compare_list_t; assumption.
  + assumption.
- apply equiv_env_refl.
Qed.

Lemma env_g_eq :
  forall e1 e2 g x1 x2, equiv_env e1 e2 -> x1 =PE= x2 -> equiv_env (env_g e1 g x1) (env_g e2 g x2).
Proof.
intros e1 e2 g x1 x2 He Hx.
constructor 2; [ | apply He].
- simpl; repeat split.
  + apply env_slice_eq_1; simpl; rewrite <- compare_list_t; assumption.
  + assumption.
Qed.

Lemma env_g_fine_eq_2 :
  forall e x1 x2, 
    x1 =t= x2 -> 
    equiv_env (env_g e Group_Fine (x1 :: nil)) (env_g e Group_Fine (x2 :: nil)).
Proof.
intros e x1 x2 Hx.
constructor 2.
- simpl; repeat split.
  + rewrite tuple_eq in Hx; apply (proj1 Hx).
  + simpl; apply compare_list_t; unfold compare_OLA; simpl.
    rewrite Hx; apply refl_equal.
- apply equiv_env_refl.
Qed.

End Sec.


Ltac env_tac :=
  match goal with
    | |- equiv_env _ ?e ?e => apply equiv_env_refl

(* env_t *)
    | He : equiv_env _ ?e1 ?e2 
      |- equiv_env _ (env_t _ ?e1 ?x) (env_t _ ?e2 ?x) =>
      apply env_t_eq_1; assumption

    | Hx : ?x1 =t= ?x2 
    |- equiv_env _ (env_t _ ?e ?x1) (env_t _ ?e ?x2) =>
      apply env_t_eq_2; assumption

    | He : equiv_env _ ?e1 ?e2, Hx : ?x1 =t= ?x2 
      |- equiv_env _ (env_t _ ?e1 ?x1) (env_t _ ?e2 ?x2) =>
      apply env_t_eq; assumption

(* env_g *)
    | Hx : Oeset.compare (Tuple.OTuple ?T) ?x1 ?x2 = Eq 
    |- equiv_env ?T (env_g ?T ?e ?g (?x1 :: nil)) 
                       (env_g ?T ?e ?g (?x2 :: nil)) =>
      rewrite <- !env_t_env_g; apply env_t_eq_2; assumption

    | Hx : Oeset.compare (Tuple.OLTuple ?T) ?x1 ?x2 = Eq
      |- equiv_env ?T (env_g ?T ?e ?g ?x1) (env_g ?T ?e ?g ?x2) =>
      apply env_g_eq_2; rewrite compare_list_t; assumption

    | He : equiv_env _ ?e1 ?e2
      |- equiv_env _ (env_g _ ?e1 ?g ?x) (env_g _ ?e2 ?g ?x) =>
      apply env_g_eq_1; assumption

    | He : equiv_env _ ?e1 ?e2, 
      Hx : Oeset.compare _ ?x1 ?x2 = Eq 
      |- equiv_env _ (env_g _ ?e1 ?g ?x1) (env_g _ ?e2 ?g ?x2) =>
      apply env_g_eq; [ | rewrite compare_list_t]; assumption

    | Hl : comparelA (Oeset.compare _) ?l1 ?l2 = Eq 
      |- equiv_env ?T (env_g ?T ?e (Group_By ?T ?g) ?l1) 
                         (env_g ?T ?e (Group_By ?T ?g) ?l2) =>
      apply env_g_eq_2; apply Oeset.permut_refl_alt; assumption

(*
    | |- Tuple.equiv_env ?T (Tuple.env_g ?T ?e ?g (?x1 :: nil)) 
                         (Tuple.env_g ?T ?e ?g (?x2 :: nil)) => 
      let h := fresh "__YY" in 
      assert (h := refl_equal 2%N);
      rewrite <- !Tuple.env_t_env_g                         

    | |- Tuple.equiv_env ?T (Tuple.env_g ?T ?e Tuple.Group_Fine (?x1 :: nil)) 
                       (Tuple.env_g ?T ?e Tuple.Group_Fine (?x2 :: nil)) =>
      assert (__XX1 := refl_equal 1%N)
*)
    | _ =>  trivial; fail
  end.
