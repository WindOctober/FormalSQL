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

Require Import Arith List ListPermut.
Require Import OrderedSet.

Set Implicit Arguments.

Module Bool.

Record Rcd : Type :=
  mk_R {
      b : Type;
      true : b;
      false : b;
      andb : b -> b -> b;
      orb : b -> b -> b;
      negb : b -> b;
      true_diff_false : true <> false;
      andb_true_l : forall b, andb true b = b;
      andb_false_l : forall b, andb false b = false;
      andb_true_iff : forall b1 b2, andb b1 b2 = true <-> (b1 = true /\ b2 = true);
      andb_false_iff : forall b1 b2, andb b1 b2 = false <-> (b1 = false \/ b2 = false);
      orb_true_l : forall b, orb true b = true;
      orb_false_l : forall b, orb false b = b;
      orb_true_iff : forall b1 b2, orb b1 b2 = true <-> (b1 = true \/ b2 = true);
      orb_false_iff : forall b1 b2, orb b1 b2 = false <-> (b1 = false /\ b2 = false);
      negb_true : negb true = false;
      negb_false : negb false = true;
      negb_andb : forall b1 b2, negb (andb b1 b2) = orb (negb b1) (negb b2);
      negb_negb : forall b, negb (negb b) = b;
      andb_comm : forall b1 b2, andb b1 b2 = andb b2 b1;
      andb_assoc : forall b1 b2 b3, andb b1 (andb b2 b3) = andb (andb b1 b2) b3;
      orb_comm : forall b1 b2, orb b1 b2 = orb b2 b1;
      orb_assoc : forall b1 b2 b3, orb b1 (orb b2 b3) = orb (orb b1 b2) b3;
      is_true : b -> bool;
      true_is_true : forall b, is_true b = Datatypes.true <-> b = true
    }.

Section Sec.

Hypothesis B : Rcd.

Lemma is_true_andb :
  forall b1 b2, is_true B (andb B b1 b2) = Datatypes.andb (is_true B b1) (is_true B b2).
Proof.
intros b1 b2.
rewrite BasicFacts.eq_bool_iff, !Bool.Bool.andb_true_iff, !true_is_true, andb_true_iff.
intuition.
Qed.

Lemma andb_diff_false_iff :
  forall b1 b2, andb B b1 b2 <> false B <-> (b1 <> false B /\ b2 <> false B).
Proof.
intros b1 b2; split; intro H.
- split.
  + intro H1; rewrite H1, andb_false_l in H; apply H; apply refl_equal.
  + intro H2; rewrite H2, andb_comm, andb_false_l in H; apply H; apply refl_equal.
- destruct H as [H1 H2]; intro H.
  rewrite andb_false_iff in H.
  destruct H as [H | H].
  + rewrite H in H1; apply H1; apply refl_equal.
  + rewrite H in H2; apply H2; apply refl_equal.
Qed.

Fixpoint existsb (A : Type) (f : A -> b B) (l : list A) :=
  match l with
  | nil => false B
  | x :: l => orb B (f x) (existsb f l)
  end.

Fixpoint forallb (A : Type) (f : A -> b B) (l : list A) :=
  match l with
  | nil => true B
  | x :: l => andb B (f x) (forallb f l)
  end.

Lemma existsb_unfold :
  forall (A : Type) (f : A -> b B) (l : list A), 
    existsb f l =
    match l with
    | nil => false B
    | x :: l => orb B (f x) (existsb f l)
    end.
Proof.
intros A f l; case l; intros; apply refl_equal.
Qed.


Lemma forallb_unfold :
  forall (A : Type) (f : A -> b B) (l : list A),
    forallb f l =
    match l with
    | nil => true B
    | x :: l => andb B (f x) (forallb f l)
    end.
Proof.
intros A f l; case l; intros; apply refl_equal.
Qed.

Lemma existsb_not_forallb_not :
  forall (A : Type) (f : A -> b B) (l : list A),
    existsb f l = negb B (forallb (fun x => negb B (f x)) l).
Proof.
intros A f l; induction l as [ | a1 l]; simpl.
- rewrite negb_true; apply refl_equal.
- rewrite IHl, negb_andb; apply f_equal2; [ | apply refl_equal].
  rewrite negb_negb; apply refl_equal.
Qed.

Lemma forallb_forall_true :
  forall (A : Type) (f : A -> b B) (l : list A),
    forallb f l = true B <-> (forall x, In x l -> f x = true B).
Proof.
intros A f l; induction l as [ | a1 l]; split; intro H.
- intros a Ha; contradiction Ha.
- apply refl_equal.
- intros a Ha; simpl in H, Ha.
  rewrite andb_true_iff in H.
  destruct Ha as [Ha | Ha].
  + subst; apply (proj1 H).
  + rewrite IHl in H; apply (proj2 H); assumption.
- simpl.
  rewrite andb_true_iff; split.
  + apply H; left; apply refl_equal.
  + rewrite IHl; intros; apply H; right; assumption.
Qed.

Lemma forallb_forall_false :
  forall (A : Type) (f : A -> b B) (l : list A), 
    forallb f l = false B <-> (exists x, In x l /\ f x = false B).
Proof.
intros A f l; induction l as [ | a1 l]; split; intro H.
- simpl in H; apply False_rec; apply (true_diff_false _ H).
- destruct H as [x [H _]]; contradiction H.
- simpl in H.
  rewrite andb_false_iff in H; destruct H as [H | H].
  + exists a1; split; [left | ]; trivial.
  + rewrite IHl in H.
    destruct H as [x [Hl Hx]].
    exists x; split; [right | ]; trivial.
- destruct H as [x [Hx H]].
  simpl in Hx; destruct Hx as [Hx | Hx].
  + subst x; simpl; rewrite H; simpl; apply andb_false_l.
  + simpl; rewrite andb_false_iff; right.
    rewrite IHl; exists x; split; trivial.
Qed.

Lemma forallb_app :
  forall (A : Type) (f : A -> b B) (l1 l2 : list A),
    forallb f (l1 ++ l2) = andb B (forallb f l1) (forallb f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; intros l2; simpl.
- rewrite andb_true_l; apply refl_equal.
- rewrite IHl1, andb_assoc; apply refl_equal.
Qed.

Lemma forallb_forallb_unfold :
  forall A (OA : Oeset.Rcd A) (i : A -> A -> b B) x1 l1 l2,
    forallb (A := A) (fun x => forallb (A := A) (i x) (x1 :: l1)) l2 = 
  andb B (forallb (A := A) (fun x => i x x1) l2) 
       (forallb (A := A) (fun x => forallb (A := A) (i x) l1) l2).
Proof.
intros A OA i x1 l1 l2; revert x1 l1; induction l2 as [ | x2 l2]; intros x1 l1.
- simpl; rewrite andb_true_l; apply refl_equal.
- rewrite 4 (forallb_unfold _ (_ :: _)), IHl2.
  rewrite 2 andb_assoc.
  apply f_equal2; [ | apply refl_equal].
  rewrite <- 2 andb_assoc; apply f_equal.
  apply andb_comm.
Qed.

Lemma forallb_eq :
  forall A (OA : Oeset.Rcd A) i1 i2 s1 s2, 
    _permut  (fun x y : A => Oeset.compare OA x y = Eq) s1 s2 ->
    (forall x1 x2, Oeset.mem_bool OA x1 s1 = Datatypes.true -> 
                   Oeset.compare OA x1 x2 = Eq -> i1 x1 = i2 x2) ->
    forallb (A := A) i1 s1 = forallb (A := A) i2 s2.
Proof.
intros A OA i1 i2 s1.
set (n := length s1); assert (Hn := le_refl n); unfold n at 1 in Hn; clearbody n.
revert s1 Hn; induction n as [ | n].
- intros s1 Hn; destruct s1; [ | inversion Hn].
  intros s2 H; inversion H.
  intros; apply refl_equal.
- intros s1 Hn; destruct s1; [intros s2 H; inversion H; intros; apply refl_equal | ].
  intros s2 H; inversion H; subst.
  intros H1; simpl.
  rewrite forallb_app; simpl.
  rewrite (andb_comm _ (forallb _ _) _), <- andb_assoc.
  apply f_equal2.
  + apply H1; [ | assumption].
    rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
  + rewrite andb_comm, <- forallb_app.
    apply IHn.
    * simpl in Hn; apply (le_S_n _ _ Hn).
    * assumption. 
    * intros x1 x2 Hx1; apply H1.
      rewrite Oeset.mem_bool_unfold, Hx1, Bool.Bool.orb_true_r.
      apply refl_equal.
Qed.

Lemma existsb_exists_true :
  forall (A : Type) (f : A -> b B) (l : list A),
    existsb f l = true B <-> (exists x, In x l /\ f x = true B).
Proof.
intros A f l; induction l as [ | a1 l]; split; intro H.
- apply False_rec; apply (true_diff_false _ (sym_eq H)).
- destruct H as [x [Hx _]]; contradiction Hx.
- simpl in H.
 rewrite Bool.orb_true_iff in H; destruct H as [H | H].
 + exists a1; split; [left; apply refl_equal | assumption].
 + rewrite IHl in H.
   destruct H as [x [Hx Kx]]; exists x; split; [right | ]; assumption.
- destruct H as [x [Hx Kx]]; simpl; rewrite Bool.orb_true_iff.
  simpl in Hx; destruct Hx as [Hx | Hx].
  + subst x; simpl; left; assumption.
  + right; rewrite IHl; exists x; split; assumption.
Qed.

Lemma existsb_exists_false :
  forall (A : Type) (f : A -> b B) (l : list A),
    existsb f l = false B <-> (forall x, In x l -> f x = false B).
Proof.
intros A f l; induction l as [ | a1 l]; split; intro H.
- intros x Hx; contradiction Hx.
- apply refl_equal.
- simpl in H; rewrite Bool.orb_false_iff in H.
  destruct H as [H1 H2].
  intros x Hx; simpl in Hx; destruct Hx as [Hx | Hx].
  + subst x; apply H1.
  + rewrite IHl in H2; apply H2; assumption.
- simpl; rewrite (H a1 (or_introl _ (refl_equal _))).
  rewrite Bool.orb_false_l, IHl.
  intros x Hx; apply H; right; assumption.
Qed.

Lemma existsb_app :
  forall (A : Type) (f : A -> b B) (l1 l2 : list A),
    existsb f (l1 ++ l2) = orb B (existsb f l1) (existsb f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; intros l2; simpl.
- rewrite orb_false_l; apply refl_equal.
- rewrite IHl1, orb_assoc; apply refl_equal.
Qed.

Lemma existsb_existsb_unfold :
  forall A (OA : Oeset.Rcd A) (i : A -> A -> b B) x1 l1 l2,
    existsb (A := A) (fun x => existsb (A := A) (i x) (x1 :: l1)) l2 = 
  orb B (existsb (A := A) (fun x => i x x1) l2) 
       (existsb (A := A) (fun x => existsb (A := A) (i x) l1) l2).
Proof.
intros A OA i x1 l1 l2; revert x1 l1; induction l2 as [ | x2 l2]; intros x1 l1.
- simpl; rewrite orb_false_l; apply refl_equal.
- rewrite 4 (existsb_unfold _ (_ :: _)), IHl2.
  rewrite 2 orb_assoc.
  apply f_equal2; [ | apply refl_equal].
  rewrite <- 2 orb_assoc; apply f_equal.
  apply orb_comm.
Qed.

Lemma existsb_eq :
  forall A (OA : Oeset.Rcd A) i1 i2 s1 s2, 
    _permut  (fun x y : A => Oeset.compare OA x y = Eq) s1 s2 ->
    (forall x1 x2, Oeset.mem_bool OA x1 s1 = Datatypes.true -> 
                   Oeset.compare OA x1 x2 = Eq -> i1 x1 = i2 x2) ->
    existsb (A := A) i1 s1 = existsb (A := A) i2 s2.
Proof.
intros A OA i1 i2 s1.
set (n := length s1); assert (Hn := le_refl n); unfold n at 1 in Hn; clearbody n.
revert s1 Hn; induction n as [ | n].
- intros s1 Hn; destruct s1; [ | inversion Hn].
  intros s2 H; inversion H.
  intros; apply refl_equal.
- intros s1 Hn; destruct s1; [intros s2 H; inversion H; intros; apply refl_equal | ].
  intros s2 H; inversion H; subst.
  intros H1; simpl.
  rewrite existsb_app; simpl.
  rewrite (orb_comm _ (existsb _ _) _), <- orb_assoc.
  apply f_equal2.
  + apply H1; [ | assumption].
    rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
  + rewrite orb_comm, <- existsb_app.
    apply IHn.
    * simpl in Hn; apply (le_S_n _ _ Hn).
    * assumption. 
    * intros x1 x2 Hx1; apply H1.
      rewrite Oeset.mem_bool_unfold, Hx1, Bool.Bool.orb_true_r.
      apply refl_equal.
Qed.

Lemma true_is_true_alt : is_true B (true B) = Datatypes.true.
Proof.
assert (Aux := refl_equal (true B)).
rewrite <- true_is_true in Aux; apply Aux.
Qed.

End Sec.

End Bool.

Definition Bool2 : Bool.Rcd.
split with bool true false andb orb negb (fun b => b).
- discriminate.
- intro; apply refl_equal.
- intro; apply refl_equal.
- intros b1 b2; split.
  + case b1; simpl; [ | intro H; discriminate H].
    exact (fun h => conj (refl_equal _) h).
  + intros [H1 H2]; subst; apply refl_equal.
- intros b1 b2; split.
  + case b1; [ | refine (fun _ => or_introl _ (refl_equal _))].
    exact (fun h => or_intror _ h).
  + intros [H1 | H2]; subst; simpl; [trivial | ].
    apply Bool.andb_false_r.
- intro; apply refl_equal.
- intro; apply refl_equal.
- intros b1 b2; rewrite Bool.Bool.orb_true_iff; exact (conj (fun h => h) (fun h => h)).
- intros b1 b2; rewrite Bool.Bool.orb_false_iff; exact (conj (fun h => h) (fun h => h)).
- apply refl_equal.
- apply refl_equal.
- intros b1 b2; rewrite Bool.Bool.negb_andb; apply refl_equal.
- intro; apply Bool.negb_involutive.
- intros; apply Bool.Bool.andb_comm.
- intros; apply Bool.Bool.andb_assoc.
- intros; apply Bool.Bool.orb_comm.
- intros; apply Bool.Bool.orb_assoc.
- intro; split; exact (fun h => h).
Defined.

Inductive bool3 : Type := true3 | false3 | unknown3.

Definition andb3 b1 b2 :=
  match b1, b2 with
    | true3, true3 => true3
    | true3, false3 => false3
    | true3, unknown3 => unknown3
    | false3, _ => false3
    | unknown3, true3 => unknown3
    | unknown3, false3 => false3
    | unknown3, unknown3 => unknown3
  end.

Definition orb3 b1 b2 :=
  match b1, b2 with
  | true3, _ => true3
  | false3, _ => b2
  | unknown3, true3 => true3
  | unknown3, _ => unknown3
  end.

Definition negb3 b :=
  match b with
  | true3 => false3
  | false3 => true3
  | unknown3 => unknown3
  end.

Definition Bool3 : Bool.Rcd.
split with bool3 true3 false3 andb3 orb3 negb3 
           (fun b => match b with true3 => true | _ => false end).
- discriminate.
- intro b; case b; apply refl_equal.
- intro b; case b; apply refl_equal.
- intros b1 b2; split.
  + case b1.
    * case b2; [simpl; intros _; split; trivial | | ]; intro H; discriminate H.
    * intro H; discriminate H.
    * case b2; intro H; discriminate H.
  + intros [H1 H2]; subst; apply refl_equal.
- intros b1 b2; split.
  + case b1.
    * case b2; intro H; try discriminate H.
      right; apply refl_equal.
    * intros _; left; apply refl_equal.
    * case b2; intro H; try discriminate H.
      right; apply refl_equal.
  + intros [H1 | H2]; subst; simpl; [trivial | ].
    case b1; apply refl_equal.
- intro b; case b; apply refl_equal.
- intro b; case b; apply refl_equal.
- intros b1 b2; case b1; simpl.
  + split; [intro H; left | intros]; apply refl_equal.
  + split; intro H; [right; trivial | ].
    destruct H as [H | H]; [ | assumption].
    discriminate H.
  + case b2.
    * split; intro H; [right | ]; apply refl_equal.
    * split; intro H; [discriminate H | ].
      destruct H as [H | H]; discriminate H.
    * split; intro H; [discriminate H | ].
      destruct H as [H | H]; discriminate H.
- intros b1 b2; case b1; simpl.
  + split; intro H; [discriminate H | ].
    apply (proj1 H). 
  + split; intro H; [split; [apply refl_equal | assumption] | ].
    apply (proj2 H).
  + split; [ | intro H].
    * case b2; intro H; discriminate H.
    * apply False_rec; discriminate (proj1 H).
- apply refl_equal.
- apply refl_equal.
- intros b1 b2; case b1; case b2; apply refl_equal.
- intro b; case b; apply refl_equal.
- intros b1 b2; case b1; case b2; apply refl_equal.
- intros b1 b2 b3; case b1; case b2; case b3; apply refl_equal.
- intros b1 b2; case b1; case b2; apply refl_equal.
- intros b1 b2 b3; case b1; case b2; case b3; apply refl_equal.
- intro b; case b.
  + split; intros _; apply refl_equal.
  + split; intro H; discriminate H.
  + split; intro H; discriminate H.
Defined.

Lemma if_is_true_true3 :
  forall (A : Type) (a1 a2 : A), (if Bool.is_true Bool3 (Bool.true Bool3) then a1 else a2) = a1.
Proof.
intros A a1 a2; apply refl_equal.
Qed.

Lemma if_is_true3 :
  forall (A : Type) (b : Bool.b Bool3) (a1 a2 : A), 
    (if Bool.is_true Bool3 b then a1 else a2) = (match b with | true3 => a1 | _ => a2 end).
Proof.
intros A b a1 a2; case b; apply refl_equal.
Qed.

Lemma eq_bool3_iff :
  forall b1 b2, b1 = b2 <-> 
                (b1 = true3 -> b2 = true3) /\ (b1 = false3 -> b2 = false3) /\ (b1 = unknown3 -> b2 = unknown3).
Proof.
intros b1 b2; split.
- intro H; subst b2; repeat split; exact (fun h => h).
- intros [H1 [H2 H3]]; destruct b1.
  + rewrite (H1 (refl_equal _)); trivial.
  + rewrite (H2 (refl_equal _)); trivial.
  + rewrite (H3 (refl_equal _)); trivial.
Qed.

Lemma forallb3_forall_unknown3 :
  forall (A : Type) (f : A -> bool3) (l : list A),
    Bool.forallb Bool3 f l = unknown3 <-> ((exists x, In x l /\ f x = unknown3) /\ forall x, In x l -> f x <> false3).
Proof.
intros A f l; induction l as [ | a1 l]; split; intro H.
- discriminate H.
- destruct H as [[x [H _]] _]; contradiction H.
- simpl in H.
  case_eq (f a1); intro Ha1; rewrite Ha1 in H; simpl in H; try discriminate H.
  + case_eq (Bool.forallb Bool3 f l); intro Hl; rewrite Hl in H; try discriminate H.
    rewrite IHl in Hl.
    destruct Hl as [[x [Hx Kx]] Hl].
    split.
    * exists x; split; [right | ]; assumption.
    * intros y Hy; simpl in Hy; destruct Hy as [Hy | Hy]; [ | apply Hl; trivial].
      subst y; rewrite Ha1; discriminate.
  + case_eq (Bool.forallb Bool3 f l); intro Hl; rewrite Hl in H; try discriminate H.
    * split; [exists a1; split; [left | ]; trivial | ].
      intros y Hy; simpl in Hy; destruct Hy as [Hy | Hy]; [subst y; rewrite Ha1; discriminate | ].
      rewrite Bool.forallb_forall_true in Hl.
      rewrite Hl; [discriminate | assumption].
    * rewrite IHl in Hl.
      destruct Hl as [[x [Hx Kx]] Hl].
      {
        split.
        - exists x; split; [right | ]; assumption.
        - intros y Hy; simpl in Hy; destruct Hy as [Hy | Hy]; [ | apply Hl; trivial].
          subst y; rewrite Ha1; discriminate.
      }
- destruct H as [[x [Hx Kx]] H].
  simpl in Hx; destruct Hx as [Hx | Hx].
  + subst x; simpl; rewrite Kx; simpl.
    case_eq (Bool.forallb Bool3 f l); intro Hl; trivial.
    rewrite Bool.forallb_forall_false in Hl.
    destruct Hl as [x [Hl Hx]].
    assert (Jx := H x (or_intror _ Hl)).
    rewrite Hx in Jx; apply False_rec; apply Jx; apply refl_equal.
  + assert (IH : Bool.forallb Bool3 f l = unknown3).
    {
      rewrite IHl; split.
      - exists x; split; assumption.
      - intros y Hy; apply H; right; assumption.
    }
    simpl; rewrite IH.
    case_eq (f a1); intro Ha1; simpl; trivial.
    apply False_rec; apply (H a1); [left | ]; trivial.
Qed.


