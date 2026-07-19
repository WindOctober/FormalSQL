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

Require Import Bool List Arith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet FiniteSet.

Section Sec.

Hypothesis A : Type.
Hypothesis OA : Oeset.Rcd A.

Hypothesis value : Type.
Hypothesis OVal : Oset.Rcd value.

Definition compare_OLA := 
  (fun l1 l2 => Oeset.compare (mk_oelists OA) (quicksort OA l1) 
                              (quicksort OA l2)).

Definition OLA : Oeset.Rcd (list A).
split with compare_OLA.
- do 3 intro; apply Oeset.compare_eq_trans.
- do 3 intro; apply Oeset.compare_eq_lt_trans.
- do 3 intro; apply Oeset.compare_lt_eq_trans.
- do 3 intro; apply Oeset.compare_lt_trans.
- do 2 intro; apply Oeset.compare_lt_gt.
Defined.

Definition compare_VOLA := (compareAB (Oset.compare OVal) (Oeset.compare OLA)).

Definition VOLA : Oeset.Rcd (value * list A).
  split with compare_VOLA.
- intros [v1 l1] [v2 l2] [v3 l3]; apply compareAB_eq_trans.              
  + apply Oset.compare_eq_trans.
  + apply Oeset.compare_eq_trans.
- intros [v1 l1] [v2 l2] [v3 l3]; apply compareAB_le_lt_trans.              
  + apply Oset.compare_eq_trans.
  + apply Oset.compare_eq_lt_trans.
  + apply Oeset.compare_eq_lt_trans.
- intros [v1 l1] [v2 l2] [v3 l3]; apply compareAB_lt_le_trans.              
  + apply Oset.compare_eq_trans.
  + apply Oset.compare_lt_eq_trans.
  + apply Oeset.compare_lt_eq_trans.
- intros [v1 l1] [v2 l2] [v3 l3]; apply compareAB_lt_trans.              
  + apply Oset.compare_eq_trans.
  + apply Oset.compare_eq_lt_trans.
  + apply Oset.compare_lt_eq_trans.
  + apply Oset.compare_lt_trans.
  + apply Oeset.compare_lt_trans.
- intros [v1 l1] [v2 l2]; apply compareAB_lt_gt.
  + apply Oset.compare_lt_gt.
  + apply Oeset.compare_lt_gt.
Defined.

Lemma compare_list_t :
  forall l1 l2, Oeset.permut OA l1 l2 <-> compare_OLA l1 l2 = Eq.
Proof.
intros l1 l2.
assert (Hl1 := quick_sorted OA l1).
assert (Hl2 := quick_sorted OA l2).
assert (Kl1 := quick_permut OA l1).
assert (Kl2 := quick_permut OA l2).
split; intro H.
- simpl; unfold compare_OLA.
  set (q1 := quicksort OA l1) in *; clearbody q1.
  set (q2 := quicksort OA l2) in *; clearbody q2.
  assert (Hq :  _permut (fun x y : A => Oeset.compare OA x y = Eq) q1 q2).
  {
    refine (Oeset.permut_trans _ Kl2).
    refine (Oeset.permut_trans _ H).
    apply Oeset.permut_sym; apply Kl1.
  }
  clear l1 l2 Kl1 Kl2 H.
  apply (sort_is_unique (OA := OA) Hl1 Hl2 Hq).
- refine (Oeset.permut_trans Kl1 _).
   apply Oeset.permut_trans with (quicksort OA l2).
   + apply Oeset.permut_refl_alt; apply H.
   + apply Oeset.permut_sym; apply Kl2.
Qed.

Fixpoint insert_in_partition v a (p : list (value * list A)) :=
  match p with
    | nil => (v, a :: nil) :: nil
    | (v1, p1) :: p => if Oset.eq_bool OVal v v1
                       then (v1, a :: p1) :: p
                       else (v1, p1) :: insert_in_partition v a p
  end.

Fixpoint partition_rec (f : A -> value) (p : list (value * list A)) (l : list A) := 
  match l with
    | nil => p
    | a1 :: l => partition_rec f (insert_in_partition (f a1) a1 p) l
  end.

Definition partition (f : A -> value) (l : list A) := partition_rec f nil l.

Lemma insert_in_partition_permut :
  forall v a p,
    _permut 
      (@eq A) (a :: flat_map (fun x => match x with (_, k) => k end) p)
      (flat_map (fun x => match x with (_, k) => k end) (insert_in_partition v a p)).
Proof.
intros v a p; induction p as [ | [v1 l1] p].
- apply _permut_refl; intros; apply refl_equal.
- simpl; case_eq (Oset.eq_bool OVal v v1); intro H.
  + apply _permut_refl; intros; apply refl_equal.
  + simpl.
    apply _permut_trans with 
        (l1 ++ a :: flat_map (fun x : value * list A => let (_, k) := x in k) p).
    * intros; subst; apply refl_equal.
    * apply Pcons; [apply refl_equal | apply _permut_refl; intros; apply refl_equal].
    * apply _permut_app1; [apply equivalence_eq | apply IHp].
Qed.

Lemma partition_rec_permut :
  forall f p l,
    _permut 
      (@eq A) ((flat_map (fun x => match x with (_, k) => k end) p) ++ l)
      (flat_map (fun x => match x with (_, k) => k end) (partition_rec f p l)).
Proof.
intros f p l; revert f p; induction l as [ | a1 l]; intros f p; simpl.
- rewrite <- app_nil_end; apply _permut_refl; intros; apply refl_equal.
- assert (H := insert_in_partition_permut (f a1) a1 p).
  set (pp := flat_map (fun x : value * list A => let (_, k) := x in k) p) in *.
  set (p' := insert_in_partition (f a1) a1 p) in *.
  clearbody pp p'.
  apply _permut_trans with (a1 :: pp ++ l).
  + intros; subst; apply refl_equal.
  + apply _permut_sym; [intros; subst; apply refl_equal | ].
    apply Pcons; [apply refl_equal | apply _permut_refl; intros; apply refl_equal].
  + apply _permut_trans with ((flat_map (fun x : value * list A => let (_, k) := x in k) p') ++ l).
    * intros; subst; apply refl_equal.
    * rewrite app_comm_cons; apply _permut_app2; [apply equivalence_eq | apply H].
    * apply IHl.
Qed.

Lemma partition_permut :
  forall f l,
    _permut (@eq A) l (flat_map (fun x => match x with (_, k) => k end) (partition f l)).
Proof.
intros f l; apply (partition_rec_permut f nil l).
Qed.

Lemma partition_rec_app :
  forall f p l1 l2, partition_rec f p (l1 ++ l2) = partition_rec f (partition_rec f p l1) l2.
Proof.
intros f p l1; revert p; induction l1 as [ | a1 l1]; intros p l2; simpl;
  [apply refl_equal | simpl; apply IHl1].
Qed.

Lemma insert_in_partition_cases :
  forall v a p, 
    (exists l, exists lv1, exists lv2,
            p = lv1 ++ (v, l) :: lv2 /\ insert_in_partition v a p = lv1 ++ (v, a :: l) :: lv2) \/
    insert_in_partition v a p = p ++ (v, a :: nil) :: nil.
Proof.
intros v a p; induction p as [ | [v1 l1] p]; simpl; [right; apply refl_equal | ].
case_eq (Oset.eq_bool OVal v v1); intro Hv; simpl.
- rewrite Oset.eq_bool_true_iff in Hv; subst v1.
  left; exists l1; exists nil; exists p; simpl; split; trivial.
- destruct IHp as [[l [lv1 [lv2 [Hp IH]]]] | IH].
  + left; exists l; exists ((v1, l1) :: lv1); exists lv2; split; simpl; apply f_equal; assumption.
  + right; apply f_equal; assumption.
Qed.    

Lemma insert_in_partition_app :
  forall v a p1 p2,
    insert_in_partition v a (p1 ++ p2) = 
    match Oset.mem_bool OVal v (map fst p1) with
    | true => (insert_in_partition v a p1) ++ p2 
    | false => p1 ++ (insert_in_partition v a p2)
    end.
Proof.
intros v a p1; induction p1 as [ | [v1 l1] p1]; intros p2; simpl; [apply refl_equal | ].
case_eq (Oset.eq_bool OVal v v1); intro Hv; simpl; [apply refl_equal | ].
rewrite IHp1.
case (Oset.mem_bool OVal v (map fst p1)); apply refl_equal.
Qed.

Lemma in_insert_in_partition_diff_nil :
  forall v a p,
    (forall v1 l1, In (v1, l1) p -> l1 <> nil) ->
    forall v1 l1, In (v1, l1) (insert_in_partition v a p) -> l1 <> nil.
Proof.
intros v a p; induction p as [ | [v1 l1] p]; intros Hp x l H; simpl in H.
- destruct H as [H | H]; [ | contradiction H].
  injection H; clear H; intros; subst; discriminate.
- case_eq (Oset.eq_bool OVal v v1); intro Hv; rewrite Hv in H; simpl in H.
  + destruct H as [H | H].
    * injection H; clear H; intros; subst; discriminate.
    * apply (Hp x l); right; assumption.
  + destruct H as [H | H].
    * injection H; clear H; intros; subst; apply (Hp x l); left; apply refl_equal.
    * refine (IHp _ _ _ H).
      intros x' l' H'; refine (Hp _ _ _); right; apply H'.
Qed.

Lemma in_partition_rec_diff_nil :
  forall f p l,
    (forall v1 l1, In (v1, l1) p -> l1 <> nil) ->
    forall v1 l1, In (v1, l1) (partition_rec f p l) -> l1 <> nil.
Proof.
intros f p l; revert p; induction l as [ | a1 l]; intros p Hp v1 l1 H; simpl in H.
- apply (Hp _ _ H).
- refine (IHl _ _ _ _ H).
  apply in_insert_in_partition_diff_nil; assumption.
Qed.

Lemma in_partition_diff_nil :
  forall f l,
    forall v1 l1, In (v1, l1) (partition f l) -> l1 <> nil.
Proof.
intros f l; apply in_partition_rec_diff_nil; intros; contradiction.
Qed.

Lemma in_map_snd_partition_diff_nil :
  forall f l,
    forall l1, In l1 (map snd (partition f l)) -> l1 <> nil.
Proof.
intros f l l1 H.
rewrite in_map_iff in H.
destruct H as [[v1 _l1] [_H H]]; simpl in _H; subst _l1.
apply (in_partition_diff_nil _ _ _ H).
Qed.

Lemma mem_map_snd_partition_diff_nil :
  forall f l,
    forall l1, Oeset.mem_bool OLA l1 (map snd (partition f l)) = true -> l1 <> nil.
Proof.
intros f l l1 H.
rewrite Oeset.mem_bool_true_iff in H.
destruct H as [l1' [H Hl1']].
assert (K := in_map_snd_partition_diff_nil _ _ Hl1').
destruct l1'; [apply False_rec; apply K; apply refl_equal | ].
simpl in H; unfold compare_OLA in H.
assert (L := comparelA_eq_length_eq _ _ _ H); rewrite !length_quicksort in L.
destruct l1; [discriminate L | discriminate].
Qed.

Lemma insert_in_partition_all_diff_values :
  forall v a p, all_diff (map (fun x => match x with (v, _) => v end) p) ->
                all_diff (map (fun x => match x with (v, _) => v end) (insert_in_partition v a p)).
Proof.
intros v a p H; induction p as [ | [v1 l1] p]; [trivial | simpl map].
case_eq (Oset.eq_bool OVal v v1); intro Hv1; [apply H | ].
simpl map in H; rewrite all_diff_unfold in H.
rewrite all_diff_unfold; split; [ | apply IHp; apply (proj2 H)].
intros x Hx K; subst x.
destruct (insert_in_partition_cases v a p) as [[l [lv1 [lv2 [H1 H2]]]] | H1].
- apply (proj1 H v1); [ | apply refl_equal].
  rewrite H1, map_app; simpl; rewrite H2, map_app in Hx; simpl in Hx; apply Hx.
- rewrite H1, map_app, (map_unfold _ (_ :: _)), (map_unfold _ nil) in Hx.
  destruct (in_app_or _ _ _ Hx) as [H2 | H2].
  + apply (proj1 H v1 H2 (refl_equal _)).
  + simpl in H2; destruct H2 as [H2 | H2]; [ | contradiction H2].
    subst v1; rewrite Oset.eq_bool_refl in Hv1; discriminate Hv1.
Qed.

Lemma partition_rec_all_diff_values :
  forall f p l, all_diff (map (fun x => match x with (v, _) => v end) p) ->
                all_diff (map (fun x => match x with (v, _) => v end) (partition_rec f p l)).
Proof.
intros f p l; revert f p; induction l as [ | a1 l]; intros f p H; [assumption | ].
simpl; apply IHl; clear l IHl.
apply insert_in_partition_all_diff_values; assumption.
Qed.

Lemma partition_all_diff_values :
  forall f l, all_diff (map (fun x => match x with (v, _) => v end) (partition f l)).
Proof.
intros f l; apply partition_rec_all_diff_values; simpl; trivial.
Qed.

Lemma partition_rec_homogeneous_values :
  forall f p l, 
    (forall v k, In (v, k) p -> forall x, In x k -> f x = v) ->
    (forall v k, In (v, k) (partition_rec f p l) -> forall x, In x k -> f x = v).
Proof.
intros f p l; revert f p; induction l as [ | a1 l]; intros f p H; [apply H | simpl].
apply IHl; clear IHl.
induction p as [ | [v1 l1] p]; intros v k H' x Hx; simpl in H'.
- destruct H' as [H' | H']; [ | contradiction H'].
  injection H'; clear H'; intros; subst.
  simpl in Hx; destruct Hx as [Hx | Hx]; [ | contradiction Hx].
  subst; apply refl_equal.
- case_eq (Oset.eq_bool OVal (f a1) v1); intro Hv1; rewrite Hv1 in H'.
  + rewrite Oset.eq_bool_true_iff in Hv1; subst v1.
    simpl in H'; destruct H' as [H' | H'].
    * injection H'; clear H'; intros; subst v k.
      simpl in Hx; destruct Hx as [Hx | Hx]; [subst; apply refl_equal | ].
      apply (H _ _ (or_introl _ (refl_equal _))); assumption.
    * apply (H _ _ (or_intror _ H')); assumption.
  + destruct H' as [H' | H'].
    * injection H'; clear H'; intros; subst.
      apply (H _ _ (or_introl _ (refl_equal _))); assumption.
    * apply IHp with k; trivial.
      do 3 intro; apply H; right; assumption.
Qed.

Lemma partition_homogeneous_values :
  forall f l, 
    (forall v k, In (v, k) (partition f l) -> forall x, In x k -> f x = v).
Proof.
intros f l; apply partition_rec_homogeneous_values.
intros; contradiction.
Qed.

Lemma in_partition :
  forall f l v k a, In (v, k) (partition f l) -> In a k -> In a l.
Proof.
intros f l v k a H Ha.
apply (in_permut_in (partition_permut f l)).
rewrite in_flat_map; eexists; split; [apply H | apply Ha].
Qed.

Lemma in_map_snd_partition :
  forall f l k a, In k (map snd (partition f l)) -> In a k -> In a l.
Proof.
intros f l k a H Ha.
rewrite in_map_iff in H.
destruct H as [[v _k] [_H H]]; simpl in _H; subst _k.
apply (in_partition _ _ _ _ _ H Ha).
Qed.


Lemma insert_in_partition_eq_2 :
  forall v a1 a2 p, Oeset.compare OA a1 a2 = Eq ->
    Oeset.permut VOLA (insert_in_partition v a1 p) (insert_in_partition v a2 p).
Proof.
intros v a1 a2 p; induction p as [ | [v1 l1] p]; intro Ha; simpl.
- apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
  simpl; unfold compare_OLA; simpl.
  rewrite Oset.compare_eq_refl, Ha.
  apply refl_equal.
- case_eq (Oset.eq_bool OVal v v1); intro Hv.
  + apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
    simpl; rewrite Oset.compare_eq_refl.
    rewrite <- compare_list_t; apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
    assumption.
  + apply Oeset.permut_cons; [apply Oeset.compare_eq_refl | ].
    apply IHp; assumption.
Qed.

Lemma insert_in_partition_eq_3 :
  forall v a p1 p2,
    all_diff (map (fun x => match x with (v, _) => v end) p1) ->
    Oeset.permut VOLA p1 p2 -> 
    Oeset.permut VOLA (insert_in_partition v a p1) (insert_in_partition v a p2).
Proof.
intros v a p1; induction p1 as [ | [v1 l1] p1]; intros p2 Hp1 Hp;
  [inversion Hp; subst; apply Oeset.permut_refl | ].
inversion Hp as [ | [_v1 _l1] [v2 l2] _p1 k1 k2]; subst _v1 _l1 _p1; simpl.
  rewrite (map_unfold _ (_ :: _)), all_diff_unfold in Hp1.
  destruct Hp1 as [Hv1 Hp1].
rewrite insert_in_partition_app.
case_eq (Oset.eq_bool OVal v v1); intro Hv.
- rewrite Oset.eq_bool_true_iff in Hv; subst v.
  assert (Hk1 : Oset.mem_bool OVal v1 (map fst k1) = false).
  {
    case_eq (Oset.mem_bool OVal v1 (map fst k1)); intro Hk1; [ | apply refl_equal].
    rewrite Oset.mem_bool_true_iff, in_map_iff in Hk1.
    destruct Hk1 as [[_v l] [_Hv Hk1]]; simpl in _Hv; subst _v.
    assert (Aux :  Oeset.mem_bool VOLA (v1, l) p1 = true).
    {
      rewrite (Oeset.permut_mem_bool_eq (v1, l) H0), Oeset.mem_bool_app, Bool.Bool.orb_true_iff.
      left; apply Oeset.in_mem_bool; assumption.
    }
    rewrite Oeset.mem_bool_true_iff in Aux.
    destruct Aux as [[_v _l] [_Hvl Aux]]; simpl in _Hvl.
    case_eq (Oset.compare OVal v1 _v); intro Hv; rewrite Hv in _Hvl; try discriminate _Hvl.
    rewrite Oset.compare_eq_iff in Hv; subst _v.
    apply False_rec.
    apply (Hv1 v1); [ | apply refl_equal].
    rewrite in_map_iff; eexists; split; [ | apply Aux]; apply refl_equal.
  }
  rewrite Hk1; simpl.
  simpl in H.
  case_eq (Oset.compare OVal v1 v2); intro Hv; rewrite Hv in H; try discriminate H.
  rewrite Oset.compare_eq_iff in Hv; subst v2; rewrite Oset.eq_bool_refl.
  constructor 2; [ | assumption].
  simpl; rewrite Oset.compare_eq_refl, <- compare_list_t.
  apply Oeset.permut_cons; [apply Oeset.compare_eq_refl | ].
  rewrite compare_list_t; assumption.
- assert (IH := IHp1 _ Hp1 H0). 
  apply Oeset.permut_trans with ((v1, l1) :: insert_in_partition v a (k1 ++ k2)).
  + apply Oeset.permut_cons; [apply Oeset.compare_eq_refl | assumption].
  + rewrite insert_in_partition_app.
    case_eq (Oset.mem_bool OVal v (map fst k1)); intro Kv.
    * constructor 2; [assumption | apply Oeset.permut_refl].
    * apply Oeset.permut_trans with (k1 ++ (v1, l1) :: insert_in_partition v a k2).
      -- constructor 2; [apply Oeset.compare_eq_refl | apply Oeset.permut_refl].
      -- apply Oeset.permut_app1; simpl.
         simpl in H.
         case_eq (Oset.compare OVal v1 v2); intro _Hv; rewrite _Hv in H; try discriminate H.
         rewrite Oset.compare_eq_iff in _Hv; subst v2; rewrite Hv.
         apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
         simpl; rewrite H, Oset.compare_eq_refl; apply refl_equal.
Qed.

Lemma partition_rec_eq_1 :
  forall f1 f2 p l,
    (forall a, Oeset.mem_bool OA a l = true -> f1 a = f2 a) ->
    partition_rec f1 p l = partition_rec f2 p l.
Proof.
intros f1 f2 p l Hl; revert p; induction l as [ | a1 l]; intro p; simpl; [apply refl_equal | ].
rewrite <- (Hl a1); [ | simpl; rewrite Oeset.eq_bool_refl; apply refl_equal].
apply IHl; intros a Ha; apply Hl.
simpl; rewrite Ha, Bool.Bool.orb_true_r; apply refl_equal.
Qed.

Lemma partition_rec_eq_2 :
  forall f p1 p2 l, 
    all_diff (map (fun x : value * list A => let (v, _) := x in v) p1) ->
    Oeset.permut VOLA p1 p2 -> Oeset.permut VOLA (partition_rec f p1 l) (partition_rec f p2 l).
Proof.
intros f p1 p2 l; revert p1 p2; 
  induction l as [ | a l]; intros p1 p2 Hp1 Hp; simpl; [assumption | apply IHl].
- apply insert_in_partition_all_diff_values; assumption.
- apply insert_in_partition_eq_3; assumption.
Qed.
  
Lemma partition_rec_eq_3 :
  forall f p l1 l2, 
    all_diff (map (fun x : value * list A => let (v, _) := x in v) p) ->
    (forall a, Oeset.mem_bool OA a l1 = true -> 
               forall a', Oeset.compare OA a a' = Eq -> f a = f a') ->
    Oeset.permut OA l1 l2 -> 
    Oeset.permut VOLA (partition_rec f p l1) (partition_rec f p l2).
Proof.
intros f p l1; revert p; 
  induction l1 as [ | a1 l1]; intros p l2 Hp Hl1 Hl;
    [inversion Hl; subst; simpl; apply Oeset.permut_refl | ].
inversion Hl as [ | __a1 _a1 _l1 k1 k2]; subst __a1 _l1.
apply Oeset.permut_trans with (partition_rec f (insert_in_partition (f a1) a1 p) (k1 ++ k2)).
- simpl; apply IHl1.
  + apply insert_in_partition_all_diff_values; assumption.
  + intros a Ha; apply Hl1; simpl; rewrite Ha, Bool.Bool.orb_true_r; apply refl_equal.
  + assumption.
- rewrite !partition_rec_app; simpl.
  apply partition_rec_eq_2.
  + apply partition_rec_all_diff_values.
    apply insert_in_partition_all_diff_values.
    assumption.
  + apply Oeset.permut_trans with
        (insert_in_partition (f _a1) a1 (partition_rec f p k1));
      [ | apply insert_in_partition_eq_2; assumption].
    assert (Ha1 : f a1 = f _a1).
    {
      apply Hl1; [ | assumption].
      simpl; rewrite Oeset.eq_bool_refl; apply refl_equal.
    }
    rewrite <- Ha1.
    clear l1 l2 k2 _a1 IHl1 Hl1 Hl H0 H3 Ha1 H.
    revert a1 p Hp.
    induction k1 as [ | b1 k1]; intros a1 p Hp; simpl; [apply Oeset.permut_refl | ].
    apply Oeset.permut_trans with 
        (partition_rec f (insert_in_partition (f a1) a1 (insert_in_partition (f b1) b1 p)) k1).    
    * apply partition_rec_eq_2.
      -- do 2 apply insert_in_partition_all_diff_values.
         assumption.
      -- clear IHk1; induction p as [ | [v1 l1] p]; simpl.
         ++ case_eq (Oset.eq_bool OVal (f b1) (f a1)); intro H.
            ** rewrite Oset.eq_bool_sym, H; apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
               rewrite Oset.eq_bool_true_iff in H; rewrite H; simpl.
               rewrite Oset.compare_eq_refl, <- compare_list_t.
               apply (Pcons b1 b1 (a1 :: nil) nil 
                            (Oeset.compare_eq_refl _ _) (Oeset.permut_refl _ _)).
            ** rewrite Oset.eq_bool_sym, H.
               apply (Pcons (f a1, a1 :: nil) (f a1, a1 :: nil)  ((f b1, b1 :: nil) :: nil) nil
                            (Oeset.compare_eq_refl _ _) (Oeset.permut_refl _ _)).
         ++ case_eq (Oset.eq_bool OVal (f a1) v1); intro Ha1.
            ** case_eq (Oset.eq_bool OVal (f b1) v1); intro Hb1; simpl.
               --- rewrite Hb1, Ha1; apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
                   simpl; rewrite Oset.compare_eq_refl.
                   rewrite <- compare_list_t.
                   apply (Pcons b1 b1 (a1 :: nil) l1 
                            (Oeset.compare_eq_refl _ _) (Oeset.permut_refl _ _)).
               --- rewrite Hb1, Ha1.
                   apply Oeset.permut_refl.
            ** case_eq (Oset.eq_bool OVal (f b1) v1); intro Hb1; simpl.
               --- rewrite Hb1, Ha1; apply Oeset.permut_cons; [ | apply Oeset.permut_refl].
                   apply Oeset.compare_eq_refl.
               --- rewrite Hb1, Ha1.
                   apply Oeset.permut_cons; [apply Oeset.compare_eq_refl | ].
                   apply IHp.
                   rewrite all_diff_unfold in Hp; apply (proj2 Hp).
    * apply IHk1.
      apply insert_in_partition_all_diff_values; assumption.
Qed.

Lemma partition_eq_2 :
  forall f l1 l2, 
    (forall a, Oeset.mem_bool OA a l1 = true -> 
               forall a', Oeset.compare OA a a' = Eq -> f a = f a') ->
    Oeset.permut OA l1 l2 -> 
    Oeset.permut VOLA (partition f l1) (partition f l2).
Proof.
intros f l1 l2 Hl1 Hl.
apply partition_rec_eq_3; simpl; trivial.
Qed.

Lemma partition_eq :
  forall f1 f2 l1 l2, 
    (forall a, Oeset.mem_bool OA a l1 = true -> 
               forall a', Oeset.compare OA a a' = Eq -> f1 a = f2 a') ->
    Oeset.permut OA l1 l2 -> 
    Oeset.permut VOLA (partition f1 l1) (partition f2 l2).
Proof.
intros f1 f2 l1 l2 Hl1 Hl.
apply Oeset.permut_trans with (partition f2 l1).
- apply Oeset.permut_refl_alt; apply comparelA_eq_refl_alt.
  + intros; apply Oeset.compare_eq_refl.
  + apply partition_rec_eq_1.
    intros a Ha; apply Hl1; [assumption | ].
    apply Oeset.compare_eq_refl.
- apply partition_eq_2; [ | assumption].
  intros a Ha a' Ha'.
  rewrite <- (Hl1 a Ha a' Ha'); apply sym_eq; apply Hl1; [assumption | ].
  apply Oeset.compare_eq_refl.
Qed.

Lemma snd_partition_eq :
  forall f1 f2 l1 l2, 
    (forall a, Oeset.mem_bool OA a l1 = true -> 
               forall a', Oeset.compare OA a a' = Eq -> f1 a = f2 a') ->
    Oeset.permut OA l1 l2 -> 
    Oeset.permut OLA (map snd (partition f1 l1)) (map snd (partition f2 l2)).
Proof.
intros f1 f2 l1 l2 Hl1 Hl.
generalize (partition_eq _ _ Hl1 Hl); apply _permut_map.
intros [a1 a2] [b1 b2] _ _; simpl.
case (Oset.compare OVal a1 b1); try discriminate.
exact (fun h => h).
Qed.

Lemma partition_eq_1_strong :
  forall f1 f2 l, 
    (forall a, In a l -> f1 a = f2 a) -> partition f1 l = partition f2 l.
Proof.
intros f1 f2 l Hl; unfold partition.
set (acc1 := @nil (value * list A)) at 1.
set (acc2 := @nil (value * list A)).
assert (H : acc1 = acc2); [apply refl_equal | ].
clearbody acc1 acc2; revert acc1 acc2 H.
induction l as [ | a1 l]; intros acc1 acc2 H; [apply H | ]; simpl.
apply IHl; [intros; apply Hl; right; assumption | ].
rewrite <- (Hl a1 (or_introl _ (refl_equal _))); rewrite <- H.
apply refl_equal.
Qed.

Lemma partition_map :
  forall f f1 l, 
    (forall a, In a l -> f (f1 a) = f a) ->
    partition f (map f1 l) = 
    map (fun x => match x with (v, k) => (v, map f1 k) end) (partition f l).
Proof.
intros f f1 l Hl; unfold partition.
set (acc1 := @nil (value * list A)) at 1.
set (acc2 := @nil (value * list A)).
assert (H : acc1 = map (fun x => match x with (v, k) => (v, map f1 k) end) acc2);
  [apply refl_equal | clearbody acc1 acc2].
revert acc1 acc2 H; induction l as [ | a1 l]; intros acc1 acc2 H; [apply H | simpl].
apply IHl.
- intros; apply Hl; right; assumption.
- rewrite H, Hl; [ | left; apply refl_equal].
clear l Hl IHl H; induction acc2 as [ | [v1 k1] l]; [apply refl_equal | simpl].
case (Oset.eq_bool OVal (f a1) v1); simpl; [apply refl_equal | ].
apply f_equal; apply IHl.
Qed.

Lemma partition_rec_cst :
  forall f l l1 c, 
    (forall x, In x l -> f x = c) ->
    partition_rec f ((c, l1) :: nil) l = 
    match l with 
    | nil => (c, l1) :: nil 
    | _ :: _ => (c,rev l ++ l1) :: nil 
    end.
Proof.
intros f l; induction l as [ | x1 l]; intros  l1 c H; [apply refl_equal | simpl].
rewrite H, Oset.eq_bool_refl, IHl; [ | intros; apply H; right; assumption| left; apply refl_equal].
destruct l as [ | x2 l]; [apply refl_equal | ].
apply f_equal2; [apply f_equal | apply refl_equal].
rewrite <- app_assoc; apply refl_equal.
Qed.

Lemma partition_cst :
  forall f c l, 
    (forall x, In x l -> f x = c) ->
    partition f l = match l with nil => nil | _ :: _ => (c, rev l) :: nil end.
Proof.
intros f c l H; unfold partition.
case l as [ | x1 l]; [apply refl_equal | simpl].
rewrite H; [ | left; apply refl_equal].
rewrite partition_rec_cst; [ | intros; apply H; right; assumption].
destruct l; simpl; trivial.
Qed.

End Sec.
