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

Require Import FTuples.
Require Import FTerms.
Require Import ATerms.
Require Import Env.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Fixpoint interp_dot (env : env T) (a : attribute T) :=
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l) :: env =>
      match quicksort (OTuple T) l with
        | nil => interp_dot env a
        | t :: _ => if a inS? labels T t then dot T t a else interp_dot env a
      end
  end.

Fixpoint interp_funterm env t := 
  match t with
    | F_Constant _ c => c
    | F_Dot _ a => interp_dot env a
    | F_Expr _ f l => interp_symbol T f (List.map (fun x => interp_funterm env x) l)
  end.

    
Definition groups_of_env_slice (s : env_slice T) :=
  match s with
    | (_, Group_By _ g, _) => g
    | (sa, Group_Fine _, _) => List.map (fun a => A_Expr _ (F_Dot _ a)) ({{{sa}}})
  end.

Definition is_a_suitable_env (sa : Fset.set (A T)) (env : env T) f :=
  is_built_upon_ag T (map (fun a => A_Expr _ (F_Dot _ a)) ({{{sa}}}) ++ flat_map groups_of_env_slice env) f.

Fixpoint find_eval_env (env : env T) f := 
  match env with
    | nil => if is_built_upon_ag T nil f 
             then Some nil
             else None
    | (sa1, _, _) :: env' => 
      match find_eval_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_suitable_env sa1 env' f
          then Some env
          else None
      end
  end.

Definition unfold_env_slice (s : env_slice T) :=
  match s with
  | (sa, g, l) => List.map (fun t => (sa, Group_Fine T, t :: nil)) (quicksort (OTuple T) l)
  end.

Fixpoint interp_aggterm (env : env T) (agt : aggterm T) := 
  match agt with
  | A_Expr _ ft => interp_funterm env ft
  | A_agg _ ag ft => 
    let env' := 
        if Fset.is_empty (A T) (variables_ft _ ft)
        then Some env 
        else find_eval_env env agt in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate T ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun _ f lag => interp_symbol T f (List.map (fun x => interp_aggterm env x) lag)
  end.

Lemma interp_dot_unfold :
  forall env a, interp_dot env a =
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l) :: env =>
      match quicksort (OTuple T) l with
        | nil => interp_dot env a
        | t :: _ => if a inS? labels T t then dot T t a else interp_dot env a
      end
  end.
Proof.
intros env a; case env; intros; apply refl_equal.
Qed.

Lemma interp_funterm_unfold :
  forall env t, interp_funterm env t = 
  match t with
    | F_Constant _ c => c
    | F_Dot _ a => interp_dot env a
    | F_Expr _ f l => interp_symbol T f (List.map (fun x => interp_funterm env x) l)
  end.
Proof.
intros env t; case t; intros; apply refl_equal.
Qed.

Lemma find_eval_env_unfold :
  forall (env : env T) f, find_eval_env env f = 
  match env with
    | nil => if is_built_upon_ag T nil f 
             then Some nil
             else None
    | (sa1, _, _) :: env' => 
      match find_eval_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_suitable_env sa1 env' f
          then Some env
          else None
      end
  end.
Proof.
intros env f; case env; intros; apply refl_equal.
Qed.

Lemma interp_aggterm_unfold :
  forall (env : env T) (agt : aggterm T), interp_aggterm env agt =
  match agt with
  | A_Expr _ ft => interp_funterm env ft
  | A_agg _ ag ft => 
    let env' := 
        if Fset.is_empty (A T) (variables_ft _ ft)
        then Some env 
        else find_eval_env env agt in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate T ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun _ f lag => interp_symbol T f (List.map (fun x => interp_aggterm env x) lag)
  end.
Proof.
intros env ag; case ag; intros; apply refl_equal.
Qed.

Lemma interp_cst_funterm :
  forall env f, Fset.is_empty (A T) (variables_ft T f) = true ->
                interp_funterm env f = interp_funterm nil f.
Proof.
intros env f; set (n := size_funterm T f); assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; [intros f Hn; destruct f; inversion Hn | ].
intros f Hn H; destruct f as [c | a | f l].
- apply refl_equal.
- simpl in H; rewrite Fset.is_empty_spec, Fset.equal_spec in H.
  assert (Ha := H a); rewrite Fset.singleton_spec, Oset.eq_bool_refl, Fset.empty_spec in Ha.
  discriminate Ha.
- simpl; apply f_equal; rewrite <- map_eq; intros x Hx.
  apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + rewrite Fset.is_empty_spec, Fset.equal_spec; intros a.
    simpl in H; rewrite Fset.is_empty_spec, Fset.equal_spec in H.
    assert (Ha := H a).
    rewrite Fset.empty_spec; case_eq (a inS? variables_ft T x); [ | intros; apply refl_equal].
    intro Ka; rewrite Fset.empty_spec in Ha; rewrite <- Ha; apply sym_eq.
    rewrite Fset.mem_Union; eexists; split; [ | apply Ka].
    rewrite in_map_iff; eexists; split; [ | apply Hx]; apply refl_equal.
Qed.

Lemma is_a_suitable_env_eq :
  forall e sa1 env1 sa2 env2, sa1 =S= sa2 -> weak_equiv_env T env1 env2 ->
                              is_a_suitable_env sa1 env1 e = is_a_suitable_env sa2 env2 e.
Proof.
assert (H : forall env1 env2 slc1, 
              weak_equiv_env T env1 env2 -> In slc1 env1 -> 
              exists slc2, In slc2 env2 /\ weak_equiv_env_slice T slc1 slc2).
{
  intro env1; induction env1 as [ | s1 e1]; intros [ | s2 e2] slc1 He Hs.
  - contradiction Hs.
  - inversion He.
  - inversion He.
  - simpl in He; inversion He; subst.
    simpl in Hs; destruct Hs as [Hs | Hs].
    + subst slc1; exists s2; split; [left | ]; trivial.
    + destruct (IHe1 _ _ H4 Hs) as [slc2 [K1 K2]].
      exists slc2; split; [right | ]; trivial.
}
intros e sa1 env1 sa2 env2 Hsa Henv.
unfold is_a_suitable_env; rewrite eq_bool_iff; split; 
apply is_built_upon_ag_incl; intros f Hf;
(destruct (in_app_or _ _ _ Hf) as [Kf | Kf]; apply in_or_app; [left | right]).
- rewrite <- (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [[[_sa1 g1] l1] [H1 H2]].
  destruct (H _ _ _ Henv H1) as [[[_sa2 g2] l2] [H3 H4]].
  rewrite in_flat_map; exists (_sa2, g2, l2); split; [assumption | ].
  simpl in H4.
  simpl; simpl in H2.
  assert (H4' := proj2 H4); subst g2.
  assert (H4' := proj1 H4); rewrite <- (Fset.elements_spec1 _ _ _ H4'); apply H2.
- rewrite (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [[[_sa1 g1] l1] [H1 H2]].
  rewrite weak_equiv_env_sym in Henv.
  destruct (H _ _ _ Henv H1) as [[[_sa2 g2] l2] [H3 H4]].
  rewrite in_flat_map; exists (_sa2, g2, l2); split; [assumption | ].
  simpl in H4.
  simpl; simpl in H2.
  assert (H4' := proj2 H4); subst g2.
  assert (H4' := proj1 H4); rewrite <- (Fset.elements_spec1 _ _ _ H4'); apply H2.
Qed.

Lemma interp_dot_eq :
  forall a e1 e2, equiv_env T e1 e2 -> interp_dot e1 a = interp_dot e2 a.
Proof.
intros a e1; induction e1 as [ | [[sa1 g1] l1] e1]; intros [ | [[sa2 g2] l2] e2] H.
- apply refl_equal.
- inversion H.
- inversion H.
- simpl in H; inversion H as [ | slc1 slc2 _e1 _e2 Hs He]; subst slc1 slc2 _e1 _e2.
  simpl in Hs; destruct Hs as [H3 [H2 H1]]; simpl.
  assert (Ll := Oeset.permut_length H1).
  rewrite <- (length_quicksort (OTuple T) l1) in Ll.
  rewrite <- (length_quicksort (OTuple T) l2) in Ll.
  rewrite compare_list_t in H1; unfold compare_OLA in H1.
  destruct (quicksort (OTuple T) l1) as [ | x1 q1];
    destruct (quicksort (OTuple T) l2) as [ | x2 q2]; try discriminate Ll.
  + apply IHe1; assumption.
  + simpl in H1.
    case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in H1; try discriminate H1.
    rewrite tuple_eq in Hx.
    rewrite <- (Fset.mem_eq_2 _ _ _ (proj1 Hx)).
    case_eq (a inS? labels T x1); intro Ha.
    * apply (proj2 Hx); assumption.
    * apply IHe1; assumption.
Qed.


Lemma interp_funterm_eq :
  forall f e1 e2, equiv_env T e1 e2 -> interp_funterm e1 f = interp_funterm e2 f.
Proof.
intro f.
set (n := size_funterm T f).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert f Hn.
induction n as [ | n];
  intros f Hn e1 e2 He. 
- destruct f; inversion Hn.
- destruct f as [c | a | f l].
  + apply refl_equal.
  + simpl; apply interp_dot_eq; trivial.
  + simpl; apply f_equal.
    rewrite <- map_eq.
    intros a Ha.
    apply IHn; [ | assumption].
    simpl in Hn.
    refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; apply Ha.
Qed.

Lemma interp_funterm_homogeneous :
  forall s1 g1 l1 s2 g2 t2 k2 env1 env2 f, quicksort (OTuple T) l1 = t2 :: k2 -> 
    interp_funterm (env1 ++ (s1, g1, l1) :: env2) f = 
    interp_funterm (env1 ++ (s2, g2, t2 :: nil) :: env2) f.
Proof.
intros s1 g1 l1 s2 g2 t2 k2 env1 env2 f Q.
set (n := size_funterm T f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn env1 env2; induction n as [ | n]; intros f Hn env1 env2; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | simpl | ].
- induction env1 as [ | [[sa g] l] env1]; simpl.
  + rewrite Q; apply refl_equal.
  + case (quicksort (OTuple T) l); [apply IHenv1 | ].
    intros t _; case (a inS? labels T t); [apply refl_equal | ].
    apply IHenv1.
- simpl; apply f_equal; rewrite <- map_eq; intros; apply IHn.
    simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
Qed.

Lemma interp_funterm_homogeneous_nil :
  forall s1 g1 l1 s2 g2 t2 k2 env f, quicksort (OTuple T) l1 = t2 :: k2 -> 
    interp_funterm ((s1, g1, l1) :: env) f = 
    interp_funterm ((s2, g2, t2 :: nil) :: env) f.
Proof.
intros s1 g1 l1 s2 g2 t2 k2 env f Q.
apply (interp_funterm_homogeneous s1 g1 l1 s2 g2 t2 k2 nil env f Q).
Qed.

Lemma unfold_env_slice_eq : 
  forall slc1 slc2, equiv_env_slice T slc1 slc2 -> 
                    equiv_env T (unfold_env_slice slc1) (unfold_env_slice slc2).
Proof.
intros [[sa1 g1] l1] [[sa2 g2] l2]; simpl.
intros [Hs [Hg Hl]].
rewrite compare_list_t in Hl; unfold compare_OLA in Hl.
set (q1 := quicksort (OTuple T) l1) in *.
set (q2 := quicksort (OTuple T) l2) in *.
clearbody q1 q2.
revert q2 Hl; induction q1 as [ | x1 q1]; intros [ | x2 q2] Hq; try discriminate Hq; simpl.
- constructor 1.
- simpl in Hq.
  case_eq (Oeset.compare (OTuple T) x1 x2); intro Hx; rewrite Hx in Hq; try discriminate Hq.
  constructor 2; [ | apply IHq1; assumption].
  simpl; repeat split; trivial.
  apply (@Pcons _ _ (fun x y => Oeset.compare (Tuple.OTuple _) x y = Eq)
                        x1 x2 nil nil nil Hx (Pnil _)).
Qed.

Lemma find_eval_env_eq :
  forall e env1 env2, 
    equiv_env T env1 env2 -> 
    match (find_eval_env env1 e), (find_eval_env env2 e) with
      | None, None => True
      | Some e1, Some e2 => equiv_env T e1 e2
      | _, _ => False
    end.
Proof.
intros e env1; induction env1 as [ | [[sa1 g1] l1] env1]; intros [ | [[sa2 g2] l2] env2] He.
- simpl; case (is_built_upon_ag T nil e); trivial.
- inversion He.
- inversion He.
- inversion He; subst.
  assert (IH := IHenv1 _ H4).
  simpl.
  destruct (find_eval_env env1 e) as [_l1 | ];
    destruct (find_eval_env env2 e) as [_l2 | ]; try contradiction IH.
  + assumption.
  + simpl in H2.
    assert (H1 := proj1 H2).
    rewrite <- (is_a_suitable_env_eq e _ _ _ _ H1 (equiv_env_weak_equiv_env _ _ _ H4)).
    case (is_a_suitable_env sa1 env1 e).
    * constructor 2; trivial.
    * trivial.
Qed.

Lemma interp_aggterm_eq :
  forall e env1 env2, equiv_env T env1 env2 -> interp_aggterm env1 e = interp_aggterm env2 e.
Proof.
intro a.
set (n := size_aggterm T a).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert a Hn.
induction n as [ | n]; intros a Hn env1 env2 He.
- destruct a; inversion Hn.
- destruct a as [f | a f | f l]; simpl.
  + apply interp_funterm_eq; trivial.
  + apply f_equal.
    case (Fset.is_empty (A T) (variables_ft T f)).
    * destruct env1 as [ | slc1 e1]; destruct env2 as [ | slc2 e2];
      try inversion He; [apply refl_equal | ].
      subst.
      rewrite !map_map.
      assert (H' := unfold_env_slice_eq _ _ H2).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      {
        revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'.
        - apply refl_equal.
        - inversion H'.
        - inversion H'.
        - inversion H' as [ | _t1 _t2 _l1 _l2 Ht Hl K3 K4]; subst.
          simpl map; apply f_equal2.
          + apply interp_funterm_eq; constructor 2; trivial.
          + apply IHl1; trivial.
      }
    * assert (H := find_eval_env_eq (A_agg T a f) _ _ He).
      destruct (find_eval_env env1 (A_agg T a f)) as [[ | slc1 e1] | ];
        destruct (find_eval_env env2 (A_agg T a f)) as [[ | slc2 e2] | ];
        try inversion H; trivial.
      subst; rewrite !map_map.
      assert (H' := unfold_env_slice_eq _ _ H3).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'; 
      try (inversion H'; fail); trivial.
      {
        inversion H'; subst.
        simpl map; apply f_equal2.
        - apply interp_funterm_eq; constructor 2; trivial.
        - apply IHl1; trivial.
      }
  + apply f_equal; rewrite <- map_eq.
    intros a Ha; apply IHn; trivial.
    simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
Qed.

Lemma interp_dot_eq_interp_funterm_eq :
  forall env1 env2 f,
    (forall a, a inS variables_ft T f -> interp_dot env1 a = interp_dot env2 a) ->
    interp_funterm env1 f = interp_funterm env2 f.
Proof.
intros env1 env2 f.
set (n := size_funterm T f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn H; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | | ].
- simpl; apply H; simpl.
  rewrite Fset.singleton_spec; apply Oset.eq_bool_refl.
- simpl; apply f_equal; rewrite <- map_eq.
  intros a Ha; apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + intros b Hb; apply H; simpl.
    rewrite Fset.mem_Union.
    eexists; split; [rewrite in_map_iff; eexists; split; [ | apply Ha] | apply Hb].
    apply refl_equal.
Qed.

Lemma is_built_upon_ft_interp_funterm_eq :
  forall g f env1 env2,
    is_built_upon_ft T g f = true ->
    (forall e, In e g -> interp_funterm env1 e = interp_funterm env2 e) ->
    interp_funterm env1 f = interp_funterm env2 f.
Proof.
intros g f env1 env2; revert g.
set (n := size_funterm T f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn g Hf Hg; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | | ]; simpl in Hf.
- apply Hg; rewrite Oset.mem_bool_true_iff in Hf; assumption.
- case_eq (Oset.mem_bool (OFun T) (F_Expr T fc lf) g); intro Kf.
  + apply Hg; rewrite Oset.mem_bool_true_iff in Kf; assumption.
  + rewrite Kf, Bool.Bool.orb_false_l in Hf; simpl; apply f_equal; rewrite <- map_eq.
    intros e He; apply IHn with g.
    * simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply in_list_size; assumption.
    * rewrite forallb_forall in Hf; apply Hf; assumption. 
    * assumption.
Qed.

Lemma find_eval_env_none :
  forall env1 env2 f, find_eval_env (env1 ++ env2) f = None -> find_eval_env env2 f = None.
Proof.
intros env1 env2 f; induction env1 as [ | [[sa1 g1] l1] env1]; simpl; intro H; [exact H | ].
- destruct (find_eval_env (env1 ++ env2) f); [discriminate H | ].
  apply IHenv1; apply refl_equal.
Qed.


End Sec.
