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

Require Import FTuples NJoinTuples FTerms ATerms Env Interp Projection.
Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Definition well_formed_ft env f := 
  is_built_upon_ft T (extract_funterms T (flat_map (groups_of_env_slice T) env)) f.

Fixpoint well_formed_ag env a :=
  match a with
  | A_Expr _ f => well_formed_ft env f
  | A_agg _ _ f => 
    Fset.is_empty (A T) (variables_ft _ f) ||
       match find_eval_env T env a with Some _ => true | None => false end
  | A_fun _ _ la => forallb (well_formed_ag env) la
  end.

Definition well_formed_s env s :=
  forallb (fun x => match x with Select_As _ e _ => well_formed_ag env e end) s &&
  Oset.all_diff_bool (OAtt T) (map (fun x => fst match x with Select_As _ e a => (a, e) end) s) &&
  Fset.is_empty 
  (A T) 
  (Fset.inter 
     _ (Fset.mk_set _ (map (fun x => fst match x with Select_As _ e a => (a, e) end) s))
     (Fset.Union _ (map (fun x => match x with (s, _, _) => s end) env))).

Fixpoint well_formed_e env:=
  match env with
  | nil => true
  | (sa, g, l) :: env =>
    match g with
      | Group_By _ g => 
        forallb (fun x => well_formed_ag (env_t _ env (default_tuple _ sa)) x) g &&
        (match l with
         | nil => false
         | t1 :: _ => 
           forallb 
             (fun t => 
                forallb 
                  (fun x => 
                     Oset.eq_bool 
                       (OVal T) (interp_aggterm _ (env_t _ env t) x) 
                       (interp_aggterm _ (env_t _ env t1) x)) g) l
         end)
      | _ => match l with _ :: nil => true | _ => false end
    end 
      && forallb (fun x => labels T x =S?= sa) l 
      && Fset.is_empty 
        _ (sa interS (Fset.Union _ (map (fun slc => match slc with (sa, _, _) => sa end) env)))
      && well_formed_e env
  end.

Lemma well_formed_ft_eq :
  forall f env1 env2, weak_equiv_env T env1 env2 -> well_formed_ft env1 f = well_formed_ft env2 f.
Proof.
intros f.
set (n := size_funterm T f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn env1 env2 He; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | | ]; simpl.
- revert env2 He; induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
  + inversion He; subst; apply refl_equal.
  + destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
    inversion He; subst; simpl.
    unfold well_formed_ft.
    unfold weak_equiv_env_slice in H2; destruct H2 as [K1 K2]; subst g2.
    unfold well_formed_ft; simpl.
    rewrite !extract_funterms_app, !Oset.mem_bool_app, <- (Fset.elements_spec1 _ _ _ K1); 
      apply f_equal.
    apply IHenv1; trivial.
- unfold well_formed_ft; simpl; apply f_equal2.
  + revert env2 He; induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
    * inversion He; subst; apply refl_equal.
    * destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
      inversion He; subst; simpl.
      unfold weak_equiv_env_slice in H2; destruct H2 as [K1 K2]; subst g2.
      unfold well_formed_ft; simpl.
      rewrite !extract_funterms_app, !Oset.mem_bool_app, <- (Fset.elements_spec1 _ _ _ K1); 
        apply f_equal.
      apply IHenv1; trivial.
  + apply forallb_eq; intros x Hx.
    apply IHn; trivial.
    simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
Qed.

Lemma well_formed_ag_eq :
  forall a env1 env2, weak_equiv_env T env1 env2 -> well_formed_ag env1 a = well_formed_ag env2 a.
Proof.
intro e; 
set (n := size_aggterm T e).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert e Hn; induction n as [ | n]; 
  intros e Hn env1 env2 He; [destruct e; inversion Hn | ].
destruct e as [f | a f | f la]; simpl.
- apply well_formed_ft_eq; trivial.
- apply f_equal.
  revert env2 He;  induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
  + inversion He; subst; apply refl_equal.
  + destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
    inversion He; subst; simpl.
    assert (IH := IHenv1 env2 H4).
    destruct (find_eval_env T env1 (A_agg T a f)); destruct (find_eval_env T env2 (A_agg T a f));
      try discriminate IH; trivial.
    unfold equiv_env_slice in H2; destruct H2 as [K1 K2].
    rewrite <- (is_a_suitable_env_eq _ _ _ _ _ _ K1 H4).
    case (is_a_suitable_env T sa1 env1 (A_agg T a f)); apply refl_equal.
- apply forallb_eq; intros x Hx.
  apply IHn; trivial.
  simpl in Hn.
  refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
  apply in_list_size; assumption.
Qed.

Lemma find_eval_env_weak_eq :
  forall e env1 env2, 
    weak_equiv_env T env1 env2 -> 
    match (find_eval_env T env1 e), (find_eval_env T env2 e) with
      | None, None => True
      | Some e1, Some e2 => weak_equiv_env T e1 e2
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
  destruct (find_eval_env T env1 e) as [_l1 | ];
    destruct (find_eval_env T env2 e) as [_l2 | ]; try contradiction IH.
  + assumption.
  + simpl in H2.
    assert (H1 := proj1 H2).
    rewrite <- (is_a_suitable_env_eq T e _ _ _ _ H1 H4).
    case (is_a_suitable_env T sa1 env1 e).
    * constructor 2; trivial.
    * trivial.
Qed.

Lemma find_eval_env_weak_weak_eq :
  forall e env1 env2 s g l,
    (forall x, In x g ->
              is_built_upon_ag 
                T (flat_map (groups_of_env_slice T)
                            ((labels T (default_tuple T s), Group_Fine T, 
                              default_tuple T s :: nil) :: env2)) x = true) ->
        match find_eval_env T (env1 ++ (s, Group_By T g, l) :: env2) e with
    | Some _ => match find_eval_env 
                        T (env1 ++
                                (labels T (default_tuple T s), Group_Fine T, 
                                 default_tuple T s :: nil) :: env2) e with
                | Some _ => True
                | _ => False
                end
    | None => True
    end.
Proof.
intros e env1; induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 s g l Hg; simpl.
- case_eq (find_eval_env T env2 e); [intros; trivial | ].
  intro H; simpl.
  assert (Aux : is_a_suitable_env T (labels T (default_tuple T s)) env2 e =
                is_a_suitable_env T s env2 e).
  {
    apply is_a_suitable_env_eq; [ | apply equiv_env_weak_equiv_env; apply equiv_env_refl].
    apply labels_mk_tuple.
  }
  rewrite Aux.
  case (is_a_suitable_env T s env2 e); trivial.
- assert (IH := IHenv1 env2 s g l).
  case_eq (find_eval_env T (env1 ++ (s, Group_By T g, l) :: env2) e);
    [intros ee Hee; rewrite Hee in IH;
     case_eq 
       (find_eval_env 
          T (env1 ++
            (labels T (default_tuple T s), Group_Fine T, default_tuple T s :: nil) :: env2) e);
    [intros ee' Hee' | intro Hee']; rewrite Hee' in IH; [trivial | contradiction IH] | ].
  case_eq (is_a_suitable_env T sa1 (env1 ++ (s, Group_By T g, l) :: env2) e); [ | intros; trivial].
  intros H1 H2.
  case_eq 
       (find_eval_env 
          T (env1 ++
            (labels T (default_tuple T s), Group_Fine T, default_tuple T s :: nil) :: env2) e);
  [intros; trivial | ].
  intro H4.
  assert (Aux : is_a_suitable_env 
                  T sa1
                  (env1 ++ (labels T (default_tuple T s), Group_Fine T, 
                            default_tuple T s :: nil) :: env2)
                  e = true).
  {
    revert H1; unfold is_a_suitable_env; apply is_built_upon_ag_trans.
    intros x Hx; destruct (in_app_or _ _ _ Hx) as [Kx | Kx].
    - apply in_is_built_upon_ag; apply in_or_app; left; assumption.
    - rewrite flat_map_app in Kx; destruct (in_app_or _ _ _ Kx) as [Jx | Jx].
      + apply in_is_built_upon_ag; apply in_or_app; right; rewrite flat_map_app.
        apply in_or_app; left; assumption.
      + simpl in Jx; destruct (in_app_or _ _ _ Jx) as [Lx | Lx]. 
        * generalize (Hg _ Lx); apply is_built_upon_ag_incl.
          intros y Hy; apply in_or_app; right.
          rewrite flat_map_app; apply in_or_app; right; assumption.
        * apply in_is_built_upon_ag; apply in_or_app; right; rewrite flat_map_app.
          apply in_or_app; right; simpl.
          apply in_or_app; right; assumption.
  }
  rewrite Aux; trivial.
Qed.

Lemma well_formed_e_unfold :
  forall env,  well_formed_e env =
  match env with
  | nil => true
  | (sa, g, l) :: env =>
    match g with
      | Group_By _ g => 
        forallb (fun x => well_formed_ag (env_t _ env (default_tuple _ sa)) x) g &&
        (match l with
         | nil => false
         | t1 :: _ => 
           forallb 
             (fun t => 
                forallb 
                  (fun x => 
                     Oset.eq_bool 
                       (OVal T) (interp_aggterm _ (env_t _ env t) x) 
                       (interp_aggterm _ (env_t _ env t1) x)) g) l
         end)
      | _ => match l with _ :: nil => true | _ => false end
    end 
      && forallb (fun x => labels T x =S?= sa) l 
      && Fset.is_empty 
        _ (sa interS (Fset.Union _ (map (fun slc => match slc with (sa, _, _) => sa end) env)))
      && well_formed_e env
  end.
Proof.
intro env; case env; intros; apply refl_equal.
Qed.

Lemma well_formed_env_t :
  forall env t, 
    well_formed_e env = true -> 
    Fset.is_empty (A T)
                  (labels T t  interS 
                          Fset.Union (A T)
                          (map (fun slc => match slc with (sa, _, _) => sa end) env)) = true -> 
                           well_formed_e (env_t _ env t) = true.
Proof.
intros env t We H; simpl.
rewrite Fset.equal_refl, We, H; apply refl_equal.
Qed.

Lemma well_formed_e_tail :
  forall e1 e2, well_formed_e (e1 ++ e2) = true -> well_formed_e e2 = true.
Proof.
intro e1; induction e1 as [ | [[s1 g1] lt1] e1]; intros e2 W; simpl.
- apply W.
- apply IHe1.
  simpl in W; rewrite !Bool.Bool.andb_true_iff in W.
  apply (proj2 W).
Qed.

Lemma well_formed_ft_tail :
  forall e1 e2 f, well_formed_ft e2 f = true -> well_formed_ft (e1 ++ e2) f = true.
Proof.
intro e1; induction e1 as [ | x1 e1]; intros e2 f Hf; [apply Hf | ].
simpl; destruct f as [c | a | f l]; [apply refl_equal | | ]; unfold well_formed_ft in *; 
  simpl; simpl in Hf.
- rewrite Oset.mem_bool_true_iff, in_extract_funterms in Hf.
  rewrite Oset.mem_bool_true_iff, in_extract_funterms, flat_map_app; 
    do 2 (apply in_or_app; right); assumption.
- rewrite Bool.Bool.orb_true_iff, Oset.mem_bool_true_iff, in_extract_funterms in Hf.
  rewrite Bool.Bool.orb_true_iff, Oset.mem_bool_true_iff, in_extract_funterms, flat_map_app.
  destruct Hf as [Hf | Hf].
  + left; do 2 (apply in_or_app; right); assumption.
  + right; rewrite !extract_funterms_app.
    rewrite forallb_forall in Hf; rewrite forallb_forall; intros a Ha.
    generalize (Hf a Ha); apply is_built_upon_ft_incl.
    intros x Hx; do 2 (apply in_or_app; right); assumption.
Qed.


Lemma well_formed_ft_variables_ft_env :
  forall env f, 
    well_formed_e env = true ->
    well_formed_ft env f = true -> 
    variables_ft T f subS Fset.Union (A T) (map (fun x => match x with (s, _, _) => s end) env).
Proof.
intros env f We Wf.
unfold well_formed_ft in Wf.
assert (H := is_built_upon_ft_variables_ft_sub _ _ _ Wf).
rewrite Fset.subset_spec in H; rewrite Fset.subset_spec; intros a Ha.
generalize (H _ Ha); clear Ha; revert a; rewrite <- Fset.subset_spec.
clear f Wf H; induction env as [ | [[s1 [g1 | ]] l1] env]; simpl.
- rewrite Fset.subset_spec; exact (fun _ h => h).
- simpl in We; rewrite !Bool.Bool.andb_true_iff, forallb_forall in We.
  destruct We as [[[[W1 W2] W3] W4] W5].
  rewrite Fset.subset_spec; intros a Ha.
  rewrite extract_funterms_app, map_app, Fset.mem_Union_app in Ha.
  case_eq (a inS? Fset.Union (A T) (map (variables_ft T) (extract_funterms T g1))); intro Ka;
    rewrite Ka in Ha.
  + rewrite Fset.mem_Union in Ka.
    destruct Ka as [sa [Hsa Ka]]; rewrite in_map_iff in Hsa.
    destruct Hsa as [f [Hf Hsa]]; subst sa.
    rewrite in_extract_funterms in Hsa.
    assert (Wf := W1 _ Hsa); simpl in Wf; unfold well_formed_ft in Wf.
    assert (Hf := is_built_upon_ft_variables_ft_sub _ _ _ Wf).
    unfold env_t, default_tuple in Hf; simpl in Hf.
    rewrite extract_funterms_app, map_app, 
      (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)), extract_funterms_A_Expr in Hf.
    rewrite Fset.subset_spec in Hf.
    generalize (Hf _ Ka); rewrite Fset.mem_Union_app, Bool.Bool.orb_true_iff.
    intros [Ja | Ja].
    * rewrite map_map, Fset.mem_Union in Ja.
      destruct Ja as [sa [Ksa Ja]]; rewrite in_map_iff in Ksa.
      destruct Ksa as [_a [_Ksa Ksa]]; subst sa.
      simpl in Ja; rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in Ja; subst _a.
      rewrite Fset.mem_union, (Fset.in_elements_mem _ _ _ Ksa); apply refl_equal.
    * rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
      revert Ja; generalize a; rewrite <- Fset.subset_spec.
      apply IHenv; apply W5.
  + rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
    simpl in Ha; revert Ha; generalize a; rewrite <- Fset.subset_spec.
    apply IHenv; apply W5.
- simpl in We; rewrite !Bool.Bool.andb_true_iff, forallb_forall in We.
  destruct We as [[[W1 W2] W3] W4].
  rewrite Fset.subset_spec; intros a Ha.
  rewrite extract_funterms_app, extract_funterms_A_Expr, map_app, Fset.mem_Union_app in Ha.
  case_eq (a inS? Fset.Union (A T)
               (map (variables_ft T) (map (fun x : attribute T => F_Dot T x) ({{{s1}}})))); intro Ka;
    rewrite Ka in Ha.
  + rewrite Fset.mem_Union in Ka.
    destruct Ka as [sa [Hsa Ka]]; rewrite in_map_iff in Hsa.
    destruct Hsa as [f [Hf Hsa]]; subst sa.
    rewrite in_map_iff in Hsa.
    destruct Hsa as [_a [_Ha Hsa]]; subst f; simpl in Ka.
    rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in Ka; subst _a.
    rewrite Fset.mem_union, (Fset.in_elements_mem _ _ _ Hsa); apply refl_equal.
  + rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
    simpl in Ha; revert Ha; generalize a; rewrite <- Fset.subset_spec.
    apply IHenv; apply W4.
Qed.

Lemma well_formed_ag_variables_ag_env :
  forall env f, 
    well_formed_e env = true ->
    well_formed_ag env f = true -> 
    variables_ag T f subS Fset.Union (A T) (map (fun x => match x with (s, _, _) => s end) env).
Proof.
intros env f.
set (n := size_aggterm T f + 
          list_size (fun x => match x with 
                              | (_, Group_Fine _, _) => 1
                              | (_, Group_By _ g, _) => 1 + list_size (size_aggterm T) g
                              end) env).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert env f Hn; induction n as [ | n]; intros env f Hn We Wf; [destruct f; inversion Hn | ].
destruct f as [f | ag f | f l].
- simpl; apply well_formed_ft_variables_ft_env; trivial.
- simpl; simpl in Wf; rewrite Bool.Bool.orb_true_iff in Wf; destruct Wf as [Wf | Wf].
  + rewrite Fset.is_empty_spec in Wf.
    rewrite Fset.subset_spec; intros a Ha.
    rewrite (Fset.mem_eq_2 _ _ _ Wf), Fset.empty_spec in Ha.
    discriminate Ha.
  + case_eq (find_eval_env T env (A_agg T ag f)); [ | intros Hf; rewrite Hf in Wf; discriminate Wf].
    clear Wf; induction env as [ | [[s1 g1] lt1] env]; intros e He; simpl in He.
    * case_eq (is_built_upon_ft T nil f); intro Hf; rewrite Hf in He; [ | discriminate He].
      injection He; intro; subst e.
      apply (is_built_upon_ft_variables_ft_sub _ _ _ Hf).
    * case_eq (find_eval_env T env (A_agg T ag f)).
      -- intros e2 He2.
         rewrite Fset.subset_spec; intros a Ha; simpl.
         rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
         revert a Ha; rewrite <- Fset.subset_spec; apply IHenv with e2; [ | | assumption].
         ++ refine (le_trans _ _ _ _ Hn); apply plus_le_compat_l; simpl.
            apply le_plus_r.
         ++ simpl in We; rewrite !Bool.Bool.andb_true_iff in We.
            apply (proj2 We).
      -- intro He'; rewrite He' in He.
         unfold is_a_suitable_env in He.
         case_eq (is_built_upon_ag T
                    (map (fun a : attribute T => A_Expr T (F_Dot T a)) ({{{s1}}}) ++
                         flat_map (groups_of_env_slice T) env) (A_agg T ag f)); 
           intro Hf; rewrite Hf in He; [ | discriminate He]; simpl in Hf.
         rewrite Oset.mem_bool_app, !Bool.Bool.orb_true_iff, !Oset.mem_bool_true_iff in Hf.
         destruct Hf as [[Hf | Hf] |Hf].
         ++ rewrite in_map_iff in Hf; destruct Hf as [a [Hf _]]; discriminate Hf.
         ++ rewrite in_flat_map in Hf.
            destruct Hf as [x [Hx Hf]].
            destruct (in_split _ _ Hx) as [env1 [env2 Henv]]; subst env; clear Hx.
            rewrite app_comm_cons in We; assert (We' := well_formed_e_tail _ _ We).
            destruct x as [[s2 [g2 | ]] lt2]; simpl in We'.
            ** injection He; intro; subst e; simpl in Hf.
               rewrite !Bool.Bool.andb_true_iff, !forallb_forall in We'.
               destruct We' as [[[W1 W2] W3] W4]; simpl in Hf.
               assert (IH : variables_ag T
                              (A_agg T ag f)
                              subS Fset.Union (A T)
                              (map (fun x : env_slice T => let (y, _) := x in let (s, _) := y in s)
                                   (env_t T env2 (default_tuple T s2)))).
               {
                 apply IHn.
                 - rewrite list_size_unfold in Hn; rewrite plus_assoc in Hn.
                   destruct g1 as [g1 | ].
                   + rewrite (plus_comm _ (1 + _)) in Hn.
                     refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
                     apply plus_le_compat.
                     * apply le_plus_r.
                     * unfold env_t; rewrite list_size_app.
                       refine (le_trans _ _ _ _ (le_plus_r _ _)); simpl.
                       apply le_n_S; apply le_plus_r.
                   + rewrite (plus_comm _ 1) in Hn.
                     refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); simpl.
                     apply le_n_S; apply plus_le_compat_l.
                     rewrite list_size_app.
                     refine (le_trans _ _ _ _ (le_plus_r _ _)); simpl.
                       apply le_n_S; apply le_plus_r.
                 - unfold env_t; simpl; rewrite !Bool.Bool.andb_true_iff; repeat split.
                   + apply Fset.equal_refl.
                   + rewrite <- W3; apply Fset.is_empty_eq.
                     apply Fset.inter_eq_1; unfold default_tuple.
                     rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
                     apply Fset.equal_refl.
                   + assumption.
                 - apply W1; assumption.
               }
               simpl in IH; rewrite Fset.subset_spec in IH; 
                 simpl; rewrite Fset.subset_spec; intros a Ha; assert (IHa := IH a Ha).
               rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
               rewrite map_app, Fset.mem_Union_app, Bool.Bool.orb_true_iff; right; simpl.
               rewrite <- IHa; apply Fset.mem_eq_2; apply Fset.union_eq_1.
               unfold default_tuple; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
               apply Fset.equal_refl.
            ** simpl in Hf; rewrite in_map_iff in Hf.
               destruct Hf as [a [Hf _]]; discriminate Hf.
         ++ destruct g1 as [g1 | ];
            [ | apply (well_formed_ft_variables_ft_env ((s1, Group_Fine T, lt1) :: env) f We Hf)].
            assert (Kf := is_built_upon_ft_variables_ft_sub _ _ _ Hf).
            rewrite extract_funterms_app, extract_funterms_A_Expr, map_app, map_map in Kf.
            rewrite Fset.subset_spec in Kf; 
              simpl; rewrite Fset.subset_spec; intros a Ha; assert (Ka := Kf a Ha).
            rewrite Fset.mem_Union_app, Bool.Bool.orb_true_iff in Ka; destruct Ka as [Ka | Ka].
            ** rewrite Fset.mem_Union in Ka.
               destruct Ka as [s [Hs Ka]]; rewrite in_map_iff in Hs.
               destruct Hs as [_a [_Hs Hs]]; subst s; simpl in Ka.
               rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in Ka; subst _a.
               rewrite Fset.mem_union, Bool.Bool.orb_true_iff; left.
               apply Fset.in_elements_mem; assumption.
            ** rewrite Fset.mem_Union in Ka.
               destruct Ka as [s [Hs Ka]]; rewrite in_map_iff in Hs.
               destruct Hs as [_f [Hs _Hf]]; subst s.
               rewrite in_extract_funterms, in_flat_map in _Hf.
               destruct _Hf as [[[s2 g2] l2] [_Hf _Kf]].
               destruct (in_split _ _ _Hf) as [env1 [env2 Ke]]; subst env.
               destruct g2 as [g2 | ].
               --- simpl in _Kf.
                   rewrite app_comm_cons in We; assert (We2 := well_formed_e_tail _ _ We); 
                     simpl in We2; rewrite !Bool.Bool.andb_true_iff, !forallb_forall in We2.
                   assert (_Jf := proj1 (proj1 (proj1 (proj1 We2))) _ _Kf).
                   rewrite Fset.mem_union, map_app, Fset.mem_Union_app, 2 Bool.Bool.orb_true_iff; 
                     do 2 right.
                   clear Ha; revert a Ka; rewrite <- Fset.subset_spec.
                   assert (_Hn : size_aggterm T (A_Expr T _f) +
                                 list_size
                                   (fun x : env_slice _ =>
                                      let (y, _) := x in
                                      let (_, y2) := y in
                                      match y2 with
                                      | Group_By _ g => 1 + list_size (size_aggterm T) g
                                      | Group_Fine _ => 1
                                      end) 
                                   ((s2, Group_Fine T, default_tuple T s2 :: nil) :: env2) <= n).
                   {
                     apply le_S_n; refine (le_trans _ _ _ _ Hn); simpl.
                     rewrite list_size_app; simpl; rewrite <- !plus_n_Sm.
                     do 3 apply le_n_S.
                     do 3 refine (le_trans _ _ _ _ (le_plus_r _ _)).
                     apply plus_le_compat_r.
                     refine (le_trans _ _ _ _ (in_list_size (size_aggterm T) _ _ _Kf)); simpl.
                     apply le_S; apply le_n.
                   }
                   apply (IHn _ _ _Hn).
                   +++ destruct We2 as [[[[W1 W2] W3] W4] W5]; simpl; unfold default_tuple.
                       rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
                         Fset.equal_refl, W4, W5; apply refl_equal.
                   +++ unfold env_t in _Jf; simpl in _Jf; unfold well_formed_ft in _Jf; 
                         simpl in _Jf.
                       unfold well_formed_ft; simpl; rewrite <- _Jf.
                       unfold default_tuple; 
                         rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)); 
                         apply refl_equal.
               --- simpl in _Kf; rewrite in_map_iff in _Kf.
                   destruct _Kf as [_a [_Kf _Ha]]; injection _Kf; intro; subst _f.
                   simpl in Ka; rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in Ka; subst _a.
                   rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
                   rewrite map_app, Fset.mem_Union_app, Bool.Bool.orb_true_iff; right.
                   simpl; rewrite Fset.mem_union, (Fset.in_elements_mem _ _ _ _Ha); 
                     apply refl_equal.
- simpl; rewrite Fset.subset_spec; intros a Ha.
  rewrite Fset.mem_Union in Ha.
  destruct Ha as [s [Hs Ha]]; rewrite in_map_iff in Hs.
  destruct Hs as [ag [_Hs Hs]]; subst s.
  revert a Ha; rewrite <- Fset.subset_spec; apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply plus_le_compat_r; apply in_list_size; assumption.
  + assumption.
  + simpl in Wf; rewrite forallb_forall in Wf; apply Wf; assumption.
Qed.

Lemma well_formed_ft_proj_env_t :
  forall s g l env1 env2, well_formed_e (env1 ++ (s, g, l) :: env2) = true ->
  forall x d, labels T d =S= s -> 
    well_formed_ft (env1 ++ (s, g, l) :: env2) x = true ->
    well_formed_ft (env1 ++ env_t T env2 d) x = true.
Proof.
intros s g l env1 env2 W x d Hd; unfold well_formed_ft.
apply is_built_upon_ft_trans; clear x; intros x Hx.
rewrite flat_map_app, extract_funterms_app in Hx; simpl in Hx.
destruct (in_app_or _ _ _ Hx) as [Kx | Kx].
- apply in_is_built_upon_ft; rewrite !flat_map_app, !extract_funterms_app; 
    apply in_or_app; left; assumption.
- rewrite extract_funterms_app in Kx; destruct (in_app_or _ _ _ Kx) as [Jx | Jx].
  + destruct g as [g | ].
    * rewrite in_extract_funterms in Jx.
      assert (W' := well_formed_e_tail _ _ W).
      simpl in W'; rewrite !Bool.Bool.andb_true_iff, forallb_forall in W'.
      assert (Wx := proj1 (proj1 (proj1 (proj1 W'))) _ Jx); simpl in Wx;
      unfold well_formed_ft in Wx; revert Wx; apply is_built_upon_ft_incl.
      intros f Hf; rewrite flat_map_app, extract_funterms_app.
      apply in_or_app; right.
      unfold env_t in *; rewrite in_extract_funterms in Hf; simpl in Hf.
      unfold default_tuple in Hf; 
        rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Hf.
      rewrite in_extract_funterms; simpl.
      rewrite (Fset.elements_spec1 _ _ _ Hd); apply Hf.
    * rewrite extract_funterms_A_Expr in Jx.
      apply in_is_built_upon_ft; rewrite in_extract_funterms, flat_map_app.
      apply in_or_app; right; unfold env_t; simpl; apply in_or_app; left.
      rewrite (Fset.elements_spec1 _ _ _ Hd).
      rewrite in_map_iff in Jx; destruct Jx as [a [_Jx Jx]]; subst x.
      rewrite in_map_iff; eexists; split; [ | apply Jx]; apply refl_equal.
  + apply in_is_built_upon_ft; rewrite !flat_map_app, !extract_funterms_app; 
    apply in_or_app; right.
    unfold env_t; simpl; rewrite extract_funterms_app; apply in_or_app; right; assumption.
Qed.

Lemma well_formed_ag_proj_env_t :
  forall s g l env1 env2, well_formed_e (env1 ++ (s, g, l) :: env2) = true ->
  forall x d, labels T d =S= s -> 
    well_formed_ag (env1 ++ (s, g, l) :: env2) x = true ->
    well_formed_ag (env1 ++ env_t T env2 d) x = true.
Proof.
intros s g l env1 env2 W x d Hd.
set (n := size_aggterm T x); assert (Hn := le_n n); unfold n at 1 in Hn.
clearbody n; revert x Hn; induction n as [ | n]; intros x Hn; [destruct x; inversion Hn | ].
destruct x as [f | a f | fc lf]; simpl.
- apply well_formed_ft_proj_env_t; assumption.
- case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Hf; [exact (fun _ => refl_equal _) | ].
  rewrite !Bool.Bool.orb_false_l.
  case_eq (find_eval_env T (env1 ++ (s, g, l) :: env2) (A_agg T a f)); 
    [ | intros _ Abs; discriminate Abs].
  intros e He _.
  clear IHn; induction env1 as [ | [[sa1 g1] l1] env1]; simpl in He; simpl.
  + case_eq (find_eval_env T env2 (A_agg T a f)); [intros; apply refl_equal | ].
    intro Ke; rewrite Ke in He.
    case_eq (is_a_suitable_env T s env2 (A_agg T a f)); intro Jf; rewrite Jf in He; 
      [injection He; clear He; intro; subst e | discriminate He].
    assert (Aux : is_a_suitable_env T (labels T d) env2 (A_agg T a f) = true).
    {
    unfold is_a_suitable_env in *; simpl in Jf; simpl.
    rewrite (Fset.elements_spec1 _ _ _ Hd).
    apply Jf.
    }
    rewrite Aux; apply refl_equal.
  + simpl in W; rewrite !Bool.Bool.andb_true_iff in W.
    case_eq (find_eval_env T (env1 ++ (s, g, l) :: env2) (A_agg T a f)).
    * intros e' He'; rewrite He' in He; injection He; clear He; intro; subst e'.
      assert (IH := IHenv1 (proj2 W) He').
      destruct (find_eval_env T (env1 ++ env_t T env2 d) (A_agg T a f));
      [apply refl_equal | discriminate IH].
    * intro Ke; rewrite Ke in He.
      case_eq (is_a_suitable_env T sa1 (env1 ++ (s, g, l) :: env2) (A_agg T a f)); intro Kf;
        rewrite Kf in He; [ | discriminate He].
      injection He; clear He; intro; subst e.
      case_eq (find_eval_env T (env1 ++ env_t T env2 d) (A_agg T a f));
        [intros; apply refl_equal | intro Jf].
      revert Kf; unfold is_a_suitable_env; simpl.
      rewrite !Oset.mem_bool_app.
      case_eq (Oset.mem_bool (OAggT T) (A_agg T a f)
                             (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{sa1}}})));
        [intros; apply refl_equal | ].
      intros _; rewrite !Bool.Bool.orb_false_l, !flat_map_app, !Oset.mem_bool_app.
      case_eq (Oset.mem_bool (OAggT T) (A_agg T a f) (flat_map (groups_of_env_slice T) env1));
        intro Lf; unfold env_slice in *; rewrite Lf; [intros; apply refl_equal | ].
      rewrite !Bool.Bool.orb_false_l; destruct g as [g | ]; simpl.
      -- rewrite Oset.mem_bool_app; case_eq (Oset.mem_bool (OAggT T) (A_agg T a f) g); intro Mf.
         ++ intros _; rewrite Oset.mem_bool_true_iff in Mf.
            destruct W as [W1 W2]; assert (W' := well_formed_e_tail _ _ W2); simpl in W'.
            rewrite !Bool.Bool.andb_true_iff, forallb_forall in W'.
            assert (Wf:= proj1 (proj1 (proj1 (proj1 W'))) _ Mf); simpl in Wf.
            case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Nf;
              [rewrite (empty_vars_is_built_upon_ft _ _ Nf), Bool.Bool.orb_true_r; 
               apply refl_equal | ].
            rewrite Nf, Bool.Bool.orb_false_l in Wf.
            assert (Pf := find_eval_env_none _ _ _ _ Ke); simpl in Pf.
            case_eq (find_eval_env T env2 (A_agg T a f));
              [intros e He; rewrite He in Pf; discriminate Pf | intro Qf; rewrite Qf in Wf].
            case_eq (is_a_suitable_env T (labels T (default_tuple T s)) env2 (A_agg T a f));
              intro Rf; rewrite Rf in Wf; [ | discriminate Wf].
            unfold is_a_suitable_env in Rf; simpl in Rf; rewrite Bool.Bool.orb_true_iff in Rf.
            unfold default_tuple in Rf; 
              rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Rf.
            rewrite (Fset.elements_spec1 _ _ _ Hd).
            destruct Rf as [Rf | Rf]; [unfold env_slice in *; rewrite Rf; apply refl_equal | ].
            assert (Aux : is_built_upon_ft T
               (extract_funterms T
                (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{sa1}}}) ++
                 flat_map (groups_of_env_slice T) env1 ++
                 map (fun a0 : attribute T => A_Expr T (F_Dot T a0))
                   ({{{s}}}) ++ flat_map (groups_of_env_slice T) env2))
               f = true).
            {
              revert Rf; apply is_built_upon_ft_incl.
              intros x Hx; rewrite in_extract_funterms in Hx; rewrite in_extract_funterms.
              do 2 (apply in_or_app; right); apply Hx.
            }
            unfold env_slice in *; rewrite Aux, Bool.Bool.orb_true_r; apply refl_equal.
         ++ rewrite Bool.Bool.orb_false_l, Oset.mem_bool_app.
            case_eq (Oset.mem_bool 
                       (OAggT T) (A_agg T a f) (flat_map (groups_of_env_slice T) env2));
              intro Nf; unfold env_slice in *;  rewrite Nf;
                [intros _; rewrite Bool.Bool.orb_true_r; apply refl_equal | ].
            rewrite Bool.Bool.orb_false_l, Bool.Bool.orb_false_r; intro Pf.
            assert (Aux : is_built_upon_ft T
               (extract_funterms T
                (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{sa1}}}) ++
                 flat_map (groups_of_env_slice T) env1 ++
                 map (fun a0 : attribute T => A_Expr T (F_Dot T a0))
                   ({{{s}}}) ++ flat_map (groups_of_env_slice T) env2))
               f = true).
            {
              revert Pf; apply is_built_upon_ft_trans.
              intros x Hx; rewrite in_extract_funterms in Hx.
              destruct (in_app_or _ _ _ Hx) as [Kx | Kx].
              - apply in_is_built_upon_ft;
                  rewrite in_extract_funterms; apply in_or_app; left; assumption.
              - destruct (in_app_or _ _ _ Kx) as [Jx | Jx].
                + apply in_is_built_upon_ft;
                    rewrite in_extract_funterms; apply in_or_app; right;
                      apply in_or_app; left; assumption.
                + destruct (in_app_or _ _ _ Jx) as [Lx | Lx].
                  * assert (W' := well_formed_e_tail _ _ (proj2 W)); simpl in W'.
                    rewrite !Bool.Bool.andb_true_iff, forallb_forall in W'.
                    assert (Wx := proj1 (proj1 (proj1 (proj1 W'))) _ Lx); simpl in Wx;
                      unfold well_formed_ft in Wx; revert Wx; apply is_built_upon_ft_incl.
                    intros y Hy; rewrite in_extract_funterms in Hy; rewrite in_extract_funterms.
                    do 2 (apply in_or_app; right).
                    unfold env_t in Hy; simpl in Hy.
                    unfold default_tuple in Hy; 
                      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Hy; 
                      apply Hy.
                  * apply in_is_built_upon_ft;
                      rewrite in_extract_funterms; do 3 (apply in_or_app; right); assumption.
            }
            unfold env_slice in *; 
              rewrite (Fset.elements_spec1 _ _ _ Hd), Aux, Bool.Bool.orb_true_r.
            apply refl_equal.
      -- rewrite !Oset.mem_bool_app, (Fset.elements_spec1 _ _ _ Hd);
         case_eq (Oset.mem_bool 
                      (OAggT T) (A_agg T a f) 
                      (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{s}}})));
           intro Mf; [intros; apply refl_equal | ].
         intro Nf; rewrite Nf; apply refl_equal.
- rewrite !forallb_forall; intros H x Hx.
  apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + apply H; assumption.
Qed.

(*
Lemma well_formed_ft_extend_env_slice :
  forall env1 env2 s sa g l,
    List.length s = List.length g ->
    all_diff s ->
    let env := (env1 ++ (sa, Group_By T g, l) :: env2) in
    (forall a, 
        In a s -> 
        a inS Fset.Union (A T) (List.map (fun x => match x with (sa, _, _) => sa end) env) -> 
        False) ->
    well_formed_e env = true ->
    forall x,
    well_formed_ft env x = true ->
    well_formed_ft
      (env1 ++ extend_env_slice T env2 s (sa, Group_By T g, l) :: env2) x = true.
Proof.
intros env1 env2 s sa g l L D env H W x;
  set (n := size_funterm T x); assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert env1 env2 s sa g l L D env H W x Hn; induction n as [ | n];
  intros env1 env2 s sa g l L D env H W x Hn Wx; [destruct x; inversion Hn | ].
destruct x as [c | a | f k].
- apply refl_equal.
- unfold well_formed_ft in Wx; simpl in Wx; rewrite Oset.mem_bool_true_iff in Wx.
  rewrite in_extract_funterms, in_flat_map in Wx.
  destruct Wx as [x [Hx Kx]].
  unfold env in Hx.
  unfold well_formed_ft; simpl; 
      rewrite Oset.mem_bool_true_iff, in_extract_funterms, in_flat_map.
  destruct (in_app_or _ _ _ Hx) as [Jx | Jx].
  + eexists; split; [apply in_or_app; left; apply Jx | ]; assumption.
  + simpl in Jx; destruct Jx as [Jx | Jx].
    * unfold env in W; assert (W' := well_formed_e_tail _ _ W); simpl in W'.
      rewrite !Bool.Bool.andb_true_iff, forallb_forall in W'.
      destruct W' as [[[[Wg _] _] _] _].
      subst x; simpl in Kx.
      assert (Wa := Wg _ Kx); simpl in Wa.
      unfold well_formed_ft in Wa; simpl in Wa.
      rewrite Oset.mem_bool_true_iff, in_extract_funterms in Wa.
      destruct (in_app_or _ _ _ Wa) as [Ha | Ha].
      -- rewrite 
    * subst x; simpl in Kx.
      eexists; split; [apply in_or_app; right; left; apply refl_equal | ].
      simpl.
; unfold well_formed_ft; induction env1 as [ | [[sa1 g1] l1] env1];
  intros env2 s sa g l L D H W x Wx; rewrite extend_env_slice_unfold.
- rewrite app_nil in Wx; rewrite app_nil.
  
Qed.

Lemma well_formed_ag_extend_env_slice :
  forall env1 env2 s sa g l,
    List.length s = List.length g ->
    all_diff s ->
    let env := (env1 ++ (sa, Group_By T g, l) :: env2) in
    (forall a, 
        In a s -> 
        a inS Fset.Union (A T) (List.map (fun x => match x with (sa, _, _) => sa end) env) -> 
        False) ->
    well_formed_e env = true ->
    forall x,
    well_formed_ag env x = true ->
    well_formed_ag
      (env1 ++ extend_env_slice T env2 s (sa, Group_By T g, l) :: env2) x = true.

Lemma well_formed_e_extend_env_slice :
  forall env1 env2 s sa g l,
    List.length s = List.length g ->
    all_diff s ->
    let env := (env1 ++ (sa, Group_By T g, l) :: env2) in
    (forall a, 
        In a s -> 
        a inS Fset.Union (A T) (List.map (fun x => match x with (sa, _, _) => sa end) env) -> 
        False) ->
    well_formed_e env = true ->
    well_formed_e (env1 ++ (extend_env_slice T env2 s (sa, Group_By T g, l)) :: env2) = true.
Proof.
intro env1; induction env1 as [ | [[sa1 g1] l1] env1];
  intros env2 s sa g l L D env H W.
- unfold env in *; 
    rewrite app_nil, well_formed_e_unfold, !Bool.Bool.andb_true_iff, forallb_forall in W.
  destruct W as [[[[W1 W2] W3] W4] W5].
  rewrite app_nil, extend_env_slice_unfold, well_formed_e_unfold.
  rewrite !Bool.Bool.andb_true_iff, forallb_forall; repeat split.
  + intros _a Ha; rewrite in_map_iff in Ha; destruct Ha as [a [_Ha Ha]]; subst _a; simpl.
    unfold well_formed_ft, env_t; subst; apply in_is_built_upon_ft.
    rewrite in_extract_funterms, in_flat_map; eexists; split; [left; apply refl_equal | ]; simpl.
    rewrite in_map_iff; eexists; split; [apply refl_equal | ].
    unfold default_tuple; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
    apply Fset.mem_in_elements; rewrite Fset.mem_union, Bool.Bool.orb_true_iff; right.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff; assumption.
  + destruct l as [ | t1 l]; [discriminate W2 | ].
    rewrite (map_unfold _ (_ :: _)) at 1.
    rewrite forallb_forall.
    intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [t [_Hx Ht]]; subst x.
    rewrite forallb_forall; intros e He; rewrite in_map_iff in He.
    destruct He as [a [_Ha Ha]]; subst e.
    rewrite Oset.eq_bool_true_iff; simpl.
    rewrite !(Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
    apply if_eq; [apply refl_equal | | intros; apply refl_equal].
    intro Ka; rewrite !dot_mk_tuple, !Ka.
    unfold pair_of_select, id_renaming; rewrite map_app, !map_map, !Oset.find_app.
    case_eq (Oset.find (OAtt T) a (map (fun x => (x, A_Expr T (F_Dot T x))) ({{{sa}}}))).
    * intros e He; assert (Ke := Oset.find_some _ _ _ He).
      rewrite in_map_iff in Ke; destruct Ke as [_b [_Hb Ke]].
      injection _Hb; do 2 intro; subst _b e; simpl.
      apply False_rec; apply (H a Ha).
      rewrite Fset.mem_Union; eexists; split; [left; apply refl_equal | ].
      apply Fset.in_elements_mem; assumption.
    * intro Ja; case_eq (Oset.find
                           (OAtt T) a
                           (map
                              (fun x : attribute T * aggterm T =>
                                 match (let (a0, e) := x in Select_As T e a0) with
                                 | Select_As _ e a0 => (a0, e)
                                 end) (combine s g)));
      [intros e He | intros; apply refl_equal].
      rewrite forallb_forall in W2; generalize (W2 _ Ht); rewrite forallb_forall.
      intros Kt; assert (Ke := Kt e); rewrite Oset.eq_bool_true_iff in Ke; apply Ke.
      assert (Je := Oset.find_some _ _ _ He); rewrite in_map_iff in Je.
      destruct Je as [[_a _e] [_Je Je]]; injection _Je; do 2 intro; subst _a _e.
      revert Je; apply in_combine_r.
  + rewrite forallb_forall; intros x Hx; rewrite in_map_iff in Hx.
    destruct Hx as [t [_Hx Ht]]; subst x.
    rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)).
    unfold id_renaming; rewrite map_app, !map_map, map_id; [ | intros; trivial].
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)).
    apply Fset.union_eq; [apply Fset.mk_set_idem | ].
    rewrite Fset.equal_spec; intro a; do 2 apply f_equal.
    revert L; generalize s g; intro s1; 
      induction s1 as [ | a1 s1]; intros g1 L; [apply refl_equal | ].
    destruct g1 as [ | x1 g1]; [discriminate L | ].
    simpl; apply f_equal; apply IHs1; injection L; exact (fun h => h).
  + rewrite Fset.is_empty_spec, Fset.equal_spec; intro a.
    rewrite Fset.mem_inter, Fset.mem_union, Fset.empty_spec.
    rewrite Bool.Bool.andb_false_iff, Bool.Bool.orb_false_iff.
    case_eq (a inS? sa); intro Ha.
    * right.
      rewrite Fset.is_empty_spec, Fset.equal_spec in W4.
      generalize (W4 a); rewrite Fset.mem_inter, Ha, Bool.Bool.andb_true_l, Fset.empty_spec.
      exact (fun h => h).
    * case_eq (a inS? Fset.mk_set (A T) s); intro Ka; [ | left; split; trivial].
      right.
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Ka.
      rewrite <- not_true_iff_false; intro Ja; rewrite Fset.mem_Union in Ja.
      destruct Ja as [_s [_Hs Ja]].
      rewrite in_map_iff in _Hs; destruct _Hs as [[[_sa _g] _l] [_Hs Hs]]; subst _sa.
      apply (H _ Ka); rewrite Fset.mem_Union.
      eexists; split; [ | apply Ja].
      rewrite in_map_iff; eexists; split; [ | right; apply Hs].
      apply refl_equal.
  + assumption.
- unfold env in W; rewrite <- app_comm_cons, well_formed_e_unfold in W.
  rewrite !Bool.Bool.andb_true_iff in W.
  destruct W as [[[W1 W2] W3] W4].
  rewrite <- app_comm_cons, well_formed_e_unfold, !Bool.Bool.andb_true_iff; repeat split.
  + destruct g1 as [g1 | ]; [rewrite Bool.Bool.andb_true_iff in W1; destruct W1 as [W1 W1'];
                             rewrite Bool.Bool.andb_true_iff; split | ].
    * rewrite forallb_forall in W1.
      rewrite forallb_forall; intros x Hx.
      generalize (W1 _ Hx).
      
rewrite !Fset.mem_mk_set.
      rewrite Oset.find_map.

      apply projection_eq.
env_tac.
  progress cbv beta iota zeta.
  
Qed.
*)

Lemma well_formed_e_proj_env_t :
  forall s g l env, 
    well_formed_e ((s, g, l) :: env) = true ->
    forall t1 k, quicksort (OTuple T) l = t1 :: k ->
    well_formed_e (env_t T env t1) = true.
Proof.
intros s g l env W; unfold env_t; intros t1 k Ql;
  simpl in W; rewrite !Bool.Bool.andb_true_iff in W; simpl;
  destruct W as [[[W1 W2] W3] W4].
rewrite Fset.equal_refl, W4, Bool.Bool.andb_true_l, Bool.Bool.andb_true_r.
rewrite <- W3; apply Fset.is_empty_eq.
apply Fset.inter_eq_1.
rewrite forallb_forall in W2; apply W2.
rewrite (In_quicksort (OTuple T)), Ql; left; apply refl_equal.
Qed.
(*
- assert (IH := IHenv1 W4); clear IHenv1.
  rewrite W2, (IH _ _ Ql), !Bool.Bool.andb_true_r, !Bool.Bool.andb_true_iff; repeat split.
  + rewrite forallb_forall in W1; rewrite forallb_forall.
    intros x Hx; generalize (proj1 W1 _ Hx); unfold env_t.
    rewrite !app_comm_cons.
    apply well_formed_ag_proj_env_t; simpl.
    * rewrite Fset.equal_refl, W4, Bool.Bool.andb_true_r; simpl.
      rewrite <- W3; apply Fset.is_empty_eq; apply Fset.inter_eq_1.
      unfold default_tuple; apply labels_mk_tuple.
    * assert (W := well_formed_e_tail _ _ W4); simpl in W.
      rewrite !Bool.Bool.andb_true_iff, forallb_forall in W.
      apply (proj2 (proj1 (proj1 W))); rewrite (In_quicksort (OTuple T)), Ql; left.
      apply refl_equal.
  + destruct W1 as [W1 W1'].
    destruct l1 as [ | u1 l1]; [discriminate W1' | ].
    rewrite forallb_forall; intros x Hx; rewrite forallb_forall; intros y Hy.
    rewrite forallb_forall in W1; assert (Wy := W1 _ Hy); unfold env_t in *.
    rewrite Oset.eq_bool_true_iff.
    rewrite forallb_forall in W1'; assert (W := W1' _ Hx).
    rewrite forallb_forall in W; assert (W' := W _ Hy).
    rewrite Oset.eq_bool_true_iff in W'.
    revert W'; unfold env_t; clear Hy; 
      set (n := size_aggterm T y); assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
    revert y Hn Wy; induction n as [ | n]; intros y Hn Wy H; [destruct y; inversion Hn | ].
    destruct y as [f | a f | f _k]; simpl.
    * assert (Kx := interp_funterm_homogeneous 
                      T s g l (labels T t1) (@Group_Fine _) t1 k 
                      ((labels T x, Group_Fine T, x :: nil) :: env1) env2 f Ql).
      simpl in H, Kx; simpl; rewrite Kx in H.
      assert (Ku1 := interp_funterm_homogeneous 
                      T s g l (labels T t1) (@Group_Fine _) t1 k 
                      ((labels T u1, Group_Fine T, u1 :: nil) :: env1) env2 f Ql).
      simpl in Ku1; simpl; rewrite Ku1 in H; apply H.
    * apply f_equal.
      case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Hf.
      -- unfold unfold_env_slice; rewrite !map_map, !quicksort_1; simpl.
         apply f_equal2; [ | apply refl_equal].
         rewrite !(interp_cst_funterm _ (_ :: _)); trivial.
      -- case_eq (find_eval_env 
                    T (env1 ++ (labels T t1, Group_Fine T, t1 :: nil) :: env2) (A_agg T a f));
           [intros; apply refl_equal | intro Kf].
         assert (Aux : is_a_suitable_env 
                         T (labels T x) (env1 ++ (labels T t1, Group_Fine T, t1 :: nil) :: env2)
                         (A_agg T a f) = 
                       is_a_suitable_env 
                         T (labels T u1) (env1 ++ (labels T t1, Group_Fine T, t1 :: nil) :: env2)
                         (A_agg T a f)).
         {
           unfold is_a_suitable_env; simpl.
           rewrite forallb_forall in W2.
           rewrite !(Fset.elements_spec1 _ _ _ (W2 _ Hx)),
             !(Fset.elements_spec1 _ _ _ (W2 _ (or_introl _ (refl_equal _)))).
           apply f_equal.
           rewrite !flat_map_app; simpl; apply refl_equal.
         }
         rewrite <- Aux.
         case_eq (is_a_suitable_env 
                    T (labels T x) (env1 ++ (labels T t1, Group_Fine T, t1 :: nil) :: env2)
                    (A_agg T a f)); intro Jf; [ | apply refl_equal].
         unfold unfold_env_slice; rewrite !map_map, !quicksort_1; simpl.
         apply f_equal2; [ | apply refl_equal].
         simpl in H; rewrite Hf in H.
         
         rewrite !interp_aggterm_unfold, !Hf in H.
         apply H.

         ++ intros e He; apply refl_equal.
         apply empty_vars_is_built_upon_ft
      rewrite <- map_eq. 
      
 apply refl_equal.
 in H.
      
simpl in Hn; generalize (le_S_n _ _ Hn); clear Hn; intro Hn.
      clear IHn; revert f Hn Wy; induction n as [ | n]; intros f Hn Wy; 
           [destruct f; inversion Hn | ].
      -- destruct f as [c | a | f _k]; [intros; apply refl_equal | | ]; intro H.
         ++ simpl in H; simpl.
            rewrite forallb_forall in W2.
            rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Hx)), 
              (Fset.mem_eq_2 _ _ _ (W2 _ (or_introl _ (refl_equal _)))) in H.
            rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Hx)), 
              (Fset.mem_eq_2 _ _ _ (W2 _ (or_introl _ (refl_equal _)))).
            destruct (a inS? sa1); [apply H | apply refl_equal].
         ++ simpl.
revert W2.
++ simpl in Wy; unfold well_formed_ft in Wy; simpl in Wy.
               rewrite extract_funterms_app, Oset.mem_bool_app in Wy; simpl.
               case_eq (Oset.mem_bool 
                          (OFun T) (F_Dot T a)
                          (extract_funterms 
                             T (map (fun a : attribute T => A_Expr T (F_Dot T a))
                                    ({{{labels T (default_tuple T sa1)}}})))); intro Ha;
                 [ | rewrite Ha, Bool.Bool.orb_false_l in Wy].
               --- rewrite Oset.mem_bool_true_iff, in_extract_funterms, in_map_iff in Ha.
                   destruct Ha as [_a [_Ha Ha]]; injection _Ha; intro; subst _a.
                   unfold default_tuple in Ha; 
                     rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
                   simpl; rewrite forallb_forall in W2; rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Hx)).
                   rewrite (Fset.in_elements_mem _ _ _ Ha); apply refl_equal.
               --- simpl; case_eq (a inS? labels T x); [intros; apply refl_equal | intro Ka].
                   
               rewrite Oset.mem_bool_true_iff, in_extract_funterms in Wy.
               simpl; case_eq (a inS? labels T x); intro Ha; [apply refl_equal | ].
                              
               unfold interp_dot;
simpl in H; simpl.
            rewrite forallb_forall in W2; 
              rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Hx)), 
                (Fset.mem_eq_2 _ _ _ (W2 _ (or_introl _ (refl_equal _)))) in H.
            rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Hx)), 
                (Fset.mem_eq_2 _ _ _ (W2 _ (or_introl _ (refl_equal _)))).
            case_eq (a inS? sa1); intro Ha; rewrite Ha in H; [apply H | ].
            apply refl_equal.
         ++ simpl in H.
            ; apply f_equal.
            
    unfold env_t in W'; unfold env_t.
    r
    * 
    assumption.
; unfold env_t in Kx; unfold env_t.
    clear Hx; revert Kx.
 well_formed_ag
    ((labels T (default_tuple T sa1), Group_Fine T, default_tuple T sa1 :: nil)
     :: env1 ++ (s, g, l) :: env2) x = true ->
  well_formed_ag
    ((labels T (default_tuple T sa1), Group_Fine T, default_tuple T sa1 :: nil)
     :: env1 ++ (labels T (default_tuple T s), Group_Fine T, default_tuple T s :: nil) :: env2) x =
  true
 set (n := size_aggterm T x); assert (Hn := le_n n); unfold n at 1 in Hn.
    clearbody n; revert x Hn; induction n as [ | n]; intros x Hn; [destruct x; inversion Hn | ].
    destruct x as [f | a f | fc lf]; simpl; 
      unfold well_formed_ag, well_formed_ft; unfold env_t in *.
    * apply is_built_upon_ft_trans; intros x; rewrite !in_extract_funterms, !in_flat_map.
      intros [[[_sa _g] _l] [H1 H2]];  destruct H1 as [H1 | H1].
      -- injection H1; do 3 intro; subst _sa _g _l; simpl in H2; rewrite in_map_iff in H2.
         destruct H2 as [a [H2 H3]]; injection H2; intro; subst x.
         apply in_is_built_upon_ft; rewrite in_extract_funterms; apply in_or_app; left; simpl.
                  rewrite in_map_iff; eexists; split; [ | apply H3]; apply refl_equal.
      -- destruct (in_app_or _ _ _ H1) as [H3 | H3].
         ++ apply in_is_built_upon_ft; rewrite in_extract_funterms, flat_map_unfold.
            apply in_or_app; right; rewrite flat_map_app; apply in_or_app; left.
            rewrite in_flat_map; eexists; split; [apply H3 | apply H2].
         ++ simpl in H3; destruct H3 as [H3 | H3].
            *** injection H3; do 3 intro; subst _sa _g _l.
                destruct g as [g | ]; simpl in H2.
                ---- assert (W := well_formed_e_tail _ _ W4); simpl in W.
                     rewrite !Bool.Bool.andb_true_iff, forallb_forall in W.
                     assert (Wx := proj1 (proj1 (proj1 (proj1 W))) _ H2); simpl in Wx.
                     unfold well_formed_ft in Wx; revert Wx; apply is_built_upon_ft_incl.
                     intros y Hy; rewrite in_extract_funterms in Hy; rewrite in_extract_funterms.
                     rewrite flat_map_unfold; apply in_or_app; right.
                     rewrite flat_map_app; apply in_or_app; right.
                     apply Hy.
                ---- rewrite in_map_iff in H2.
                     destruct H2 as [a [_H2 H2]]; injection _H2; intro; subst x.
                     apply in_is_built_upon_ft; rewrite in_extract_funterms, flat_map_unfold.
                     apply in_or_app; right; rewrite flat_map_app; apply in_or_app; right; simpl.
                     apply in_or_app; left; unfold default_tuple.
                     rewrite in_map_iff, (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _ )).
                     eexists; split; [ | apply H2]; apply refl_equal.
            *** apply in_is_built_upon_ft; rewrite in_extract_funterms, flat_map_unfold.
                apply in_or_app; right; rewrite flat_map_app; apply in_or_app; right; simpl.
                apply in_or_app; right; rewrite in_flat_map; eexists; split; [apply H3 | apply H2].
    * case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Hf; [intros; apply refl_equal | ].
      destruct g as [g | ].
      assert (Aux : find_eval_env T (env1 ++ (s, Group_By T g, l) :: env2) (A_agg T a f) =
                    find_eval_env T
           (env1 ++
            (labels T (default_tuple T s), Group_Fine T, default_tuple T s :: nil) :: env2)
           (A_agg T a f)).
weak_equiv_env 
                      T (env1 ++ (s, g, l) :: env2)
                      (env1 ++ (labels T (default_tuple T s), 
                                Group_Fine T, default_tuple T s :: nil) :: env2)).
      {
        apply Forall2_app; [apply equiv_env_weak_equiv_env; apply equiv_env_refl | ].
        constructor 2; [ | apply equiv_env_weak_equiv_env; apply equiv_env_refl].
        simpl.
      }
= find_eval_env_weak_eq  (A_agg T a f) (env1 ++ (s, g, l) :: env2) (env1 ++ (labels T (default_tuple T s), Group_Fine T, default_tuple T s :: nil) :: env2)).
      induction env1 as [ | [[_sa [_g | ]] _l] env1]; simpl.
      -- case_eq (find_eval_env T env2 (A_agg T a f)); [intros; apply refl_equal | ].
         exact (fun h => h).
  simpl in W; rewrite !Bool.Bool.andb_true_iff in W; simpl;
  destruct W as [[[W1 W2] W3] W4].      induction env1 as [
                assumption.
rewrite in_flat_map; eexists; split; [apply H3 | apply H2].

            rewrite in_flat_map; eexists; split; [apply H3 | apply H2].
                     
in_extract_funterms.
                     
apply is_built_upon_ft_incl with (groups_of_env_slice T (s, g, l)
        [eexists; split; [ | apply H2]; right; apply in_or_app; left; assumption | ].
      destruct H3 as [H3 | H3]; 
        [ | eexists; split; [ | apply H2]; right; apply in_or_app; do 2 right; assumption].
      injection H3; do 3 intro; subst _sa _g _l.
      simpl in H2; destruct g as [g | ].
      eexists; split; [right | ].
assumption ].
      destruct (in_split _ _ H1) as [e1 [e2 H3]].
 in Hx; rewrite in_extract_funterms.
      
    * revert
rewrite <- (proj1 W1); apply forallb_eq; intros x Hx; unfold env_t.
    unfold well_formed_ag.
    apply well_formed_ag_eq; constructor 2.
    * simpl; split; [apply Fset.equal_refl | apply refl_equal].
    * apply Forall2_app; [apply equiv_env_weak_equiv_env; apply equiv_env_refl | ].
      constructor 2; [ | apply equiv_env_weak_equiv_env; apply equiv_env_refl].
      simpl; split.
 [ | apply refl_equal].
apply weak_equiv_env_slice_refl.
[ | ].
destruct W1 as [W0 W1]; rewrite W2.
Qed.
*)
Lemma well_formed_ag_variables_ag_env_alt :
  forall slc env f, 
    well_formed_e (slc :: env) = true ->
    In f (groups_of_env_slice T slc) ->
    (variables_ag T f)
      subS Fset.Union (A T) (map (fun x => match x with (s, _, _) => s end) (slc :: env)).
Proof.
intros [[s g] l] env f We Hf; simpl in Hf.
assert (Wf : well_formed_ag (env_t T env (default_tuple T s)) f = true).
{
  simpl in We; rewrite !Bool.Bool.andb_true_iff in We; simpl;
    destruct We as [[[W1 W2] W3] W4].
  destruct g as [g | ].
  - rewrite Bool.Bool.andb_true_iff, forallb_forall in W1; apply (proj1 W1 _ Hf).
  - rewrite in_map_iff in Hf; destruct Hf as [a [Hf Ha]]; subst f; simpl.
    unfold well_formed_ft; simpl.
    rewrite extract_funterms_app, Oset.mem_bool_app, extract_funterms_A_Expr.
    unfold default_tuple; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
    rewrite Bool.Bool.orb_true_iff; left.
    rewrite Oset.mem_bool_true_iff, in_map_iff.
    eexists; split; [apply refl_equal | assumption].
}
case_eq l; [intro Hl | intros t1 k Hl]; 
  [destruct g; rewrite Hl in We; simpl in We; 
   [rewrite Bool.Bool.andb_false_r in We | ]; discriminate We | ].
assert (L := length_quicksort (OTuple T) l); rewrite Hl in L at 2.
case_eq (quicksort (OTuple T) l); [intro Ql; rewrite Ql in L; discriminate L | ].
intros u1 k' Ql.
assert (We' : well_formed_e (env_t T env (default_tuple T s)) = true).
{
  apply well_formed_env_t; [apply (well_formed_e_tail (_ :: nil) env We) | ].
  simpl in We; rewrite !Bool.Bool.andb_true_iff in We.
  destruct We as [[[_ _] W3] _].
  rewrite <- W3; apply Fset.is_empty_eq.
  apply Fset.inter_eq_1.
  unfold default_tuple; apply labels_mk_tuple.
}
rewrite <- (well_formed_ag_variables_ag_env _ f We' Wf).
apply Fset.subset_eq_2; simpl; apply Fset.union_eq_1.
unfold default_tuple; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
apply Fset.equal_refl.
Qed.

End Sec.
