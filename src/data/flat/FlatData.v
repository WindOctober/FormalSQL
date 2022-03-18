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
Require Export NJoinTuples.
Require Export FTerms.
Require Export ATerms.
Require Export Env.
Require Export Interp.
Require Export Projection.
Require Export WellFormed.
Require Export EnvInv.
Import Tuple.

Section Sec.

Hypothesis T : Rcd.
(* 
dot, funterm, aggterm and their interpretation 
*)

(*
wellformedness of funterms, aggterms, environments
*)


Lemma simplify_renaming :
  forall (x : attribute T * attribute T),
    match 
      (match x return select T with 
         (a, b) => Select_As T (A_Expr T (F_Dot T a)) b end)  with
    | Select_As _ e a => (a, e)
    end = (snd x, (A_Expr T (F_Dot T (fst x)))).
Proof.
intros [a b]; simpl; apply refl_equal.
Qed.

Lemma map_simplify_renaming :
  forall ll,
    map
      (fun x : attribute T * attribute T =>
         match (let (a, b0) := x in Select_As T (A_Expr T (F_Dot T a)) b0) with
         | Select_As _ e a => (a, e)
         end) ll =
    map (fun x => (snd x, (A_Expr T (F_Dot T (fst x))))) ll.
Proof.
intro ll;
  rewrite <- map_eq; intros; apply simplify_renaming.
Qed.


(*
Lemma interp_dot_eq_strong :
  forall env1 env2 s g l s1 s2 a,
    well_formed_e T (env1 ++ (s, g, l) :: env2) = true ->
    well_formed_ft  T (env1 ++ (s, g, l) :: env2) (F_Dot T a) = true ->
    s =S= (s1 unionS s2) ->
    (a inS s2 -> a inS s1) ->
    interp_dot T (env1 ++ (s, g, l) :: env2) a =
    interp_dot T
      (env1 ++ (s1, g, (map (fun t => mk_tuple T s1 (dot T t)) l)) :: env2) a.
Proof.
intros env1 env2 s g l s1 s2 a We Wf Hs Hfa.
induction env1 as [ | [[sa1 g1] l1] env1]; simpl.
- assert (L := length_quicksort (OTuple T) l).
  assert (L' := 
            length_quicksort (OTuple T) (map (fun t : tuple T => mk_tuple T s1 (dot T t)) l)).
  rewrite map_length in L'.
  case_eq (quicksort (OTuple T) l).
  + intro Q; rewrite Q in L; destruct l; [ | discriminate L].
    simpl; apply refl_equal.
  + intros t1 l1 Q; rewrite Q in L; rewrite <- L in L'.
    case_eq (quicksort (OTuple T) (map (fun t : tuple T => mk_tuple T s1 (dot T t)) l));
      [intro Q'; rewrite Q' in L'; discriminate L' | ].
    intros u1 k1 Q'.
    assert (Hu1 : In u1 (u1 :: k1)); [left; apply refl_equal | ].
    rewrite <- Q', <- In_quicksort, in_map_iff  in Hu1.
    destruct Hu1 as [tu1 [Hu1 Htu1]]; subst u1.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
    simpl in We; rewrite !Bool.Bool.andb_true_iff in We; destruct We as [[[W1 W2] W3] W4].
    rewrite forallb_forall in W2.
    assert (Ht1 : In t1 (t1 :: l1)); [left; apply refl_equal | ].
    rewrite <- Q, <- In_quicksort in Ht1.
    rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Ht1)).
    assert (Ha : (a inS? s) = (a inS? s1)).
    {
      rewrite (Fset.mem_eq_2 _ _ _ Hs), Fset.mem_union.
      case_eq (a inS? s2); intro Ha.
      - rewrite (Hfa Ha); apply refl_equal.
      - rewrite Bool.Bool.orb_false_r; apply refl_equal.
    }
    rewrite Ha; case_eq (a inS? s1); intro Ka; [ | apply refl_equal].
    rewrite dot_mk_tuple, Ka.
    unfold well_formed_ft in Wf; simpl in Wf.
    rewrite Oset.mem_bool_true_iff, in_extract_funterms in Wf.
    destruct (in_app_or _ _ _ Wf) as [Wa | Wa].
    * destruct g as [g | ].
      -- rewrite Bool.Bool.andb_true_iff, !forallb_forall in W1.
         destruct l as [ | u _l]; [contradiction Ht1 | ].
         rewrite forallb_forall in W1.
         assert (Ktu1 := proj2 W1 _ Htu1); rewrite forallb_forall in Ktu1.
         assert (Jtu1 := Ktu1 _ Wa); rewrite Oset.eq_bool_true_iff in Jtu1.
         assert (Kt1 := proj2 W1 _ Ht1); rewrite forallb_forall in Kt1.
         assert (Jt1 := Kt1 _ Wa); rewrite Oset.eq_bool_true_iff in Jt1.
         simpl in Jtu1, Jt1.            
         rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Htu1)), Ha, Ka in Jtu1.
         rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Ht1)), Ha, Ka in Jt1.
         rewrite Jtu1, Jt1; apply refl_equal.
      -- destruct l as [ | u [ | ]]; try discriminate W1.
         simpl in Htu1; destruct Htu1 as [Htu1 | Htu1]; [subst tu1 | contradiction Htu1].
         simpl in Ht1; destruct Ht1 as [Ht1 | Ht1]; [subst t1 | contradiction Ht1].
         apply refl_equal.
    * apply False_rec.
      rewrite in_flat_map in Wa.
      destruct Wa as [[[s' g'] l'] [W' Wa]]; simpl in Wa.
      destruct (in_split _ _ W') as [e1 [e2 He]].
      assert (We' : well_formed_e T ((s', g', l') :: e2) = true).
      {
        rewrite He in W4; apply (well_formed_e_tail _ _ _ W4).
      }
      assert (H := well_formed_ag_variables_ag_env_alt _ _ (A_Expr (F_Dot a)) We' Wa).
      simpl in H; rewrite Fset.subset_spec in H.
      rewrite Fset.is_empty_spec, Fset.equal_spec in W3.
      generalize (W3 a).
      rewrite Fset.mem_inter, Ha, Ka, He, map_app, (map_unfold _ (_ :: _)).
      rewrite Fset.mem_Union_app; simpl; rewrite Fset.empty_spec.
      rewrite (H a), Bool.Bool.orb_true_r; [discriminate | ].
      rewrite Fset.singleton_spec, Oset.eq_bool_refl; apply refl_equal.
- simpl in We; rewrite !Bool.Bool.andb_true_iff in We.
  destruct We as [[[Wg1 Wl1] Wsa1] We]; rewrite Fset.is_empty_spec, Fset.equal_spec in Wsa1.
  case_eq (quicksort (OTuple T) l1); [intro Q | intros t1 q1 Q].
  + assert (L := length_quicksort (OTuple T) l1).
    rewrite Q in L; destruct l1; [ | discriminate L].
    destruct g1; [ | discriminate Wg1].
    rewrite Bool.Bool.andb_false_r in Wg1; discriminate Wg1.
  + case_eq (a inS? labels T t1); intro Ha1; [apply refl_equal | ].
    assert (Ka1 : a inS? sa1 = false).
    {
      rewrite <- Ha1; apply sym_eq; apply Fset.mem_eq_2.
      rewrite forallb_forall in Wl1; apply Wl1.
      rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
    }
    apply IHenv1; [apply We | ].
    unfold well_formed_ft in Wf; simpl in Wf.
    rewrite extract_funterms_app, Oset.mem_bool_app, Bool.Bool.orb_true_iff in Wf.
    destruct Wf as [Wf | Wf]; [ | apply Wf].
    rewrite Oset.mem_bool_true_iff, in_extract_funterms in Wf.
    destruct g1 as [g1 | ].
    * rewrite Bool.Bool.andb_true_iff, forallb_forall in Wg1.
      generalize (proj1 Wg1 _ Wf); simpl; unfold env_t, well_formed_ft, is_built_upon_ft.
      simpl; rewrite extract_funterms_app, extract_funterms_A_Expr, Oset.mem_bool_app, 
             Bool.Bool.orb_true_iff.
      intros [H | H]; [ | apply H].
      rewrite Oset.mem_bool_true_iff, in_map_iff in H.
      destruct H as [_a [_H H]]; injection _H; intro; subst _a.
      unfold default_tuple in H; 
        rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in H.
      rewrite (Fset.in_elements_mem _ _ _ H) in Ka1; discriminate Ka1.
    * rewrite in_map_iff in Wf.
      destruct Wf as [_a [_H H]]; injection _H; intro; subst _a.
      rewrite (Fset.in_elements_mem _ _ _ H) in Ka1; discriminate Ka1.
Qed.

*)




Lemma interp_aggterm_eq_env_t_strong :
  forall env1 env2 s1 s2 t e,
    well_formed_e T (env1 ++ env_t T env2 t) = true ->
    labels T t =S= (s1 unionS s2) ->
    (forall a, a inS (s2 interS (variables_ag T e)) -> a inS s1) ->
    interp_aggterm T (env1 ++ env_t T env2 t) e =
    interp_aggterm T (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) e.
Proof.
intros env1 env2 s1 s2 t e.
set (n := size_aggterm T e).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert e Hn; induction n as [ | n]; 
  intros e Hn We Ht1 He; [destruct e; inversion Hn | ].
destruct e as [f | a f | f la].
- simpl.
  apply interp_funterm_eq_env_t_strong with s2; trivial.
- rewrite 2 interp_aggterm_unfold; cbv beta iota zeta; apply f_equal.
  case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Hf.
  + destruct env1 as [ | [[sa1 g1] ll1] env1].
    * simpl; apply f_equal2; [ | apply refl_equal].
      apply (interp_funterm_eq_env_t_strong T nil env2 s1 s2 t f We Ht1 He).
    * simpl; rewrite !map_map, <- map_eq; simpl.
      intros x Hx.
      apply (interp_funterm_eq_env_t_strong T (_ :: env1) env2 s1 s2 t f).
      -- simpl in We; simpl.
         rewrite !Bool.Bool.andb_true_iff in We; destruct We as [[[W1 W2] W3] W4].
         rewrite !Bool.Bool.andb_true_iff; repeat split; trivial.
         ++ rewrite forallb_forall in W2; apply W2; rewrite (In_quicksort (OTuple T)); assumption.
      -- assumption.
      -- intros b Hb; simpl in Hb.
         apply He; apply Hb.
  + assert (Aux : find_eval_env T (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) (A_agg T a f) =
                  find_eval_env T (env1 ++ env_t T env2 t) (A_agg T a f) \/
                  (exists env1' env1'', 
                      env1 = env1' ++ env1'' /\ 
                      find_eval_env T (env1 ++ env_t T env2 t) (A_agg T a f) = 
                      Some (env1'' ++ env_t T env2 t) /\
                      find_eval_env T (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) (A_agg T a f) = 
                      Some (env1'' ++ env_t T env2 (mk_tuple T s1 (dot T t))))).
    {
      clear IHn.
      induction env1 as [ | [[sa1 g1] ll1] env1].
      - simpl.
        case_eq (find_eval_env T env2 (A_agg T a f)); [intros; left; apply refl_equal | ].
        intro H1; unfold is_a_suitable_env.
        rewrite (Fset.elements_spec1 _ _ _ Ht1).
        rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
        assert (Aux : is_built_upon_ag T
                        (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{s1 unionS s2}}}) ++
                                flat_map (groups_of_env_slice T) env2) (A_agg T a f) = 
                       is_built_upon_ag T
                         (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{s1}}}) ++
                                flat_map (groups_of_env_slice T) env2) (A_agg T a f)).
        {
          apply is_built_upon_ag_restrict.
          intros b Hb; apply He; apply Hb.
        }
        rewrite Aux.
         case (is_built_upon_ag T
                 (map (fun a0 : attribute T => A_Expr T (F_Dot T a0)) ({{{s1}}}) ++
                      flat_map (groups_of_env_slice T) env2) (A_agg T a f)); 
           [ | left; apply refl_equal].
         right; exists nil; exists nil; split; [ | split]; apply refl_equal.
      - assert (IH : find_eval_env T (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) (A_agg T a f) =
                     find_eval_env T (env1 ++ env_t T env2 t) (A_agg T a f) \/
           (exists env1' env1'' : list (Fset.set (A T) * (group_by T) * list (tuple T)),
              env1 = env1' ++ env1'' /\
              find_eval_env T (env1 ++ env_t T env2 t) (A_agg T a f) = Some (env1'' ++ env_t T env2 t) /\
              find_eval_env T (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) (A_agg T a f) =
              Some (env1'' ++ env_t T env2 (mk_tuple T s1 (dot T t))))).
        {
          apply IHenv1.
          simpl in We; rewrite Bool.Bool.andb_true_iff in We; apply (proj2 We).
        }
        simpl; destruct IH as [IH | IH].
        + rewrite IH.
          case_eq (find_eval_env T (env1 ++ env_t T env2 t) (A_agg T a f)); 
            [intros; left; apply refl_equal | intro H].
          assert (Aux : is_a_suitable_env T
                          sa1 (env1 ++ env_t T env2 (mk_tuple T s1 (dot T t))) (A_agg T a f) = 
                        is_a_suitable_env T sa1 (env1 ++ env_t T env2 t) (A_agg T a f)).
          {
            unfold is_a_suitable_env.
            assert (Aux := is_built_upon_ag_restrict T
                           (flat_map (groups_of_env_slice T) ((sa1, Group_Fine T, ll1) :: env1 ++ env2))
                           s1 s2 (A_agg T a f) He).
            apply eq_sym; refine (eq_trans _ (eq_trans Aux _)).
            - apply is_built_upon_ag_permut; simpl.
              rewrite !flat_map_app; simpl.
              rewrite (Fset.elements_spec1 _ _ _ Ht1), !ass_app.
              apply _permut_app; [ | apply Oset.permut_refl].
              refine (Oset.permut_trans (_permut_swapp _ _) _);
              [apply Oset.permut_refl | apply Oset.permut_refl | ].
              rewrite <- ass_app; apply Oset.permut_refl.
            - apply is_built_upon_ag_permut; simpl.
              rewrite !flat_map_app; simpl.
              rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)), !ass_app.
              apply _permut_app; [ | apply Oset.permut_refl].
              rewrite <- ass_app; apply _permut_swapp; apply Oset.permut_refl.
          }
          rewrite Aux.
          case (is_a_suitable_env T sa1 (env1 ++ env_t T env2 t) (A_agg T a f)); 
            [ | left; apply refl_equal].
          right; exists nil; exists ((sa1, g1, ll1) :: env1).
          split; [ | split]; apply refl_equal.
        + destruct IH as [env1' [env1'' [IH1 [IH2 IH3]]]]; rewrite IH2, IH3; right.
          eexists; eexists; split; [ | split; apply refl_equal].
          rewrite IH1, app_comm_cons; apply f_equal2; [ | apply refl_equal].
          apply refl_equal.
    }
    destruct Aux as [Aux | [env1' [env1'' [Aux1 [Aux2 Aux3]]]]].
    * rewrite Aux; apply refl_equal.
    * rewrite Aux2, Aux3.
      destruct env1'' as [ | [[sa g] ll] env1'']; unfold env_t, unfold_env_slice; simpl.
      -- apply f_equal2; [ | apply refl_equal].
         apply (interp_funterm_eq_env_t_strong T nil env2 s1 s2 t f); trivial.
         revert We; clear; simpl app.
         induction env1 as [ | [[sa g] ll] env1]; [exact (fun h => h) | ].
         intro H; apply IHenv1; simpl in H.
         rewrite Bool.Bool.andb_true_iff in H; apply (proj2 H).
      -- rewrite !map_map, <- map_eq; intros x Hx.
         apply (interp_funterm_eq_env_t_strong 
                  T ((sa, _, x :: nil) :: env1'') env2 s1 s2 t f); trivial.
         rewrite Aux1 in We.
         revert We; clear -Hx; simpl app.
         induction env1' as [ | [[sa1 g1] ll1] env1'].
         ++ simpl; rewrite !Bool.Bool.andb_true_iff;
              intros [[[W1 W2] W3] W4]; repeat split; trivial.
            rewrite forallb_forall in W2; apply W2.
            apply (In_quicksort (OTuple T)); apply Hx.
         ++ intro W; apply IHenv1'.
            simpl in W; rewrite Bool.Bool.andb_true_iff in W; apply (proj2 W).
- simpl; apply f_equal; rewrite <- map_eq; intros x Hx.
  apply IHn; trivial.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + intros a Ha; apply He.
    rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ha.
    rewrite Fset.mem_inter, (proj1 Ha), Bool.Bool.andb_true_l; simpl.
    rewrite Fset.mem_Union.
    eexists; split; [ | apply (proj2 Ha)].
    rewrite in_map_iff; eexists; split; [apply refl_equal | assumption].
Qed.

(*
Lemma interp_aggterm_eq_env_t_strong_alt :
  forall s s' g env t e, 
    let lb := map (fun x => match x with Select_As _ _ b => b end) s' in
    Fset.is_empty 
      _ (s unionS (Fset.mk_set _ lb) 
           interS (Fset.Union _ (map (fun slc => match slc with (sa, _, _) => sa end) env))) = true ->
     well_formed_e T env = true ->
     well_formed_ag T (env_t T env (default_tuple T s)) e = true ->
     labels T t =S= s -> In e g ->
     interp_aggterm T (env_t T env (projection T (env_t T env t) 
                                            (Select_List _ (_Select_List _ (id_renaming T s ++ s'))))) e =
     interp_aggterm T (env_t T env t) e.
Proof.
  intros s s' g env t1 e lb Hlb We Wg Wt1 _.
  set (t := (projection T (env_t T env t1) (Select_List _ (_Select_List _ (id_renaming T s ++ s'))))).
  assert (Kt1 := Oeset.compare_eq_sym _ _ _ (projection_id_env_t env _ _ Wt1)).
  assert (Wt : labels T t =S= (s unionS Fset.mk_set _ lb)).
  {
    unfold t, projection, id_renaming.
    rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), !map_app, !map_map.
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)).
    apply Fset.union_eq.
    - rewrite map_id; [apply Fset.mk_set_idem | intros; trivial].
    - unfold lb; rewrite Fset.equal_spec; intro b. 
      do 2 apply f_equal; rewrite <- map_eq; intros [ ] _; apply refl_equal.
  }
  assert (We' : well_formed_e (env_t env (default_tuple s)) = true).
  {
  apply well_formed_env_t.
  - apply We.
  - rewrite Fset.is_empty_spec, Fset.equal_spec; intro a.
    unfold default_tuple; 
      rewrite Fset.mem_inter, (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.empty_spec.
    case_eq (a inS? s); intro Ha; [ | apply refl_equal].
    rewrite Fset.is_empty_spec, Fset.equal_spec in Hlb.
    assert (Ka := Hlb a); rewrite Fset.empty_spec, Fset.mem_inter, Fset.mem_union, Ha in Ka.
    apply Ka.
  }
  assert (Jt1 : t1 =t= mk_tuple T s (dot T t)).
  {
    rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ Wt1), 
      (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)); split; [apply Fset.equal_refl | ].
    intros a Ha; rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ Wt1), Ha.
    assert (Ha' : a inS labels T t).
    {
      rewrite (Fset.mem_eq_2 _ _ _ Wt), Fset.mem_union, <- (Fset.mem_eq_2 _ _ _ Wt1), Ha.
      apply refl_equal.
    }
    generalize (tuple_eq_dot t _ (projection_app _ _ _) a); rewrite Ha';
      intro Aux; rewrite Aux; clear Aux.
    unfold join_tuple; rewrite dot_mk_tuple.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
    rewrite <- (Fset.mem_eq_2 _ _ _ (tuple_eq_labels _ _ Kt1)), Ha, Bool.Bool.orb_true_l.
    rewrite (tuple_eq_dot_alt _ _ Kt1); [apply refl_equal | assumption].
  }    
  apply trans_eq with (interp_aggterm (env_t env (mk_tuple T s (dot T t))) e).
  - apply (interp_aggterm_eq_env_t_strong nil env s (Fset.mk_set _ lb)).
    + apply well_formed_env_t; [apply We | ].
      rewrite Fset.is_empty_spec, (Fset.equal_eq_1 _ _ _ _ (Fset.inter_eq_1 _ _ _ _ Wt)).
      rewrite Fset.is_empty_spec in Hlb; apply Hlb.
    + assumption.
    + intros a Ha; rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ha.
      assert (H2 := well_formed_ag_variables_ag_env _ _ We' Wg).
      rewrite Fset.subset_spec in H2; assert (H3 := H2 _ (proj2 Ha)).
      unfold env_t in H3; simpl in H3; unfold default_tuple in H3.
      rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in H3.
      case_eq (a inS? s); intro Ka; [apply refl_equal | ].
      rewrite Ka, Bool.Bool.orb_false_l in H3.
      rewrite Fset.is_empty_spec, Fset.equal_spec in Hlb.
      generalize (Hlb a); rewrite Fset.mem_inter, H3, Bool.Bool.andb_true_r.
      rewrite Fset.mem_union, Ka, (proj1 Ha), Fset.empty_spec.
      exact (fun h => sym_eq h).
  - apply sym_eq; apply interp_aggterm_eq; constructor 2; [ | apply equiv_env_refl].
    simpl; repeat split.
    + apply tuple_eq_labels; assumption.
    + rewrite compare_list_t; unfold compare_OLA; rewrite !quicksort_1; simpl.
      rewrite Jt1; apply refl_equal.
Qed.

*)
Lemma well_formed_e_extend :
  forall env s s' l,
    let lb := map (fun x => match x with Select_As _ _ b => b end) s' in
    let g := map (fun x => match x with Select_As _ ag _ => ag end) s' in
    well_formed_e T ((s, Group_By T g, l) :: env) = true ->
    Fset.is_empty _ (Fset.inter _ s (Fset.mk_set (A T) lb)) = true ->
    Fset.is_empty (A T)
    ((Fset.mk_set (A T) lb) 
       interS 
       Fset.Union (A T) (map (fun slc : env_slice T => let (y, _) := slc in let (sa, _) := y in sa) env)) =
    true ->
    well_formed_e T
      ((s unionS Fset.mk_set (A T) lb, Group_By T (map (fun b => A_Expr _ (F_Dot _ b)) lb),
        map (fun x => projection T (env_t T env x) (Select_List T (_Select_List T (id_renaming T s ++ s')))) l) :: env) = true.
Proof.
intros env s s' l lb g W H H'; rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff in W.
destruct W as [[[[W1 W2] W3] W4] W5]; rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff; repeat split.
- rewrite forallb_forall; intros b Hb.
  rewrite in_map_iff in Hb; destruct Hb as [_b [_Hb Hb]]; subst b; simpl.
  unfold well_formed_ft; simpl.
  rewrite extract_funterms_app, extract_funterms_A_Expr, Oset.mem_bool_app, Bool.Bool.orb_true_iff.
  left; rewrite Oset.mem_bool_true_iff, in_map_iff.
  eexists; split; [apply refl_equal | ].
  apply Fset.mem_in_elements; unfold default_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union, Fset.mem_mk_set.
  rewrite <- (Oset.mem_bool_true_iff (OAtt T)) in Hb; rewrite Hb, Bool.Bool.orb_true_r.
  apply refl_equal.
- destruct l as [ | t1 l]; [discriminate W2 | ].
  set (l' :=  map (fun x => 
                     projection T (env_t T env x) 
                       (Select_List T (_Select_List _ (id_renaming T s ++ s')))) 
                  (t1 :: l)).
  unfold l' at 1.
  rewrite map_unfold, forallb_forall; intros x Hx; rewrite forallb_forall.
  intros e He; rewrite in_map_iff in He.
  destruct He as [b [He Hb]]; subst e; rewrite !interp_aggterm_unfold, !interp_funterm_unfold.
  unfold env_t; rewrite !(interp_dot_unfold T (_ :: env) b), !quicksort_1.
  unfold l' in Hx; rewrite in_map_iff in Hx.
  destruct Hx as [t [_Hx Ht]]; subst x.
  rewrite !(Fset.mem_eq_2 _ _ _ (labels_projection _ _ _)); unfold projection.
  unfold sort_of_select_list, id_renaming; rewrite map_app, map_map, map_id; [ | intros; trivial].
  rewrite Fset.mem_mk_set_app, !Fset.mem_mk_set; fold lb.
  rewrite !dot_mk_tuple, (proj2 (Oset.mem_bool_true_iff (OAtt T) b lb)), Bool.Bool.orb_true_r;
    [ | assumption].
  rewrite Fset.mem_mk_set_app, !Fset.mem_mk_set, (proj2 (Oset.mem_bool_true_iff (OAtt T) b lb)), 
     Bool.Bool.orb_true_r; simpl; trivial.
  unfold pair_of_select; rewrite map_app, map_map, Oset.find_app.
  case_eq (Oset.find 
             (OAtt T) b (map (fun x : attribute T => (x, A_Expr _ (F_Dot _ x))) ({{{s}}}))).
  + intros a Ha; apply False_rec.
    assert (Ja := Oset.find_some _ _ _ Ha); rewrite in_map_iff in Ja.
    destruct Ja as [_a [_Ja Ja]]; injection _Ja; do 2 intro; subst _a a.
    rewrite Fset.is_empty_spec, Fset.equal_spec in H.
    generalize (H b); rewrite Fset.mem_inter, Fset.empty_spec, Fset.mem_mk_set.
    rewrite (Fset.in_elements_mem _ _ _ Ja), Bool.Bool.andb_true_l, <- not_true_iff_false, 
    Oset.mem_bool_true_iff; intro Abs; apply Abs; assumption.
  + intros _; case_eq (Oset.find 
                         (OAtt T) b (map (fun x : select T => match x with
                                                              | Select_As _ e a => (a, e)
                                                              end) s'));
    [ | intros; apply Oset.eq_bool_refl].
    intros a Ha; unfold env_t; simpl; rewrite Oset.eq_bool_true_iff.
    assert (Ka := Oset.find_some _ _ _ Ha).
    rewrite in_map_iff in Ka; destruct Ka as [[_a _b] [_Ka Ka]]; injection _Ka; 
      do 2 intro; subst _a _b.
    assert (Ja : In a g).
    {
      unfold g; rewrite in_map_iff.
      eexists; split; [ | apply Ka]; apply refl_equal.
    }
    rewrite forallb_forall in W2.
    assert (W2t := W2 _ Ht); rewrite forallb_forall in W2t.
    assert (Wa := W2t _ Ja); rewrite Oset.eq_bool_true_iff in Wa; unfold env_t in Wa.
    apply Wa.
- rewrite forallb_forall; intros x Hx; rewrite in_map_iff in Hx.
  destruct Hx as [y [Hx Hy]]; subst x.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)).
  unfold id_renaming; rewrite map_app, map_map.
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)); apply Fset.union_eq.
  + rewrite map_id; [ | intros; apply refl_equal].
    apply Fset.mk_set_idem.
  + apply Fset.equal_refl.
- rewrite Fset.is_empty_spec, Fset.equal_spec in H, H', W4; 
    rewrite Fset.is_empty_spec, Fset.equal_spec.
  intro a; generalize (H' a) (W4 a).
  rewrite !Fset.mem_inter, Fset.mem_union, !Fset.empty_spec.
  case (a inS? s); simpl.
  * exact (fun _ h => h).
  * exact (fun h _ => h).
- assumption.
Qed.


(*
Lemma interp_funterm_eq_env_g_strong :
  forall env1 env2 s s' l,
    let lb := map (fun x => match x with Select_As _ _ b => b end) s' in
    let g := map (fun x => match x with Select_As _ ag _ => ag end) s' in
    well_formed_e T (env1 ++ (s, Group_By T g, l) :: env2) = true ->
    well_formed_e T (env1 ++ (s unionS Fset.mk_set (A T) lb, 
                    Group_By _ (map (fun b : attribute T => A_Expr _ (F_Dot _ b)) lb),
                    map (fun x => 
                           projection _ (env1 ++ env_t _ env2 x) 
                                      (Select_List _ (_Select_List _ (id_renaming _ s ++ s')))) l)
                          :: env2) = true ->
    forall e,
      well_formed_ft T (env1 ++ (s, Group_By T g, l) :: env2) e = true ->
    interp_funterm T (env1 ++ (s, Group_By T g, l) :: env2) e =
    interp_funterm T
      (env1 ++ (s unionS Fset.mk_set (A T) lb, 
                Group_By _ (map (fun b : attribute T => A_Expr _ (F_Dot _ b)) lb),
                map (fun x => projection 
                                _ (env1 ++ env_t _ env2 x) 
                                (Select_List _ (_Select_List _ (id_renaming _ s ++ s')))) l)
            :: env2) e.
Proof.
intros env1 env2 s s' l lb g We' We'' e.
assert (W0 := well_formed_e_proj_env_t _ _ _ _ We').
set (n := size_funterm e).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert e Hn; induction n as [ | n]; intros f Hn Wf; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | apply interp_dot_eq_env_g_strong; trivial | ].
unfold well_formed_ft in Wf; simpl in Wf.
case_eq (Oset.mem_bool OFun (F_Expr fc lf) (extract_funterms (g ++ flat_map groups_of_env_slice env)));
  intro H; [ | rewrite H, Bool.Bool.orb_false_l in Wf].
- rewrite Oset.mem_bool_true_iff, in_extract_funterms in H.
  destruct (in_app_or _ _ _ H) as [H' | H'].
  + case_eq (quicksort 
               (OTuple T) 
               (map (fun x => projection (env_t env x) (Select_List (id_renaming s ++ s'))) l)).
    * intro Q; generalize (f_equal (@length _) Q); rewrite length_quicksort, map_length.
      intro L; destruct l; [ | discriminate L].
      simpl in We'; rewrite Bool.Bool.andb_false_r in We'; discriminate We'.
    * intros u1 k Q.
      rewrite (interp_funterm_homogeneous _ _ _ s Group_Fine _ _ _ _ Q).
      assert (Hu1 : In u1 (u1 :: k)); [left; apply refl_equal | ].
      rewrite <- Q, <- In_quicksort, in_map_iff in Hu1.
      destruct Hu1 as [t1 [Hu1 Ht1]]; subst u1.
      apply trans_eq with (interp_funterm ((s, Group_Fine, t1 :: nil) :: env) (F_Expr fc lf)).
      -- destruct l as [ | t l]; [contradiction Ht1 | ].
         rewrite (well_formed_e_interp_grouping_expressions _ _ _ _ _ _ We' H' s Group_Fine).
         rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff, forallb_forall in We'.
         destruct We' as [[[[W1 W2] W3] W4] W5].
         rewrite forallb_forall in W2.
         assert (Wt1 := W2 _ Ht1); rewrite forallb_forall in Wt1.
         assert (_Wf := Wt1 _ H'); rewrite Oset.eq_bool_true_iff in _Wf.
         unfold env_t in _Wf; rewrite !interp_aggterm_unfold in _Wf.
         apply sym_eq; refine (trans_eq _ (trans_eq _Wf _)).
         ++ apply (interp_funterm_homogeneous _ _ _ _ _ _ _ _ _ (quicksort_1 _ _)).
         ++ apply (interp_funterm_homogeneous _ _ _ _ _ _ _ _ _ (quicksort_1 _ _)).
      -- apply interp_dot_eq_interp_funterm_eq.
         intros a Ha; unfold id_renaming; simpl.
         rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), dot_mk_tuple.
         rewrite !map_app, !map_map, Oset.find_app, map_id; [ | intros; apply refl_equal].
         rewrite Fset.mem_mk_set_app, (Fset.mem_eq_2 _ _ _ (Fset.mk_set_idem _ _)).
         rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff, forallb_forall in We'.
         destruct We' as [[[[W1 W2] W3] W4] W5].
         rewrite forallb_forall in W3.
         rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Ht1)).
         case_eq (a inS? s); intro Ka.
         ++ rewrite Bool.Bool.orb_true_l, Oset.find_map; simpl.
            ** rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Ht1)), Ka; apply refl_equal.
            ** apply Fset.mem_in_elements; assumption.
         ++ rewrite Bool.Bool.orb_false_l.
            case_eq (a inS? Fset.mk_set (A T) (map (fun x : select => fst match x with
                                                            | Select_As e a0 => (a0, e)
                                                            end) s')); 
              intro Ja; [ | apply refl_equal].
            apply False_rec.
            assert (W1f := well_formed_ag_variables_ag_env _ _ W0 (W1 _ H')).
            unfold env_t in W1f; simpl in W1f; rewrite Fset.subset_spec in W1f.
            assert (Wa := W1f a Ha); unfold default_tuple in Wa.
            rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Ka, 
               Bool.Bool.orb_false_l in Wa.
            rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff in We''.
            destruct We'' as [[[[W1' W2'] W3'] W4'] W5'].
            rewrite Fset.is_empty_spec, Fset.equal_spec in W4'.
            generalize (W4' a); 
              rewrite Fset.mem_inter, Wa, Fset.mem_union, Ka, Fset.empty_spec, Bool.Bool.andb_true_r.
            unfold lb; rewrite Fset.mem_mk_set, <- not_true_iff_false; intro Abs; apply Abs.
            simpl; rewrite <- Ja, Fset.mem_mk_set; simpl; apply f_equal; rewrite <- map_eq.
            intros [] _; apply refl_equal.
  + rewrite in_flat_map in H'.
    destruct H' as [slc [H' H'']]; destruct (in_split _ _ H') as [e1 [e2 He]]; rewrite He, !app_comm_cons.
    rewrite !interp_funterm_in_env_tail; trivial.
    * rewrite <- app_comm_cons, <- He; assumption.
    * rewrite <- app_comm_cons, <- He; assumption.
- rewrite !interp_funterm_unfold; apply f_equal; rewrite <- map_eq.
  intros a Ha; apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + unfold well_formed_ft; rewrite forallb_forall in Wf; apply Wf; assumption.
Qed.


*)
Lemma projection_sub :
  forall env t t' rho, 
    labels T t subS labels T t' -> 
    (forall a, a inS labels T t -> dot T t a = dot T t' a) ->
    (forall a e, In (Select_As _ e a) rho -> 
                 match e with 
                 | A_Expr _ (F_Dot _ b) => b inS? labels T t 
                 | _ => false 
                 end = true) ->
    projection _ (env_g _ env (Group_Fine T) (t' :: nil)) (Select_List _ (_Select_List _ rho)) =t= 
    projection _ (env_g _ env (Group_Fine T) (t :: nil)) (Select_List _ (_Select_List _ rho)).
Proof.
intros env t t' rho H1 H2 H3.
rewrite tuple_eq; split; [simpl | ].
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)),
    (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  apply Fset.equal_refl.
- unfold projection.
  intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha;
    rewrite 2 dot_mk_tuple, Ha.
  case_eq (Oset.find (OAtt T) a (_Select_List T rho)); [ | intros; apply refl_equal].
  intros e He.
  assert (Ke := Oset.find_some _ _ _ He).
  simpl in Ke; unfold pair_of_select in Ke; rewrite in_map_iff in Ke.
  destruct Ke as [[_e _a] [_Ke Ke]]; injection _Ke; clear _Ke; do 2 intro; subst _a _e.
  assert (Ka := H3 _ _ Ke).
  destruct e; try discriminate Ka.
  destruct f as [ | b | ]; try discriminate Ka.
  simpl; rewrite Ka.
  rewrite Fset.subset_spec in H1.
  rewrite (H1 _ Ka); apply sym_eq; apply H2; assumption.
Qed.

(*
Definition equiv_abstract_env_slice (e1 e2 : (Fset.set (A T) * group_by)) := 
  match e1, e2 with
    | (sa1, g1), (sa2, g2) => 
      sa1 =S= sa2 /\ g1 = g2 
  end.

Definition equiv_abstract_env := Forall2 equiv_abstract_env_slice.

Lemma equiv_abstract_env_refl : forall e, equiv_abstract_env e e.
Proof.
intro e; unfold equiv_abstract_env; induction e as [ | [sa g] e]; simpl; trivial.
constructor 2; [simpl | apply IHe].
split; [apply Fset.equal_refl | apply refl_equal].
Qed.



Definition equiv_env_slice_strong (e1 e2 : (Fset.set (A T) * group_by * (list (tuple T)))) := 
  match e1, e2 with
    | (sa1, g1, x1), (sa2, g2, x2) => 
      sa1 =S= sa2 /\ g1 = g2 /\ 
      (map (fun t => mk_tuple T sa1 (dot T t)) x1) =PE= 
      (map (fun t => mk_tuple T sa2 (dot T t)) x2) 
  end.

Definition equiv_env_strong e1 e2 := Forall2 equiv_env_slice_strong e1 e2.

Fixpoint att_of_env (e : list (Fset.set (A T) * group_by * (list (tuple T))))  :=
  match e with
  | nil => Fset.empty (A T)
  | (sa, _, _) :: e => sa unionS (att_of_env e)
  end.

Fixpoint well_formed_env_strong (e : list (Fset.set (A T) * group_by * (list (tuple T)))) :=
  match e with
  | nil => True
  | (sa, g, x) :: e => 
    x <> nil /\ (forall t, In t x -> sa subS labels T t) /\ well_formed_env_strong e
  end.
*)

Definition make_groups env (s : list (tuple T)) gby := 
  match gby with
    | Group_By _ g =>
      map snd (partition (A := tuple T) (mk_olists (OVal T))
                         (fun t => map (fun f => interp_aggterm _ (env_t _ env t) f) g) s)
    | Group_Fine _ => List.map (fun x => x :: nil) s  
  end.

Lemma make_groups_eq :
  forall env1 env2 g b1 b2, equiv_env T env1 env2 -> b1 =PE= b2 -> 
     forall l, Oeset.nb_occ (OLTuple T) l (make_groups env1 b1 g) = 
               Oeset.nb_occ (OLTuple T) l (make_groups env2 b2 g).
Proof.
intros env1 env2 [g | ] b1 b2 He Hb l.
- simpl; apply Oeset.permut_nb_occ.
  refine (_permut_map _ _ _ _ (partition_eq _ (OA := OTuple T) _ _ _ _)).
  + intros [a1 a2] [c1 c2] _ _; simpl.
    case (comparelA (Oset.compare (OVal T)) a1 c1); try discriminate.
    exact (fun h => h).
  + intros t Ht t' H; rewrite <- map_eq.
    intros f Hf; apply interp_aggterm_eq; env_tac.
  + assumption.
- apply (Oeset.nb_occ_map_eq_3 (OTuple T)).
  + intros x1 x2 Hx1 Hx2 Hx; simpl; unfold compare_OLA; simpl.
    rewrite Hx; trivial.
  + intro x; apply Oeset.permut_nb_occ; assumption.
Qed.

Lemma make_groups_eq_bag :
  forall env1 env2 g b1 b2, 
    equiv_env T env1 env2 -> b1 =BE= b2 -> 
    forall l, 
      Oeset.nb_occ 
        (OLTuple T) l (make_groups env1 (Febag.elements (Fecol.CBag (CTuple T)) b1) g) = 
      Oeset.nb_occ (OLTuple T) l (make_groups env2 (Febag.elements _ b2) g).
Proof.
intros; apply make_groups_eq; [assumption | ].
apply Oeset.nb_occ_permut; intro t.
rewrite <- !Febag.nb_occ_elements; apply Febag.nb_occ_equal; assumption.
Qed.

Definition N_join_bag ll :=
  Febag.mk_bag (Fecol.CBag (CTuple T)) 
               ((N_join_list _ (join_tuple T) (empty_tuple T)) (map (Febag.elements (Fecol.CBag (CTuple T))) ll)).

Lemma N_join_bag_unfold :
  forall ll, N_join_bag ll =
             Febag.mk_bag 
               (Fecol.CBag (CTuple T)) 
               ((N_join_list _ (join_tuple T) (empty_tuple T)) 
                  (map (Febag.elements (Fecol.CBag (CTuple T))) ll)).
Proof.
intro ll; apply refl_equal.
Qed.

Lemma N_join_bag_1 :
  forall t b, Febag.nb_occ _ t (N_join_bag (b :: nil)) = Febag.nb_occ _ t b.
Proof.
intros t b; unfold N_join_bag; rewrite Febag.nb_occ_mk_bag.
rewrite (map_unfold _ (_ :: _)), (map_unfold _ nil), Febag.nb_occ_elements.
apply Oeset.permut_nb_occ; apply Oeset.permut_refl_alt; apply N_join_list_1.
intro; apply join_tuple_empty_2.
Qed.

End Sec.




