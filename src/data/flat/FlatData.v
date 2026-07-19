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
              apply _permut_app; [ | apply aggterm_permut_refl].
              eapply aggterm_permut_trans.
              + apply _permut_swapp; apply aggterm_permut_refl.
              + rewrite <- ass_app; apply aggterm_permut_refl.
            - apply is_built_upon_ag_permut; simpl.
              rewrite !flat_map_app; simpl.
              rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)), !ass_app.
              apply _permut_app; [ | apply aggterm_permut_refl].
              rewrite <- ass_app; apply _permut_swapp; apply aggterm_permut_refl.
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
  rewrite extract_funterms_app, extract_funterms_A_Expr, funterm_mem_app,
    Bool.Bool.orb_true_iff.
  left; rewrite funterm_mem_true_iff, in_map_iff.
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
  unfold select_list_sort, select_list_outputs, id_renaming;
    rewrite map_app, map_map, map_id; [ | intros; trivial].
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
