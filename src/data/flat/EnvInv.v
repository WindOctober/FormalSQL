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
Import Tuple.

Section Sec.

Hypothesis T : Tuple.Rcd.

Notation predicate := (Tuple.predicate T).
Notation symb := (Tuple.symbol T).
Notation aggregate := (Tuple.aggregate T).
Notation OPredicate := (Tuple.OPred T).
Notation OSymb := (Tuple.OSymb T).
Notation OAggregate := (Tuple.OAgg T).

Import Tuple.
Notation value := (value T).
Notation attribute := (attribute T).
Notation tuple := (tuple T).
Arguments default_tuple {T}.
Arguments funterm {T}.
Arguments aggterm {T}.
Arguments Select_Star {T}.
Arguments Select_As {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_Fine {T}.
Arguments Group_By {T}.
Arguments F_Dot {T}.
Arguments A_Expr {T}.
Arguments F_Expr {T}.
Arguments A_agg {T}.
(* Arguments Sql_True {T}. *)
(* Arguments Sql_Pred {T}. *)
(* Arguments Sql_Quant {T}. *)
(* Arguments Sql_In {T dom}. *)
(* Arguments Sql_Exists {T}. *)
(* Arguments join_tuple {T}. *)
(* Arguments default_tuple {T}. *)
(* Arguments join_compatible_tuple {T}. *)
(* Arguments mk_tuple {r}. *)
Arguments interp_funterm {T}.
Arguments projection {T}.
Arguments env_t {T}.
Arguments env_slice {T}.
Arguments groups_of_env_slice {T}.
Arguments id_renaming {T}.
Arguments extract_funterms {T}.
Arguments well_formed_e {T}.
Arguments find_eval_env {T}.
Arguments find_eval_env_unfold {T}.
Arguments is_a_suitable_env {T}.
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Lemma interp_funterm_in_env_tail : 
   forall (env1 : list (_ * group_by T * _)) slc env2 f,
     well_formed_e (env1 ++ slc :: env2) = true ->
     In (A_Expr f) (groups_of_env_slice slc) ->
    interp_funterm (env1 ++ slc :: env2) f = interp_funterm (slc :: env2) f.
Proof.
intros env1; induction env1 as [ | [[sa1 g1] l1] env1]; 
  intros slc env2 f We H; [apply refl_equal | ].
rewrite <- (IHenv1 slc env2); 
  [ | simpl in We; rewrite Bool.Bool.andb_true_iff in We; apply (proj2 We) | assumption].
clear IHenv1.
destruct slc as [[sa g] l]; simpl in H.
assert (Hf : variables_ft T f
       subS Fset.Union (A T)
              (map (fun x : env_slice => let (y, _) := x in let (s, _) := y in s)
                 ((sa, g, l) :: env2))).
{
  destruct g as [g | ].
  - apply (well_formed_ag_variables_ag_env_alt T
                   (sa, Group_By g, l) env2 (A_Expr f) (well_formed_e_tail _ _ _ We) H).
  - rewrite in_map_iff in H.
    destruct H as [a [_H H]]; injection _H; intro; subst f; simpl.
    rewrite Fset.subset_spec; 
      intros b Hb; rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in Hb; subst b.
    rewrite Fset.mem_union, (Fset.in_elements_mem _ _ _ H); apply refl_equal.
}
apply interp_dot_eq_interp_funterm_eq.
intros a Ha; rewrite Fset.subset_spec in Hf.
assert (Ka := Hf _ Ha); simpl.
case_eq (quicksort (OTuple T) l1); [intro Q; apply refl_equal | ].
intros t1 k1 Q; case_eq (a inS? labels T t1); intro Ja; [ | apply refl_equal].
assert (Ht1 : In t1 l1).
{
  rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
}
simpl in We; rewrite !Bool.Bool.andb_true_iff, forallb_forall in We.
destruct We as [[[W1 W2] W3] W4].
rewrite (Fset.mem_eq_2 _ _ _ (W2 _ Ht1)) in Ja.
rewrite Fset.is_empty_spec, Fset.equal_spec in W3; assert (W3a := W3 a).
unfold env_slice in *.
rewrite Fset.empty_spec, Fset.mem_inter, Ja, map_app, Fset.mem_Union_app, Ka in W3a.
rewrite Bool.Bool.orb_true_r in W3a; discriminate W3a.
Qed.

Lemma interp_dot_eq_env_g_strong :
  forall env s s' l,
    let lb := map (fun x => match x with Select_As _ b => b end) s' in
    let g := map (fun x => match x with Select_As ag _ => ag end) s' in
    well_formed_e ((s, Group_By g, l) :: env) = true ->
    well_formed_e ((s unionS Fset.mk_set (A T) lb, Group_By (map (fun b => A_Expr (F_Dot b)) lb),
     map (fun x => projection (env_t env x) (Select_List (_Select_List (id_renaming s ++ s')))) l)
     :: env) = true ->
    forall a,
    well_formed_ft T ((s, Group_By g, l) :: env) (F_Dot a) = true ->
    interp_dot T ((s, Group_By g, l) :: env) a =
    interp_dot T
    ((s unionS Fset.mk_set (A T) lb, Group_By (map (fun b => A_Expr (F_Dot b)) lb),
     map (fun x => projection (env_t env x) (Select_List (_Select_List (id_renaming s ++ s')))) l)
     :: env) a.
Proof.
intros env s s' l lb g We' We'' a Ha; unfold well_formed_ft in Ha; simpl in Ha.
rewrite Oset.mem_bool_true_iff, extract_funterms_app in Ha.
simpl in We'; rewrite !Bool.Bool.andb_true_iff, forallb_forall in We'.
destruct We' as [[[[W1 W2] W3] W4] W5].
simpl in We''; rewrite !Bool.Bool.andb_true_iff, !forallb_forall in We''.
destruct We'' as [[[[W1' W2'] W3'] W4'] W5'].  
rewrite !interp_dot_unfold.
assert (L := length_quicksort (OTuple T) l).
case_eq (quicksort (OTuple T) l); 
  [intro Q; rewrite Q in L; destruct l; [discriminate W2 | discriminate L] | ].
intros t1 k Q.
assert (Ht1 : In t1 (t1 :: k)); [left; apply refl_equal | ].
rewrite <- Q, <- In_quicksort in Ht1.
assert (L' := length_quicksort (OTuple T) 
                (map 
                   (fun x => projection (env_t env x) 
                               (Select_List (_Select_List (id_renaming s ++ s')))) l)).
rewrite map_length, <- L, Q in L'.
case_eq (quicksort 
           (OTuple T)
           (map (fun x => projection 
                            (env_t env x) (Select_List (_Select_List (id_renaming s ++ s')))) l));
  [intro Q'; rewrite Q' in L'; discriminate L' | ].
intros v1 k' Q'.
assert (Hv1 : In v1 (v1 :: k')); [left; apply refl_equal | ].
rewrite <- Q', <- In_quicksort, in_map_iff in Hv1.
destruct Hv1 as [u1 [_Hv1 Hv1]]; subst v1.
rewrite (Fset.mem_eq_2 _ _ _ (labels_projection _ _ _)).   
rewrite forallb_forall in W3.
assert (Wt1 := W3 _ Ht1); rewrite (Fset.mem_eq_2 _ _ _ Wt1).
unfold id_renaming at 1; rewrite !map_app, !map_map, map_id; [ | intros; apply refl_equal].
rewrite Fset.mem_mk_set, Oset.mem_bool_app, <- Fset.mem_elements.
destruct l as [ | v1 l]; [discriminate W2 | ].
rewrite forallb_forall in W2.
assert (_W2 := W2 _ Ht1).
assert (__W2 := W2 _ Hv1).
rewrite forallb_forall in _W2, __W2.
case_eq (a inS? s); intro Ka.
- rewrite Bool.Bool.orb_true_l.
  unfold projection, id_renaming, sort_of_select_list; simpl;
    rewrite dot_mk_tuple, !map_app, !map_map.
  rewrite map_id; [ | intros; apply refl_equal].
  rewrite Fset.mem_mk_set, Oset.mem_bool_app, <- Fset.mem_elements, Ka, Bool.Bool.orb_true_l.
  unfold pair_of_select; simpl.
  rewrite Oset.find_app, Oset.find_map; [ | apply Fset.mem_in_elements; assumption]; simpl.
  rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Hv1)), Ka.
  rewrite <- extract_funterms_app, in_extract_funterms, <- (Oset.mem_bool_true_iff (OAggT T)), 
     Oset.mem_bool_app in Ha.
  case_eq (Oset.mem_bool (OAggT T) (A_Expr (F_Dot a)) g); intro Ha'.
  + rewrite Oset.mem_bool_true_iff in Ha'.
    generalize (_W2 _ Ha'); clear _W2; 
      intro _W2; rewrite Oset.eq_bool_true_iff in _W2; simpl in _W2.
    rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Ht1)), Ka in _W2; rewrite _W2.
    generalize (__W2 _ Ha'); clear __W2; 
      intro __W2; rewrite Oset.eq_bool_true_iff in __W2; simpl in __W2.
    rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Hv1)), Ka in __W2; rewrite __W2.
    apply refl_equal.
  + rewrite Ha', Bool.Bool.orb_false_l, Oset.mem_bool_true_iff in Ha.
    rewrite Fset.is_empty_spec, Fset.equal_spec in W4.
    assert (Ja := W4 a); rewrite Fset.mem_inter, Ka, Bool.Bool.andb_true_l, Fset.empty_spec in Ja.
    rewrite in_flat_map in Ha.
    destruct Ha as [[[sa1 g1] l1] [H1 H2]].
    destruct (in_split _ _ H1) as [e1 [e2 He]]; rewrite He in W5.
    assert (W' := well_formed_e_tail _ _ _ W5).
    assert (Aux := well_formed_ag_variables_ag_env_alt _ _ _ _ W' H2).
    rewrite Fset.subset_spec in Aux; simpl in Aux.
    assert (Abs : a inS Fset.Union (A T) 
                    (map (fun slc : env_slice => let (y, _) := slc in let (sa, _) := y in sa) 
                         env)).
    {
      rewrite He, map_app, Fset.mem_Union_app, Bool.Bool.orb_true_iff; right.
      apply Aux; rewrite Fset.singleton_spec, Oset.eq_bool_refl; apply refl_equal.
    }    
    unfold env_slice in *; rewrite Abs in Ja; discriminate Ja.
- rewrite Bool.Bool.orb_false_l.
  case_eq (Oset.mem_bool (OAtt T) a (map (fun x : select T => match x with
                                                       | Select_As _ a1 => a1
                                                            end) s')); 
    intro Ja; [ | apply refl_equal].
  rewrite <- extract_funterms_app, in_extract_funterms, <- (Oset.mem_bool_true_iff (OAggT T)), 
     Oset.mem_bool_app in Ha.
  case_eq (Oset.mem_bool (OAggT T) (A_Expr (F_Dot a)) g); intro Ha'.
  + rewrite Oset.mem_bool_true_iff in Ha'.
    apply False_rec; generalize (W1 _ Ha'); simpl; unfold well_formed_ft; simpl.
    rewrite Oset.mem_bool_true_iff, in_extract_funterms; intro H.
    destruct (in_app_or _ _ _ H) as [H' | H'].
    * rewrite in_map_iff in H'.
      destruct H' as [_a [_H' H']]; injection _H'; intro; subst _a.
      unfold default_tuple in H'; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in H'.
      rewrite <- (Oset.mem_bool_true_iff (OAtt T)), <- Fset.mem_elements, Ka in H'.
      discriminate H'.
    * rewrite in_flat_map in H'.
      destruct H' as [[[sa1 g1] l1] [H1 H2]].
      destruct (in_split _ _ H1) as [e1 [e2 He]]; rewrite He in W5'.
      assert (W' := well_formed_e_tail _ _ _ W5').
      assert (Aux := well_formed_ag_variables_ag_env_alt _ _ _ _ W' H2).
      rewrite Fset.subset_spec in Aux; simpl in Aux.
      assert (Abs : a inS Fset.Union 
                      (A T) (map (fun slc : env_slice => 
                                    let (y, _) := slc in let (sa, _) := y in sa) env)).
      {
        rewrite He, map_app, Fset.mem_Union_app, Bool.Bool.orb_true_iff; right.
        apply Aux; rewrite Fset.singleton_spec, Oset.eq_bool_refl; apply refl_equal.
      }    
      rewrite Fset.is_empty_spec, Fset.equal_spec in W4'.
      generalize (W4' a).
      unfold env_slice in *; rewrite Fset.mem_inter, Abs, Fset.empty_spec, Bool.andb_true_r.
      rewrite Fset.mem_union, Ka, Bool.Bool.orb_false_l.
      assert (Abs' : a inS Fset.mk_set (A T) lb).
      {
        unfold lb; rewrite <- Ja, Fset.mem_mk_set.
        apply f_equal; rewrite <- map_eq; intros [] _; apply refl_equal.
      }
      rewrite Abs'; discriminate.
  + rewrite Ha', Bool.Bool.orb_false_l in Ha.
    rewrite Oset.mem_bool_true_iff, in_flat_map in Ha.
    destruct Ha as [[[sa1 g1] l1] [H1 H2]].
    destruct (in_split _ _ H1) as [e1 [e2 He]]; rewrite He in W5'.
    assert (W' := well_formed_e_tail _ _ _ W5').
    assert (Aux := well_formed_ag_variables_ag_env_alt _ _ _ _ W' H2).
    rewrite Fset.subset_spec in Aux; simpl in Aux.
    assert (Abs : a inS Fset.Union 
                    (A T) (map (fun slc : env_slice => 
                                  let (y, _) := slc in let (sa, _) := y in sa) env)).
    {
      rewrite He, map_app, Fset.mem_Union_app, Bool.Bool.orb_true_iff; right.
      apply Aux; rewrite Fset.singleton_spec, Oset.eq_bool_refl; apply refl_equal.
    }    
    rewrite Fset.is_empty_spec, Fset.equal_spec in W4'.
    generalize (W4' a).
    unfold env_slice in *; rewrite Fset.mem_inter, Abs, Fset.empty_spec, Bool.andb_true_r.
    rewrite Fset.mem_union, Ka, Bool.Bool.orb_false_l.
    assert (Abs' : a inS Fset.mk_set (A T) lb).
    {
      unfold lb; rewrite <- Ja, Fset.mem_mk_set.
      apply f_equal; rewrite <- map_eq; intros [] _; apply refl_equal.
    }
    rewrite Abs'; discriminate.
Qed.

Lemma well_formed_e_interp_grouping_expressions :
  forall s g t l (env : list (_ * group_by T * _)) f, 
    well_formed_e ((s, g, t :: l) :: env) = true ->
    In (A_Expr f) (groups_of_env_slice (s, g, t :: l)) ->
    forall s' g',
    interp_funterm ((s, g, t :: l) :: env) f = interp_funterm ((s', g', t :: nil) :: env) f.
Proof.
intros s g t l env f W H s' g'.
rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff in W.
destruct W as [[[W1 W2] W3] W4].
case_eq (quicksort (OTuple T) (t :: l)).
- intro Q; generalize (f_equal (@length _) Q).
  rewrite length_quicksort; intro Abs; discriminate Abs.
- intros u1 k Q.
  apply trans_eq with (interp_funterm ((s', g', u1 :: nil) :: env) f).
  + apply (interp_funterm_homogeneous T s g (t :: l) s' g' u1 k nil env f Q).
  + destruct g as [g | ]; simpl in H.
    * rewrite Bool.Bool.andb_true_iff, !forallb_forall in W1.
      destruct W1 as [W0 W1].
      assert  (Hu1 : In u1 (u1 :: k)); [left; apply refl_equal | ].
      rewrite <- Q, <- In_quicksort in Hu1.
      assert (Wu1 := W1 _ Hu1); rewrite forallb_forall in Wu1.
      assert (Wf := Wu1 _ H); rewrite Oset.eq_bool_true_iff in Wf; simpl in Wf.
      refine (eq_trans (eq_trans _ Wf) _); unfold env_t.
      -- assert (Q1 := quicksort_1 (OTuple T) u1).
         apply (interp_funterm_homogeneous 
                  T s' g' (u1 :: nil) (labels T u1) Group_Fine u1 nil nil env f Q1).
      -- assert (Q1 := quicksort_1 (OTuple T) t).
         apply (interp_funterm_homogeneous 
                  T (labels T t) Group_Fine (t :: nil) s' g' t nil nil env f Q1).
    * destruct l; [ | discriminate W1].
      rewrite quicksort_1 in Q; injection Q; do 2 intro; subst.
      apply refl_equal.
Qed.


Lemma interp_funterm_eq_env_g_strong :
  forall env s s' l,
    let lb := map (fun x => match x with Select_As _ b => b end) s' in
    let g := map (fun x => match x with Select_As ag _ => ag end) s' in
    well_formed_e ((s, Group_By g, l) :: env) = true ->
    well_formed_e ((s unionS Fset.mk_set (A T) lb, 
                    Group_By (map (fun b => A_Expr (F_Dot b)) lb),
                    map (fun x => 
                           projection (env_t env x) 
                                      (Select_List (_Select_List (id_renaming s ++ s')))) l)
                     :: env) = true ->
    forall e,
    well_formed_ft T ((s, Group_By g, l) :: env) e = true ->
    interp_funterm ((s, Group_By g, l) :: env) e =
    interp_funterm
    ((s unionS Fset.mk_set (A T) lb, Group_By (map (fun b => A_Expr (F_Dot b)) lb),
     map (fun x => projection (env_t env x) (Select_List (_Select_List (id_renaming s ++ s')))) l)
     :: env) e.
Proof.
intros env s s' l lb g We' We'' e.
case_eq (quicksort (OTuple T) l);
  [intro Q; apply False_rec; assert (L := length_quicksort (OTuple T) l); rewrite Q in L;
   destruct l; [simpl in We'; rewrite Bool.Bool.andb_false_r in We'; discriminate We' 
               | discriminate L] | ].
intros _t _k Q.
assert (W0 := well_formed_e_proj_env_t _ _ _ _ _ We' _ _ Q).
set (n := size_funterm T e).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert e Hn; induction n as [ | n]; intros f Hn Wf; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | apply interp_dot_eq_env_g_strong; trivial | ].
unfold well_formed_ft in Wf; simpl in Wf.
case_eq (Oset.mem_bool (OFun T) (F_Expr fc lf) (extract_funterms (g ++ flat_map groups_of_env_slice env)));
  intro H; [ | rewrite H, Bool.Bool.orb_false_l in Wf].
- rewrite Oset.mem_bool_true_iff, in_extract_funterms in H.
  destruct (in_app_or _ _ _ H) as [H' | H'].
  + case_eq (quicksort 
               (OTuple T) 
               (map (fun x => projection (env_t env x) 
                                (Select_List (_Select_List (id_renaming s ++ s')))) l)).
    * intro Q'; generalize (f_equal (@length _) Q'); rewrite length_quicksort, map_length.
      intro L; destruct l; [ | discriminate L].
      simpl in We'; rewrite Bool.Bool.andb_false_r in We'; discriminate We'.
    * intros u1 k1 Q'.
      rewrite (interp_funterm_homogeneous_nil _ _ _ _ (labels T _t) Group_Fine _ _ _ _ Q).
      rewrite (interp_funterm_homogeneous_nil
                 _ _ _ _ (s unionS Fset.mk_set (A T) lb) Group_Fine _ _ _ _ Q').
      assert (Hu1 : In u1 (u1 :: k1)); [left; apply refl_equal | ].
      rewrite <- Q', <- In_quicksort, in_map_iff in Hu1.
      destruct Hu1 as [t1 [Hu1 Ht1]]; subst u1.
      apply trans_eq with 
          (interp_funterm ((labels T t1, Group_Fine, t1 :: nil) :: env) (F_Expr fc lf)).
      -- destruct l as [ | t l]; [contradiction Ht1 | ].
         rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff, !forallb_forall in We'.
         destruct We' as [[[[W1 W2] W3] W4] W5].
         assert (_Ht : In _t (t :: l)).
         {
           rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
         }
         assert (_Wt := W2 _ _Ht); rewrite forallb_forall in _Wt.
         assert (_Wf := _Wt _ H'); rewrite Oset.eq_bool_true_iff in _Wf.
         unfold env_t in _Wf; rewrite !interp_aggterm_unfold in _Wf; rewrite _Wf.
         assert (Wt1 := W2 _ Ht1); rewrite forallb_forall in Wt1.
         assert (Wf1 := Wt1 _ H'); rewrite Oset.eq_bool_true_iff in Wf1.
         apply (sym_eq Wf1).
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
         ++ rewrite !Bool.Bool.orb_true_l; unfold pair_of_select; simpl.
            rewrite Oset.find_map; simpl.
            ** rewrite (Fset.mem_eq_2 _ _ _ (W3 _ Ht1)), Ka; apply refl_equal.
            ** apply Fset.mem_in_elements; assumption.
         ++ rewrite Bool.Bool.orb_false_l.
            case_eq (a inS? Fset.mk_set (A T) (map (fun x : select T => match x with
                                                     | Select_As _ a1 => a1
                                                     end) s')); 
              intro Ja; [ | apply refl_equal].
            apply False_rec.
            assert (_Wt : labels T _t =S= s).
            {
              apply W3; rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
            }
            assert (Wf' : well_formed_ag T (env_t env _t) (A_Expr (F_Expr fc lf)) = true).
            {
              rewrite <- (W1 _ H'); apply well_formed_ag_eq; 
                constructor 2; [ | apply equiv_env_weak_equiv_env; apply equiv_env_refl].
              simpl; split; [ | apply refl_equal].
              unfold default_tuple; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _));
              assumption.
            }
            assert (W1f := well_formed_ag_variables_ag_env _ _  (A_Expr (F_Expr fc lf)) W0 Wf').
            unfold env_t in W1f; simpl in W1f; rewrite Fset.subset_spec in W1f.
            assert (Wa := W1f a Ha); unfold default_tuple in Wa.
            rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ _Wt), Ka, Bool.Bool.orb_false_l in Wa. 
            rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff in We''.
            destruct We'' as [[[[W1' W2'] W3'] W4'] W5'].
            rewrite Fset.is_empty_spec, Fset.equal_spec in W4'.
            generalize (W4' a); 
              rewrite Fset.mem_inter, Wa, Fset.mem_union, Ka, Fset.empty_spec, Bool.Bool.andb_true_r.
            unfold lb; rewrite Fset.mem_mk_set, <- not_true_iff_false; intro Abs; apply Abs.
            simpl; rewrite <- Ja, Fset.mem_mk_set; simpl; apply f_equal; rewrite <- map_eq.
            intros [] _; apply refl_equal.
  + rewrite in_flat_map in H'.
    destruct H' as [slc [H' H'']]; destruct (in_split _ _ H') as [e1 [e2 He]]; 
      rewrite He, !app_comm_cons.
    rewrite !interp_funterm_in_env_tail; trivial.
    * rewrite <- app_comm_cons; subst env; assumption.
    * rewrite <- app_comm_cons; subst env; assumption.
- rewrite !interp_funterm_unfold; apply f_equal; rewrite <- map_eq.
  intros a Ha; apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + unfold well_formed_ft; rewrite forallb_forall in Wf; apply Wf; assumption.
Qed.

Lemma interp_funterm_eq_env_t_strong :
  forall env1 env2 s1 s2 t e,
    well_formed_e (env1 ++ env_t env2 t) = true ->
    labels T t =S= (s1 unionS s2) ->
    (forall a, a inS (s2 interS (variables_ft T e)) -> a inS s1) ->
    interp_funterm (env1 ++ env_t env2 t) e =
    interp_funterm (env1 ++ env_t env2 (mk_tuple T s1 (dot T t))) e.
Proof.
intros env1 env2 s1 s2 t f.
set (n := size_funterm T f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn We Ht Hf; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | | ]; simpl.
- assert (Hfa : a inS s2 -> a inS s1).
  {
    intro Ha; apply Hf.
    rewrite Fset.mem_inter, Ha; simpl.
    rewrite Fset.singleton_spec, Oset.eq_bool_refl; apply refl_equal.
  }
  clear Hf IHn.
  induction env1 as [ | [[sa1 g1] l1] env1]; simpl.
  + rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), (Fset.mem_eq_2 _ _ _ Ht), 
      Fset.mem_union, dot_mk_tuple.
    case_eq (a inS? s1); intro Ha; simpl; [apply refl_equal | ].
    case_eq (a inS? s2); intro Ka; [ | apply refl_equal].
    rewrite Hfa in Ha; [discriminate Ha | assumption].
  + simpl in We; rewrite !Bool.Bool.andb_true_iff in We.
    destruct We as [[[Wg1 Wl1] Wsa1] We]; rewrite Fset.is_empty_spec, Fset.equal_spec in Wsa1.
    case_eq (quicksort (OTuple T) l1); [intro Q | intros t1 q1 Q];
      [apply IHenv1; apply We | ].
    case_eq (a inS? labels T t1); intro Ha1; [apply refl_equal | ].
    apply IHenv1; apply We.
- apply f_equal; rewrite <- map_eq.
  intros a Ha; apply IHn.
  + simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + assumption.
  + assumption.
  + intros e He; 
      rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in He.
    apply Hf; rewrite Fset.mem_inter, (proj1 He), Bool.Bool.andb_true_l; simpl.
    destruct He as [_ He].
    rewrite Fset.mem_Union; eexists; split; 
      [rewrite in_map_iff; eexists; split; [ | apply Ha]; apply refl_equal | apply He].
Qed.

Lemma interp_aggterm_eq_env_g_strong :
  (forall (a : aggregate T), 
      forall l1 l2, Oset.permut (OVal T) l1 l2 -> 
                    interp_aggregate T a l1 = interp_aggregate T a l2) -> 
  forall env s s' l,
    let lb := map (fun x => match x with Select_As _ b => b end) s' in
    let g := map (fun x => match x with Select_As ag _ => ag end) s' in
    well_formed_e ((s, Group_By g, l) :: env) = true ->
    well_formed_e ((s unionS Fset.mk_set (A T) lb, 
                      Group_By (map (fun b => A_Expr (F_Dot b)) lb),
                      map (fun x => 
                             projection (env_t env x) 
                                        (Select_List (_Select_List (id_renaming s ++ s')))) l)
     :: env) = true ->
    forall e, 
    well_formed_ag T ((s, Group_By g, l) :: env) e = true ->
    interp_aggterm T ((s, Group_By g, l) :: env) e =
    interp_aggterm T
    ((s unionS Fset.mk_set (A T) lb, 
      Group_By (map (fun b => A_Expr (F_Dot b)) lb),
      map (fun x => projection (env_t env x) (Select_List (_Select_List (id_renaming s ++ s')))) l)
     :: env) e.
Proof.
intros Haggregate env s s' l lb g We' We'' e.
set (n := size_aggterm T e).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert e Hn; induction n as [ | n]; 
  intros e Hn We; [destruct e; inversion Hn | ].
destruct e as [f | a f | f la].
- rewrite !interp_aggterm_unfold; apply interp_funterm_eq_env_g_strong; trivial.
- case_eq (Fset.is_empty (A T) (variables_ft T f)); intro Hf.
  + rewrite !interp_aggterm_unfold; rewrite Hf; unfold unfold_env_slice; rewrite ! map_map.
    apply Haggregate.
    * apply Oset.permut_trans with 
          (map (fun x => interp_funterm ((s, Group_Fine, x :: nil) :: env) f) l).
      -- apply _permut_map with (fun x y => Oeset.compare (OTuple T) x y = Eq).
         ++ intros; subst; rewrite Oset.compare_eq_iff; apply interp_funterm_eq.
            constructor 2; [ | apply equiv_env_refl].
            simpl; repeat split; [apply Fset.equal_refl | ].
            rewrite compare_list_t; unfold compare_OLA; simpl.
            rewrite H1; apply refl_equal.
         ++ apply Oeset.permut_sym; apply quick_permut.
      -- apply Oset.permut_trans with
             (map
                (fun x =>
                   interp_funterm
                     ((s unionS Fset.mk_set (A T) lb, Group_Fine
                     (* Group_By (map (fun b => A_Expr (F_Dot b)) lb)*), x :: nil) :: env) f)
                (map (fun x => 
                        projection (env_t env x) 
                                   (Select_List (_Select_List (id_renaming s ++ s')))) l)).
         ++ rewrite map_map; apply Oset.permut_refl_alt2; rewrite <- map_eq.
            intros t Ht; apply interp_dot_eq_interp_funterm_eq.
            intros b Hb; rewrite Fset.is_empty_spec, Fset.equal_spec in Hf.
            rewrite Hf, Fset.empty_spec in Hb; discriminate Hb.
         ++ apply _permut_map with (fun x y => Oeset.compare (OTuple T) x y = Eq).
            ** intros; subst; rewrite Oset.compare_eq_iff; apply interp_funterm_eq.
               constructor 2; [ | apply equiv_env_refl].
               simpl; repeat split; [apply Fset.equal_refl | ].
               rewrite compare_list_t; unfold compare_OLA; simpl.
               rewrite H1; apply refl_equal.
            ** apply quick_permut.
  + simpl in We; rewrite Hf, Bool.Bool.orb_false_l in We.
    case_eq (find_eval_env env (A_agg a f)); 
      [intros e Kf;
       rewrite !interp_aggterm_unfold, Hf, !(find_eval_env_unfold (T := T) (_ :: _)), Kf; 
       apply refl_equal 
      | intro Kf; rewrite Kf in We].
    case_eq (is_a_suitable_env s env (A_agg a f)); intro Jf; 
      [ | rewrite Jf in We; discriminate We].
    assert (Aux : is_a_suitable_env (s unionS Fset.mk_set (A T) lb) env (A_agg a f) = true).
    {
      unfold is_a_suitable_env in *; simpl in Jf; simpl.
      rewrite Oset.mem_bool_app in Jf.
      case_eq (Oset.mem_bool (OAggT T) (A_agg a f) (map (fun a => A_Expr (F_Dot a)) ({{{s}}})));
      intro Lf.
      - rewrite Oset.mem_bool_true_iff, in_map_iff in Lf.      
        destruct Lf as [_a [Lf _]]; discriminate Lf.
      - rewrite Lf, Bool.Bool.orb_false_l in Jf.
        case_eq (Oset.mem_bool (OAggT T) (A_agg a f) (flat_map groups_of_env_slice env)); intro Mf.
        + rewrite Oset.mem_bool_app, Mf, Bool.Bool.orb_true_r; apply refl_equal.
        + rewrite Mf, Bool.Bool.orb_false_l in Jf.
          rewrite Bool.Bool.orb_true_iff; right.
          revert Jf; apply is_built_upon_ft_incl; intros x Hx; rewrite in_extract_funterms in Hx.
          rewrite in_extract_funterms.
          apply in_or_app; destruct (in_app_or _ _ _ Hx) as [Kx | Kx]; [left | right; assumption].
          rewrite in_map_iff in Kx.
          destruct Kx as [b [Kx Hb]].
          rewrite in_map_iff; exists b; split; [assumption | ].
          apply Fset.mem_in_elements; rewrite Fset.mem_union, Bool.Bool.orb_true_iff.
          left; apply Fset.in_elements_mem; assumption.
    }
    unfold is_a_suitable_env in Jf; simpl in Jf.
    rewrite Oset.mem_bool_app in Jf.
    case_eq (Oset.mem_bool (OAggT T) (A_agg a f) (map (fun a  => A_Expr (F_Dot a)) ({{{s}}})));
      intro Lf; [ | rewrite Lf, Bool.Bool.orb_false_l in Jf].
    * rewrite Oset.mem_bool_true_iff, in_map_iff in Lf.
      destruct Lf as [_b [Lf _]]; discriminate Lf.
    * case_eq (Oset.mem_bool (OAggT T) (A_agg a f) (flat_map groups_of_env_slice env)); intro Mf.
      -- rewrite Oset.mem_bool_true_iff, in_flat_map in Mf.
         destruct Mf as [[[sa1 g1] l1] [Hx Mf]].
         destruct (in_split _ _ Hx) as [e1 [e2 He]].
         simpl in We'; rewrite Bool.Bool.andb_true_iff in We'; destruct We' as [We' W5].
         rewrite He in Kf, W5; apply False_rec.
         revert Kf Mf W5.
         clear Hx He.
         revert e1; induction e1 as [ | [[sa2 g2] l2] e1]; simpl.
         ++ case_eq (find_eval_env e2 (A_agg a f)); [intros; discriminate | ].
            intro H2; case_eq (is_a_suitable_env sa1 e2 (A_agg a f)); [intros; discriminate | ].
            intros H3 _.
            destruct g1 as [g1 | ]; [ | rewrite in_map_iff; intros [b1 [H4 _]]; discriminate H4].
            intros H4 H5; rewrite !Bool.Bool.andb_true_iff, forallb_forall in H5.
            destruct H5 as [[[[W1 W2] W3] W4] W5].
            assert (Wf := W1 _ H4); simpl in Wf; rewrite Hf, H2 in Wf; simpl in Wf.
            case_eq (is_a_suitable_env (labels T (default_tuple sa1)) e2 (A_agg a f));
              intro Nf; [ | rewrite Nf in Wf; discriminate Wf].
            unfold is_a_suitable_env in H3, Nf; simpl in H3, Nf.
            unfold default_tuple in Nf; 
              rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Nf.
            rewrite H3 in Nf; discriminate Nf.
         ++ case_eq (find_eval_env (e1 ++ (sa1, g1, l1) :: e2) (A_agg a f)); 
              [intros e He; unfold env_slice in *; rewrite He; intro Abs; discriminate Abs | ].
            intros H1 H2 H3 H4.
            apply IHe1; [assumption | apply H3 | ].
            rewrite Bool.Bool.andb_true_iff in H4; apply (proj2 H4).
      -- rewrite Mf, Bool.Bool.orb_false_l in Jf.
         rewrite !interp_aggterm_unfold, Hf, !(find_eval_env_unfold (T := T) (_ :: _)), Kf, Aux.
         unfold is_a_suitable_env, is_built_upon_ag.
         rewrite Oset.mem_bool_app, Lf, Mf, Jf; rewrite Bool.Bool.orb_true_r.
         unfold unfold_env_slice; rewrite !map_map; apply Haggregate.
         apply Oset.permut_trans with 
          (map (fun x => interp_funterm ((s, Group_Fine, x :: nil) :: env) f) l).
         ++ apply _permut_map with (fun x y => Oeset.compare (OTuple T) x y = Eq).
            ** intros t1 t2 Ht1 Ht2 Ht; subst; 
                 rewrite Oset.compare_eq_iff; apply interp_funterm_eq.
               constructor 2; [ | apply equiv_env_refl].
               simpl; repeat split; [apply Fset.equal_refl | ].
               rewrite compare_list_t; unfold compare_OLA; simpl.
               rewrite Ht; apply refl_equal.
            ** apply Oeset.permut_sym; apply quick_permut.
         ++ apply Oset.permut_trans with
             (map
                (fun x =>
                   interp_funterm
                     ((s unionS Fset.mk_set (A T) lb, Group_Fine, x :: nil) :: env) f)
                (map (fun x => 
                        projection (env_t env x) 
                                   (Select_List (_Select_List (id_renaming s ++ s')))) l)).
            ** rewrite map_map; apply Oset.permut_refl_alt2; rewrite <- map_eq.
               rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff in We', We'';
                 destruct We' as [[[[W1 W2] W3] W4] W5]; 
                 destruct We'' as [[[[W1' W2'] W3'] W4'] W5'].
               intros t Ht.
               refine (trans_eq 
                         _ (trans_eq 
                              (eq_sym 
                                 (interp_funterm_eq_env_t_strong 
                                    nil env s (Fset.mk_set (A T) lb)
                                    (projection 
                                       (env_t env t) 
                                       (Select_List (_Select_List (id_renaming s ++ s')))) 
                                    f _ _ _)) _)).
               --- unfold env_t; apply interp_funterm_eq; constructor 2; [ | apply equiv_env_refl].
                   simpl; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
                   split; [apply Fset.equal_refl | split; [apply refl_equal | ]].
                   refine (Pcons (R := fun x y => Oeset.compare (OTuple T) x y = Eq)
                                 _ _ nil nil _ (Oeset.permut_refl _ _)); rewrite tuple_eq.
                   rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _));
                     rewrite forallb_forall in W3; split; [apply W3; assumption | ].
                   intros b Hb; rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ (W3 _ Ht)), Hb.
                   unfold id_renaming; rewrite !map_app, !map_map, dot_mk_tuple.
                   rewrite Fset.mem_mk_set_app, map_id, 
                     (Fset.mem_eq_2 _ _ _ (Fset.mk_set_idem _ _));
                     [ | intros; trivial].
                   rewrite <- (Fset.mem_eq_2 _ _ _ (W3 _ Ht)), Hb, Bool.Bool.orb_true_l.
                   unfold pair_of_select.
                   rewrite Oset.find_app, Oset.find_map; simpl.
                   +++ rewrite Hb; apply refl_equal.
                   +++ apply Fset.mem_in_elements; rewrite <- (Fset.mem_eq_2 _ _ _ (W3 _ Ht)), Hb.
                       apply refl_equal.
               --- simpl app; unfold env_t; rewrite well_formed_e_unfold, !Bool.Bool.andb_true_iff;
                   repeat split; trivial.
                   +++ rewrite forallb_forall; intros x [Hx | Hx]; [subst x | contradiction Hx].
                       apply Fset.equal_refl.
                   +++ rewrite <- W4'; apply Fset.is_empty_eq.
                       apply Fset.inter_eq_1; 
                         rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
                       unfold id_renaming; rewrite !map_app, !map_map, map_id; 
                         [ | intros; trivial].
                       rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)); 
                         apply Fset.union_eq.
                       *** apply Fset.mk_set_idem.
                       *** unfold lb; apply Fset.equal_refl_alt; apply f_equal; rewrite <- map_eq.
                           intros [] _; apply refl_equal.
               --- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)).
                   unfold id_renaming; rewrite !map_app, !map_map, map_id; [ | intros; trivial].
                   rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)); apply Fset.union_eq.
                   +++ apply Fset.mk_set_idem.
                   +++ unfold lb; apply Fset.equal_refl_alt; apply f_equal; rewrite <- map_eq.
                       intros [] _; apply refl_equal.
               --- intros b Hb; rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Hb.
                   destruct Hb as [H1 H2].
                   assert (H3 := is_built_upon_ft_variables_ft_sub _ _ _ Jf).
                   rewrite Fset.subset_spec in H3; assert (H4 := H3 _ H2).
                   rewrite Fset.is_empty_spec, Fset.equal_spec in W4'.
                   assert (H5 := W4' b); rewrite Fset.mem_inter, Fset.mem_union, H1 in H5.
                   rewrite Bool.Bool.orb_true_r, Bool.Bool.andb_true_l, Fset.empty_spec in H5.
                   rewrite extract_funterms_app, map_app, Fset.mem_Union_app, 
                     extract_funterms_A_Expr in H4.
                   rewrite map_map in H4.
                   case_eq (b inS? Fset.Union 
                              (A T) (map (fun x => variables_ft T (F_Dot x)) ({{{s}}})));
                     intro H6; [ | rewrite H6, Bool.Bool.orb_false_l in H4].
                   +++ rewrite Fset.mem_Union in H6.
                       destruct H6 as [_s [H6 H7]]; rewrite in_map_iff in H6.
                       destruct H6 as [_b [_H6 H6]]; subst _s; simpl in H7.
                       rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in H7; subst _b.
                       apply Fset.in_elements_mem; assumption.
                   +++ rewrite Fset.mem_Union in H4.
                       destruct H4 as [_s [H4 H7]]; rewrite in_map_iff in H4.
                       destruct H4 as [_f [_H4 H4]]; subst _s.
                       rewrite in_extract_funterms, in_flat_map in H4.
                       destruct H4 as [[[sa1 g1] l1] [_H4 H4]].
                       apply False_rec; rewrite <- not_true_iff_false in H5; apply H5.
                       destruct (in_split _ _ _H4) as [e1 [e2 He]].
                       rewrite He in W5; assert (W := well_formed_e_tail _ _ _ W5).
                       assert (Aux2 := well_formed_ag_variables_ag_env_alt _ _ _ _ W H4).
                       simpl in Aux2; rewrite Fset.subset_spec in Aux2.
                       assert (H8 := Aux2 _ H7).
                       rewrite He, map_app, Fset.mem_Union_app; simpl.
                       unfold env_slice in *; rewrite H8, Bool.Bool.orb_true_r; apply refl_equal.
               --- unfold env_t; rewrite app_nil.
                   apply (interp_funterm_homogeneous_nil _ _ _ _ _ _ _ _ _ _ (quicksort_1 _ _)).
            ** apply _permut_map with (fun x y => Oeset.compare (OTuple T) x y = Eq).
               --- intros t1 t2 Ht1 Ht2 Ht; rewrite Oset.compare_eq_iff.
                   apply trans_eq with 
                       (interp_funterm 
                          ((s unionS Fset.mk_set (A T) lb, Group_Fine, t2 :: nil) :: env) f).
                   +++ apply interp_funterm_eq.
                       constructor 2; [ | apply equiv_env_refl].
                       simpl; repeat split; [apply Fset.equal_refl | ].
                       rewrite compare_list_t; unfold compare_OLA; simpl.
                       rewrite Ht; apply refl_equal.
                   +++ apply (interp_funterm_homogeneous_nil
                                _ _ _ _ _ _ _ _ _ _ (quicksort_1 _ _)).
               --- apply quick_permut.
- simpl; apply f_equal; rewrite <- map_eq; intros x Hx.
  apply IHn; trivial.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + simpl in We; rewrite forallb_forall in We.
    apply We; assumption.
Qed.

End Sec.
