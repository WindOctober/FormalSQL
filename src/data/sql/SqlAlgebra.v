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
Require Import Bool List Arith NArith Psatz.

Require Import BasicTacs BasicFacts ListFacts ListPermut ListSort OrderedSet
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Bool3 Formula
        Partition.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.

Import Tuple.

Notation tuple := (tuple T).
Arguments Select_As {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_By {T}.
Arguments A_Expr {T}.
Arguments Sql_True {T}.
Arguments Sql_Pred {T}.
Arguments Sql_Quant {T}.
Arguments Sql_In {T}.
Arguments Sql_Exists {T}.

Inductive query : Type := 
  | Q_Empty_Tuple : query
  | Q_Empty_Relation : Fset.set (A T) -> query
  | Q_Table : relname -> query
  | Q_Set : set_op -> query -> query -> query
  | Q_CrossJoin : query -> query -> query
  | Q_Pi : _select_list T -> query -> query
  | Q_Sigma : (sql_formula T query) -> query -> query
  | Q_Gamma : _select_list T -> list (@aggterm T) -> (sql_formula T query) -> query -> query.

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.

Definition well_sorted_table_instance :=
  forall table row,
    row inBE (instance table) -> labels T row =S= basesort table.


Fixpoint sort (q : query) : setA :=
  match q with
    | Q_Empty_Tuple => Fset.empty _
    | Q_Empty_Relation s => s
    | Q_Table t => basesort t
    | Q_Set _ q1 _ => sort q1
    | Q_CrossJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi select_list _
    | Q_Gamma select_list _ _ _ => select_list_sort select_list
  end.

Fixpoint free_variables_q q :=
  match q with
  | Q_Empty_Tuple
  | Q_Empty_Relation _
  | Q_Table _ => Fset.empty (A T)
  | Q_Set _ q1 q2
  | Q_CrossJoin q1 q2 => (free_variables_q q1) unionS (free_variables_q q2)
  | Q_Pi (_Select_List s) q => free_variables_q q unionS 
                 (Fset.diff _
                    (Fset.Union _
                       (map (fun x => match x with Select_As e _ => variables_ag T e end) s))
                    (sort q))
  | Q_Sigma f q => free_variables_q q unionS 
                      (Fset.diff _ (attributes_sql_f free_variables_q f) (sort q))
  | Q_Gamma (_Select_List s) g f q =>
              free_variables_q q unionS 
                 ((Fset.diff _
                    (Fset.Union _
                       (map (fun x => match x with Select_As e _ => variables_ag T e end) s))
                    (sort q)) unionS
                 ((Fset.diff _
                    (Fset.Union _ (map (@variables_ag T) g)) (sort q)) unionS
                  (Fset.diff _ (attributes_sql_f free_variables_q f) (sort q))))
  end.

Lemma sort_unfold :
  forall q, sort q =
  match q with
    | Q_Empty_Tuple => Fset.empty _
    | Q_Empty_Relation s => s
    | Q_Table t => basesort t
    | Q_Set _ q1 _ => sort q1
    | Q_CrossJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi select_list _
    | Q_Gamma select_list _ _ _ => select_list_sort select_list
  end.
Proof.
intro q; case q; intros; apply refl_equal.
Qed.

Notation make_groups := 
  (fun env b => @make_groups T env (Febag.elements (Fecol.CBag (CTuple T)) b)).
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.
Hypothesis contains_nulls_eq : forall t1 t2, t1 =t= t2 -> contains_nulls t1 = contains_nulls t2.

Notation eval_sql_formula := (eval_sql_formula unknown contains_nulls).
Notation cross_join_bag b1 b2 :=
  (Febag.mk_bag
     (Fecol.CBag (CTuple T))
     (brute_left_join_list tuple (join_tuple T)
        (Febag.elements (Fecol.CBag (CTuple T)) b1) (Febag.elements (Fecol.CBag (CTuple T)) b2))).

Fixpoint eval_query env q {struct q} : bagT :=
  match q with
  | Q_Empty_Tuple => Febag.singleton _ (empty_tuple T)
  | Q_Empty_Relation _ => Febag.empty _
  | Q_Table r => instance r
  | Q_Set o q1 q2 =>
    if sort q1 =S?= sort q2 
    then Febag.interp_set_op _ o (eval_query env q1) (eval_query env q2)
    else Febag.empty _
  | Q_CrossJoin q1 q2 => cross_join_bag (eval_query env q1) (eval_query env q2)
  | Q_Pi s q => 
    Febag.map _  _ (fun t => projection T (env_t T env t) (Select_List s)) (eval_query env q) 
  | Q_Sigma f q => 
    Febag.filter 
      _ (fun t => Bool.is_true (B T) (eval_sql_formula eval_query (env_t T env t) f)) 
      (eval_query env q)
  | Q_Gamma s lf f q => 
    Febag.mk_bag 
      _ (map (fun l => projection T (env_g T env (Group_By lf) l) (Select_List s))
             (filter (fun l => 
                        Bool.is_true (B T) 
                          (eval_sql_formula eval_query (env_g T env (Group_By lf) l) f))
                     (make_groups env (eval_query env q) (Group_By lf))))
  end.

Lemma eval_query_unfold :
  forall env q, eval_query env q =
  match q with
  | Q_Empty_Tuple => Febag.singleton _ (empty_tuple T)
  | Q_Empty_Relation _ => Febag.empty _
  | Q_Table r => instance r
  | Q_Set o q1 q2 =>
    if sort q1 =S?= sort q2 
    then Febag.interp_set_op _ o (eval_query env q1) (eval_query env q2)
    else Febag.empty _
  | Q_CrossJoin q1 q2 => cross_join_bag (eval_query env q1) (eval_query env q2)
  | Q_Pi s q => 
    Febag.map _  _ (fun t => projection T (env_t T env t) (Select_List s)) (eval_query env q) 
  | Q_Sigma f q => 
    Febag.filter 
      _ (fun t => Bool.is_true (B T) (eval_sql_formula eval_query (env_t T env t) f)) 
      (eval_query env q)
  | Q_Gamma s lf f q => 
    Febag.mk_bag 
      _ (map (fun l => projection T (env_g T env (Group_By lf) l) (Select_List s))
             (filter (fun l => 
                        Bool.is_true (B T) 
                          (eval_sql_formula eval_query (env_g T env (Group_By lf) l) f))
                     (make_groups env (eval_query env q) (Group_By lf))))
  end.
Proof.
intros env q; case q; intros; apply refl_equal.
Qed.

(** * Syntactic comparison of queries *)

Definition All := (All T relname).

Fixpoint tree_of_query (q : query) : tree All :=
  match q with
    | Q_Empty_Tuple => Node 4 nil 
    | Q_Empty_Relation s => Node 15 (map (fun a => Leaf (@All_attribute T relname a)) (Fset.elements _ s))
    | Q_Table r => Node 5 (Leaf (All_relname T r) :: nil)
    | Q_Set o q1 q2 => 
      Node 
        (match o with 
           | Union => 6 
           | Inter => 7 
           | Diff => 8 
           | UnionMax => 9 end)
        (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_CrossJoin q1 q2 => Node 14 (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Pi s q => Node 11 (tree_of_select_item _ (Select_List s) :: tree_of_query q :: nil)
    | Q_Sigma f q => Node 12 (tree_of_sql_formula tree_of_query f ::  tree_of_query q :: nil)
    | Q_Gamma s lf f q => 
      Node 13 (tree_of_sql_formula tree_of_query f  
               :: tree_of_select_item _ (Select_List s)
               :: tree_of_query q 
               :: (map (fun x => Leaf (All_aggterm _ x)) lf))
  end.

Lemma tree_of_query_unfold :
  forall q, tree_of_query q =
  match q with
    | Q_Empty_Tuple => Node 4 nil 
    | Q_Empty_Relation s => Node 15 (map (fun a => Leaf (@All_attribute T relname a)) (Fset.elements _ s))
    | Q_Table r => Node 5 (Leaf (All_relname T r) :: nil)
    | Q_Set o q1 q2 => 
      Node 
        (match o with 
           | Union => 6 
           | Inter => 7 
           | Diff => 8 
           | UnionMax => 9 end)
        (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_CrossJoin q1 q2 => Node 14 (tree_of_query q1 :: tree_of_query q2 :: nil)
    | Q_Pi s q => Node 11 (tree_of_select_item _ (Select_List s) :: tree_of_query q :: nil)
    | Q_Sigma f q => Node 12 (tree_of_sql_formula tree_of_query f ::  tree_of_query q :: nil)
    | Q_Gamma s lf f q => 
      Node 13 (tree_of_sql_formula tree_of_query f  
               :: tree_of_select_item _ (Select_List s)
               :: tree_of_query q 
               :: (map (fun x => Leaf (All_aggterm _ x)) lf))
  end.
Proof.
intro q; case q; intros; apply refl_equal.
Qed.

Lemma eval_query_eq_etc :
  forall n,
    (forall q, 
       tree_size (tree_of_query q) <= n -> 
       forall env1 env2, equiv_env T env1 env2 -> eval_query env1 q =BE= eval_query env2 q) /\
    (forall f, 
        tree_size (tree_of_sql_formula tree_of_query f) <= n ->
        forall env1 env2, 
          equiv_env T env1 env2 ->
          eval_sql_formula eval_query env1 f = eval_sql_formula eval_query env2 f).
Proof.
intro n; induction n as [ | n]; repeat split.
- intros q Hn; destruct q; inversion Hn.
- intros f Hn; destruct f; inversion Hn.
- intros q Hn env1 env2 He;
  destruct q as [ | s0 | r | o q1 q2 | q1 q2 | [s] q | f q | [s] g f q];
  rewrite Febag.nb_occ_equal; intro t.
  + apply refl_equal. 
  + apply refl_equal.
  + apply refl_equal.
  + rewrite 2 (eval_query_unfold _ (Q_Set _ _ _)).
    assert (IH1 : eval_query env1 q1 =BE= eval_query env2 q1).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 : eval_query env1 q2 =BE= eval_query env2 q2).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    case (sort q1 =S?= sort q2); [ | apply refl_equal].
    destruct o; simpl.
    * rewrite 2 Febag.nb_occ_union, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_union_max, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_inter, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_diff, IH1, IH2; apply refl_equal.
  + rewrite 2 (eval_query_unfold _ (Q_CrossJoin _ _)).
    assert (IH1 : eval_query env1 q1 =BE= eval_query env2 q1).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 : eval_query env1 q2 =BE= eval_query env2 q2).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    rewrite 2 Febag.nb_occ_mk_bag.
    apply Oeset.permut_nb_occ.
    unfold brute_left_join_list.
    apply (theta_join_list_permut_eq
             _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
             (fun _ _ : tuple => true) (fun _ _ _ _ _ _ => refl_equal _)).
    * apply Oeset.permut_refl_alt; apply Febag.elements_spec1.
      apply Febag.nb_occ_equal; intro e; apply IH1.
    * apply Oeset.permut_refl_alt; apply Febag.elements_spec1.
      apply Febag.nb_occ_equal; intro e; apply IH2.
  + rewrite 2 (eval_query_unfold _ (Q_Pi _ _)).
    assert (IH : eval_query env1 q =BE= eval_query env2 q).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
    * intros x1 x2 Hx; apply projection_eq; env_tac.
    * intro x; apply Oeset.permut_nb_occ.
      apply Oeset.permut_refl_alt; apply Febag.elements_spec1; apply IH.
  + rewrite 2 (eval_query_unfold _ (Q_Sigma _ _)).
    assert (IHq : eval_query env1 q =BE= eval_query env2 q).
    {
      apply (proj1 IHn); [ | assumption].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    assert (IHf : forall env1 env2, 
               equiv_env T env1 env2 -> 
               eval_sql_formula eval_query env1 f = eval_sql_formula eval_query env2 f).
    {
      apply (proj2 IHn).
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    rewrite 2 Febag.nb_occ_filter.
    * {
        apply f_equal2.
        - rewrite Febag.nb_occ_equal in IHq; apply IHq.
        - apply if_eq; [ | intros; apply refl_equal | intros; apply refl_equal].
          apply f_equal; apply IHf; env_tac.
      }
    * intros u1 u2 _ Hu; apply f_equal; apply IHf; env_tac.
    * intros u1 u2 _ Hu; apply f_equal; apply IHf; env_tac.
  + rewrite 2 (eval_query_unfold _ (Q_Gamma _ _ _ _)).
    rewrite 2 Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3 (OLTuple T)).
    * intros l1 l2 Hl; apply projection_eq; env_tac.
    * {
        intro l; rewrite 2 Oeset.nb_occ_filter.
        - apply if_eq.
          + apply f_equal; apply (proj2 IHn).
            * rewrite tree_of_query_unfold in Hn; simpl in Hn.
              refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
              apply le_plus_l.
            * env_tac.
          + intro Hl.
            apply Oeset.permut_nb_occ; unfold FlatData.make_groups.
            apply snd_partition_eq.
            * intros x1 Hx1 x2 Hx; rewrite <- map_eq.
              intros a Ha; apply interp_aggterm_eq; env_tac.
            * apply Oeset.nb_occ_permut; intro x; rewrite <- !Febag.nb_occ_elements; revert x.
              rewrite <- Febag.nb_occ_equal; apply (proj1 IHn); [ | assumption].
              rewrite tree_of_query_unfold in Hn; simpl in Hn.
              refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
              refine (le_trans _ _ _ _ (le_plus_r _ _)).
              apply le_S.
              refine (le_trans _ _ _ _ (le_plus_r _ _)).
              apply le_plus_l.
          + intros; apply refl_equal.
        - intros x1 x2 _ Hx; apply f_equal; apply (proj2 IHn).
          + rewrite tree_of_query_unfold in Hn; simpl in Hn.
            refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
          + env_tac.
        - intros x1 x2 _ Hx; apply f_equal; apply (proj2 IHn).
          + rewrite tree_of_query_unfold in Hn; simpl in Hn.
            refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
          + env_tac.
      }
- intros f Hn env1 env2 He.
  apply eval_sql_formula_eq_etc with relname tree_of_query n.
  + apply contains_nulls_eq.
  + apply (proj1 IHn).
  + assumption.
  + assumption.
Qed.

Lemma eval_query_eq :
  forall q env1 env2, equiv_env T env1 env2 -> eval_query env1 q =BE= eval_query env2 q.
Proof.
intros q env1 env2 He.
apply (proj1 (eval_query_eq_etc _) _ (le_n _) _ _ He).
Qed.

Lemma eval_formula_eq :
  forall f env1 env2, equiv_env T env1 env2 ->
                      eval_sql_formula eval_query env1 f = eval_sql_formula eval_query env2 f.
Proof.
intros f env1 env2 He.
apply (proj2 (eval_query_eq_etc _) _ (le_n _) _ _ He).
Qed.

Lemma well_sorted_query_etc :
  well_sorted_table_instance ->
  forall n q, tree_size (tree_of_query q) <= n -> 
              forall env t, t inBE (eval_query env q) -> labels T t =S= sort q.
Proof.
intros WI n; induction n as [ | n]; intros q Hn env t Ht;
  [destruct q; inversion Hn | ].
destruct q as [ | s0 | r | o q1 q2 | q1 q2 | [s] q | f q | [s] g f q];
  rewrite eval_query_unfold in Ht.
- rewrite Febag.mem_nb_occ, Febag.nb_occ_singleton in Ht.
  case_eq (Oeset.eq_bool (OTuple T) t (empty_tuple T)); intro Kt; rewrite Kt in Ht.
  + rewrite Oeset.eq_bool_true_compare_eq in Kt.
    rewrite tuple_eq in Kt.
    rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Kt)); unfold empty_tuple.
    rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
    apply Fset.equal_refl.
  + discriminate Ht.
- rewrite Febag.empty_spec_weak in Ht; discriminate Ht.
- apply (WI _ _ Ht).
- case_eq (sort q1 =S?= sort q2); intro Hq; rewrite Hq in Ht.
  + destruct o; simpl in Ht.
    * rewrite Febag.mem_union, Bool.Bool.orb_true_iff in Ht.
      destruct Ht as [Ht | Ht].
      -- apply (IHn q1) with env; [ | assumption].
         rewrite tree_of_query_unfold in Hn; simpl in Hn.
         refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         apply le_plus_l.
      -- rewrite (Fset.equal_eq_2 _ _ _ _ Hq).
         apply (IHn q2) with env; [ | assumption].
         rewrite tree_of_query_unfold in Hn; simpl in Hn.
         refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         refine (le_trans _ _ _ _ (le_plus_r _ _)).
         apply le_plus_l.
    * rewrite Febag.mem_union_max, Bool.Bool.orb_true_iff in Ht.
      destruct Ht as [Ht | Ht].
      -- apply (IHn q1) with env; [ | assumption].
         rewrite tree_of_query_unfold in Hn; simpl in Hn.
         refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         apply le_plus_l.
      -- rewrite (Fset.equal_eq_2 _ _ _ _ Hq).
         apply (IHn q2) with env; [ | assumption].
         rewrite tree_of_query_unfold in Hn; simpl in Hn.
         refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         refine (le_trans _ _ _ _ (le_plus_r _ _)).
         apply le_plus_l.
    * rewrite Febag.mem_inter, Bool.Bool.andb_true_iff in Ht.
      apply (IHn q1) with env; [ | apply (proj1 Ht)].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * apply (IHn q1) with env; [ | apply (Febag.diff_spec_weak _ _ _ _ Ht)].
      rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
  + rewrite Febag.empty_spec_weak in Ht; discriminate Ht.
- rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ht.
  destruct Ht as [t' [Ht Ht']].
  unfold brute_left_join_list in Ht'; rewrite theta_join_list_unfold, in_flat_map in Ht'.
  destruct Ht' as [t1 [Ht1 Ht']].
  rewrite d_join_list_unfold, in_map_iff in Ht'.
  destruct Ht' as [t2 [Ht2 Ht']].
  rewrite filter_In in Ht'.
  rewrite tuple_eq in Ht; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ht)); rewrite <- Ht2.
  simpl; unfold join_tuple.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  apply Fset.union_eq.
  + apply IHn with env.
    * rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
      exists t1; split; [apply Oeset.compare_eq_refl | assumption].
  + apply IHn with env.
    * rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
      exists t2; split; [apply Oeset.compare_eq_refl | apply (proj1 Ht')].
- unfold Febag.map in Ht.
  rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ht.
  destruct Ht as [t' [Ht Ht']].
  rewrite in_map_iff in Ht'.
  destruct Ht' as [t'' [Ht' Ht'']].
  rewrite (Fset.equal_eq_1 _ _ _ _ (tuple_eq_labels _ _ _ Ht)); rewrite <- Ht'.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)), sort_unfold.
  apply Fset.equal_refl.
- rewrite Febag.mem_filter, Bool.Bool.andb_true_iff in Ht.
  + simpl; apply IHn with env.
    * rewrite tree_of_query_unfold in Hn; simpl in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * apply (proj1 Ht).
  + intros; apply f_equal; apply eval_formula_eq; env_tac.
- rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ht.
  destruct Ht as [t' [Ht Ht']].
  rewrite in_map_iff in Ht'.
  destruct Ht' as [l [Ht' Hl]].
  rewrite (Fset.equal_eq_1 _ _ _ _ (tuple_eq_labels _ _ _ Ht)); rewrite <- Ht'.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)), sort_unfold.
  apply Fset.equal_refl.
Qed.

Lemma well_sorted_query :
  well_sorted_table_instance ->
  forall q env t, t inBE (eval_query env q) -> labels T t =S= sort q.
Proof.
intros WI q env t.
apply (well_sorted_query_etc WI _ (le_n _)).
Qed.

Lemma eval_f_eq :
  forall env f,
    let eval_f := fun t => eval_sql_formula eval_query (env_t T env t) f in
    forall t1 t2, t1 =t= t2 -> eval_f t1 = eval_f t2.
Proof.
intros env f eval_f t1 t2 Ht; unfold eval_f.
refine (eval_sql_formula_eq_etc unknown _ contains_nulls_eq _ _ _ _ _ _).
- apply eval_query_eq_etc.
- apply le_S; apply le_refl.
- env_tac.
Qed.

Lemma is_true_eval_f_eq :
  forall env f,
    let eval_f := fun t => eval_sql_formula eval_query (env_t T env t) f in
    forall t1 t2, t1 =t= t2 -> Bool.is_true (B T) (eval_f t1) = Bool.is_true (B T) (eval_f t2).
Proof.
intros env f eval_f t1 t2 Ht; apply f_equal.
apply eval_f_eq; assumption.
Qed.

Definition fresh_att_in_env s (env : list (setA * group_by T * list tuple)) :=
  Fset.is_empty
    _ (s interS (Fset.Union _ (map (fun slc => match slc with (sa, _, _) => sa end) env))).

Fixpoint well_formed_q env q {struct q} :=
  match q with
  | Q_Empty_Tuple => true
  | Q_Empty_Relation s => fresh_att_in_env s env
  | Q_Table r =>  fresh_att_in_env (basesort r) env
  | Q_Set _ q1 q2
  | Q_CrossJoin q1 q2 => well_formed_q env q1 && well_formed_q env q2
  | Q_Pi (_Select_List s) q => 
       well_formed_q env q 
       && well_formed_s T (env_t T env (default_tuple T (sort q))) s
       && fresh_att_in_env (sort (Q_Pi (_Select_List s) q)) env
       && forallb (fun x => match x with Select_As (A_Expr _) _ => true | _ => false end) s
  | Q_Sigma f q => 
    let well_formed_f :=
        (fix well_formed_f env f {struct f} :=
           match f with
           | Sql_Conj _ f1 f2 => well_formed_f env f1 && well_formed_f env f2
           | Sql_Not f => well_formed_f env f
           | Sql_True _ => true
           | Sql_Pred _ _ l => forallb (well_formed_ag T env) l
           | Sql_Quant _ _ _ l q => well_formed_q env q && forallb (well_formed_ag T env) l
           | Sql_In _ s q => well_formed_q env q && well_formed_s T env s
           | Sql_Exists _ q => well_formed_q env q
           end) in
      well_formed_q env q && well_formed_f (env_t T env (default_tuple T (sort q))) f
  | Q_Gamma s g f q => 
    let well_formed_f :=
        (fix well_formed_f env f {struct f} :=
           match f with
           | Sql_Conj _ f1 f2 => well_formed_f env f1 && well_formed_f env f2
           | Sql_Not f => well_formed_f env f
           | Sql_True _ => true
           | Sql_Pred _ _ l => forallb (well_formed_ag T env) l
           | Sql_Quant _ _ _ l q => well_formed_q env q && forallb (well_formed_ag T env) l
           | Sql_In _ s q => well_formed_q env q && well_formed_s T env s
           | Sql_Exists _ q => well_formed_q env q
           end) in
      well_formed_q env q 
      && forallb (well_formed_ag T (env_t T env (default_tuple T (sort q)))) g
      && fresh_att_in_env (sort (Q_Gamma s g f q)) env
      && well_formed_f (env_g T env (Group_By g) (default_tuple T (sort q) :: nil)) f
  end.

Fixpoint well_formed_f env f {struct f} :=
  match f with
  | Sql_Conj _ f1 f2 => well_formed_f env f1 && well_formed_f env f2
  | Sql_Not f => well_formed_f env f
  | Sql_True _ => true
  | Sql_Pred _ _ l => forallb (well_formed_ag T env) l
  | Sql_Quant _ _ _ l q => well_formed_q env q && forallb (well_formed_ag T env) l
  | Sql_In _ s q => well_formed_q env q && well_formed_s T env s
  | Sql_Exists _ q => well_formed_q env q
  end.

Lemma well_formed_q_unfold :
  forall env q, well_formed_q env q =
  match q with
  | Q_Empty_Tuple => true
  | Q_Empty_Relation s => fresh_att_in_env s env
  | Q_Table r =>  fresh_att_in_env (basesort r) env
  | Q_Set _ q1 q2
  | Q_CrossJoin q1 q2 => well_formed_q env q1 && well_formed_q env q2
  | Q_Pi (_Select_List s) q => 
       well_formed_q env q 
       && well_formed_s T (env_t T env (default_tuple T (sort q))) s
       && fresh_att_in_env (sort (Q_Pi (_Select_List s) q)) env
       && forallb (fun x => match x with Select_As (A_Expr _) _ => true | _ => false end) s
  | Q_Sigma f q => 
      well_formed_q env q && well_formed_f (env_t T env (default_tuple T (sort q))) f
  | Q_Gamma s g f q => 
      well_formed_q env q 
      && forallb (well_formed_ag T (env_t T env (default_tuple T (sort q)))) g
      && fresh_att_in_env (sort (Q_Gamma s g f q)) env
      && well_formed_f (env_g T env (Group_By g) (default_tuple T (sort q) :: nil)) f
  end.
Proof.
intros env q; case_eq q; intros; apply refl_equal.
Qed.

Lemma well_formed_q_disj_sort :
  forall env q, well_formed_q env q = true -> fresh_att_in_env (sort q) env = true.
Proof.
intros env q.
unfold fresh_att_in_env.
set (n := tree_size (tree_of_query q)).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert q Hn; induction n as [ | n]; intros q Hn Wq; [destruct q; inversion Hn | ].
  destruct q as [ | s0 | r | o q1 q2 | q1 q2 | [s] q | f q | [s] g f q];
    simpl.
- rewrite Fset.is_empty_spec, Fset.equal_spec.
  intros a; rewrite Fset.mem_inter, Fset.empty_spec; apply refl_equal.
- apply Wq.
- apply Wq.
- simpl in Hn, Wq; rewrite Bool.Bool.andb_true_iff in Wq; destruct Wq as [Wq1 Wq2].
  apply IHn; [ | assumption].
  simpl in Hn.
  refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
  apply le_plus_l.
- simpl in Hn, Wq; rewrite !Bool.Bool.andb_true_iff in Wq; destruct Wq as [Wq1 Wq2].
  assert (Hn1 : (tree_size (tree_of_query q1) <= n)%nat).
  {
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_plus_l.
  }
  assert (IH1 := IHn _ Hn1 Wq1); rewrite Fset.is_empty_spec, Fset.equal_spec in IH1.
  assert (Hn2 : (tree_size (tree_of_query q2) <= n)%nat).
  {
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    refine (le_trans _ _ _ _ (le_plus_r _ _)).
    apply le_plus_l.
  }
  assert (IH2 := IHn _ Hn2 Wq2); rewrite Fset.is_empty_spec, Fset.equal_spec in IH2.
  rewrite Fset.is_empty_spec, Fset.equal_spec; intro a.
  assert (Ha1 := IH1 a); assert (Ha2 := IH2 a).
  rewrite Fset.mem_inter, Fset.empty_spec, Bool.Bool.andb_false_iff in Ha1, Ha2.
  rewrite Fset.mem_inter, Fset.mem_union, Fset.empty_spec.
  case_eq (a inS? sort q1); intro Ka1; rewrite Ka1 in Ha1.
  + destruct Ha1 as [Ha1 | Ha1]; [discriminate Ha1 | ].
    rewrite Ha1, Bool.Bool.andb_false_r; apply refl_equal.
  + case_eq (a inS? sort q2); intro Ka2; rewrite Ka2 in Ha2.
    destruct Ha2 as [Ha2 | Ha2]; [discriminate Ha2 | ].
    * rewrite Ha2, Bool.Bool.andb_false_r; apply refl_equal.
    * apply refl_equal.
- simpl in Wq; rewrite !Bool.Bool.andb_true_iff in Wq.
  unfold fresh_att_in_env in Wq.
  apply (proj2 (proj1 Wq)).
- apply IHn.
  + simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    refine (le_trans _ _ _ _ (le_plus_r _ _)).
    apply le_plus_l.
  + simpl in Wq; rewrite Bool.Bool.andb_true_iff in Wq; apply (proj1 Wq).
- rewrite well_formed_q_unfold in Wq; rewrite !Bool.Bool.andb_true_iff in Wq.
  destruct Wq as [[[W1 W2] W3] W4].
  apply W3.
Qed.

Lemma well_formed_env_t_in_query :
  well_sorted_table_instance ->
  forall env q t, well_formed_e T env = true -> well_formed_q env q = true -> 
                  t inBE (eval_query env q) ->
                  well_formed_e T (env_t T env t) = true.
Proof.
intros W env q t We Wq Ht.
apply well_formed_env_t; [assumption | ].
rewrite Fset.is_empty_spec, 
  (Fset.equal_eq_1 _ _ _ _ (Fset.inter_eq_1 _ _ _ _ (well_sorted_query W q env t Ht))).
assert (Aux := well_formed_q_disj_sort _ _ Wq).
unfold fresh_att_in_env in Aux; rewrite Fset.is_empty_spec in Aux; apply Aux.
Qed.

Lemma well_formed_q_eq_etc :
  forall n,
  (forall f, (tree_size (tree_of_sql_formula tree_of_query f) <= n)%nat ->
             forall env1 env2, weak_equiv_env T env1 env2 -> 
                               well_formed_f env1 f = well_formed_f env2 f) /\
  (forall q, (tree_size (tree_of_query q) <= n)%nat ->
             forall env1 env2, weak_equiv_env T env1 env2 ->
                               well_formed_q env1 q = well_formed_q env2 q).
Proof.
intro n; induction n as [ | n]; split.
- intros f Hn; destruct f; inversion Hn.
- intros q Hn; destruct q; inversion Hn.
- intros f Hn env1 env2 He; 
  destruct f as [c f1 f2 | f | | p l | qtf p l q | l q | q].
  + simpl in Hn; generalize (le_S_n _ _ Hn); rewrite plus_0_r; clear Hn; intro Hn.
    simpl; apply f_equal2; apply (proj1 IHn); trivial.
    * refine (le_trans _ _ _ _ Hn); apply le_plus_l.
    * refine (le_trans _ _ _ _ Hn); apply le_plus_r.
  + simpl in Hn; generalize (le_S_n _ _ Hn); rewrite plus_0_r; clear Hn; intro Hn.
    simpl; apply (proj1 IHn); trivial.
  + apply refl_equal.
  + simpl; apply forallb_eq.
    intros x Hx; apply well_formed_ag_eq; assumption.
  + simpl; apply f_equal2.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      do 2 apply le_S.
      rewrite <- !Nat.add_assoc; apply le_plus_l.
    * apply forallb_eq.
      intros x Hx; apply well_formed_ag_eq; assumption.
  + simpl; apply f_equal2.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      do 2 apply le_S.
      refine (le_trans _ _ _ _ (le_plus_l _ _)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * unfold well_formed_s; apply f_equal2; [apply f_equal2 | ].
      -- apply forallb_eq.
         intros [a e] H; apply well_formed_ag_eq; assumption.
      -- apply refl_equal.
      -- apply Fset.is_empty_eq; apply Fset.inter_eq_2.
         revert env2 He; induction env1 as [ | [[s1 g1] l1] env1]; 
           intros [ | [[s2 g2] l2] env2] He; 
           [apply Fset.equal_refl | inversion He | inversion He | ].
         inversion He; subst; simpl.
         apply Fset.union_eq; [ | apply IHenv1; trivial].
         simpl in H2; apply (proj1 H2).
  + simpl; apply (proj2 IHn); trivial.
    simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_S.
    refine (le_trans _ _ _ _ (le_plus_l _ _)).
    apply le_plus_l.
- intros q Hn env1 env2 He;
  destruct q as [ | s0 | r | o q1 q2 | q1 q2 | [s] q | f q | [s] g f q].
  + apply refl_equal.
  + simpl; unfold fresh_att_in_env; apply Fset.is_empty_eq.
    apply Fset.inter_eq_2.
    revert env2 He;  induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
    * inversion He; subst; apply Fset.equal_refl.
    * destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
      unfold equiv_env in He; inversion He; subst; simpl.
      unfold equiv_env_slice in H2; destruct H2 as [K1 K2].
      simpl; apply Fset.union_eq; [assumption | ].
      apply IHenv1; assumption.
  + simpl; unfold fresh_att_in_env; apply Fset.is_empty_eq.
    apply Fset.inter_eq_2.
    revert env2 He;  induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
    * inversion He; subst; apply Fset.equal_refl.
    * destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
      unfold equiv_env in He; inversion He; subst; simpl.
      unfold equiv_env_slice in H2; destruct H2 as [K1 K2].
      simpl; apply Fset.union_eq; [assumption | ].
      apply IHenv1; assumption.
  + simpl; apply f_equal2.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
  + simpl; apply f_equal2.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
  + simpl; apply f_equal2; [apply f_equal2; [apply f_equal2 | ] | ].
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * unfold well_formed_s, default_tuple; apply f_equal2; [apply f_equal2 | ].
      -- apply forallb_eq.
         intros [a e] Hx; apply well_formed_ag_eq; unfold equiv_env; constructor 2; [ | apply He].
         unfold weak_equiv_env_slice; repeat split.
         apply Fset.equal_refl.
      -- apply refl_equal.
      -- apply Fset.is_empty_eq; apply Fset.inter_eq_2; simpl.
         apply Fset.union_eq_2.
         revert env2 He; induction env1 as [ | [[s1 g1] l1] env1]; 
           intros [ | [[s2 g2] l2] env2] He; 
           [apply Fset.equal_refl | inversion He | inversion He | ].
         inversion He; subst; simpl.
         apply Fset.union_eq; [ | apply IHenv1; trivial].
         simpl in H2; apply (proj1 H2).
    * unfold fresh_att_in_env.
      apply Fset.is_empty_eq; apply Fset.inter_eq_2; simpl.
         revert env2 He; induction env1 as [ | [[s1 g1] l1] env1]; 
           intros [ | [[s2 g2] l2] env2] He; 
           [apply Fset.equal_refl | inversion He | inversion He | ].
         inversion He; subst; simpl.
         apply Fset.union_eq; [ | apply IHenv1; trivial].
         simpl in H2; apply (proj1 H2).
    * apply refl_equal.
  + rewrite !(well_formed_q_unfold _ (Q_Sigma _ _)); apply f_equal2.
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * apply (proj1 IHn); trivial.
      -- simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); apply le_plus_l.
      -- unfold env_t, weak_equiv_env; constructor 2; [ | assumption].
         unfold weak_equiv_env_slice; repeat split; trivial.
         apply Fset.equal_refl.
  + rewrite !(well_formed_q_unfold _ (Q_Gamma _ _ _ _));
      apply f_equal2; [apply f_equal2; [apply f_equal2 | ] | ].
    * apply (proj2 IHn); trivial.
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * apply forallb_eq; intros x Hx.
      apply well_formed_ag_eq; constructor 2; [ | assumption].
      simpl; repeat split.
      apply Fset.equal_refl.
    * unfold fresh_att_in_env; apply Fset.is_empty_eq.
      apply Fset.inter_eq_2.
      revert env2 He;  induction env1 as [ | [[sa1 g1] l1] env1]; intros env2 He.
      -- inversion He; subst; apply Fset.equal_refl.
      -- destruct env2 as [ | [[sa2 g2] l2] env2]; [inversion He | ].
         unfold weak_equiv_env in He; inversion He; subst; simpl.
         unfold weak_equiv_env_slice in H2; destruct H2 as [K1 K2].
         simpl; apply Fset.union_eq; [assumption | ].
         apply IHenv1; assumption.
    * apply (proj1 IHn).
      -- simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         apply le_plus_l.
      -- constructor 2; [ | assumption].
         simpl; split; [ | apply refl_equal].
         apply Fset.equal_refl.
Qed.

End Sec.
