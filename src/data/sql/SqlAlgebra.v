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
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Term Bool3 Formula 
        Partition Sql.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

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
  | Q_NaturalJoin : query -> query -> query
  | Q_CrossJoin : query -> query -> query
  | Q_Pi : _select_list T -> query -> query
  | Q_Sigma : (sql_formula T query) -> query -> query
  | Q_Gamma : _select_list T -> list (@aggterm T) -> (sql_formula T query) -> query -> query.

Notation sql_formula := (sql_formula T query). 

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Notation interp_funterm := (interp_funterm T).
Notation interp_aggterm := (interp_aggterm T).
Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.


Fixpoint sort (q : query) : setA :=
  match q with
    | Q_Empty_Tuple => Fset.empty _
    | Q_Empty_Relation s => s
    | Q_Table t => basesort t
    | Q_Set _ q1 _ => sort q1
    | Q_NaturalJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_CrossJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi (_Select_List l) _ 
    | Q_Gamma (_Select_List l) _ _ _ => Fset.mk_set _ (map (fun x => match x with Select_As _ a => a end) l)
  end.

Fixpoint free_variables_q q :=
  match q with
  | Q_Empty_Tuple
  | Q_Empty_Relation _
  | Q_Table _ => Fset.empty (A T)
  | Q_Set _ q1 q2 
  | Q_NaturalJoin q1 q2
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
    | Q_NaturalJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_CrossJoin q1 q2 => Fset.union _ (sort q1) (sort q2)
    | Q_Sigma _ q => sort q
    | Q_Pi (_Select_List l) _ 
    | Q_Gamma (_Select_List l) _ _ _ => 
        Fset.mk_set _ (map (fun x => match x with Select_As _ a => a end) l)
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
Notation natural_join_bag b1 b2 := 
  (Febag.mk_bag 
     (Fecol.CBag (CTuple T))
     (natural_join_list T
        (Febag.elements (Fecol.CBag (CTuple T)) b1) (Febag.elements (Fecol.CBag (CTuple T)) b2))).

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
  | Q_NaturalJoin q1 q2 => natural_join_bag (eval_query env q1) (eval_query env q2)
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
  | Q_NaturalJoin q1 q2 => natural_join_bag (eval_query env q1) (eval_query env q2)
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

Fixpoint N_Q_NaturalJoin l :=
  match l with
    | nil => Q_Empty_Tuple
    | q1 :: l => Q_NaturalJoin q1 (N_Q_NaturalJoin l)
  end.

Lemma N_Q_NaturalJoin_unfold :
  forall l, N_Q_NaturalJoin l =
  match l with
    | nil => Q_Empty_Tuple
    | q1 :: l => Q_NaturalJoin q1 (N_Q_NaturalJoin l)
  end.
Proof.
intros [ | x1 l]; apply refl_equal.
Qed.

Lemma sort_N_Q_Join :
  forall l, sort (N_Q_NaturalJoin l) =S= Fset.Union _ (map sort l).
Proof.
intro l; induction l as [ | x1 l].
- apply Fset.equal_refl.
- rewrite map_unfold, Fset.Union_unfold, N_Q_NaturalJoin_unfold, sort_unfold.
  apply Fset.union_eq_2; apply IHl.
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
    | Q_NaturalJoin q1 q2 => Node 10 (tree_of_query q1 :: tree_of_query q2 :: nil)
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
    | Q_NaturalJoin q1 q2 => Node 10 (tree_of_query q1 :: tree_of_query q2 :: nil)
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
- intros q Hn env1 env2 He; destruct q as [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | [s] q | f q | [s] g f q];
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
  + rewrite 2 (eval_query_unfold _ (Q_NaturalJoin _ _)).
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
    apply natural_join_list_eq.
    * intro t1; rewrite <- 2 Febag.nb_occ_elements; apply IH1.
    * intro t2; rewrite <- 2 Febag.nb_occ_elements; apply IH2.
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
  well_sorted_sql_table T basesort instance ->
  forall n q, tree_size (tree_of_query q) <= n -> 
              forall env t, t inBE (eval_query env q) -> labels T t =S= sort q.
Proof.
intros WI n; induction n as [ | n]; intros q Hn env t Ht;
  [destruct q; inversion Hn | ].
destruct q as [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | [s] q | f q | [s] g f q]; rewrite eval_query_unfold in Ht.
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
  unfold natural_join_list in Ht'; rewrite theta_join_list_unfold, in_flat_map in Ht'.
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
  well_sorted_sql_table T basesort instance ->
  forall q env t, t inBE (eval_query env q) -> labels T t =S= sort q.
Proof.
intros WI q env t.
apply (well_sorted_query_etc WI _ (le_n _)).
Qed.

Fixpoint sql_query_to_alg (sq : sql_query T relname) :=
  match sq with
    | Sql_Table _ r => Q_Table r
    | Sql_Set o sq1 sq2 => Q_Set o (sql_query_to_alg sq1) (sql_query_to_alg sq2)
    | Sql_Select s lsq f1 g f2 =>
      let sql_formula_to_alg :=
          (fix sql_formula_to_alg f :=
             match f with
             | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_to_alg f1) (sql_formula_to_alg f2)
             | Sql_Not f => Sql_Not (sql_formula_to_alg f)
             | Sql_True _ => Sql_True _
             | Sql_Pred _ p l => Sql_Pred _ p l
             | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (sql_query_to_alg sq)
             | Sql_In _ s sq => Sql_In _ s (sql_query_to_alg sq)
             | Sql_Exists _ sq => Sql_Exists _ (sql_query_to_alg sq)
             end) in 
      match s with
      | Select_Star =>
        let s := _Select_List (id_renaming _ (sql_sort basesort sq)) in
        let q1 := N_Q_NaturalJoin (map sql_item_to_alg lsq) in 
        let q2 := Q_Sigma (sql_formula_to_alg f1) q1 in 
        match g with
        | Group_Fine => Q_Sigma (sql_formula_to_alg f2) q2 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q2 
        end
      | Select_List s =>
        let q1 := N_Q_NaturalJoin (map sql_item_to_alg lsq) in 
        let q2 := Q_Sigma (sql_formula_to_alg f1) q1 in 
        match g with
        | Group_Fine => Q_Pi s (Q_Sigma (sql_formula_to_alg f2) q2) 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q2 
        end
      end
  end

with sql_item_to_alg i :=
  match i with
    | From_Item sq (Att_Ren_Star _) => sql_query_to_alg sq
    | From_Item sq (Att_Ren_List s) =>
      Q_Pi 
        (_Select_List
           (map (fun x => match x with Att_As _ a a' => Select_As (A_Expr (F_Dot a)) a' end) s))
        (sql_query_to_alg sq)
  end.

Fixpoint sql_formula_to_alg f : (@Formula.sql_formula T query) :=
  match f with
    | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_to_alg f1) (sql_formula_to_alg f2)
    | Sql_Not f => Sql_Not (sql_formula_to_alg f)
    | Sql_True _ => Sql_True _
    | Sql_Pred _ p l => Sql_Pred _ p l
    | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (sql_query_to_alg sq)
    | Sql_In _ s sq => Sql_In _ s (sql_query_to_alg sq)
    | Sql_Exists _ sq => Sql_Exists _ (sql_query_to_alg sq)
  end.

Lemma sql_query_to_alg_unfold :
  forall sq, sql_query_to_alg sq =
  match sq with
    | Sql_Table _ r => Q_Table r
    | Sql_Set o sq1 sq2 => Q_Set o (sql_query_to_alg sq1) (sql_query_to_alg sq2)
    | Sql_Select s lsq f1 g f2 =>
      match s with
      | Select_Star =>
        let s := _Select_List (id_renaming _ (sql_sort basesort sq)) in
        let q1 := N_Q_NaturalJoin (map sql_item_to_alg lsq) in 
        let q2 := Q_Sigma (sql_formula_to_alg f1) q1 in 
        match g with
        | Group_Fine => Q_Sigma (sql_formula_to_alg f2) q2 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q2 
        end
      | Select_List s =>
        let q1 := N_Q_NaturalJoin (map sql_item_to_alg lsq) in 
        let q2 := Q_Sigma (sql_formula_to_alg f1) q1 in 
        match g with
        | Group_Fine => Q_Pi s (Q_Sigma (sql_formula_to_alg f2) q2) 
        | Group_By g => Q_Gamma s g (sql_formula_to_alg f2) q2 
        end
      end
  end.
Proof.
intro sq; case sq; intros; apply refl_equal.
Qed.

Fixpoint all_distinct lsa :=
  match lsa with
    | nil => true
    | sa1 :: lsa => Fset.is_empty (A T) (sa1 interS (Fset.Union _ lsa)) && all_distinct lsa
  end.

Fixpoint weak_well_formed_q (sq : sql_query T relname) :=
  match sq with
    | Sql_Table _ _ => true
    | Sql_Set _ sq1 sq2 => weak_well_formed_q sq1 && weak_well_formed_q sq2
    | Sql_Select s lsq f1 g f2 => 
      let weak_well_formed_f :=
          (fix weak_well_formed_f f :=
             match f with
             | Sql_Conj _ f1 f2 => weak_well_formed_f f1 && weak_well_formed_f f2
             | Sql_Not f => weak_well_formed_f f
             | Sql_True _ 
             | Sql_Pred _ _ _ => true
             | Sql_Quant _ _ _ _ sq 
             | Sql_In _ _ sq 
             | Sql_Exists _ sq => weak_well_formed_q sq
             end) in
      (all_distinct (map (fun x => sql_from_item_sort basesort x) lsq))
        && (forallb (fun x => match x with From_Item sq _ => weak_well_formed_q sq end) lsq)
        && (weak_well_formed_f f1) 
        && (weak_well_formed_f f2)
  end.

Fixpoint weak_well_formed_f (f : @Formula.sql_formula T (sql_query T relname)) :=
  match f with
    | Sql_Conj _ f1 f2 => weak_well_formed_f f1 && weak_well_formed_f f2
    | Sql_Not f => weak_well_formed_f f
    | Sql_True _
    | Sql_Pred _ _ _ => true
    | Sql_Quant _ _ _ _ sq 
    | Sql_In _ _ sq 
    | Sql_Exists _ sq => weak_well_formed_q sq
  end.
         
Lemma weak_well_formed_q_unfold :
 forall sq, weak_well_formed_q sq =
  match sq with
    | Sql_Table _ _ => true
    | Sql_Set _ sq1 sq2 => weak_well_formed_q sq1 && weak_well_formed_q sq2
    | Sql_Select s lsq f1 g f2 => 
      (all_distinct (map (fun x => sql_from_item_sort basesort x) lsq))
        && (forallb (fun x => match x with From_Item sq _ => weak_well_formed_q sq end) lsq)
        && (weak_well_formed_f f1) 
        && (weak_well_formed_f f2)
  end.
Proof.
intro sq; case sq; intros; apply refl_equal.
Qed.

Lemma weak_well_formed_f_unfold :
  forall f, weak_well_formed_f f =
  match f with
    | Sql_Conj _ f1 f2 => weak_well_formed_f f1 && weak_well_formed_f f2
    | Sql_Not f => weak_well_formed_f f
    | Sql_True _
    | Sql_Pred _ _ _ => true
    | Sql_Quant _ _ _ _ sq 
    | Sql_In _ _ sq 
    | Sql_Exists _ sq => weak_well_formed_q sq
 end.
Proof.
intro a; case a; intros; apply refl_equal.
Qed.

 Ltac sql_size_tac := 
  match goal with
    | Hn : tree_size (tree_of_sql_query (Sql_Set _ ?q1 _)) <= S ?n 
      |- tree_size (tree_of_sql_query ?q1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Set _ _ ?q2)) <= S ?n 
      |- tree_size (tree_of_sql_query ?q2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n
      |- list_size (tree_size (All:=All)) (map tree_of_sql_from_item ?lsq) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      do 2 apply le_S; apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star ?lsq _ _ _)) <= S ?n,
      Hi : In ?fi ?lsq
      |- tree_size (tree_of_sql_from_item ?fi) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size; rewrite in_map_iff; eexists; split; [apply refl_equal | trivial]

    | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) ?lsq _ _ _)) <= S ?n,
           Hy : In ?y ?lsq
      |- tree_size (tree_of_sql_from_item ?y) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size; rewrite in_map_iff; 
      eexists; split; [apply refl_equal | assumption]

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n,
      Hi : In ?fi ?lsq
      |- tree_size (tree_of_sql_from_item ?fi) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size;
      rewrite in_map_iff; exists fi; split; trivial

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n,
           Hf : In (From_Item ?sq ?r) ?lsq
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply (le_trans _ (tree_size (tree_of_sql_from_item (From_Item sq r))) _);
        [simpl; apply le_S; apply le_plus_l | ];
      apply in_list_size; rewrite in_map_iff; eexists; split; [ | apply Hf]; trivial

    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star _ ?f1 _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) _ ?f1 _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ _ ?f _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

(*    | Hn : tree_size  (tree_of_sql_query (Sql_Select _ _ Sql_True _ ?f)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l
*)            
    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star _ _ _ ?f2)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      do 2 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

   | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) _ _ _ ?f2)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      do 3 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ _ _ _ ?f)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      do 3 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_from_item (From_Item ?sq _)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_from_item_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Conj _ ?f _)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      simpl; apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Conj _ _ ?f)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Not ?f)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      simpl; apply le_plus_l

(*    | Hn : tree_size (tree_of_sql_formula (Sql_Atom ?a)) <= S ?n
      |- tree_size (tree_of_sql_atom ?a) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l *)

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Quant _ _ _ ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (Le.le_trans _ _ _ _ (le_plus_l _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_In _ _ ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Exists ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S; refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply le_plus_l

    | _ => idtac
  end.

Lemma sort_sql_to_alg : 
  forall sq, sort (sql_query_to_alg sq) =S= sql_sort basesort sq.
Proof.
intro sq; set (n := tree_size (tree_of_sql_query sq)).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert sq Hn; induction n as [ | n]; [intros sq Hn; destruct sq; inversion Hn | ].
intros sq Hn; destruct sq as [r | o sq1 sq2 | s lsq f1 g f2].
- apply Fset.equal_refl.  
- simpl; change (sort (sql_query_to_alg sq1) =S= sql_sort basesort sq1); apply IHn; sql_size_tac.
- assert (IH : 
            forall f, 
              In f lsq -> 
              sort (sql_item_to_alg f) =S= sql_from_item_sort basesort f).
  {
    intros [sq [ | r]] H.
    - rewrite sql_from_item_sort_unfold; simpl.
      apply IHn.
      rewrite tree_of_sql_query_unfold, tree_size_unfold in Hn; simpl plus in Hn.
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_l _ _)).
      apply le_trans with (tree_size (tree_of_sql_from_item (From_Item sq (Att_Ren_Star T)))).
      + simpl; apply le_S; apply le_plus_l.
      + apply in_list_size; rewrite in_map_iff; eexists; split; [ | apply H]; trivial.
    - rewrite sql_from_item_sort_unfold; simpl.
      unfold att_as_as_pair; rewrite 2 map_map.
      apply Fset.equal_refl_alt; apply f_equal; rewrite <- map_eq.
      intros [a b] Hab; apply refl_equal.
  }
  rewrite sql_sort_unfold; simpl sort.
  destruct s as [ | [s]]; destruct g as [g | ].
  + unfold id_renaming.
    rewrite sort_unfold, map_map, map_id; [ | intros; apply refl_equal].
    apply Fset.mk_set_idem.
  + rewrite 2 sort_unfold.
    rewrite (Fset.equal_eq_1 _ _ _ _ (sort_N_Q_Join _)), map_map.
    apply Fset.Union_map_eq.
    intros [q [ | rho]] H; rewrite sql_from_item_sort_unfold.
    * simpl sql_item_to_alg; apply IHn; sql_size_tac.
    * simpl; rewrite 2 map_map; rewrite Fset.equal_spec.
      intro a; do 2 apply f_equal; rewrite <- map_eq.
      intros [x y] _; apply refl_equal.
  + rewrite sort_unfold, map_map.
    rewrite Fset.equal_spec; intro a.
    do 2 apply f_equal; rewrite <- map_eq.
    intros [e _a] Ha; apply refl_equal.
  + rewrite sort_unfold, map_map.
    rewrite Fset.equal_spec; intro a.
    do 2 apply f_equal; rewrite <- map_eq.
    intros [e _a] Ha; apply refl_equal.
Qed.

Lemma sort_sql_item_to_alg : 
  forall x, sort (sql_item_to_alg x) =S= sql_from_item_sort basesort x.
Proof.
intros [sq [ | r]]; simpl.
- apply sort_sql_to_alg.
- rewrite 2 map_map, Fset.equal_spec.
  intro a; do 2 apply f_equal; rewrite <- map_eq.
  intros [_a b] Ha; apply refl_equal.
Qed.

Notation eval_sql_query := (eval_sql_query  basesort instance unknown contains_nulls).
Notation eval_sql_from_item := (eval_sql_from_item  basesort instance unknown contains_nulls).
Notation tree_of_sql_query := (@tree_of_sql_query T relname).

Lemma sql_query_to_alg_is_sound_etc :
  well_sorted_sql_table T basesort instance ->
  forall n, 
  (forall env (sq : sql_query T relname),
     tree_size (tree_of_sql_query sq) <= n -> weak_well_formed_q sq = true ->
     eval_query env (sql_query_to_alg sq) =BE= eval_sql_query env sq) /\
  (forall env f, 
     tree_size (tree_of_sql_from_item f) <= n -> 
     match f with From_Item sq _ => weak_well_formed_q sq end = true ->
     eval_query env (sql_item_to_alg f) =BE= eval_sql_from_item env f) /\
  (forall env f, 
     tree_size (tree_of_sql_formula tree_of_sql_query f) <= n -> weak_well_formed_f f = true -> 
     eval_sql_formula eval_query env (sql_formula_to_alg f) =
     eval_sql_formula eval_sql_query env f).
Proof.
intros WI n; induction n as [ | n]; [repeat split | ].
- intros env sq Hn; destruct sq; inversion Hn.
- intros env [sq r] Hn; inversion Hn.
- intros env f Hn; destruct f; inversion Hn.
- assert (IHsq : (forall env sq,
                    tree_size (tree_of_sql_query sq) <= S n -> weak_well_formed_q sq = true ->
                    eval_query env (sql_query_to_alg sq) =BE= eval_sql_query env sq)).
  {
    intros env sq Hn Wsq. 
    destruct sq as [r | o sq1 sq2 | s lsq f1 g f2].
    - apply Febag.nb_occ_equal; intro t; apply refl_equal.
    - assert (IH1 : eval_query env (sql_query_to_alg sq1) =BE= eval_sql_query env sq1).
      {
        apply (proj1 IHn); sql_size_tac.
        rewrite weak_well_formed_q_unfold, Bool.Bool.andb_true_iff in Wsq; apply (proj1 Wsq).
      }
      assert (IH2 : eval_query env (sql_query_to_alg sq2) =BE= eval_sql_query env sq2).
      {
        apply (proj1 IHn); sql_size_tac.
        rewrite weak_well_formed_q_unfold, Bool.Bool.andb_true_iff in Wsq; apply (proj2 Wsq).
      }
      rewrite Febag.nb_occ_equal in IH1, IH2.
      rewrite Febag.nb_occ_equal; intro t.
      rewrite eval_sql_query_unfold; simpl.
      rewrite (Fset.equal_eq_1 _ _ _ _ (sort_sql_to_alg _)), 
      (Fset.equal_eq_2 _ _ _ _ (sort_sql_to_alg _)).
      case (sql_sort basesort sq1 =S?= sql_sort basesort sq2); [ | apply refl_equal].
      destruct o; simpl.
      * rewrite 2 Febag.nb_occ_union, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_union_max, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_inter, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_diff, <- IH1, <- IH2; apply refl_equal.
    - assert (IHlsq : eval_query env (N_Q_NaturalJoin (map sql_item_to_alg lsq)) =BE=
                       (N_join_bag T (map (eval_sql_from_item env) lsq))).
      {
        assert (IH : forall y, 
                   In y lsq -> 
                   eval_query env (sql_item_to_alg y) =BE= (eval_sql_from_item env y)).
        {
          intros [sq1 r1] H1. 
          assert (IH : eval_query env (sql_query_to_alg sq1) =BE= eval_sql_query env sq1).
          {
            apply (proj1 IHn).
            - apply le_trans with 
                    (tree_size (tree_of_sql_from_item (From_Item sq1 r1))).
              + simpl; apply le_S; apply le_plus_l.
              + sql_size_tac.
            - rewrite weak_well_formed_q_unfold, 3 Bool.Bool.andb_true_iff, 
              forallb_forall in Wsq.
              apply (proj2 (proj1 (proj1 Wsq)) _ H1).
          }
          destruct r1 as [ | r1].
          - simpl; rewrite (Febag.equal_eq_1 _ _ _ _ IH).
            rewrite Febag.nb_occ_equal; intro a.
            simpl.
            unfold Febag.map; rewrite map_id; [ | intros; apply refl_equal].
            rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements; apply refl_equal.
          - simpl sql_item_to_alg; rewrite eval_query_unfold, eval_sql_from_item_unfold.
            rewrite Febag.nb_occ_equal; intro t1.
            unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
            apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T) (OTuple T)).
            + intros x1 x2 Hx1 Hx12; apply projection_eq; env_tac.
            + intros x1; rewrite <- 2 Febag.nb_occ_elements; revert x1.
              rewrite <- Febag.nb_occ_equal; apply IH.
        }
        {
          rewrite weak_well_formed_q_unfold, 3 Bool.Bool.andb_true_iff in Wsq.
          destruct Wsq as [[[Wlsq _] _] _].
          clear Hn; induction lsq as [ | x1 lsq]; rewrite Febag.nb_occ_equal; intro t; simpl.
          - unfold N_join_bag; rewrite Febag.nb_occ_singleton, Febag.nb_occ_mk_bag; simpl.
            rewrite N.add_0_r; unfold Oeset.eq_bool;
              case (Oeset.compare (OTuple T) t (empty_tuple T)); apply refl_equal.
          - rewrite N_join_bag_unfold, !Febag.nb_occ_mk_bag, (map_unfold _ (_ :: _)).
            rewrite N_join_list_unfold, <- natural_join_list_brute_left_join_list.
            + apply natural_join_list_eq.
              * intro t1; rewrite <- !Febag.nb_occ_elements; revert t1.
                rewrite <- Febag.nb_occ_equal.
                apply IH; left; apply refl_equal.
              * simpl in Wlsq; rewrite Bool.Bool.andb_true_iff in Wlsq.
                assert (IH' := IHlsq (proj2 Wlsq) (fun y h => IH _ (or_intror _ h))).
                rewrite Febag.nb_occ_equal in IH'.
                intro t2; rewrite <- !Febag.nb_occ_elements, IH', N_join_bag_unfold.
                rewrite Febag.nb_occ_mk_bag; apply refl_equal.
            + intros t1 t2 Ht1 Ht2.
              assert (Wt1 : labels T t1 =S= sql_from_item_sort basesort x1).
              {
                refine (well_sorted_sql_from_item unknown _ contains_nulls_eq WI x1 t1 env _).
                rewrite <- Febag.mem_unfold in Ht1; assumption.
              }
              assert (Wt2 : labels T t2 =S= 
                            Fset.Union _ (map (fun x => sql_from_item_sort basesort x) lsq)).
              {
                refine (proj2 (well_sorted_sql_query_etc 
                                 unknown _ contains_nulls_eq WI _) _ (le_n _) _ env _).
                unfold N_join_bag; rewrite Febag.mem_mk_bag; apply Ht2.
              }
              rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.inter_eq_1 _ _ _ _ Wt1)).
              rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.inter_eq_2 _ _ _ _ Wt2)).
              simpl in Wlsq; rewrite Bool.Bool.andb_true_iff, Fset.is_empty_spec in Wlsq.
              apply (proj1 Wlsq).
        }
      }
      assert (IHf1 : forall env, eval_sql_formula eval_query env (sql_formula_to_alg f1) =
                                   eval_sql_formula eval_sql_query env f1).
      {
        intro env'; apply (proj2 IHn); [sql_size_tac | ].
        rewrite weak_well_formed_q_unfold, 3 Bool.Bool.andb_true_iff in Wsq.
        apply (proj2 (proj1 Wsq)).
      }
      assert (IHf2 : forall env, eval_sql_formula eval_query env (sql_formula_to_alg f2) =
                                 eval_sql_formula eval_sql_query env f2).
      {
        intro env'; apply (proj2 IHn); [sql_size_tac | ].
        rewrite weak_well_formed_q_unfold, 3 Bool.Bool.andb_true_iff in Wsq.
        apply (proj2 Wsq).
      }
      assert (IH' : eval_query env (Q_Sigma (sql_formula_to_alg f1)
                                            (N_Q_NaturalJoin (map sql_item_to_alg lsq))) =BE=
                    (Febag.filter
                       BTupleT
                       (fun t =>
                          Bool.is_true 
                            (B T) (eval_sql_formula eval_sql_query (env_t T env t) f1))
                       (N_join_bag T (map (eval_sql_from_item env) lsq)))).
      {
        rewrite eval_query_unfold, Febag.nb_occ_equal; intro t.
        rewrite 2 Febag.nb_occ_filter, IHf1.
        - apply f_equal2; [ | apply refl_equal].
          rewrite Febag.nb_occ_equal in IHlsq; apply IHlsq.
        - intros u1 u2 _ Hu;
            apply f_equal; apply eval_sql_formula_eq; [apply contains_nulls_eq | env_tac].
        - intros u1 u2 _ Hu; rewrite 2 IHf1.
          apply f_equal; apply eval_sql_formula_eq; [apply contains_nulls_eq | env_tac].
      }
      apply Febag.nb_occ_equal; intro t.
      rewrite eval_sql_query_unfold, Febag.nb_occ_mk_bag; cbv iota beta zeta.
      apply trans_eq with
          (Oeset.nb_occ 
             (OTuple T) t
             (map (fun g0 : list tuple => projection T (env_g T env g g0) s)
                  (filter
                     (fun g0 : list tuple =>
                        Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_g T env g g0) f2))
                     (FlatData.make_groups T env
                        (Febag.elements BTupleT
                           (eval_query 
                              env (Q_Sigma 
                                     (sql_formula_to_alg f1) 
                                     (N_Q_NaturalJoin (map sql_item_to_alg lsq))))) g)))).
      + destruct g as [g | ]; destruct s as [ | s]; 
          rewrite sql_query_to_alg_unfold; cbv beta iota zeta.
        * rewrite eval_query_unfold, Febag.nb_occ_mk_bag, sql_sort_unfold.
          apply (Oeset.nb_occ_map_eq_2_3_alt (OLTuple T) (OTuple T)); clear t.
          -- intros l1 l2 Hl1 Hl.
             apply Oeset.compare_eq_trans with 
                 (projection T (env_g T env (Group_By g) l1) Select_Star);
               [ | apply projection_eq; env_tac].
             clear l2 Hl.
             rewrite Oeset.mem_bool_filter, Bool.Bool.andb_true_iff in Hl1;
               [destruct Hl1 as [_ Hl1] | intros; apply f_equal; apply eval_formula_eq; env_tac].
             unfold FlatData.make_groups in Hl1.
             assert (Kl1 := mem_map_snd_partition_diff_nil _ _ _ _ Hl1).
             unfold id_renaming; simpl; rewrite !map_map, map_id; 
               [ | intros; apply refl_equal].
             case_eq (quicksort (OTuple T) l1);
               [intro Q; assert (Ll1 := length_quicksort (OTuple T) l1); rewrite Q in Ll1;
                destruct l1; 
                [apply False_rec; apply Kl1; apply refl_equal | discriminate Ll1 ] | ].
             intros u1 q1 Q.
             rewrite Oeset.mem_bool_true_iff in Hl1.
             destruct Hl1 as [l2 [Hl Hl2]].
             assert (Hu1 : Oeset.mem_bool (OTuple T) u1 l2 = true).
             {
               assert (Hu1 : Oeset.mem_bool (OTuple T) u1 l1 = true).
               {
                 apply Oeset.in_mem_bool; apply (In_quicksort (OTuple T)); rewrite Q.
                 left; apply refl_equal.
               }
               rewrite <- Hu1.
               apply sym_eq; apply Oeset.permut_mem_bool_eq.
               refine (Oeset.permut_trans (quick_permut _ _) _).
               refine (Oeset.permut_trans _ (Oeset.permut_sym (quick_permut _ _))).
               apply Oeset.permut_refl_alt; apply Hl.
             }
             rewrite Oeset.mem_bool_true_iff in Hu1.
             destruct Hu1 as [u2 [Hu1 Hu2]].
             rewrite (Oeset.compare_eq_2 _ _ _ _ Hu1).
             assert (Ku2 := Oeset.in_mem_bool 
                              (OTuple T) _ _ (in_map_snd_partition _ _ _ _ _ Hl2 Hu2)).
             assert (Wu2 := well_sorted_query WI _ _ _ Ku2); simpl in Wu2.
             rewrite (Fset.equal_eq_2 _ _ _ _ (sort_N_Q_Join _)), map_map in Wu2.
             rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)),
               (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_idem _ _)).
             assert (Ws : Fset.Union (A T) (map (fun x  => sort (sql_item_to_alg x)) lsq) =S=
                          Fset.Union (A T) (map (sql_from_item_sort basesort) lsq)).
             {
               apply Fset.Union_map_eq; intros x Hx.
               rewrite (Fset.equal_eq_1 _ _ _ _ (sort_sql_item_to_alg _)); apply Fset.equal_refl.
             }
             split.
             ++ rewrite (Fset.equal_eq_2 _ _ _ _ Wu2), <- (Fset.equal_eq_1 _ _ _ _ Ws).
                apply Fset.equal_refl.
             ++ intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha. 
                rewrite dot_mk_tuple, Ha.
                unfold pair_of_select; rewrite Oset.find_map; 
                  [ | rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha; apply Ha].
                rewrite Fset.mem_mk_set in Ha.
                rewrite tuple_eq in Hu1.
                simpl; rewrite Q.
                rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hu1)), Fset.mem_elements,
                (Fset.elements_spec1 _ _ _ Wu2), (Fset.elements_spec1 _ _ _ Ws), Ha.
                apply (proj2 Hu1).
                rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hu1)), Fset.mem_elements,
                (Fset.elements_spec1 _ _ _ Wu2), (Fset.elements_spec1 _ _ _ Ws), Ha.
                apply refl_equal.
          -- intro l; rewrite !Oeset.nb_occ_filter.
             ++ apply if_eq; intros; trivial.
                rewrite IHf2; apply refl_equal.
             ++ intros; apply f_equal; apply eval_sql_formula_eq; env_tac.
             ++ intros; apply f_equal; apply eval_formula_eq; env_tac.
        * rewrite eval_query_unfold, Febag.nb_occ_mk_bag.
          apply (Oeset.nb_occ_map_eq_2_3_alt (OLTuple T) (OTuple T)); clear t.
          -- intros l1 l2 Hl1 Hl; apply projection_eq; env_tac.
          -- intro l; rewrite !Oeset.nb_occ_filter.
             ++ apply if_eq; intros; trivial.
                rewrite IHf2; apply refl_equal.
             ++ intros; apply f_equal; apply eval_sql_formula_eq; env_tac.
             ++ intros; apply f_equal; apply eval_formula_eq; env_tac.
        * rewrite !(eval_query_unfold _ (Q_Sigma _ _)), !Febag.nb_occ_filter.
          -- unfold FlatData.make_groups; rewrite filter_map, map_map, map_id; 
               [ | intros; apply refl_equal].
             rewrite !Oeset.nb_occ_filter;
               [ | intros; apply f_equal; apply eval_sql_formula_eq; env_tac].
             rewrite <- env_t_env_g, IHf2.
              case (Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_t T env t) f2));
                  [rewrite !N.mul_1_r | rewrite !N.mul_0_r; apply refl_equal].
             rewrite <- !Febag.nb_occ_elements, !Febag.nb_occ_filter;
               [apply refl_equal | intros; apply f_equal; apply eval_formula_eq; env_tac].
          -- intros; apply f_equal; apply eval_formula_eq; env_tac.
          -- intros; apply f_equal; apply eval_formula_eq; env_tac.
        * rewrite (eval_query_unfold _ (Q_Pi _ _)), !(eval_query_unfold _ (Q_Sigma _ _)).
          unfold Febag.map, FlatData.make_groups; rewrite filter_map, map_map, Febag.nb_occ_mk_bag.
          apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T) (OTuple T)); clear t.
          -- intros x1 x2 Hx1 Hx; rewrite env_t_env_g; apply projection_eq; env_tac.
          -- intro x.
             rewrite <- Febag.nb_occ_elements, !Febag.nb_occ_filter, Oeset.nb_occ_filter,
               <- Febag.nb_occ_elements, Febag.nb_occ_filter, <- env_t_env_g, IHf2.
             ++ case (Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_t T env x) f2));
                      [rewrite N.mul_1_r; apply refl_equal | rewrite N.mul_0_r; apply refl_equal].
             ++ intros; apply f_equal; apply eval_formula_eq; env_tac.
             ++ intros; apply f_equal; apply eval_sql_formula_eq; env_tac.
             ++ intros; apply f_equal; apply eval_formula_eq; env_tac.
             ++ intros; apply f_equal; apply eval_formula_eq; env_tac.
      + apply (Oeset.nb_occ_map_eq_2_3_alt (OLTuple T) (OTuple T)); clear t.
        * intros l1 l2 Hl1 Hl; apply projection_eq; env_tac.
        * intro l; rewrite !Oeset.nb_occ_filter.
          -- apply if_eq; trivial.
             intros; unfold FlatData.make_groups; apply Oeset.permut_nb_occ; destruct g as [g | ].
             ++ apply (_permut_map 
                      (R := fun x y => 
                              Oeset.compare (VOLA (OTuple T)  (mk_olists (OVal T)) ) x y = Eq)).
                ** intros [a1 a2] [b1 b2] _ _; simpl; unfold compare_OLA.
                   case (comparelA (Oset.compare (OVal T)) a1 b1); (discriminate || trivial).
                ** apply partition_eq_2; 
                     [intros; rewrite <- map_eq; intros; apply interp_aggterm_eq; env_tac | ].
                   apply Oeset.nb_occ_permut; intro x.
                   rewrite <- !Febag.nb_occ_elements; revert x; rewrite <- Febag.nb_occ_equal.
                   apply IH'.
             ++ apply (_permut_map 
                      (R := fun x y => Oeset.compare (OTuple T) x y = Eq)).
                ** intros a b _ _ K; simpl; unfold compare_OLA; simpl; rewrite K; apply refl_equal.
                ** apply Oeset.nb_occ_permut; intro x.
                   rewrite <- !Febag.nb_occ_elements; revert x; rewrite <- Febag.nb_occ_equal.
                   apply IH'.
          -- intros l1 l2 Hl1 Hl; apply f_equal; apply eval_sql_formula_eq; env_tac.
          -- intros l1 l2 Hl1 Hl; apply f_equal; apply eval_sql_formula_eq; env_tac.
  }
  split; [assumption | split].
  + intros env [sq r] Hn Wsq.
    assert (IH : eval_query env (sql_query_to_alg sq) =BE= eval_sql_query env sq).
    {
      apply IHsq; [ | assumption].
      refine (le_trans _ _ _ _ Hn).
      simpl; apply le_S; apply le_plus_l.
    }
    destruct r as [ | r].
    * simpl sql_item_to_alg; rewrite eval_sql_from_item_unfold; simpl.
      rewrite (Febag.equal_eq_1 _ _ _ _ IH), Febag.nb_occ_equal; intro t.
      unfold Febag.map; rewrite map_id; [ | intros; trivial].
      rewrite Febag.nb_occ_mk_bag, <- Febag.nb_occ_elements; apply refl_equal.
    * simpl sql_item_to_alg; rewrite eval_query_unfold, eval_sql_from_item_unfold.
      unfold Febag.map; rewrite Febag.nb_occ_equal; intro t.
      rewrite 2 Febag.nb_occ_mk_bag.
	      apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T) (OTuple T)).
      -- intros x1 x2 Hx1 Hx; apply projection_eq; env_tac.
      -- intro x; rewrite <- 2 Febag.nb_occ_elements.
         rewrite Febag.nb_occ_equal in IH; apply IH.
  + intros env f Hn Wf; destruct f as [a f1 f2 | f |  | p l | qtf p l sq | s sq | sq].
    * simpl sql_formula_to_alg.
      rewrite 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Conj _ _ _)).
      simpl in Wf; rewrite Bool.Bool.andb_true_iff in Wf; destruct Wf as [Wf1 Wf2].
      assert (IHf1 : eval_sql_formula eval_query env (sql_formula_to_alg f1) = 
                       eval_sql_formula eval_sql_query env f1).
      {
        apply (proj2 IHn); [sql_size_tac | assumption].
      }
      assert (IHf2 : eval_sql_formula eval_query env (sql_formula_to_alg f2) = 
                     eval_sql_formula eval_sql_query env f2).
      {
        apply (proj2 IHn); [sql_size_tac | assumption].
      }
      rewrite IHf1, IHf2; destruct a; apply refl_equal.
    * simpl sql_formula_to_alg.
      rewrite 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Not _)).
      apply f_equal; apply (proj2 IHn); [sql_size_tac | assumption].
    * apply refl_equal.
    * apply refl_equal.
    * simpl sql_formula_to_alg.
      rewrite 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Quant _ _ _ _ _)).
      apply (Formula.interp_quant_eq (B T) (OTuple T)).
      -- apply Oeset.nb_occ_permut; intro a; apply Oeset.nb_occ_eq_2; apply Febag.elements_spec1.
         apply (proj1 IHn); [ | assumption].
         rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn.
         refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
         do 2 apply le_S; refine (le_trans _ _ _ _ (le_plus_l _ _)).
         apply le_plus_l.
      -- intros x1 x2 Hx1 Hx; do 2 apply f_equal.
         rewrite tuple_eq in Hx.
         rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)), <- map_eq.
         intros a Ha; apply (proj2 Hx).
         apply Fset.in_elements_mem; assumption.
    * simpl sql_formula_to_alg.
      rewrite 2 (eval_sql_formula_unfold _ _ _ _ (Sql_In _ _ _)).
      cbv beta iota zeta; apply (interp_quant_eq (B T) (OTuple T)).
      -- apply Oeset.nb_occ_permut.
         intro x; rewrite <- 2 Febag.nb_occ_elements; revert x; rewrite <- Febag.nb_occ_equal.
         apply (proj1 IHn); [ sql_size_tac | assumption].
      -- {
          intros x1 x2 Hx1 Hx.
          rewrite <- (Oeset.compare_eq_2 _ _ _ _ Hx), <- (contains_nulls_eq _ _ Hx).
          apply refl_equal.
        }
    * simpl sql_formula_to_alg.
      rewrite 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Exists _ _)).
      apply if_eq; [ | intros; apply refl_equal | intros; apply refl_equal].
      rewrite 2 Febag.is_empty_spec; apply Febag.equal_eq_1.
      apply (proj1 IHn).
    -- rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn.
       refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
       apply le_S; refine (le_trans _ _ _ _ (le_plus_l _ _)).
       apply le_plus_l.
    -- simpl in Wf; apply Wf.
Qed.

Lemma sql_query_to_alg_is_sound :
  well_sorted_sql_table T basesort instance ->
  forall env sq,  weak_well_formed_q sq = true ->
     eval_query env (sql_query_to_alg sq) =BE= 
     eval_sql_query env sq.
Proof.
intros WI env sq.
apply (proj1 (sql_query_to_alg_is_sound_etc WI _) env sq (le_n _)).  
Qed.

Hypothesis default_table : relname.
Hypothesis default_table_not_empty : Febag.is_empty _ (instance default_table) = false.
Hypothesis fresh : list attribute -> attribute.
Hypothesis fresh_is_fresh : forall s, Oset.mem_bool (OAtt T) (fresh s) s = false.
Hypothesis Pred_Equal : predicate T.
Hypothesis interp_Pred_Equal :
  forall v1 v2, 
    interp_predicate T Pred_Equal (v1 :: v2 :: nil) = 
    if Oset.eq_bool (OVal T) v1 v2 then Bool.true (B T) else Bool.false (B T).

Fixpoint freshes (n : nat) s :=
  match n with
  | O => nil
  | S n => let ff := freshes n s in ff ++ (fresh (ff ++ s)) :: nil
  end.

Definition to_direct_renaming_att (ll : list (attribute * attribute)) := 
  List.map (fun x => match x with (a2,b2) => Att_As T a2 b2 end) ll.

Definition to_inverse_renaming (ll : list (attribute * attribute)) := 
  map (fun x => match x with (a, b) => Select_As (A_Expr (F_Dot b)) a end) ll.

Definition rho1 (s1 s2 : list attribute) :=
  let s12 := s1 ++ s2 in
  let s1' := freshes (List.length s1) s12 in
  let ss1 := combine s1 s1' in
  (combine s1 s1').

Definition rho2 (s1 s2 : list attribute) := 
  let s12 := s1 ++ s2 in
  let s1' := freshes (List.length s1) s12 in
  let s2' := freshes (List.length s2) (s1' ++ s12) in
  (combine s2 s2').

Definition rho (s1 s2 : list attribute) env (t : tuple) :=
  projection T (env_t T env t) (Select_List (to_direct_renaming T (rho1 s1 s2 ++ rho2 s1 s2))).

Definition rho1' (s1 s2 : list attribute) := 
    let s12 := s1 ++ s2 in
    let s1' := freshes (List.length s1) s12 in
    to_inverse_renaming (combine s1 s1').

Definition rho2' (s1 s2 : list attribute) := 
    let s12 := s1 ++ s2 in
    let s1' := freshes (List.length s1) s12 in
    let s2' := freshes (List.length s2) (s1' ++ s12) in
    let ss2 := combine s2 s2' in
    to_inverse_renaming
      (List.filter 
         (fun x => match x with (a2, _) => negb (Oset.mem_bool (OAtt T) a2 s1) end) ss2).

Definition rho' (s1 s2 : list attribute) env (t : tuple) :=
  projection T (env_t T env t) (Select_List (_Select_List (rho1' s1 s2 ++ rho2' s1 s2))).

Definition f_join (s1 s2 : list attribute) :=
    let s12 := s1 ++ s2 in
    let s1' := freshes (List.length s1) s12 in
    let s2' := freshes (List.length s2) (s1' ++ s12) in
    let ss1 := combine s1 s1' in
    let ss2 := combine s2 s2' in
    let ss := fold_left
                (fun acc a => match Oset.find (OAtt T) a ss1, Oset.find (OAtt T) a ss2 with
                              | Some b1, Some b2 => (b1, b2) :: acc
                              | _, _ => acc
                              end) s1 nil in
        Sql_Conj_N (dom := query) 
          And_F 
          (map (fun x => 
                  match x with
                  | (b1,b2) => 
                    Sql_Pred _ Pred_Equal (A_Expr (F_Dot b1) ::  A_Expr (F_Dot b2) :: nil)
                  end) ss) (Sql_True _).

Lemma env_g_env_t :
  forall env t, env_g T env Group_Fine (t :: nil) = env_t T env t.
Proof.
intros env t; unfold env_t, env_g; simpl; apply refl_equal.
Qed.

(*
Lemma simplify_renaming : 
  forall ll, 
    att_renaming_item_to_from_item 
      symb aggregate
      (Att_Ren_List
         (map (fun x : attribute * attribute => let (a1, b1) := x in Att_As T a1 b1) ll)) = 
    Select_List (to_direct_renaming ll).
Proof.
intro ll; simpl; rewrite map_map; apply f_equal.
unfold to_direct_renaming; rewrite <- map_eq.
intros [a b] _; apply refl_equal.
Qed.
*)

Lemma one_to_one_renaming_aux :
  forall s s', length s = length s' -> all_diff s -> all_diff s' ->
               forall a b, Oset.find (OAtt T) a (combine s s') = Some b -> 
                           Oset.find (OAtt T) b (combine s' s) = Some a.
Proof.
intros s s' L D D' a b H.
apply Oset.all_diff_fst_find.
- rewrite fst_combine; [assumption | rewrite L; apply le_n].
- rewrite in_combine_swapp; apply (Oset.find_some _ _ _ H).
Qed.

Lemma one_to_one_renaming :
  forall s s', length s = length s' -> all_diff s -> all_diff s' ->
               forall a b, Oset.find (OAtt T) a (combine s s') = Some b <-> 
                           Oset.find (OAtt T) b (combine s' s) = Some a.
Proof.
intros s s' L D D' a b; split; apply one_to_one_renaming_aux; trivial.
apply sym_eq; assumption.
Qed.

Lemma simplify_renaming :
  forall (x : attribute * attribute),
    match (match x with (a, b) => Select_As (A_Expr (F_Dot a)) b end)  with
    | Select_As e a => (a, e)
    end = (snd x, (A_Expr (F_Dot (fst x)))).
Proof.
intros [a b]; simpl; apply refl_equal.
Qed.

Lemma projection_renaming :
  forall env ss t, 
    Oset.permut (OAtt T) (map (@fst _ _) ss) ({{{labels T t}}}) ->
    all_diff (map snd ss) ->
    projection T (env_t T env t) (Select_List (to_direct_renaming T ss)) =t= 
    rename_tuple T (apply_renaming T ss) t.
Proof.
intros env ss t Hp Hd; unfold rename_tuple, apply_renaming, to_direct_renaming, Fset.map; simpl.
assert (Hss : all_diff (map fst ss)).
{
  refine (Oset.all_diff_permut_all_diff _ (Oset.permut_sym Hp)).
  apply Fset.all_diff_elements.
}
rewrite (map_map _ _ ss); apply mk_tuple_eq.
- rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_mk_set; apply Oset.permut_mem_bool_eq; apply Oset.nb_occ_permut; intro b.
  refine (eq_trans _ (Oset.nb_occ_map_eq_3 _ _ _ _ _ (fun x => Oset.permut_nb_occ x Hp) _)).
  rewrite map_map; apply f_equal.
  rewrite <- map_eq; intros [a1 b1] H1; simpl.
  rewrite (Oset.all_diff_fst_find (OAtt T) _ _ _ Hss H1); apply refl_equal.
- intros a Ha Ka; unfold pair_of_select; rewrite map_map.
  rewrite <- (Oset.all_diff_bool_permut_find_map_eq ss (dot T t) Hss Hd Hp a), map_map.
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha; 
    destruct Ha as [[b _a] [_Ha Ha]].
  simpl in _Ha; subst _a.
  assert (Hb : b inS labels T t).
  {
    assert (Hb : In b (map fst ss)).
    {
      rewrite in_map_iff; eexists; split; [ | apply Ha]; trivial.
    }
    apply Fset.in_elements_mem; apply (Oset.in_permut_in (OA := OAtt T) _ Hb Hp).
  }
  unfold default_tuple; rewrite dot_mk_tuple, Fset.empty_spec.
  clear Hp Ka; induction ss as [ | [b1 a1] ss]; simpl; [apply refl_equal | ].
  rewrite Oset.eq_bool_refl.
  case_eq (Oset.eq_bool (OAtt T) a a1); intro Ja; simpl.
  + rewrite Oset.eq_bool_true_iff in Ja; subst a1.
    simpl in Ha; destruct Ha as [Ha | Ha]; 
      [injection Ha; intros; subst; rewrite Hb; apply refl_equal | ].
    apply False_rec.
    rewrite map_unfold, all_diff_unfold in Hd.
    apply ((proj1 Hd) a); [ | apply refl_equal].
    rewrite in_map_iff; eexists; split; [ | apply Ha]; apply refl_equal.
  + simpl in Ha; destruct Ha as [Ha | Ha]; 
      [injection Ha; intros; subst; rewrite Oset.eq_bool_refl in Ja; discriminate Ja | ].
    rewrite all_diff_unfold in Hd, Hss; destruct Hd as [Hd1 Hd2]; destruct Hss as [Hss1 Hss2].
    rewrite IHss; trivial.
    apply match_option_eq; apply f_equal; rewrite <- map_eq.
    intros [_b _a] H; simpl.
    case_eq (Oset.eq_bool (OAtt T) _b b1); intro K; [ | apply refl_equal].
    rewrite Oset.eq_bool_true_iff in K; subst _b.
    apply False_rec; apply (Hss1 b1); [ | apply refl_equal].
    rewrite in_map_iff; eexists; split; [ | apply H]; apply refl_equal.
Qed.

Lemma tuple_renaming_inj : 
  forall env t1 t2 l1 l2 rho,
    length l1 = length l2 -> all_diff l1 -> all_diff l2 ->
    let ll := combine l1 l2 in
    rho = to_direct_renaming T ll ->
    let s := Fset.mk_set (A T) l1 in
    s subS labels T t1 -> s subS labels T t2 ->
    mk_tuple T s (dot T t1) =t= mk_tuple T s (dot T t2) <->
    projection T (env_t T env t1) (Select_List rho) =t= 
    projection T (env_t T env t2) (Select_List rho).
Proof.
intros env t1 t2 l1 l2 rho L D1 D2 ll Hrho s H1 H2.
assert (Hp1 : (Oset.permut (OAtt T) (map fst ll) ({{{labels T (mk_tuple T s (dot T t1))}}}))).
{
  unfold ll, s.
  rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
  rewrite fst_combine; [ | rewrite L; apply le_n].
  apply Fset.permut_elements_mk_set; assumption.
}
assert (D2' : all_diff (map snd ll)).
{
  unfold ll; rewrite snd_combine; [assumption | rewrite L; apply le_n].
}
assert (Hs1 : projection T (env_g T env Group_Fine (t1 :: nil)) (Select_List rho) =t=
          projection T (env_g T env Group_Fine (mk_tuple T s (dot T t1) :: nil)) (Select_List rho)).
{
  rewrite Hrho; unfold to_direct_renaming.
  apply projection_sub.
  - rewrite (Fset.subset_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); apply H1.
  - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
    rewrite dot_mk_tuple, Ha; apply refl_equal.
  - intros a e H; rewrite in_map_iff in H.
    destruct H as [[_a _b] [_H H]]; injection _H; intros; subst.
    unfold s; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_mk_set.
    rewrite Oset.mem_bool_true_iff.
    apply (in_combine_l _ _ _ _ H).
}
rewrite (Oeset.compare_eq_1 _ _ _ _ Hs1); clear Hs1.
assert (Hp2 : (Oset.permut (OAtt T) (map fst ll) ({{{labels T (mk_tuple T s (dot T t2))}}}))).
{
  unfold ll, s.
  rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
  rewrite fst_combine; [ | rewrite L; apply le_n].
  apply Fset.permut_elements_mk_set; assumption.
}
assert (Hs2 : projection T (env_g T env Group_Fine (t2 :: nil)) (Select_List rho) =t=
          projection T (env_g T env Group_Fine (mk_tuple T s (dot T t2) :: nil)) (Select_List rho)).
{
  rewrite Hrho; unfold to_direct_renaming.
  apply projection_sub.
  - rewrite (Fset.subset_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); apply H2.
  - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
    rewrite dot_mk_tuple, Ha; apply refl_equal.
  - intros a e H; rewrite in_map_iff in H.
    destruct H as [[_a _b] [_H H]]; injection _H; intros; subst.
    unfold s; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_mk_set.
    rewrite Oset.mem_bool_true_iff.
    apply (in_combine_l _ _ _ _ H).
}
rewrite (Oeset.compare_eq_2 _ _ _ _ Hs2); clear Hs2.
split; intro H.
- apply projection_eq; env_tac.
- rewrite 2 env_g_env_t, Hrho in H.
  rewrite (Oeset.compare_eq_1 
             _ _ _ _ (projection_renaming env ll (mk_tuple T s (dot T t1)) Hp1 D2')) in H.
  rewrite (Oeset.compare_eq_2 
             _ _ _ _ (projection_renaming env ll (mk_tuple T s (dot T t2)) Hp2 D2')) in H.
  refine ((proj2 (rename_tuple_inj _ _ _ _ _) H)).
  intros a1 a2 Ha1 Ha2; apply all_diff_one_to_one_apply_renaming; trivial.
  + refine (Oset.all_diff_permut_all_diff _ (Oset.permut_sym Hp1)).
    apply Fset.all_diff_elements.
  + refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp1)).
    apply Fset.mem_in_elements; assumption.
  + refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp2)).
    apply Fset.mem_in_elements; assumption.
Qed.

Fixpoint alg_query_to_sql (q : query) : sql_query T relname :=
  match q with
  | Q_Empty_Tuple => 
    Sql_Select 
      (Select_List (_Select_List nil)) 
      (From_Item (Sql_Table _ default_table) (Att_Ren_Star T) :: nil) 
      (Sql_True _) (Group_By nil) (Sql_True _)
  | Q_Empty_Relation s =>
    let witness :=
        Sql_Select
          (Select_List
             (_Select_List
                (map (fun a => Select_As (A_Expr (F_Dot a)) a) (Fset.elements _ s))))
          (From_Item (Sql_Table _ default_table) (Att_Ren_Star T) :: nil)
          (Sql_True _) Group_Fine (Sql_True _) in
    Sql_Set Diff witness witness
  | Q_Table tbl => Sql_Table _ tbl
  | Q_Set op q1 q2 => Sql_Set op (alg_query_to_sql q1) (alg_query_to_sql q2)
  | Q_NaturalJoin q1 q2 => 
    let s1 := Fset.elements _ (sort q1) in
    let s2 := Fset.elements _ (sort q2) in
    let s12 := s1 ++ s2 in
    let s1' := freshes (List.length s1) s12 in
    let s2' := freshes (List.length s2) (s1' ++ s12) in
    let ss1 := combine s1 s1' in
    let ss2 := combine s2 s2' in
    let ss := fold_left
                (fun acc a => match Oset.find (OAtt T) a ss1, Oset.find (OAtt T) a ss2 with
                              | Some b1, Some b2 => (b1, b2) :: acc
                              | _, _ => acc
                              end) s1 nil in
(*    let rho1 := List.map (fun x => match x with (a1,b1) => Att_As T a1 b1 end) ss1 in *)
(*    let rho2 := List.map (fun x => match x with (a2,b2) => Att_As T a2 b2 end) ss2 in *)
    let rho1' := 
        List.map (fun x => match x with (a1,b1) => Select_As (A_Expr (F_Dot b1)) a1 end) ss1 in
    let rho2' := 
        List.map 
          (fun x => match x with (a2,b2) => Select_As (A_Expr (F_Dot b2)) a2 end) 
          (List.filter 
             (fun x => match x with (a2, _) => negb (Oset.mem_bool (OAtt T) a2 s1) end) ss2) in
    let f_join := 
        Sql_Conj_N 
          And_F 
          (map (fun x => 
                  match x with
                  | (a,b) => Sql_Pred _ Pred_Equal (A_Expr (F_Dot a) ::  A_Expr (F_Dot b) :: nil)
                  end) ss) (Sql_True _) in
    Sql_Select 
      (Select_List (_Select_List (rho1' ++ rho2')))
      (From_Item (alg_query_to_sql q1) (Att_Ren_List (to_direct_renaming_att (rho1 s1 s2))) :: 
      From_Item (alg_query_to_sql q2) (Att_Ren_List (to_direct_renaming_att (rho2 s1 s2))) :: nil) 
      f_join Group_Fine (Sql_True _)

  | Q_CrossJoin q1 q2 =>
    Sql_Select
      Select_Star
      (From_Item (alg_query_to_sql q1) (Att_Ren_Star T) ::
       From_Item (alg_query_to_sql q2) (Att_Ren_Star T) :: nil)
      (Sql_True _) Group_Fine (Sql_True _)

  | Q_Pi s q => 
    Sql_Select 
      (Select_List s) 
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (Sql_True _) Group_Fine (Sql_True _)

  | Q_Sigma f q => 
    let alg_formula_to_sql :=
        (fix alg_formula_to_sql f :=
             match f with
             | Sql_Conj a f1 f2 => Sql_Conj a (alg_formula_to_sql f1) (alg_formula_to_sql f2)
             | Sql_Not f => Sql_Not (alg_formula_to_sql f)
             | Sql_True _ => Sql_True _
             | Sql_Pred _ p l => Sql_Pred _ p l
             | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (alg_query_to_sql sq)
             | Sql_In _ s sq => Sql_In _ s (alg_query_to_sql sq)
             | Sql_Exists _ sq => Sql_Exists _ (alg_query_to_sql sq)
             end) in 
    Sql_Select 
      Select_Star
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (alg_formula_to_sql f) Group_Fine (Sql_True _)

  | Q_Gamma s g h q => 
    let alg_formula_to_sql :=
        (fix alg_formula_to_sql f :=
             match f with
             | Sql_Conj a f1 f2 => Sql_Conj a (alg_formula_to_sql f1) (alg_formula_to_sql f2)
             | Sql_Not f => Sql_Not (alg_formula_to_sql f)
             | Sql_True _ => Sql_True _
             | Sql_Pred _ p l => Sql_Pred _ p l
             | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (alg_query_to_sql sq)
             | Sql_In _ s sq => Sql_In _ s (alg_query_to_sql sq)
             | Sql_Exists _ sq => Sql_Exists _ (alg_query_to_sql sq)
             end) in 
    Sql_Select 
      (Select_List s)
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (Sql_True _) (Group_By g) (alg_formula_to_sql h) 
  end.

Fixpoint alg_formula_to_sql f : Formula.sql_formula T (sql_query T relname) :=
  match f with
  | Sql_Conj a f1 f2 => Sql_Conj a (alg_formula_to_sql f1) (alg_formula_to_sql f2)
  | Sql_Not f => Sql_Not (alg_formula_to_sql f)
  | Sql_True _ => Sql_True _
  | Sql_Pred _ p l => Sql_Pred _ p l
  | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (alg_query_to_sql sq)
  | Sql_In _ s sq => Sql_In _ s (alg_query_to_sql sq)
  | Sql_Exists _ sq => Sql_Exists _ (alg_query_to_sql sq)
  end.

Lemma alg_query_to_sql_unfold :
  forall q, alg_query_to_sql q =
  match q with
  | Q_Empty_Tuple => 
    Sql_Select 
      (Select_List (_Select_List nil))
      (From_Item (Sql_Table _ default_table) (Att_Ren_Star T) :: nil) 
      (Sql_True _) (Group_By nil) (Sql_True _)
  | Q_Empty_Relation s =>
    let witness :=
        Sql_Select
          (Select_List
             (_Select_List
                (map (fun a => Select_As (A_Expr (F_Dot a)) a) (Fset.elements _ s))))
          (From_Item (Sql_Table _ default_table) (Att_Ren_Star T) :: nil)
          (Sql_True _) Group_Fine (Sql_True _) in
    Sql_Set Diff witness witness
  | Q_Table tbl => Sql_Table _ tbl
  | Q_Set op q1 q2 => Sql_Set op (alg_query_to_sql q1) (alg_query_to_sql q2)
  | Q_NaturalJoin q1 q2 => 
    let s1 := Fset.elements _ (sort q1) in
    let s2 := Fset.elements _ (sort q2) in
    let s12 := s1 ++ s2 in
    let s1' := freshes (List.length s1) s12 in
    let s2' := freshes (List.length s2) (s1' ++ s12) in
    let ss1 := combine s1 s1' in
    let ss2 := combine s2 s2' in
    let ss := fold_left
                (fun acc a => match Oset.find (OAtt T) a ss1, Oset.find (OAtt T) a ss2 with
                              | Some b1, Some b2 => (b1, b2) :: acc
                              | _, _ => acc
                              end) s1 nil in
(*    let rho1 := List.map (fun x => match x with (a1,b1) => Att_As T a1 b1 end) ss1 in *)
(*    let rho2 := List.map (fun x => match x with (a2,b2) => Att_As T a2 b2 end) ss2 in *)
    let rho1' := 
        List.map (fun x => match x with (a1,b1) => Select_As (A_Expr (F_Dot b1)) a1 end) ss1 in
    let rho2' := 
        List.map 
          (fun x => match x with (a2,b2) => Select_As (A_Expr (F_Dot b2)) a2 end) 
          (List.filter 
             (fun x => match x with (a2, _) => negb (Oset.mem_bool (OAtt T) a2 s1) end) ss2) in
    let f_join := 
        Sql_Conj_N 
          And_F 
          (map (fun x => 
                  match x with
                  | (a,b) => Sql_Pred _ Pred_Equal (A_Expr (F_Dot a) ::  A_Expr (F_Dot b) :: nil)
                  end) ss) (Sql_True _) in
    Sql_Select 
      (Select_List (_Select_List (rho1' ++ rho2')))
      (From_Item (alg_query_to_sql q1) (Att_Ren_List (to_direct_renaming_att (rho1 s1 s2))) :: 
      From_Item (alg_query_to_sql q2) (Att_Ren_List (to_direct_renaming_att (rho2 s1 s2))) :: nil) 
      f_join Group_Fine (Sql_True _)

  | Q_CrossJoin q1 q2 =>
    Sql_Select
      Select_Star
      (From_Item (alg_query_to_sql q1) (Att_Ren_Star T) ::
       From_Item (alg_query_to_sql q2) (Att_Ren_Star T) :: nil)
      (Sql_True _) Group_Fine (Sql_True _)

  | Q_Pi s q => 
    Sql_Select 
      (Select_List s) 
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (Sql_True _) Group_Fine (Sql_True _)

  | Q_Sigma f q => 
    Sql_Select 
      Select_Star
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (alg_formula_to_sql f) Group_Fine (Sql_True _)

  | Q_Gamma s g h q => 
    Sql_Select 
      (Select_List s)
      (From_Item (alg_query_to_sql q) (Att_Ren_Star T) :: nil) 
      (Sql_True _) (Group_By g) (alg_formula_to_sql h) 
  end.
Proof.
intro q; case q; intros; apply refl_equal.
Qed.

Lemma alg_formula_to_sql_unfold :
  forall f, alg_formula_to_sql f =
  match f with
  | Sql_Conj a f1 f2 => Sql_Conj a (alg_formula_to_sql f1) (alg_formula_to_sql f2)
  | Sql_Not f => Sql_Not (alg_formula_to_sql f)
  | Sql_True _ => Sql_True _
  | Sql_Pred _ p l => Sql_Pred _ p l
  | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (alg_query_to_sql sq)
  | Sql_In _ s sq => Sql_In _ s (alg_query_to_sql sq)
  | Sql_Exists _ sq => Sql_Exists _ (alg_query_to_sql sq)
  end.
Proof.
intros f; case f; intros; apply refl_equal.
Qed.

Lemma length_freshes :
  forall n l, length (freshes n l) = n.
Proof.
intro n; induction n as [ | n]; intro l; [apply refl_equal | ].
simpl; rewrite app_length, IHn; simpl.
rewrite plus_comm; apply refl_equal.
Qed.

Lemma all_diff_freshes :
  forall n l, all_diff (freshes n l).
Proof.
intro n; induction n as [ | n]; intro l; simpl; [trivial | ].
rewrite <- all_diff_app_iff; split; [apply IHn | ].
split; [simpl; trivial | ].
intros a Ha Ka.
simpl in Ka; destruct Ka as [Ka | Ka]; [ | contradiction Ka].
assert (Abs := fresh_is_fresh (freshes n l ++ l)).
rewrite Oset.mem_bool_app, Bool.Bool.orb_false_iff in Abs.
rewrite Ka in Abs.
assert (Abs' : false = true).
{
  rewrite <- (proj1 Abs), Oset.mem_bool_true_iff; assumption.
}
discriminate Abs'.
Qed.

Lemma freshes_are_fresh :
  forall a n l,  In a (freshes n l) -> In a l -> False.
Proof.
intros a n; induction n as [ | n]; intros l H1 H2; simpl in H1.
- contradiction H1.
- destruct (in_app_or _ _ _ H1) as [H3 | H3].
  + apply (IHn _ H3 H2).
  + simpl in H3; destruct H3 as [H3 | H3]; [ | contradiction H3].
    subst a.
    assert (Abs := fresh_is_fresh ((freshes n l ++ l))).
    rewrite <- (Oset.mem_bool_true_iff (OAtt T)) in H2.
    rewrite Oset.mem_bool_app, H2, Bool.orb_true_r in Abs.
    discriminate Abs.
Qed.

Lemma sql_sort_sql_to_alg : 
  forall q, sql_sort basesort (alg_query_to_sql q) =S= sort q.
Proof.
intro q; set (n := tree_size (tree_of_query q)).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert q Hn; induction n as [ | n]; [intros q Hn; destruct q; inversion Hn | ].
intros q Hn; destruct q as [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | [s] q | f q | [s] g f q].
- apply Fset.equal_refl.  
- rewrite alg_query_to_sql_unfold; simpl.
  rewrite Fset.equal_spec; intro a.
  rewrite eq_bool_iff, Fset.mem_mk_set, Fset.mem_elements.
  rewrite 2 Oset.mem_bool_true_iff.
  split; intro H.
  + rewrite in_map_iff in H.
    destruct H as [p [Hp Hp_in]].
    rewrite in_map_iff in Hp_in.
    destruct Hp_in as [sel [Hsel Hsel_in]].
    rewrite in_map_iff in Hsel_in.
    destruct Hsel_in as [a0 [Ha0 Ha0_in]].
    subst sel; simpl in Hsel; subst p; simpl in Hp; subst a; exact Ha0_in.
  + rewrite in_map_iff.
    exists (A_Expr (F_Dot a), a); split; [apply refl_equal | ].
    rewrite in_map_iff.
    exists (Select_As (A_Expr (F_Dot a)) a); split; [apply refl_equal | ].
    rewrite in_map_iff; exists a; split; [apply refl_equal | assumption].
- apply Fset.equal_refl.  
- simpl; change (sql_sort basesort (alg_query_to_sql q1) =S= sort q1); apply IHn.
  simpl in Hn.
  refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); apply le_plus_l.
- simpl.
  unfold select_as_as_pair.
  rewrite map_map, map_app, 2 map_map.
  rewrite Fset.equal_spec; intro a.
  rewrite Fset.mem_mk_set, Oset.mem_bool_app, Fset.mem_union.
  rewrite 2 Fset.mem_elements.
  set (l1 := Fset.elements _ (sort q1)) in *.
  set (l2 := Fset.elements _ (sort q2)) in *.
  clearbody l1 l2.
  assert (Hl1 :  forall a, Oset.mem_bool (OAtt T) a
    (map
       (fun x : attribute * attribute =>
        snd
          match (match x with (a1, b1) => 
                              @Select_As T (A_Expr (F_Dot b1)) a1 end) with
          | Select_As e a0 => (e, a0)
          end) (combine l1 (freshes (length l1) (l1 ++ l2)))) = Oset.mem_bool (OAtt T) a l1).
  {
    set (l := (freshes (length l1) (l1 ++ l2))).
    assert (Hl : length l = length l1).
    {
      subst l; rewrite length_freshes; apply refl_equal.
    }
    clearbody l; clear a.
    intro a; revert l Hl; induction l1 as [ | a1 l1]; intros l Hl; [apply refl_equal | ].
    destruct l as [ | _a l]; [discriminate Hl | ].
    simpl combine; rewrite (map_unfold _ (_ :: _)), (Oset.mem_bool_unfold _ _ (_ :: _)).
    simpl; apply f_equal; apply IHl1.
    simpl in Hl; injection Hl; exact (fun h => h).
  }
  rewrite Hl1; clear Hl1.  
  case_eq (Oset.mem_bool (OAtt T) a l1); intro Ha; 
    [apply refl_equal | rewrite 2 Bool.Bool.orb_false_l].
  set (l := (freshes (length l2) (freshes (length l1) (l1 ++ l2) ++ l1 ++ l2))).
  assert (Hl : length l = length l2).
  {
    subst l; rewrite length_freshes; apply refl_equal.
  }
  clearbody l.
  revert l Hl; induction l2 as [ | a2 l2]; intros l Hl; [apply refl_equal | ].
  destruct l as [ | _a l]; [discriminate Hl | ].
  simpl combine; rewrite filter_unfold, (Oset.mem_bool_unfold _ _ (_ :: _)).
  simpl in Hl; injection Hl; clear Hl; intro Hl.
  case_eq (Oset.compare (OAtt T) a a2); intro Ka.
  + rewrite Oset.compare_eq_iff in Ka; subst a2.
    rewrite Ha; simpl.
    rewrite Oset.eq_bool_refl; apply refl_equal.
  + case_eq (Oset.mem_bool (OAtt T) a2 l1); intro Ha2; simpl.
    * apply IHl2; trivial.
    * unfold Oset.eq_bool; rewrite Ka; apply IHl2; trivial.
	  + case_eq (Oset.mem_bool (OAtt T) a2 l1); intro Ha2; simpl.
	    * apply IHl2; trivial.
	    * unfold Oset.eq_bool; rewrite Ka; apply IHl2; trivial.
- rewrite alg_query_to_sql_unfold, sql_sort_unfold, sort_unfold.
  rewrite 2 map_unfold, Fset.Union_unfold.
  rewrite 2 sql_from_item_sort_unfold, Fset.Union_unfold.
  apply Fset.union_eq.
  + apply IHn.
    simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_plus_l.
  + rewrite Fset.Union_unfold; simpl.
    rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_empty_r _ _)).
    apply IHn.
    simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    refine (le_trans _ _ _ _ (le_plus_r _ _)).
    apply le_plus_l.
- rewrite alg_query_to_sql_unfold, sql_sort_unfold, sort_unfold.
  unfold select_as_as_pair; rewrite map_map.
  rewrite Fset.equal_spec; intro a; do 2 apply f_equal.
  rewrite <- map_eq; intros [ ] _; apply refl_equal.
- rewrite alg_query_to_sql_unfold, sql_sort_unfold, sort_unfold.
  rewrite 2 map_unfold, 2 Fset.Union_unfold.
  rewrite sql_from_item_sort_unfold.
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_empty_r _ _)).
  apply IHn.
  simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
  refine (le_trans _ _ _ _ (le_plus_r _ _)).
  apply le_plus_l.  
- rewrite alg_query_to_sql_unfold, sql_sort_unfold, sort_unfold.
  unfold select_as_as_pair; rewrite map_map.
  rewrite Fset.equal_spec; intro a; do 2 apply f_equal.
  rewrite <- map_eq; intros [ ] _; apply refl_equal.
Qed.

Ltac tuple_tac :=
  match goal with
    | |- ?x =t= ?x => apply Oeset.compare_eq_refl
    | |- ?x =S= ?x => apply Fset.equal_refl
    | |- context G[_ =S= labels _ (mk_tuple _ _ _)] =>
           rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _))
    | |- context G[labels _ (mk_tuple _ _ _) =S= _] =>
           rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _))
    | |- context G[_ inS? (labels _ (mk_tuple _ _ _))] =>
           rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _))
    | |- context G[_ inS? (labels _ (mk_tuple _ _ _))] =>
            rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _))
    | |- context G[_ inS? (labels _ (mk_tuple _ _ _))] =>
            rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _))
    | H : ?a inS ?s
      |- context G[dot T (mk_tuple _ ?s _) ?a] =>
      rewrite dot_mk_tuple; [ | apply H]
    | H : ?a inS ?s
      |- context G[dot T (mk_tuple _ (Fset.mk_set _ (Fset.elements _ ?s)) _) ?a] =>
      rewrite dot_mk_tuple; 
      [ | rewrite (Fset.mem_eq_2 _ _ _ (Fset.mk_set_idem _ _)); apply H]

    | H : ?a inS ?s
      |- context G[dot T (mk_tuple _ ?s _) ?a] =>
      rewrite dot_mk_tuple; [ | apply H]

    | |- context G[match Fset.mem _ ?x ?s with true => _ | false => _ end] => 
      case_eq (?x inS? ?s)
end.

Ltac bug_tac :=
  match goal with
  | |- (match Fset.mem _ ?x ?s with true => _ | false => _ end) = _ => 
      case_eq (?x inS? ?s)
  end.

Lemma partition_default :
  Febag.elements BTupleT
    (Febag.filter BTupleT 
       (fun _ : tuple => Bool.is_true (B T) (Bool.true (B T)))
       (N_join_bag T 
          (Febag.map BTupleT BTupleT (fun t0 : tuple => t0) (instance default_table)
                     :: nil))) <> nil.
Proof.
unfold Febag.map; rewrite map_id; [ | intros; apply refl_equal].
case_eq (Febag.elements _ (instance default_table)).
- intro H; apply False_rec.
  rewrite <- Bool.Bool.not_true_iff_false in default_table_not_empty; 
    apply default_table_not_empty.
  rewrite Febag.is_empty_spec, Febag.nb_occ_equal.
  intro t; rewrite Febag.nb_occ_elements, H, Febag.nb_occ_empty; apply refl_equal.
- intros x l H K.
  assert (Abs : Oeset.mem_bool (OTuple T) x nil = true).
  {
    rewrite <- K, <- Febag.mem_unfold, Febag.mem_filter; [ | intros; apply refl_equal].
    rewrite Bool.Bool.andb_true_iff; split; [ | apply Bool.true_is_true; apply refl_equal].
    unfold N_join_bag; rewrite Febag.mem_mk_bag; simpl.
    assert (Abs : Oeset.mem_bool (OTuple T) x 
                                 (Febag.elements _ (x addBE Febag.mk_bag BTupleT l)) = true).
    {
      rewrite <- Febag.mem_unfold.
      apply Febag.nb_occ_mem.
      rewrite Febag.nb_occ_add, Oeset.eq_bool_refl.
      destruct (Febag.nb_occ BTupleT x (Febag.mk_bag BTupleT l)); discriminate.
    }
    set (k := Febag.elements BTupleT (x addBE Febag.mk_bag BTupleT l)) in *.
    clearbody k.
    induction k as [ | x1 k]; [discriminate Abs | ].
    simpl in Abs.
    case_eq ( Oeset.eq_bool (OTuple T) x x1); intro Hx1; rewrite Hx1 in Abs.
    - simpl; rewrite Bool.Bool.orb_true_iff; left.
      rewrite Oeset.eq_bool_true_compare_eq in Hx1.
      rewrite Oeset.eq_bool_true_compare_eq, (Oeset.compare_eq_1 _ _ _ _ Hx1).
      rewrite (Oeset.compare_eq_2 _ _ _ _ (join_tuple_empty_2 _ _)).
      apply Oeset.compare_eq_refl.
    - simpl; rewrite Bool.Bool.orb_true_iff; right.
      apply IHk; assumption.
  }
  discriminate Abs.
Qed.   

Lemma alg_query_to_sql_is_sound_etc :
  well_sorted_sql_table T basesort instance ->
  forall n, 
  (forall env q, tree_size (tree_of_query q) <= n -> 
     eval_query env q =BE= eval_sql_query env (alg_query_to_sql q)) /\
  (forall env f, 
     tree_size (tree_of_sql_formula tree_of_query f) <= n -> 
     eval_sql_formula eval_query env f =
     eval_sql_formula eval_sql_query env (alg_formula_to_sql f)).
Proof.
intros W n; induction n as [ | n]; split.
- intros env q Hn; destruct q; inversion Hn.
- intros env f Hn; destruct f; inversion Hn.
- intros env [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | s q | f q | s g h q] Hn.
  + rewrite Febag.nb_occ_equal; intro t; simpl.
    simpl.
    rewrite filter_true; [ | intros; rewrite Bool.true_is_true; apply refl_equal].
    rewrite Febag.nb_occ_singleton, Febag.nb_occ_mk_bag; simpl.
    rewrite (partition_cst (mk_olists (OVal T)) (fun _ : tuple => nil) (c := nil));
    [ | intros; apply refl_equal].
    assert (Aux := partition_default).
    set (l := Febag.elements BTupleT
              (Febag.filter BTupleT (fun _ : tuple => Bool.is_true (B T) (Bool.true (B T)))
                 (N_join_bag T
                    (Febag.map BTupleT BTupleT (fun t0 : tuple => t0) (instance default_table)
                     :: nil)))) in *.
    destruct l; [apply False_rec; apply Aux; apply refl_equal | ].
    simpl; rewrite N.add_0_r; unfold Oeset.eq_bool.
    assert (Aux2 : empty_tuple T =t= 
                   mk_tuple T (emptysetS) 
                            (fun a : attribute => dot T (default_tuple T (emptysetS)) a)).
    {
      unfold empty_tuple, default_tuple.
      apply mk_tuple_eq_2; intros a Ha.
      rewrite Fset.empty_spec in Ha; discriminate Ha.
    }
	    rewrite <- (Oeset.compare_eq_2 _ _ _ _ Aux2).
	    case (Oeset.compare (OTuple T) t (empty_tuple T)); apply refl_equal.
  + rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    rewrite Febag.nb_occ_equal; intro t.
    rewrite Febag.nb_occ_empty; simpl.
    rewrite Fset.equal_refl.
    rewrite Febag.nb_occ_diff, N.sub_diag.
    apply refl_equal.
  + rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    rewrite Febag.nb_occ_equal; intros; apply refl_equal.
  + rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    rewrite (Fset.equal_eq_1 _ _ _ _ (sql_sort_sql_to_alg _)),
    (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
    case_eq (sort q1 =S?= sort q2); [ | rewrite Febag.nb_occ_equal; intros; apply refl_equal].
    intro Hs.
    assert (IH1 :  eval_query env q1 =BE= eval_sql_query env (alg_query_to_sql q1)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 :  eval_query env q2 =BE= eval_sql_query env (alg_query_to_sql q2)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    destruct o; simpl; rewrite Febag.nb_occ_equal; intro t.
    * rewrite 2 Febag.nb_occ_union, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_union_max, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_inter, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_diff, IH1, IH2; apply refl_equal.
  + assert (IH1 :  eval_query env q1 =BE= eval_sql_query env (alg_query_to_sql q1)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 :  eval_query env q2 =BE= eval_sql_query env (alg_query_to_sql q2)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite Febag.nb_occ_equal, eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    cbv beta iota zeta.
    intro t.
    set (s1 := {{{sort q1}}}).
    set (s2 := {{{sort q2}}}).
    set (s12 := s1 ++ s2).
    set (s1' := freshes (length s1) s12).
    set (s2' := freshes (length s2) (s1' ++ s12)) in *.
    set (ss1 := combine s1 s1') in *.
    set (ss2 := combine s2 s2') in *.
    set (ss :=
         fold_left
           (fun (acc : list (attribute * attribute)) (a : attribute) =>
            match Oset.find (OAtt T) a ss1 with
            | Some b1 =>
                match Oset.find (OAtt T) a ss2 with
                | Some b2 => (b1, b2) :: acc
                | None => acc
                end
            | None => acc
            end) s1 nil) in *.
    rewrite (filter_true
               (fun g : list tuple =>
                  Bool.is_true (B T)
                               (eval_sql_formula eval_sql_query (env_g T env Group_Fine g)
                                                 (Sql_True (sql_query T relname)))));
      [ | intros; simpl; rewrite Bool.true_is_true; apply refl_equal].
    unfold FlatData.make_groups; rewrite map_map.
    set (f_join := Sql_Conj_N And_F
                         (map
                            (fun x : attribute * attribute =>
                             let (a, b) := x in
                             Sql_Pred (sql_query T relname) Pred_Equal
                               (A_Expr (F_Dot a) :: A_Expr (F_Dot b) :: nil)) ss)
                         (Sql_True (sql_query T relname))).
    assert (Hs1 : map fst ss1 = s1).
    {
      unfold ss1; rewrite fst_combine; [apply refl_equal | ].
      unfold s1'; rewrite length_freshes; apply le_n.
    }
    assert (Hs2 : map fst ss2 = s2).
    {
      unfold ss2; rewrite fst_combine; [apply refl_equal | ].
      unfold s2'; rewrite length_freshes; apply le_n.
    }
    assert (Hs1' : map snd ss1 = s1').
    {
      unfold ss1; rewrite snd_combine; [apply refl_equal | ].
      unfold s1'; rewrite length_freshes; apply le_n.
    }
    assert (Hs2' : map snd ss2 = s2').
    {
      unfold ss2; rewrite snd_combine; [apply refl_equal | ].
      unfold s2'; rewrite length_freshes; apply le_n.
    }
    rewrite 2 (map_unfold _ (_ :: _)), (map_unfold _ nil).
    rewrite 2 eval_sql_from_item_unfold.
    unfold Febag.map.
    rewrite Febag.nb_occ_mk_bag.
    set (l1 := Febag.elements BTupleT (eval_sql_query env (alg_query_to_sql q1))).
    set (l2 := Febag.elements BTupleT (eval_sql_query env (alg_query_to_sql q2))).
    set (l1' := Febag.elements BTupleT (eval_query env q1)).
    set (l2' := Febag.elements BTupleT (eval_query env q2)).
    rewrite (natural_join_list_eq T l1' l2' l1 l2);
      [ | unfold l1, l1'; intro x; rewrite <- 2 Febag.nb_occ_elements;
          rewrite Febag.nb_occ_equal in IH1; apply IH1 
        | unfold l2, l2'; intro x; rewrite <- 2 Febag.nb_occ_elements;
          rewrite Febag.nb_occ_equal in IH2; apply IH2].
    assert (Hdss : all_diff
           (map snd
              (ss1 ++
               filter
                 (fun x : attribute * attribute =>
                  let (a2, _) := x in negb (Oset.mem_bool (OAtt T) a2 s1)) ss2))).
    {
      rewrite map_app, <- all_diff_app_iff; repeat split.
      - rewrite Hs1'; apply all_diff_freshes.
      - apply all_diff_map_filter.
        rewrite Hs2'; apply all_diff_freshes.
      - intros a Ha Ka; rewrite Hs1' in Ha.
        rewrite in_map_iff in Ka.
        destruct Ka as [[b _a] [_Ka Ka]]; simpl in _Ka; subst _a.
        rewrite filter_In in Ka.
        destruct Ka as [Ka _].
        unfold ss2, s2' in Ka.
        assert (Aux3 := in_combine_r _ _ _ _ Ka).
        apply (freshes_are_fresh _ _ _ Aux3).
        apply in_or_app; left; assumption.
    }
    assert (Aux : 
        Oeset.nb_occ (OTuple T) t (natural_join_list T l1 l2) =
        Oeset.nb_occ (OTuple T) t
          (map
             (fun x : tuple =>
              mk_tuple T (sort q1 unionS sort q2)
                (fun a : attribute =>
                 dot T x
                   (apply_renaming T
                      (rho1 ({{{sort q1}}}) ({{{sort q2}}}) ++
                       filter
                         (fun x0 : attribute * attribute =>
                          negb
                            (Oset.mem_bool (OAtt T) (fst x0)
                               (map fst (rho1 ({{{sort q1}}}) ({{{sort q2}}})))))
                         (rho2 ({{{sort q1}}}) ({{{sort q2}}}))) a)))
             (filter
                (fun x : tuple =>
                 Fset.for_all (A T)
                   (fun a : attribute =>
                    Oset.eq_bool (OVal T)
                      (dot T x (apply_renaming T (rho1 ({{{sort q1}}}) ({{{sort q2}}})) a))
                      (dot T x (apply_renaming T (rho2 ({{{sort q1}}}) ({{{sort q2}}})) a)))
                   (sort q1 interS sort q2))
                (natural_join_list T
                   (map
                      (rename_tuple T (apply_renaming T (rho1 ({{{sort q1}}}) ({{{sort q2}}}))))
                      l1)
                   (map
                      (rename_tuple T (apply_renaming T (rho2 ({{{sort q1}}}) ({{{sort q2}}}))))
                      l2))))).
    {
      apply rename_join; fold s1 s2 s12 s1' s2' ss1 ss2.
      - unfold rho1; fold s1 s2 s12 s1' s2' ss1 ss2.
        rewrite Hs1; apply _permut_refl; intros; apply Oset.compare_eq_refl.
      - unfold rho2; fold s1 s2 s12 s1' s2' ss1 ss2.
        rewrite Hs2; apply _permut_refl; intros; apply Oset.compare_eq_refl.
      - intros u1 Hu1; rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
        apply (proj1 (well_sorted_sql_query_etc
                                  unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
        apply Febag.in_elements_mem; apply Hu1.
      - intros u2 Hu2; rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
        apply (proj1 (well_sorted_sql_query_etc
                                  unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
        apply Febag.in_elements_mem; apply Hu2.
      - unfold rho1; fold s1 s2 s12 s1' s2' ss1 ss2.
        rewrite Hs1; apply Fset.all_diff_elements.
      - unfold rho2; fold s1 s2 s12 s1' s2' ss1 ss2.
        rewrite Hs2; apply Fset.all_diff_elements.
      - rewrite map_app.
        unfold rho1; rewrite snd_combine; [ | rewrite length_freshes; apply le_n].
        unfold rho2; rewrite snd_combine; [ | rewrite length_freshes; apply le_n].
        rewrite <- all_diff_app_iff; repeat split.
        + apply all_diff_freshes.
        + apply all_diff_freshes.
        + fold s1; fold s2.
          intros a Ha Ka; apply (freshes_are_fresh a _ _ Ka).
          apply in_or_app; left; assumption.
    }
    rewrite Aux; rewrite Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T)).
    * intros x1 x2 Hx1 Hx.
      assert (_Hx : equiv_env T (env_g T env Group_Fine (x1 :: nil)) 
                              (env_g T env Group_Fine (x2 :: nil))); [env_tac | ].
      refine (Oeset.compare_eq_trans _ _ _ _ _ (projection_eq _ _ _ _ _Hx)); clear _Hx Hx.
      rewrite <- map_app, <- to_direct_renaming_unfold_alt.
      unfold projection; rewrite tuple_eq; split_tac.
      -- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
         rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
         unfold to_direct_renaming; rewrite !map_map, map_app.
         rewrite Fset.equal_spec; intro a; unfold sort_of_select_list.
         rewrite !map_app, !map_map, Fset.mem_mk_set_app, Fset.mem_union.
         case_eq (a inS? sort q1); intro Ha.
         ++ assert (Ka := Fset.mem_in_elements _ _ _ Ha); fold s1 in Ka; rewrite <- Hs1 in Ka.
            rewrite in_map_iff in Ka; destruct Ka as [[_a b] [H K]].
            simpl in H; subst _a.
            rewrite Bool.Bool.orb_true_l; apply sym_eq.
            rewrite Bool.Bool.orb_true_iff; left; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff.
            rewrite in_map_iff.
            eexists; split; [ | apply K]; apply refl_equal.
         ++ assert (Aux2 : a inS? Fset.mk_set (A T)
                             (map
                                (fun x : attribute * attribute =>
                                   match
                                     (let (a0, b) := let (x0, x3) := x in 
                                                     (x3, x0) in Select_As (A_Expr (F_Dot a0)) b)
                                   with
                                   | Select_As _ a1 => a1
                                   end) ss1) = false).
            {
              rewrite Fset.mem_mk_set, <- Ha, Fset.mem_elements; fold s1; rewrite <- Hs1.
              apply f_equal; rewrite <- map_eq; intros [] _; apply refl_equal.
            }
            rewrite Aux2, !Bool.Bool.orb_false_l.
            rewrite Fset.mem_elements; fold s2; rewrite <- Hs2, Fset.mem_mk_set.
            case_eq (Oset.mem_bool (OAtt T) a (map fst ss2)); intro Ka; apply sym_eq.
            ** rewrite Oset.mem_bool_true_iff, in_map_iff in Ka.
               destruct Ka as [[_a b] [_Ka Ka]]; simpl in _Ka; subst _a.
               rewrite Oset.mem_bool_true_iff, in_map_iff.
               eexists (a, b); split; [apply refl_equal | ].
               rewrite filter_In; split; [apply Ka | ].
               unfold s1; rewrite <- Fset.mem_elements, Ha; apply refl_equal.
            ** rewrite <- not_true_iff_false in Ka.
               rewrite <- not_true_iff_false; intro Ja; apply Ka.
               rewrite Oset.mem_bool_true_iff, in_map_iff in Ja.
               destruct Ja as [[_a b] [_Ja Ja]]; subst _a.
               rewrite filter_In in Ja; destruct Ja as [Ja _].
               rewrite Oset.mem_bool_true_iff, in_map_iff.
               eexists; split; [ | apply Ja]; apply refl_equal.
      -- intros a Ha; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)) in H.
         rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)) in H.
         rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
         rewrite 2 dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ H), Ha.
         fold s1 s2; unfold rho1, rho2; fold s12 s1' s2' ss1 ss2; rewrite Hs1.
         unfold apply_renaming, to_direct_renaming; rewrite !map_map.
         assert (Aux2 : (ss1 ++
                            filter (fun x0  => negb (Oset.mem_bool (OAtt T) (fst x0) s1)) ss2) =
                       ss1 ++
                           filter
                           (fun x : attribute * attribute =>
                              let (a2, _) := x in negb (Oset.mem_bool (OAtt T) a2 s1)) ss2).
         {
           apply f_equal; apply filter_eq.
           intros [a1 a2] _; apply refl_equal.
         }
         rewrite <- Aux2.
         rewrite (Fset.mem_eq_2 _ _ _ H) in Ha; unfold to_direct_renaming in Ha.
         rewrite !map_map, <- Aux2 in Ha.
         set (ll := ss1 ++ filter (fun x0 => negb (Oset.mem_bool (OAtt T) (fst x0) s1)) ss2) in *.
         assert (Hll : forall a b, In (a, b) ll -> b inS labels T x1).
         {
           unfold ll; intros a1 b1 H1.
           rewrite Oeset.mem_bool_true_iff in Hx1.
           destruct Hx1 as [y1 [Hx1 Hy1]]; rewrite tuple_eq in Hx1;
             rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)).
           rewrite filter_In in Hy1; destruct Hy1 as [Hy1 _].
           unfold natural_join_list in Hy1; rewrite in_theta_join_list in Hy1.
           destruct Hy1 as [z1 [z2 [Hz1 [Hz2 [_ Hy1]]]]]; rewrite Hy1.
           unfold join_tuple; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
           rewrite in_map_iff in Hz1; destruct Hz1 as [u1 [Hz1 Hu1]]; rewrite <- Hz1.
           rewrite in_map_iff in Hz2; destruct Hz2 as [u2 [Hz2 Hu2]]; rewrite <- Hz2.
           unfold rename_tuple;
             rewrite Fset.mem_union, 2 (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
           assert (Ku1 : labels T u1 =S= sort q1).
           {
             rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
             apply (proj1 (well_sorted_sql_query_etc
                             unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
             apply Febag.in_elements_mem; apply Hu1.
           }
           assert (Ku2 : labels T u2 =S= sort q2).
           {
             rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
             apply (proj1 (well_sorted_sql_query_etc
                             unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
             apply Febag.in_elements_mem; apply Hu2.
           }
           unfold Fset.map.
           rewrite (Fset.elements_spec1 _ _ _ Ku1), (Fset.elements_spec1 _ _ _ Ku2).
           fold s1 s2; unfold rho1, rho2.
           fold s12 s1' s2' ss1 ss2.
           rewrite 2 Fset.mem_mk_set, Bool.Bool.orb_true_iff.
           destruct (in_app_or _ _ _ H1) as [H2 | H2].
           - left; rewrite Oset.mem_bool_true_iff, in_map_iff.
             exists a1; split.
             + apply apply_renaming_att; [rewrite Hs1; apply Fset.all_diff_elements | assumption].
             + rewrite <- Hs1, in_map_iff.
               eexists; split; [ | apply H2]; apply refl_equal.
           - right; rewrite Oset.mem_bool_true_iff, in_map_iff.
             rewrite filter_In in H2.
             exists a1; split.
             + apply apply_renaming_att; [rewrite Hs2; apply Fset.all_diff_elements |].
               apply (proj1 H2).
             + rewrite <- Hs2, in_map_iff.
               eexists; split; [ | apply (proj1 H2)]; apply refl_equal.
         }
         clearbody ll; clear Aux2; induction ll as [ | [a1 b1] ll]; simpl; simpl in Ha;
           [rewrite Fset.empty_spec in Ha; discriminate Ha | ].
         rewrite Fset.add_spec in Ha.
         case_eq (Oset.eq_bool (OAtt T) a a1).
         ++ rewrite Oset.eq_bool_true_iff; intro; subst a1; simpl.
            rewrite (Hll _ _ (or_introl _ (refl_equal _))); apply refl_equal.
         ++ intro Ka; rewrite Ka in Ha; apply IHll; trivial.
            intros _a _b _H; apply (Hll _a); right; assumption.
    * clear t Aux.
      fold s1 s2; unfold rho1, rho2; fold s12 s1' s2' ss1 ss2.
      assert (Aux : 
                forall t, 
                  labels T t =S= (Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1) unionS
                                 Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2)) ->
                Fset.for_all 
                    (A T)
                    (fun a : attribute =>
                       Oset.eq_bool (OVal T) (dot T t (apply_renaming T ss1 a))
                                    (dot T t (apply_renaming T ss2 a))) 
                    (sort q1 interS sort q2) =
                  Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_t T env t) f_join)).
      {
        intros t Ht; apply eq_bool_iff.
        rewrite Fset.for_all_spec, forallb_forall, Bool.true_is_true; split.
        - intros H; unfold f_join; rewrite eval_Sql_Conj_N_And_F.
          split; [apply refl_equal | ].
          intros f Hf; rewrite in_map_iff in Hf.
          destruct Hf as [[a b] [_Hf Hf]]; subst f.
          rewrite eval_sql_formula_unfold, !(map_unfold _ (_ :: _)), (map_unfold _ nil).
          rewrite interp_Pred_Equal; simpl.
          unfold ss in Hf.
          assert (Aux : exists c, Oset.find (OAtt T) c ss1 = Some a /\ 
                                       Oset.find (OAtt T) c ss2 = Some b).
          {
            assert (Aux : (exists c, Oset.find (OAtt T) c ss1 = Some a /\ 
                                     Oset.find (OAtt T) c ss2 = Some b) \/ In (a, b) nil).
            revert Hf; generalize (@nil (attribute * attribute)).
            generalize s1; intro l; induction l as [ | a1 l]; intros _l1 Hl1; simpl in Hl1.
            - right; assumption.
            - destruct (IHl _ Hl1) as [[c [H1 H2]] | H1].
              + left; exists c; split; trivial.
              + case_eq (Oset.find (OAtt T) a1 ss1).
                * intros c1 Hc1; rewrite Hc1 in H1.
                  case_eq (Oset.find (OAtt T) a1 ss2).
                  -- intros c2 Hc2; rewrite Hc2 in H1.
                     simpl in H1; destruct H1 as [H1 | H1].
                     ++ injection H1; clear H1; do 2 intro; subst c1 c2.
                        left; exists a1; split; trivial.
                     ++ right; assumption.
                  -- intro Kc1; rewrite Kc1 in H1.
                     right; assumption.
                * intro Kc1; rewrite Kc1 in H1.
                  right; assumption.
            - destruct Aux as [Aux | Aux]; [assumption | contradiction Aux].
          }
          destruct Aux as [c [H1 H2]].
          assert (K1 := Oset.find_some _ _ _ H1); unfold ss1 in K1.
          generalize (in_combine_r _ _ _ _ K1); clear K1; intro K1; unfold s1' in K1.
          rewrite <- (Oset.mem_bool_true_iff (OAtt T)) in K1.
          assert (K2 := Oset.find_some _ _ _ H2); unfold ss2 in K2.
          generalize (in_combine_r _ _ _ _ K2); clear K2; intro K2; unfold s2' in K2.
          rewrite <- (Oset.mem_bool_true_iff (OAtt T)) in K2.
          assert (K1' : Oset.mem_bool (OAtt T) b s1' = false).
          {
            rewrite <- not_true_iff_false; intro K1'.
            apply (freshes_are_fresh b (length s2) (s1' ++ s12)).
            - rewrite <- (Oset.mem_bool_true_iff (OAtt T)); apply K2.
            - apply in_or_app; left.
              rewrite <- (Oset.mem_bool_true_iff (OAtt T)); apply K1'.
          }
          fold s12 s1' s2' in K1, K2.
          assert (Hc :  
                    Oset.eq_bool 
                      (OVal T) 
                      (dot T t (apply_renaming T (rho1 ({{{sort q1}}}) ({{{sort q2}}})) c))
                      (dot T t (apply_renaming T (rho2 ({{{sort q1}}}) ({{{sort q2}}})) c)) = 
                    true).
          {
            apply H.
            apply Fset.mem_in_elements; rewrite Fset.mem_inter, Bool.Bool.andb_true_iff; split.
            - apply Fset.in_elements_mem; fold s1; rewrite <- Hs1; rewrite in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H1)]; apply refl_equal.
            - apply Fset.in_elements_mem; fold s2; rewrite <- Hs2; rewrite in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H2)]; apply refl_equal.
          }
          fold s1 s2 in Hc; unfold rho1, rho2 in Hc.
          fold s12 s1' s2' ss1 ss2 in Hc; unfold apply_renaming in Hc.
          rewrite H1, H2 in Hc.
          assert (Ha : a inS labels T t).
          {
            rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Bool.Bool.orb_true_iff; left.
            unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
            exists c; split.
            - unfold apply_renaming; rewrite H1; apply refl_equal.
            - fold s1; rewrite <- Hs1, in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H1)]; apply refl_equal.
          }
          assert (Hb : b inS labels T t).
          {
            rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Bool.Bool.orb_true_iff; right.
            unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
            exists c; split.
            - unfold apply_renaming; rewrite H2; apply refl_equal.
            - fold s2; rewrite <- Hs2, in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H2)]; apply refl_equal.
          }
          rewrite Ha, Hb, Hc; apply refl_equal.
        - unfold f_join; rewrite eval_Sql_Conj_N_And_F; intros [_ Hf] c Hc.
          case_eq (Oset.find (OAtt T) c ss1);
            [ | intro Abs; apply False_rec; apply (Oset.find_none_alt _ _ _ Abs); 
                rewrite Hs1; rewrite Fset.elements_inter in Hc; apply (proj1 Hc)].
          intros a H1.
          case_eq (Oset.find (OAtt T) c ss2);
            [ | intro Abs; apply False_rec; apply (Oset.find_none_alt _ _ _ Abs); 
                rewrite Hs2; rewrite Fset.elements_inter in Hc; apply (proj2 Hc)].
          intros b H2.
          assert (H : In (a, b) ss); unfold ss.
          {
            assert (Aux : forall l0 a1 b1, 
                       (In (a1, b1) l0 \/ (In c (map fst ss1) /\
                          Oset.find (OAtt T) c ss1 = Some a1 /\ 
                          Oset.find (OAtt T) c ss2 = Some b1)) -> 
                       In (a1, b1) (fold_left
                                      (fun (acc : list (attribute * attribute)) (a0 : attribute) =>
                                         match Oset.find (OAtt T) a0 ss1 with
                                         | Some b1 =>
                                           match Oset.find (OAtt T) a0 ss2 with
                                           | Some b2 => (b1, b2) :: acc
                                           | None => acc
                                           end
                                         | None => acc
                                         end) s1 l0)).
            {
              intros l0 a1 b1; rewrite <- Hs1.
              revert l0.
              generalize ss1 at 1 4.
              intro ll; induction ll as [ | [a2 b2] ll]; intros l0 H; simpl.
              - destruct H as [H | H]; [assumption | ].
                contradiction (proj1 H).
              - apply IHll.
                destruct H as [H | H].
                + left; case (Oset.find (OAtt T) a2 ss1); intros; [ | assumption].
                  case (Oset.find (OAtt T) a2 ss2); intros; [right |]; assumption.
                + simpl in H.
                  destruct H as [[K1 | K1] [K2 K3]].
                  * subst a2; rewrite K2, K3; left; left; apply refl_equal.
                  * right; repeat split; assumption.
            }
            apply Aux; right; repeat split; trivial.
            rewrite in_map_iff; eexists; split; [ | apply (Oset.find_some _ _ _ H1)]; 
              apply refl_equal.
          }
          assert (H' : let f :=  Sql_Pred (sql_query T relname) Pred_Equal
                                          (A_Expr (F_Dot a) :: A_Expr (F_Dot b) :: nil) in
                      eval_sql_formula eval_sql_query (env_t T env t) f = Bool.true (B T)). 
          {
            intro f; apply Hf; rewrite in_map_iff.
            eexists; split; [ | apply H]; apply refl_equal.
          }
          simpl in H'; rewrite interp_Pred_Equal in H'.
          assert (Ha : a inS labels T t).
          {
            rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Bool.Bool.orb_true_iff; left.
            unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
            exists c; split.
            - unfold apply_renaming; rewrite H1; apply refl_equal.
            - fold s1; rewrite <- Hs1, in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H1)]; apply refl_equal.
          }
          assert (Hb : b inS labels T t).
          {
            rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Bool.Bool.orb_true_iff; right.
            unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
            exists c; split.
            - unfold apply_renaming; rewrite H2; apply refl_equal.
            - fold s2; rewrite <- Hs2, in_map_iff.
              eexists; split; [ | apply (Oset.find_some _ _ _ H2)]; apply refl_equal.
          }
          rewrite Ha, Hb in H'.
          unfold apply_renaming; simpl; rewrite  H1, H2.
          case_eq (Oset.eq_bool (OVal T) (dot T t a) (dot T t b));
            [intros; apply refl_equal | intro Abs; rewrite Abs in H'].
          apply False_rec; apply (Bool.true_diff_false (B T) (sym_eq H')).
      }
      intro t; rewrite <- Febag.nb_occ_elements, Febag.nb_occ_filter;
      [ | intros; apply f_equal; apply eval_sql_formula_eq; [assumption | env_tac]].
      rewrite Oeset.nb_occ_filter.
      -- assert (Hl1 : forall t0 : tuple, In t0 l1 -> labels T t0 =S= (sort q1)).
         {
           intros x1 Hx1.
           rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
           apply (proj1 (well_sorted_sql_query_etc
                           unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
           unfold l1 in Hx1.
           rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
           exists x1; split; [apply Oeset.compare_eq_refl | ].
           assumption.
         }
         assert (Hrl1 : forall t0 : tuple,
                    In t0 (map (rename_tuple T (apply_renaming T ss1)) l1) ->
                    labels T t0 =S= Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1)).
         {
           intros u1 Hu1.
           rewrite in_map_iff in Hu1.
           destruct Hu1 as [x1 [Hu1 Hx1]].
           rewrite <- Hu1; unfold rename_tuple.
           rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
           unfold Fset.map.
           rewrite (Fset.elements_spec1 _ _ _ (Hl1 _ Hx1)); apply Fset.equal_refl.
         }
         assert (Hl2 : forall t0 : tuple, In t0 l2 -> labels T t0 =S= (sort q2)).
         {
           intros x2 Hx2.
           rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
           apply (proj1 (well_sorted_sql_query_etc
                           unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
           unfold l2 in Hx2.
           rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
           exists x2; split; [apply Oeset.compare_eq_refl | ].
           assumption.
         }
         assert (Hrl2 : forall t0 : tuple,
                    In t0 (map (rename_tuple T (apply_renaming T ss2)) l2) ->
                    labels T t0 =S= Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2)).
         {
           intros u2 Hu2.
           rewrite in_map_iff in Hu2.
           destruct Hu2 as [x2 [Hu2 Hx2]].
           rewrite <- Hu2; unfold rename_tuple.
           rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
           unfold Fset.map.
           rewrite (Fset.elements_spec1 _ _ _ (Hl2 _ Hx2)); apply Fset.equal_refl.
         }
         case_eq (labels T t =S?=
                      (Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1)
                                unionS Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2))); 
           intro Ht.
         ++ rewrite (Aux _ Ht).
            case (Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_t T env t) f_join));
              [rewrite N.mul_1_r | rewrite N.mul_0_r; apply refl_equal].
            set (k1 := map
                         (fun t0 : tuple =>
                            projection T
                              (env_t T env t0)
                              (att_renaming_item_to_from_item 
                                 (Att_Ren_List (to_direct_renaming_att ss1))))
                         l1) in *.
            set (k2 := map
                         (fun t0 : tuple =>
                            projection T
                              (env_t T env t0)
                              (att_renaming_item_to_from_item 
                                 (Att_Ren_List (to_direct_renaming_att ss2))))
                         l2) in *.
            unfold N_join_bag; rewrite !(map_unfold _ (_ :: _)), (map_unfold _ nil).
            rewrite N_join_list_unfold, Febag.nb_occ_mk_bag.
            unfold brute_left_join_list.
            assert (Aux2 : Oeset.permut 
                             (OTuple T)
                             (theta_join_list 
                                tuple (join_tuple T) (fun _ _ : tuple => true)
                                (Febag.elements BTupleT (Febag.mk_bag BTupleT k1))
                                (N_join_list 
                                   tuple (join_tuple T) (empty_tuple T)
                                   (Febag.elements BTupleT (Febag.mk_bag BTupleT k2) :: nil)))
                             (theta_join_list tuple (join_tuple T) 
                                              (fun _ _ : tuple => true) k1 k2)).
               {
                 apply (theta_join_list_permut_eq 
                          _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
                          (fun _ _ => true) (fun _ _ _ _ _ _ => refl_equal _)
                          (Febag.elements BTupleT (Febag.mk_bag BTupleT k1)) k1
                          _ k2);
                   apply Oeset.nb_occ_permut; intro.
                 - rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag; apply refl_equal.
                 - rewrite (Oeset.permut_nb_occ 
                              _ (Oeset.permut_refl_alt
                                   _ _ _ (N_join_list_1 
                                            _ (OTuple T) (join_tuple T) (empty_tuple T)
                                            (Febag.elements BTupleT (Febag.mk_bag BTupleT k2)) 
                                            (join_tuple_empty_2 T)))).
                rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag.
                apply refl_equal.
               }
               rewrite (Oeset.permut_nb_occ _ Aux2).
               apply trans_eq with (Oeset.nb_occ (OTuple T) t (natural_join_list T k1 k2)).
               ** apply natural_join_list_eq.
                  --- intro t1; unfold k1; apply sym_eq.
                      apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T)).
                      +++ intros x1 x2 Hx1 Hx.
                          refine (Oeset.compare_eq_trans 
                                    _ _ _ _ _ (projection_renaming env _ _ _ _)).
                          *** assert (Aux3 : equiv_env T (env_t T env x1) (env_t T env x2)); 
                                [env_tac | ].
                              refine (Oeset.compare_eq_trans 
                                        _ _ _ _ (projection_eq T _ _ _ Aux3) _).
                              apply Oeset.compare_eq_refl_alt; apply f_equal.
                              unfold att_renaming_item_to_from_item, to_direct_renaming_att, 
                         to_direct_renaming; do 2 apply f_equal; rewrite map_map, <- map_eq.
                              intros [] _; apply refl_equal.
                          *** rewrite tuple_eq in Hx; 
                                rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)).
                              assert (Kx1 : labels T x1 =S= sort q1).
                              {
                                rewrite Oeset.mem_bool_true_iff in Hx1.
                                destruct Hx1 as [y1 [Hx1 Hy1]].
                                rewrite tuple_eq in Hx1.
                                rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Hx1)).
                                apply Hl1; assumption.
                              }
                              rewrite (Fset.elements_spec1 _ _ _ Kx1); fold s1; rewrite Hs1.
                              apply _permut_refl; intros; apply Oset.compare_eq_refl.
                          *** rewrite Hs1'; apply all_diff_freshes.
                      +++ intros; apply refl_equal.
                  --- intro t2; unfold k2; apply sym_eq.
                      apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T)).
                      +++ intros x1 x2 Hx1 Hx.
                          refine (Oeset.compare_eq_trans 
                                    _ _ _ _ _ (projection_renaming env _ _ _ _)).
                          *** assert (Aux3 : equiv_env T (env_t T env x1) (env_t T env x2)); 
                                [env_tac | ].
                              refine (Oeset.compare_eq_trans 
                                        _ _ _ _ (projection_eq T _ _ _ Aux3) _).
                              apply Oeset.compare_eq_refl_alt; apply f_equal.
                              unfold att_renaming_item_to_from_item, to_direct_renaming_att, 
                              to_direct_renaming; do 2 apply f_equal; rewrite map_map, <- map_eq.
                              intros [] _; apply refl_equal.
                          *** rewrite tuple_eq in Hx; 
                                rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)).
                              assert (Kx1 : labels T x1 =S= sort q2).
                              {
                                rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
                                apply (proj1 (well_sorted_sql_query_etc
                                                unknown _ contains_nulls_eq W _) _ (le_n _)) 
                                  with env.
                                unfold l2 in Hx1; rewrite <- Febag.mem_unfold in Hx1; apply Hx1.
                              }
                              rewrite (Fset.elements_spec1 _ _ _ Kx1); fold s2; rewrite Hs2.
                              apply _permut_refl; intros; apply Oset.compare_eq_refl.
                          *** rewrite Hs2'; apply all_diff_freshes.
                      +++ intros; apply refl_equal.
            ** unfold natural_join_list.
               apply f_equal; apply theta_join_list_eq_1.
               intros t1 t2 Ht1 Ht2; rewrite join_compatible_tuple_alt.
               intros a Ha Ka.
               unfold k1 in Ht1; unfold k2 in Ht2; rewrite in_map_iff in Ht1, Ht2.
               destruct Ht1 as [u1 [Ht1 Hu1]]; destruct Ht2 as [u2 [Ht2 Hu2]].
               rewrite <- Ht1 in Ha; rewrite <- Ht2 in Ka.
               unfold projection in Ha, Ka; simpl in Ha, Ka.
               rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
               rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ka.
               unfold to_direct_renaming, to_direct_renaming_att in Ha, Ka; 
                 rewrite !map_map, Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha; 
                 rewrite !map_map, Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ka.
               destruct Ha as [[b1 _a] [_Ha Ha]]; simpl in _Ha; subst _a.
               destruct Ka as [[b2 _a] [_Ka Ka]]; simpl in _Ka; subst _a.
               unfold ss1 in Ha; assert (Ha' := in_combine_r _ _ _ _ Ha).
               unfold ss2 in Ka; assert (Ka' := in_combine_r _ _ _ _ Ka).
               unfold s2' in Ka'.
               apply False_rec; apply (freshes_are_fresh _ _ _ Ka');
                 apply in_or_app; left; assumption.
         ++ apply trans_eq with 0%N.
            ** rewrite (nb_occ_natural_join_list T _ _
                       (Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1))
                       (Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2))), Ht, N.mul_0_r;
               trivial.
               case (Fset.for_all 
                       (A T)
                       (fun a : attribute =>
                               Oset.eq_bool (OVal T) (dot T t (apply_renaming T ss1 a))
                                            (dot T t (apply_renaming T ss2 a))) 
                            (sort q1 interS sort q2)); apply refl_equal.
            ** case (Bool.is_true (B T) (eval_sql_formula eval_sql_query (env_t T env t) f_join));
                 [ | rewrite N.mul_0_r; apply refl_equal].
               rewrite N.mul_1_r.
               unfold N_join_bag; rewrite Febag.nb_occ_mk_bag.
               case_eq (Oeset.nb_occ (OTuple T) t
    (N_join_list tuple (join_tuple T) (empty_tuple T)
       (map (Febag.elements BTupleT)
          (Febag.mk_bag BTupleT
             (map
                (fun t0 : tuple =>
                 projection T (env_t T env t0)
                   (att_renaming_item_to_from_item (Att_Ren_List (to_direct_renaming_att ss1))))
                l1)
           :: Febag.mk_bag BTupleT
                (map
                   (fun t0 : tuple =>
                    projection T (env_t T env t0)
                      (att_renaming_item_to_from_item (Att_Ren_List (to_direct_renaming_att ss2))))
                   l2) :: nil)))); [intros; apply refl_equal | ].
               intros p Hp.
               assert (Abs : Oeset.mem_bool (OTuple T) t
         (N_join_list tuple (join_tuple T) (empty_tuple T)
            (map (Febag.elements BTupleT)
               (Febag.mk_bag BTupleT
                  (map
                     (fun t0 : tuple =>
                      projection T (env_t T env t0)
                        (att_renaming_item_to_from_item
                           (Att_Ren_List (to_direct_renaming_att ss1)))) l1)
                :: Febag.mk_bag BTupleT
                     (map
                        (fun t0 : tuple =>
                         projection T (env_t T env t0)
                           (att_renaming_item_to_from_item
                              (Att_Ren_List (to_direct_renaming_att ss2)))) l2) :: nil))) = true).
               {
                 apply Oeset.nb_occ_mem; rewrite Hp; discriminate.
               }
               rewrite Oeset.mem_bool_true_iff in Abs.
               destruct Abs as [t' [Kt Abs]].
               rewrite in_N_join_list in Abs.
               destruct Abs as [llt [K1 [K2 K3]]].
               destruct llt as [ | [k1 u1] llt]; [discriminate K2 | ].
               destruct llt as [ | [k2 u2] llt]; [discriminate K2 | ].
               destruct llt as [ | [k3 u3] llt]; [ | discriminate K2].
               rewrite (map_unfold _ (_ :: _)), !(map_unfold fst) in K2; simpl fst in K2.
               assert (Dummy : forall (C : Type) (x1 x2 : C) l1 l2, x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2).
               {
                 intros C x1 x2 _k1 _k2 H; injection H; split; trivial.
               }
               assert (Kl1 := proj1 (Dummy _ _ _ _ _ K2)).
               assert (Kl2 := proj1 (Dummy _ _ _ _ _ (proj2 (Dummy _ _ _ _ _ K2)))).
               assert (Hu1 := K1 _ _ (or_introl _ (refl_equal _))); rewrite Kl1 in Hu1.
               assert (Hu2 := K1 _ _ (or_intror _ (or_introl _ (refl_equal _)))); 
                 rewrite Kl2 in Hu2.
               simpl in K3.
               rewrite tuple_eq in Kt; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Kt)) in Ht.
               rewrite K3 in Ht.
               unfold join_tuple at 1 in Ht; 
                 rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)) in Ht.
               revert Ht; intro Ht.
               assert (Ku1 : labels T u1 =S= 
                             Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1)).
               {
                 assert (Ku1 : Oeset.mem_bool (OTuple T) u1 (Febag.elements BTupleT
             (Febag.mk_bag BTupleT
                (map
                   (fun t0 : tuple =>
                    projection T (env_t T env t0)
                      (att_renaming_item_to_from_item (Att_Ren_List (to_direct_renaming_att ss1))))
                   l1))) = true).
                 {
                   rewrite Oeset.mem_bool_true_iff; exists u1; split; [ | trivial].
                   apply Oeset.compare_eq_refl.
                 }
                 rewrite <- Febag.mem_unfold, Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ku1.
                 destruct Ku1 as [u1' [Ku1 Hu1']].
                 rewrite tuple_eq in Ku1; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ku1)).
                 rewrite in_map_iff in Hu1'.
                 destruct Hu1' as [u1'' [Ku1' Hu1'']]; rewrite <- Ku1'.
                 unfold projection, to_direct_renaming_att, apply_renaming; simpl.
                 rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), !map_map.
                 unfold Fset.map; fold s1; rewrite <- Hs1, map_map.
                 apply Fset.equal_refl_alt; apply f_equal.
                 rewrite <- map_eq; intros [a b] H; simpl.
                 assert (Aux2 : all_diff (map fst ss1)).
                 {
                   rewrite Hs1; apply Fset.all_diff_elements.
                 }
                 rewrite <- (apply_renaming_att T ss1 Aux2 _ _ H); apply refl_equal.
               }
               assert (Ku2 : labels T u2 =S= 
                             Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2)).
               {
                 assert (Ku2 : Oeset.mem_bool (OTuple T) u2 (Febag.elements BTupleT
             (Febag.mk_bag BTupleT
                (map
                   (fun t0 : tuple =>
                    projection T (env_t T env t0)
                      (att_renaming_item_to_from_item (Att_Ren_List (to_direct_renaming_att ss2))))
                   l2))) = true).
                 {
                   rewrite Oeset.mem_bool_true_iff; exists u2; split; [ | trivial].
                   apply Oeset.compare_eq_refl.
                 }
                 rewrite <- Febag.mem_unfold, Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ku2.
                 destruct Ku2 as [u2' [Ku2 Hu2']].
                 rewrite tuple_eq in Ku2; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ku2)).
                 rewrite in_map_iff in Hu2'.
                 destruct Hu2' as [u2'' [Ku2' Hu2'']]; rewrite <- Ku2'.
                 unfold projection, to_direct_renaming_att, apply_renaming; simpl.
                 rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), !map_map.
                 unfold Fset.map; fold s2; rewrite <- Hs2, map_map.
                 apply Fset.equal_refl_alt; apply f_equal.
                 rewrite <- map_eq; intros [a b] H; simpl.
                 assert (Aux2 : all_diff (map fst ss2)).
                 {
                   rewrite Hs2; apply Fset.all_diff_elements.
                 }
                 rewrite <- (apply_renaming_att T ss2 Aux2 _ _ H); apply refl_equal.
               }
               rewrite <- (Fset.equal_eq_2 _ _ _ _ (Fset.union_eq _ _ _ _ _ Ku1 Ku2)) in Ht.
               unfold join_tuple, empty_tuple in Ht.
               rewrite (Fset.equal_eq_1 
                          _ _ _ _ (Fset.union_eq_2 _ _ _ _ (labels_mk_tuple _ _ _))) in Ht.
               rewrite (Fset.equal_eq_1
                          _ _ _ _ (Fset.union_eq_2 
                                     _ _ _ _ (Fset.union_eq_2 
                                                _ _ _ _ (labels_mk_tuple _ _ _)))) in Ht.
               rewrite (Fset.equal_eq_1 
                          _ _ _ _ (Fset.union_eq_2 
                                     _ _ _ _ (Fset.union_empty_r _ _))) in Ht.
               rewrite Fset.equal_refl in Ht; discriminate Ht.
      -- intros x1 x2 Hx1 Hx.
         rewrite 2 Fset.for_all_spec; apply forallb_eq.
         intros a Ha.
         assert (Kx1 := Oeset.mem_nb_occ _ _ _ Hx1);
           rewrite (nb_occ_natural_join_list T _ _
                       (Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1))
                       (Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2))) in Kx1.
         ++ case_eq (labels T x1 =S?=
           (Fset.map (A T) (A T) (apply_renaming T ss1) (sort q1)
            unionS Fset.map (A T) (A T) (apply_renaming T ss2) (sort q2)));
              intro Jx1; rewrite Jx1 in Kx1;
            [ | rewrite N.mul_0_r in Kx1; apply False_rec; apply Kx1; apply refl_equal].
            rewrite tuple_eq in Hx.
            apply f_equal2; apply Hx; 
              rewrite (Fset.mem_eq_2 _ _ _ Jx1), Fset.mem_union, Bool.Bool.orb_true_iff;
              [left | right]; 
              unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff;
                (exists a; split; [apply refl_equal | ]).
            ** rewrite Fset.elements_inter in Ha; apply (proj1 Ha).
            ** rewrite Fset.elements_inter in Ha; apply (proj2 Ha).
         ++ intros x _Hx; rewrite in_map_iff in _Hx.
            destruct _Hx as [y [_Hx Hy]]; rewrite <- _Hx.
            unfold rename_tuple.
            rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); unfold Fset.map.
            apply Fset.equal_refl_alt; do 2 apply f_equal.
            apply Fset.elements_spec1.
            rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
            apply (proj1 (well_sorted_sql_query_etc
                            unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
            unfold l1 in Hy.
            rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
            exists y; split; [ | assumption].
            apply Oeset.compare_eq_refl.
         ++ intros x _Hx; rewrite in_map_iff in _Hx.
            destruct _Hx as [y [_Hx Hy]]; rewrite <- _Hx.
            unfold rename_tuple.
            rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); unfold Fset.map.
            apply Fset.equal_refl_alt; do 2 apply f_equal.
            apply Fset.elements_spec1.
            rewrite <- (Fset.equal_eq_2 _ _ _ _ (sql_sort_sql_to_alg _)).
            apply (proj1 (well_sorted_sql_query_etc
                            unknown _ contains_nulls_eq W _) _ (le_n _)) with env.
	            unfold l2 in Hy.
	            rewrite Febag.mem_unfold, Oeset.mem_bool_true_iff.
	            exists y; split; [ | assumption].
	            apply Oeset.compare_eq_refl.
  + assert (IH1 :  eval_query env q1 =BE= eval_sql_query env (alg_query_to_sql q1)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    }
    assert (IH2 :  eval_query env q2 =BE= eval_sql_query env (alg_query_to_sql q2)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    cbv beta iota zeta.
    rewrite Febag.nb_occ_equal; intro t.
    rewrite Febag.nb_occ_mk_bag.
    rewrite filter_true; [ | intros; simpl; rewrite Bool.true_is_true; apply refl_equal].
    unfold FlatData.make_groups; rewrite map_map.
    rewrite Febag.nb_occ_mk_bag.
    unfold N_join_bag; rewrite !(map_unfold _ (_ :: _)), (map_unfold _ nil).
    rewrite N_join_list_unfold.
    unfold brute_left_join_list.
    assert (Hstar :
              forall b,
                Febag.map BTupleT BTupleT
                  (fun t0 : tuple =>
                     projection T (env_t T env t0)
                       (att_renaming_item_to_from_item (Att_Ren_Star T))) b =BE= b).
    {
      intro b; unfold Febag.map; rewrite Febag.nb_occ_equal; intro u.
      rewrite Febag.nb_occ_mk_bag.
      rewrite Febag.nb_occ_elements.
      transitivity
        (Oeset.nb_occ (OTuple T) u
           (map (fun z : tuple => z) (Febag.elements BTupleT b))).
      - apply (Oeset.nb_occ_map_eq_2_3_alt
                 (OTuple T) (OTuple T)
                 (fun t0 : tuple =>
                    projection T (env_t T env t0)
                      (att_renaming_item_to_from_item (Att_Ren_Star T)))
                 (fun z : tuple => z)
                 (Febag.elements BTupleT b) (Febag.elements BTupleT b)).
        + intros x1 x2 Hx1 Hx; simpl; apply Hx.
        + intro x; apply refl_equal.
      - rewrite map_id; [apply refl_equal | intros; apply refl_equal].
    }
    apply trans_eq with
      (Oeset.nb_occ (OTuple T) t
        (theta_join_list tuple (join_tuple T) (fun _ _ : tuple => true)
          (Febag.elements BTupleT (eval_sql_query env (alg_query_to_sql q1)))
          (Febag.elements BTupleT (eval_sql_query env (alg_query_to_sql q2))))).
    * apply Oeset.permut_nb_occ.
      apply (theta_join_list_permut_eq
               _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
               (fun _ _ : tuple => true) (fun _ _ _ _ _ _ => refl_equal _)).
      -- apply Oeset.nb_occ_permut; intro u.
         rewrite <- 2 Febag.nb_occ_elements.
         rewrite Febag.nb_occ_equal in IH1; apply IH1.
      -- apply Oeset.nb_occ_permut; intro u.
         rewrite <- 2 Febag.nb_occ_elements.
         rewrite Febag.nb_occ_equal in IH2; apply IH2.
    * apply sym_eq.
      match goal with
      | |- Oeset.nb_occ _ _ (map _ _) = Oeset.nb_occ _ _ ?l2 =>
          replace l2 with (map (fun z : tuple => z) l2)
            by (rewrite map_id; [apply refl_equal | intros; apply refl_equal])
      end.
      apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T) (OTuple T)).
      -- intros x1 x2 Hx1 Hx.
         rewrite env_g_env_t.
         simpl.
         apply Hx.
      -- intro u; rewrite <- Febag.nb_occ_elements.
         assert (Hfilter :=
                   @Febag.filter_true_alt _ _ BTupleT (B T)
                     (Febag.mk_bag BTupleT
                        (theta_join_list tuple (join_tuple T)
                           (fun _ _ : tuple => true)
                           (Febag.elements BTupleT
                              (eval_sql_from_item env
                                 (From_Item (alg_query_to_sql q1) (Att_Ren_Star T))))
                           (N_join_list tuple (join_tuple T) (empty_tuple T)
                              (Febag.elements BTupleT
                                 (eval_sql_from_item env
                                    (From_Item (alg_query_to_sql q2) (Att_Ren_Star T)))
                               :: map (Febag.elements BTupleT) nil))))).
         rewrite Febag.nb_occ_equal in Hfilter.
         rewrite Hfilter.
         rewrite Febag.nb_occ_mk_bag.
         apply Oeset.permut_nb_occ.
         apply (theta_join_list_permut_eq
                  _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
                  (fun _ _ : tuple => true) (fun _ _ _ _ _ _ => refl_equal _)).
         ++ rewrite eval_sql_from_item_unfold.
            apply Oeset.nb_occ_permut; intro u0.
            rewrite <- 2 Febag.nb_occ_elements.
            assert (Hs := Hstar (eval_sql_query env (alg_query_to_sql q1))).
            rewrite Febag.nb_occ_equal in Hs; apply Hs.
         ++ rewrite eval_sql_from_item_unfold.
            apply Oeset.nb_occ_permut; intro u0.
            transitivity
              (Oeset.nb_occ (OTuple T) u0
                 (Febag.elements BTupleT
                    (Febag.map BTupleT BTupleT
                       (fun t0 : tuple =>
                          projection T (env_t T env t0)
                            (att_renaming_item_to_from_item (Att_Ren_Star T)))
                       (eval_sql_query env (alg_query_to_sql q2))))).
            ** apply Oeset.permut_nb_occ.
               apply Oeset.permut_refl_alt.
               apply N_join_list_1.
               apply join_tuple_empty_2.
            ** rewrite <- 2 Febag.nb_occ_elements.
               assert (Hs := Hstar (eval_sql_query env (alg_query_to_sql q2))).
               rewrite Febag.nb_occ_equal in Hs; apply Hs.
	  + assert (IH :  eval_query env q =BE= eval_sql_query env (alg_query_to_sql q)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    cbv beta iota zeta.
    rewrite Febag.nb_occ_equal; intro t.
    unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
    rewrite filter_true; [ | simpl; intros; apply Bool.true_is_true; apply refl_equal].
    unfold FlatData.make_groups; rewrite map_map.
    apply (Oeset.nb_occ_map_eq_2_3_alt (OTuple T)).
    * intros x1 x2 Hx1 Hx; rewrite env_g_env_t; apply projection_eq; env_tac.
    * clear t; intro t.
      rewrite <- 2 Febag.nb_occ_elements, Febag.nb_occ_filter;
        [simpl | intros; apply refl_equal].
      assert (Dummy := refl_equal (Bool.true (B T))); rewrite <- Bool.true_is_true in Dummy.
      rewrite Dummy, N.mul_1_r; unfold N_join_bag.
      rewrite (map_unfold _ (_ ::_)), (map_unfold _ nil).
      rewrite Febag.nb_occ_mk_bag, (Oeset.permut_nb_occ 
                              _ (Oeset.permut_refl_alt
                                   _ _ _ (N_join_list_1 
                                            _ (OTuple T) (join_tuple T) (empty_tuple T)
                                            _ 
                                            (join_tuple_empty_2 T)))).
      rewrite <- Febag.nb_occ_elements; simpl.
      unfold Febag.map; rewrite map_id; [ | intros; apply refl_equal].
      rewrite Febag.nb_occ_mk_bag, <- Febag.nb_occ_elements.
      apply Febag.nb_occ_equal; assumption.
  + assert (IH :  eval_query env q =BE= eval_sql_query env (alg_query_to_sql q)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    cbv beta iota zeta.
    rewrite Febag.nb_occ_equal; intro t.
    rewrite Febag.nb_occ_filter, Febag.nb_occ_mk_bag.
    * unfold FlatData.make_groups.
      rewrite filter_map, map_map; simpl.
      rewrite map_id; [ | intros; apply refl_equal].
      assert (Dummy := refl_equal (Bool.true (B T))); rewrite <- Bool.true_is_true in Dummy.
      rewrite filter_true; [ | intros; apply Dummy].
      rewrite <- Febag.nb_occ_elements, Febag.nb_occ_filter.
      -- apply f_equal2.
         ++ unfold N_join_bag.
            rewrite (map_unfold _ (_ ::_)), (map_unfold _ nil).
            rewrite Febag.nb_occ_mk_bag, (Oeset.permut_nb_occ 
                                            _ (Oeset.permut_refl_alt
                                                 _ _ _ (N_join_list_1 
                                            _ (OTuple T) (join_tuple T) (empty_tuple T)
                                            _ 
                                            (join_tuple_empty_2 T)))).
            rewrite <- Febag.nb_occ_elements; simpl.
            unfold Febag.map; rewrite map_id; [ | intros; apply refl_equal].
            rewrite Febag.nb_occ_mk_bag, <- Febag.nb_occ_elements.
            apply Febag.nb_occ_equal; assumption.
         ++ apply if_eq; trivial.
            apply f_equal; apply (proj2 IHn).
            simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
      -- intros; apply f_equal.
         apply eval_sql_formula_eq; trivial.
         env_tac.
    * intros; apply f_equal.
      apply eval_sql_formula_eq_etc with relname tree_of_query n; trivial.
      -- intros; apply eval_query_eq; trivial.
      -- simpl in Hn; refine (le_trans _ _ _ _ Hn).
         apply le_S.
         apply le_plus_l.
      -- env_tac.
  + assert (IH :  eval_query env q =BE= eval_sql_query env (alg_query_to_sql q)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    }
    rewrite eval_query_unfold, alg_query_to_sql_unfold, eval_sql_query_unfold.
    cbv beta iota zeta.
    rewrite Febag.nb_occ_equal; intro t.
    rewrite 2 Febag.nb_occ_mk_bag.
    apply Oeset.nb_occ_map_eq_2_3_alt with (OLTuple T).
    * intros; apply projection_eq; env_tac.
    * clear t; intro t.
      rewrite 2 Oeset.nb_occ_filter.
      -- apply if_eq.
         ++ apply f_equal; apply (proj2 IHn).
            simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
            apply le_plus_l.
         ++ intro Ht; unfold FlatData.make_groups; simpl.
            apply Oeset.permut_nb_occ.
            apply snd_partition_eq.
            ** intros; rewrite <- map_eq; intros; apply interp_aggterm_eq; env_tac.
            ** apply Oeset.nb_occ_permut.
               intro u; rewrite <- !Febag.nb_occ_elements, Febag.nb_occ_filter;
                 [ | intros; apply refl_equal].
               assert (Aux := refl_equal ( Bool.true (B T))).
               rewrite <- Bool.true_is_true in Aux; rewrite Aux, N.mul_1_r, N_join_bag_1.
               unfold Febag.map.
               rewrite Febag.nb_occ_mk_bag, map_id; [ | intros; apply refl_equal].
               rewrite <- !Febag.nb_occ_elements; revert u.
               rewrite <- Febag.nb_occ_equal; apply IH.
         ++ intros; apply refl_equal.
      -- intros; apply f_equal; apply eval_sql_formula_eq; env_tac.
      -- intros; apply f_equal; apply eval_formula_eq; env_tac.
- intros env f Hn; destruct f as [ | | | | | | ].
  + rewrite alg_formula_to_sql_unfold, 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Conj _ _ _)).
    apply f_equal2.
    * apply (proj2 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_plus_l.
    * apply (proj2 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
  + rewrite alg_formula_to_sql_unfold, 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Not _)).
    apply f_equal.
    apply (proj2 IHn).
    simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply le_plus_l.
  + apply refl_equal.
  + apply refl_equal. 
  + rewrite alg_formula_to_sql_unfold, 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Quant _ _ _ _ _)).
    cbv beta iota zeta.
    apply interp_quant_eq with (OTuple T).
    * apply Oeset.nb_occ_permut.
      intro t; rewrite <- 2 Febag.nb_occ_elements; revert t; rewrite <- Febag.nb_occ_equal.
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S; apply le_S.
      refine (le_trans _ _ _ _ (le_plus_l _ _)).
      apply le_plus_l.
    * intros x1 x2 Hx1 Hx; rewrite tuple_eq in Hx.
      rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)).
      apply f_equal; apply f_equal.
      rewrite <- map_eq.
      intros a Ha; apply (proj2 Hx).
      apply Fset.in_elements_mem; assumption.
  + rewrite alg_formula_to_sql_unfold, 2 (eval_sql_formula_unfold _ _ _ _ (Sql_In _ _ _)).
    cbv beta iota zeta.
    apply interp_quant_eq with (OTuple T).
    * apply Oeset.nb_occ_permut.
      intro t; rewrite <- 2 Febag.nb_occ_elements; revert t; rewrite <- Febag.nb_occ_equal.
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S; apply le_S.
      refine (le_trans _ _ _ _ (le_plus_l _ _)).
      refine (le_trans _ _ _ _ (le_plus_r _ _)).
      apply le_plus_l.
    * intros x1 x2 Hx1 Hx.
      rewrite <- (Oeset.compare_eq_2 _ _ _ _ Hx), <- (contains_nulls_eq _ _ Hx).
      apply refl_equal.
  + rewrite alg_formula_to_sql_unfold, 2 (eval_sql_formula_unfold _ _ _ _ (Sql_Exists _ _)).
    cbv beta iota zeta.
    apply if_eq; trivial.
    rewrite eq_bool_iff, 2 Febag.is_empty_spec.
    assert (IH : eval_query env q =BE= eval_sql_query env (alg_query_to_sql q)).
    {
      apply (proj1 IHn).
      simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
      apply le_S.
      refine (le_trans _ _ _ _ (le_plus_l _ _)).
      apply le_plus_l.
    }
    split; intro H.
    * rewrite <- (Febag.equal_eq_1 _ _ _ _ IH); assumption.
    * rewrite (Febag.equal_eq_1 _ _ _ _ IH); assumption.
Qed.

(* Lemma tuple_fresh_renaming :
  forall env t l1 l2 rho rho',
    length l1 = length l2 -> all_diff l2 ->
    let ll := combine l1 l2 in
    rho = List.map (fun x => match x with (a,b) => Select_As T (A_Expr (F_Dot a)) b end) ll ->
    rho' = List.map (fun x => match x with (a,b) => Select_As T (A_Expr (F_Dot b)) a end) ll ->
    let s := Fset.mk_set (A T) l1 in
    s subS labels T t ->
    projection 
      (env_g T env Group_Fine (projection (env_t T env t) (Select_List rho) :: nil)) 
      (Select_List rho') =t= mk_tuple T s (dot T t).
Proof.
intros env t l1 l2 rho rho' L D2 ll Hrho Hrho' s Hs; simpl.
rewrite tuple_eq; split.
- rewrite Hrho', (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  unfold ll, s; rewrite !map_map.
  apply Fset.equal_refl_alt; apply f_equal.
  assert (L' : length l1 <= length l2); [rewrite L; apply le_n | ].
  rewrite <- (fst_combine l1 l2 L') at 2.
  rewrite <- map_eq; intros [a b] _; apply refl_equal.
- intro a; rewrite Hrho, Hrho'; unfold ll.
  rewrite !map_map.
  case_eq (a inS? s); intro Ha.
  + rewrite dot_mk_tuple.
    * case_eq (Oset.find (OAtt T) a
      (map
         (fun x : attribute * attribute =>
          match (match x with (a0, b) => Select_As _ (A_Expr (F_Dot b)) a0 end) with
          | Select_As _ e a0 => (a0, e)
          end) (combine l1 l2))).
      -- intros e He; assert (Ke := Oset.find_some _ _ _ He).
         rewrite in_map_iff in Ke.
         destruct Ke as [[_a b] [Ke Je]]; simpl in Ke; 
           injection Ke; clear Ke; do 2 intro; subst _a e.
         rewrite He; simpl; unfold interp_dot_env_slice; simpl.
         rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
         assert (Hb : b inS Fset.mk_set (A T)
                        (map
                           (fun x : attribute * attribute =>
                              fst
                                match (match x return (@SqlCommon.select T symb aggregate) with 
                                         (a0, b0) => Select_As (A_Expr (F_Dot a0)) b0 end) with
                                | Select_As e a0 => (a0, e)
                                end) (combine l1 l2))).
         {
           rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
           eexists; split; [ | apply Je]; apply refl_equal.
         }
         rewrite Hb, dot_mk_tuple; [ | assumption].
         case_eq (Oset.find (OAtt T) b
                            (map
                               (fun x : attribute * attribute =>
                                  match (match x with 
                                           (a0, b0) => Select_As (A_Expr (F_Dot a0)) b0 end) with
                                  | Select_As e a0 => (a0, e)
                                  end) (combine l1 l2))).
         ++ intros e Ke.
            assert (Le := Oset.find_some _ _ _ Ke); rewrite in_map_iff in Le.
            destruct Le as [[_a _b] [Le Me]]; simpl in Le; injection Le; clear Le; do 2 intro.
            subst _b e.
            assert (Ka : _a = a).
            {
              apply (all_diff_snd (combine l1 l2)) with b.
              - rewrite snd_combine; [assumption | ].
                rewrite L; apply le_n.
              - assumption.
              - assumption.
            }
            subst _a.
            rewrite Ke; simpl; unfold interp_dot_env_slice; simpl.
            rewrite Fset.subset_spec in Hs; rewrite (Hs _ Ha), dot_mk_tuple; trivial.
         ++ intro Abs; apply False_rec.
            refine (Oset.find_none _ _ _ Abs _ _).
            rewrite in_map_iff; eexists; split; [ | apply Je]; apply refl_equal.
      -- unfold s in Ha; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha.
         rewrite <- (fst_combine l1 l2) in Ha; [ | rewrite L; apply le_n].
         rewrite in_map_iff in Ha.
         destruct Ha as [[_a b] [_Ha Ha]]; simpl in _Ha; subst _a.
         intro Abs; apply False_rec.
         apply (Oset.find_none _ _ _ Abs (A_Expr (F_Dot b))).
         rewrite in_map_iff; eexists; split; [ | apply Ha]; apply refl_equal.
    * unfold s in Ha; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha.
      rewrite <- (fst_combine l1 l2), in_map_iff in Ha; [ | rewrite L; apply le_n].
      destruct Ha as [[_a b] [_Ha Ha]]; simpl in _Ha; subst _a.
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
      eexists; split; [ | apply Ha]; apply refl_equal.
  + unfold dot; rewrite 2 (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Ha.
    replace (a inS? Fset.mk_set (A T)
           (map
              (fun x : attribute * attribute =>
               fst
                 match (match x with (a0, b) => Select_As (A_Expr (F_Dot b)) a0 end) with
                 | Select_As e a0 => (a0, e)
                 end) (combine l1 l2))) with (a inS? s).
    * rewrite Ha; apply refl_equal.
    * unfold s; do 2 apply f_equal.
      rewrite <- (fst_combine l1 l2) at 1; [ | rewrite L; apply le_n].
      rewrite <- map_eq.
      intros [_a b] _; simpl; apply refl_equal.
Qed.
*)


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
  | Q_NaturalJoin q1 q2
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
  | Q_NaturalJoin q1 q2
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
  destruct q as [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | [s] q | f q | [s] g f q]; simpl.
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
  well_sorted_sql_table T basesort instance ->
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
- intros q Hn env1 env2 He; destruct q as [ | s0 | r | o q1 q2 | q1 q2 | q1 q2 | [s] q | f q | [s] g f q].
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

Fixpoint query_optim (q : query) :=
  match q with
  | Q_Set op q1 q2 => Q_Set op (query_optim q1) (query_optim q2)
  | Q_NaturalJoin q Q_Empty_Tuple => query_optim q
  | Q_NaturalJoin q1 q2 => Q_NaturalJoin (query_optim q1) (query_optim q2)
  | Q_Pi s q => Q_Pi s (query_optim q)
  | Q_Sigma (Sql_True _) q => query_optim q
  | Q_Sigma f q =>
    let sql_formula_optim :=
        (fix sql_formula_optim f :=
           match f with
           | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_optim f1) (sql_formula_optim f2)
           | Sql_Not f => Sql_Not (sql_formula_optim f)
           | Sql_True _ => Sql_True _
           | Sql_Pred _ p l => Sql_Pred _ p l
           | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (query_optim sq)
           | Sql_In _ s sq => Sql_In _ s (query_optim sq)
           | Sql_Exists _ sq => Sql_Exists _ (query_optim sq)
           end) in
    Q_Sigma (sql_formula_optim f) (query_optim q)
  | Q_Gamma s aggs f q =>
    let sql_formula_optim :=
        (fix sql_formula_optim f :=
           match f with
           | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_optim f1) (sql_formula_optim f2)
           | Sql_Not f => Sql_Not (sql_formula_optim f)
           | Sql_True _ => Sql_True _
           | Sql_Pred _ p l => Sql_Pred _ p l
           | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (query_optim sq)
           | Sql_In _ s sq => Sql_In _ s (query_optim sq)
           | Sql_Exists _ sq => Sql_Exists _ (query_optim sq)
           end) in
    Q_Gamma s aggs (sql_formula_optim f) (query_optim q)
  | _ => q
  end.

Fixpoint sql_formula_optim f : (@Formula.sql_formula T query) :=
  match f with
  | Sql_Conj a f1 f2 => Sql_Conj a (sql_formula_optim f1) (sql_formula_optim f2)
  | Sql_Not f => Sql_Not (sql_formula_optim f)
  | Sql_True _ => Sql_True _
  | Sql_Pred _ p l => Sql_Pred _ p l
  | Sql_Quant _ qtf p l sq => Sql_Quant _ qtf p l (query_optim sq)
  | Sql_In _ s sq => Sql_In _ s (query_optim sq)
  | Sql_Exists _ sq => Sql_Exists _ (query_optim sq)
  end.

Lemma query_optim_unfold (q : query) :
  query_optim q =
  match q with
  | Q_Set op q1 q2 => Q_Set op (query_optim q1) (query_optim q2)
  | Q_NaturalJoin q Q_Empty_Tuple => query_optim q
  | Q_NaturalJoin q1 q2 => Q_NaturalJoin (query_optim q1) (query_optim q2)
  | Q_Pi s q => Q_Pi s (query_optim q)
  | Q_Sigma (Sql_True _) q => query_optim q
  | Q_Sigma f q => Q_Sigma (sql_formula_optim f) (query_optim q)
  | Q_Gamma s aggs f q => Q_Gamma s aggs (sql_formula_optim f) (query_optim q)
  | _ => q
  end.
Proof. case q; reflexivity. Qed.

Lemma sort_query_optim :
  forall q, sort (query_optim q) =S= sort q.
Proof.
  intro q; set (n := tree_size (tree_of_query q)).
  assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
  revert q Hn; induction n as [ |n IHn]; [intros q Hn; destruct q; inversion Hn| ].
  intros q Hn; destruct q as [ |s0|r|op q1 q2|q1 q2|q1 q2|s q|f q|s aggs f q].
  - (* Q_Empty_Tuple *)
    apply Fset.equal_refl.
  - (* Q_Empty_Relation *)
    apply Fset.equal_refl.
  - (* Q_Table *)
    apply Fset.equal_refl.
  - (* Q_Set *)
    simpl. apply IHn.
    rewrite tree_of_query_unfold in Hn; simpl in Hn;
      refine (Nat.le_trans _ _ _ _ (le_S_n _ _ Hn)); apply le_plus_l.
  - (* Q_NaturalJoin *)
    assert (H:sort (Q_NaturalJoin (query_optim q1) (query_optim q2)) =S= (sort q1 unionS sort q2)).
    {
      simpl. rewrite (Fset.equal_eq_1 _ _ _ ((sort q1) unionS sort (query_optim q2))).
      - apply Fset.union_eq_2, IHn.
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          refine (le_trans _ _ _ _ (le_plus_r _ _));
          apply le_plus_l.
      - apply Fset.union_eq_1, IHn.
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          apply le_plus_l.
    }
    simpl. destruct q2 as [ |s0|r|op q21 q22|q21 q22|q21 q22|s q2|f q2|s aggs f q2]; try apply H.
    simpl. rewrite (Fset.equal_eq_2 _ _ _ (sort q1)).
    + simpl. apply IHn.
      rewrite tree_of_query_unfold in Hn; simpl in Hn;
        refine (Nat.le_trans _ _ _ _ (le_S_n _ _ Hn)); apply le_plus_l.
    + apply Fset.union_empty_r.
  - (* Q_CrossJoin *)
    apply Fset.equal_refl.
  - (* Q_Pi *)
    apply Fset.equal_refl.
  - (* Q_Sigma *)
    assert (H:sort (Q_Sigma (sql_formula_optim f) (query_optim q)) =S= sort (Q_Sigma f q)).
    {
      simpl. apply IHn.
      rewrite tree_of_query_unfold in Hn; simpl in Hn;
        refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
        refine (le_trans _ _ _ _ (le_plus_r _ _));
        apply le_plus_l.
    }
    rewrite query_optim_unfold. destruct f; apply H.
  - (* Q_Gamma *)
    apply Fset.equal_refl.
Qed.

Lemma query_optim_is_sound_etc :
  forall n,
    (forall env q,
        tree_size (tree_of_query q) <= n ->
        eval_query env (query_optim q) =BE=
        eval_query env q) /\
    (forall env f,
    tree_size (tree_of_sql_formula tree_of_query f) <= n ->
    eval_sql_formula eval_query env (sql_formula_optim f) =
    eval_sql_formula eval_query env f).
Proof.
  induction n as [ |n IHn]; split.
  - intros env q Hn; destruct q; inversion Hn.
  - intros env f Hn; destruct f; inversion Hn.
  - intros env q Hn.
    destruct q as [ |s0|r|op q1 q2|q1 q2|q1 q2|s q|f q|s aggs f q].
    + (* Q_Empty_Tuple *)
      apply Febag.nb_occ_equal; intro t; apply refl_equal.
    + (* Q_Empty_Relation *)
      apply Febag.nb_occ_equal; intro t; apply refl_equal.
    + (* Q_Table *)
      apply Febag.nb_occ_equal; intro t; apply refl_equal.
    + (* Q_Set *)
      assert (IH1: eval_query env (query_optim q1) =BE= eval_query env q1).
      { apply (proj1 IHn).
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          apply le_plus_l.
      }
      assert (IH2: eval_query env (query_optim q2) =BE= eval_query env q2).
      { apply (proj1 IHn).
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          refine (le_trans _ _ _ _ (le_plus_r _ _));
          apply le_plus_l.
      }
      rewrite Febag.nb_occ_equal in IH1, IH2.
      rewrite Febag.nb_occ_equal; intro t.
      simpl.
      rewrite (Fset.equal_eq_1 _ _ _ _ (sort_query_optim _)),
      (Fset.equal_eq_2 _ _ _ _ (sort_query_optim _)).
      case (sort q1 =S?= sort q2); [ |reflexivity].
      destruct op; simpl.
      * rewrite 2 Febag.nb_occ_union, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_union_max, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_inter, <- IH1, <- IH2; apply refl_equal.
      * rewrite 2 Febag.nb_occ_diff, <- IH1, <- IH2; apply refl_equal.
    + (* Q_NaturalJoin *)
      assert (IH1: eval_query env (query_optim q1) =BE= eval_query env q1).
      { apply (proj1 IHn).
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          apply le_plus_l.
      }
      assert (IH2: eval_query env (query_optim q2) =BE= eval_query env q2).
      { apply (proj1 IHn).
        rewrite tree_of_query_unfold in Hn; simpl in Hn;
          refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
          refine (le_trans _ _ _ _ (le_plus_r _ _));
          apply le_plus_l.
      }
      rewrite Febag.nb_occ_equal in IH1, IH2.
      rewrite Febag.nb_occ_equal; intro t.
      assert (H:Febag.nb_occ BTupleT t (eval_query env (Q_NaturalJoin (query_optim q1) (query_optim q2))) = Febag.nb_occ BTupleT t (natural_join_bag (eval_query env q1) (eval_query env q2))).
      {
        simpl. rewrite !Febag.nb_occ_mk_bag.
        apply natural_join_list_eq;
          intro t1; now rewrite <- !Febag.nb_occ_elements.
      }
      simpl. destruct q2; try apply H.
      simpl. rewrite Febag.nb_occ_mk_bag.
      destruct (Febag.elements_singleton BTupleT (empty_tuple T)) as [t0 [H1 H2]].
      rewrite H2.
      assert (H3:forall l, Oeset.compare (mk_oelists (OTuple T)) (natural_join_list T l (t0 :: nil)) l = Eq).
      {
        induction l as [ |t1 l IHl]; auto.
        simpl. unfold d_join_list. simpl.
        replace (join_compatible_tuple T t1 t0) with true.
        - simpl. change (comparelA (Oeset.compare (OTuple T)) (natural_join_list T l (t0 :: nil)) l = Eq) in IHl.
          rewrite IHl.
          replace (Oeset.compare (OTuple T) (join_tuple T t1 t0) t1) with Eq; auto.
          symmetry.
          rewrite (Oeset.compare_eq_1 _ _ (join_tuple T t1 (empty_tuple _))).
          + apply join_tuple_empty_2.
          + now apply join_tuple_eq_2, Oeset.compare_eq_sym.
        - symmetry. unfold join_compatible_tuple.
          rewrite Fset.for_all_spec_alt. intros e He.
          rewrite (Fset.mem_eq_2 _ _ (emptysetS)) in He.
          + rewrite Fset.empty_spec in He. discriminate.
          + rewrite (Fset.equal_eq_1 _ _ _ (labels T t1 interS (emptysetS))).
            * rewrite Fset.equal_spec; intro a.
              now rewrite Fset.mem_inter, Fset.empty_spec, Bool.andb_false_r.
            * apply Fset.inter_eq_2. rewrite (Fset.equal_eq_1 _ _ _ (labels T (empty_tuple T))).
              -- apply labels_empty_tuple.
              -- now apply tuple_eq_labels, Oeset.compare_eq_sym.
      }
      rewrite (Oeset.nb_occ_eq_2 _ _ _ (Febag.elements BTupleT (eval_query env q1))).
      * rewrite <- Febag.nb_occ_elements. apply IH1.
      * apply H3.
    + (* Q_CrossJoin *)
      apply Febag.nb_occ_equal; intro t; apply refl_equal.
    + (* Q_Pi *)
      simpl. rewrite !Febag.nb_occ_equal. intro t.
      unfold Febag.map. rewrite !Febag.nb_occ_mk_bag.
      apply (Oeset.nb_occ_map_eq_3 (OTuple _)).
      * intros x1 x2 H1 H2 H12. apply mk_tuple_eq_2. intros a Ha.
        case_eq (Oset.find (OAtt T) a s); try reflexivity.
        intros agg Hagg. now apply interp_aggterm_eq, env_t_eq_2.
      * intro x. rewrite <- !Febag.nb_occ_elements.
        revert x. apply Febag.nb_occ_eq_2.
        apply IHn. simpl in Hn. lia.
    + (* Q_Sigma *)
      rewrite query_optim_unfold.
      assert (H:eval_query env (Q_Sigma (sql_formula_optim f) (query_optim q))
                =BE= eval_query env (Q_Sigma f q)).
      {
        simpl. apply Febag.filter_eq.
        - apply IHn. simpl in Hn. lia.
        - intros x1 x2 H1 H2. destruct IHn as [IHn1 IHn2]. rewrite IHn2.
          + erewrite eval_f_eq; eauto.
          + simpl in Hn. clear -Hn.
            assert (H:forall (x y:nat), S (x + y) <= S n -> x <= n) by (intros; lia).
            eauto.
      }
      destruct f; auto.
      simpl. rewrite (Febag.equal_eq_1 _ _ _ (eval_query env q)).
      * apply Febag.equal_sym, Febag.filter_true_alt.
      * apply IHn. simpl in Hn. lia.
    + (* Q_Gamma *)
      rewrite query_optim_unfold, eval_query_unfold.
      change (eval_query env (Q_Gamma s aggs f q)) with
          (Febag.mk_bag BTupleT
        (map
           (fun l : list tuple =>
            projection T (env_g T env (Group_By aggs) l) (Select_List s))
           (filter
              (fun l : list tuple =>
               Bool.is_true (B T)
                 (eval_sql_formula eval_query (env_g T env (Group_By aggs) l) f))
              (make_groups env (eval_query env q) (Group_By aggs))))).
      rewrite Febag.nb_occ_equal. intro t.
      rewrite !Febag.nb_occ_mk_bag.
      apply (Oeset.nb_occ_map_eq_2_3 (OLTuple T)).
      * intros l1 l2 H. apply projection_eq. apply env_g_eq_2.
        change (compare_OLA (OTuple T) l1 l2 = Eq) in H.
        now rewrite <- compare_list_t in H.
      * intro l. apply Oeset.nb_occ_filter_eq.
        -- intro l1. apply make_groups_eq_bag.
           ++ apply equiv_env_refl.
           ++ apply IHn. simpl in Hn. lia.
        -- intros l1 l2 _ H.
           transitivity (Bool.is_true (B T)
    (eval_sql_formula eval_query (env_g T env (Group_By aggs) l1)
       f)).
           ++ destruct IHn as [_ IH]. rewrite IH; auto.
              simpl in Hn. clear -Hn.
              assert (H:forall x y, (S (x + y) <= S n) -> (x <= n)) by (intros; lia).
              eauto.
           ++ erewrite eval_formula_eq; eauto.
              apply env_g_eq_2.
              change (compare_OLA (OTuple T) l1 l2 = Eq) in H.
              now rewrite <- compare_list_t in H.
  - intros env [ao f1 f2|f| |p aggs|qu p aggs q|s q|q] Hn.
    + (* Sql_Conj *)
      destruct IHn as [_ IH].
      simpl.
      case ao; simpl;
        rewrite !IH; try reflexivity; simpl in Hn; lia.
    + (* Sql_Not *)
      destruct IHn as [_ IH].
      simpl. rewrite IH; try reflexivity; simpl in Hn; lia.
    + (* Sql_True *)
      trivial.
    + (* Sql_Pred *)
      trivial.
    + (* Sql_Quant *)
      simpl. apply (interp_quant_eq _ (OTuple T)).
      * apply Oeset.nb_occ_permut. intro t. rewrite <- !Febag.nb_occ_elements.
        revert t. apply Febag.nb_occ_eq_2. apply IHn. simpl in Hn. clear -Hn.
        assert (H:forall x y, (S (S (S (x + y + 0))) <= S n) -> x <= n)
          by (intros; lia).
        eauto.
      * intros t1 t2 _ H.
        rewrite <- (Fset.elements_spec1 _ (labels T t1) (labels T t2));
          [ |now apply tuple_eq_labels].
        replace (map (dot T t2) ({{{labels T t1}}}))
          with (map (dot T t1) ({{{labels T t1}}})); auto.
        apply map_ext_in. intros a H1. apply Fset.in_elements_mem in H1.
        now apply tuple_eq_dot_alt.
    + (* Sql_In *)
      change (sql_formula_optim (Sql_In query s q))
        with (Sql_In query s (query_optim q)).
      rewrite !eval_sql_formula_unfold.
      apply (interp_quant_eq _ (OTuple T)).
      * apply Oeset.nb_occ_permut. intro t. rewrite <- !Febag.nb_occ_elements.
        revert t. apply Febag.nb_occ_eq_2. apply IHn. simpl in Hn. clear -Hn.
        assert (H:forall x y, S (S (S (y + (x + 0) + 0))) <= S n -> x <= n)
          by (intros; lia).
        eauto.
      * intros t1 t2 _ H.
        rewrite <- (Oeset.compare_eq_2 _ _ _ _ H).
        case (Oeset.compare (OTuple T) (projection T env (Select_List (_Select_List s))) t1); auto; now rewrite (contains_nulls_eq _ _ H).
    + (* Sql_Exists *)
      simpl. rewrite (Febag.is_empty_eq _ _ (eval_query env q)); auto.
      apply IHn. simpl in Hn. clear -Hn.
      assert (H:forall x, S (S (x + 0 + 0)) <= S n -> x <= n)
        by (intros; lia).
      eauto.
Qed.

Lemma query_optim_is_sound :
  forall env q,
     eval_query env (query_optim q) =BE=
     eval_query env q.
Proof.
  intros env q.
  destruct (query_optim_is_sound_etc (tree_size (tree_of_query q))) as [H1 _].
  now apply H1.
Qed.

End Sec.
