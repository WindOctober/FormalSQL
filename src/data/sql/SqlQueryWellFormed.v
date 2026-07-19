(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                 Well-formedness of exact ordered SQL queries                   *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Formula Projection ATerms
        SqlAlgebra SqlOutcome SqlOrder SqlQuerySyntax SqlQuerySemantics.

(** [query_expr] is the only exact query syntax.  This module states the
    conservative structural obligations required at that semantic boundary;
    it deliberately introduces no mirror syntax and no second evaluator. *)

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Arguments Select_As {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_By {T}.

Local Definition setA := Fset.set (A T).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> setA.

Definition query_values_well_sorted
    (attributes : setA) (rows : bagT) : Prop :=
  forall row, row inBE rows -> labels T row =S= attributes.

Definition query_row_map_well_sorted
    (attributes : setA)
    (row_map : tuple T -> sql_outcome (tuple T)) : Prop :=
  forall input output,
    row_map input = SqlSuccess output -> labels T output =S= attributes.

(** A projection list is an ordinal witness only when no two positions denote
    the same SQL attribute.  The cardinality test uses [OAtt], exactly as the
    tuple-label sets and join operations do. *)
Definition query_output_attributes_unique
    (outputs : list (attribute T)) : Prop :=
  length outputs =
    Fset.cardinal (A T) (Fset.mk_set (A T) outputs).

Definition query_select_list_outputs_unique
    (select_list : @_select_list T) : Prop :=
  query_output_attributes_unique (select_list_outputs select_list).

Definition query_output_sorts_disjoint (left right : setA) : Prop :=
  (left interS right) =S= Fset.empty (A T).

Definition query_grouping_sets_well_formed
    (grouping_sets : list (query_grouping_set T)) : Prop :=
  match grouping_sets with
  | nil => False
  | (first_select, _) :: rest =>
      query_select_list_outputs_unique first_select /\
      Forall
        (fun grouping_set =>
          select_list_outputs (fst grouping_set) =
            select_list_outputs first_select /\
          query_select_list_outputs_unique (fst grouping_set))
        rest
  end.

(** Every join source that can be emitted for a kind must project the declared
    result schema.  Projection lists unused by that join kind need no premise. *)
Definition query_join_projection_sorts_compatible
    (kind : query_join_kind)
    (matched_select left_select right_select : @_select_list T) : Prop :=
  match kind with
  | QueryJoinInner => True
  | QueryJoinLeft =>
      select_list_sort matched_select =S= select_list_sort left_select
  | QueryJoinRight =>
      select_list_sort matched_select =S= select_list_sort right_select
  | QueryJoinFull =>
      select_list_sort matched_select =S= select_list_sort left_select /\
      select_list_sort matched_select =S= select_list_sort right_select
  | QueryJoinSemi | QueryJoinAnti => True
  end.

(** Only projection lists evaluated by a join kind carry obligations.  This
    mirrors [query_join_projection_sorts_compatible] and prevents
    [projection] from silently collapsing two output positions into one tuple
    label. *)
Definition query_join_projections_unique
    (kind : query_join_kind)
    (matched_select left_select right_select : @_select_list T) : Prop :=
  match kind with
  | QueryJoinInner =>
      query_select_list_outputs_unique matched_select
  | QueryJoinLeft =>
      query_select_list_outputs_unique matched_select /\
      query_select_list_outputs_unique left_select
  | QueryJoinRight =>
      query_select_list_outputs_unique matched_select /\
      query_select_list_outputs_unique right_select
  | QueryJoinFull =>
      query_select_list_outputs_unique matched_select /\
      query_select_list_outputs_unique left_select /\
      query_select_list_outputs_unique right_select
  | QueryJoinSemi | QueryJoinAnti =>
      query_select_list_outputs_unique left_select
  end.

(** Positional IN alignment is stronger than set equality: it rejects empty
    row values, duplicate aliases, arity mismatches, label mismatches, and
    swapped columns. *)
Definition query_in_positionally_aligned
    (select_list : @_select_list T)
    (right_outputs : list (attribute T)) : Prop :=
  select_list_outputs select_list <> nil /\
  query_select_list_outputs_unique select_list /\
  select_list_outputs select_list = right_outputs.

Definition query_sort_keys_in_scope
    (scope : setA) (keys : list (sort_key T)) : Prop :=
  forall key, In key keys -> sort_key_attribute key inS scope.

(** Compact [QExpr_Bag] leaves reuse the deterministic bag algebra, but they do
    not bypass the exact-query boundary.  The bag-algebra natural join is
    intentionally excluded: exact SQL natural join uses the NULL-aware
    [QExpr_NaturalJoin] constructor. *)
Inductive bag_query_admissible : @query T relname -> Prop :=
  | BagQuery_EmptyTuple :
      bag_query_admissible (@Q_Empty_Tuple T relname)
  | BagQuery_EmptyRelation :
      forall attributes,
        bag_query_admissible (@Q_Empty_Relation T relname attributes)
  | BagQuery_Table :
      forall table,
        bag_query_admissible (@Q_Table T relname table)
  | BagQuery_Set :
      forall operation left right,
        bag_query_admissible left ->
        bag_query_admissible right ->
        @sort T relname basesort left =S= @sort T relname basesort right ->
        bag_query_admissible (@Q_Set T relname operation left right)
  | BagQuery_CrossJoin :
      forall left right,
        bag_query_admissible left ->
        bag_query_admissible right ->
        query_output_sorts_disjoint
          (@sort T relname basesort left) (@sort T relname basesort right) ->
        bag_query_admissible (@Q_CrossJoin T relname left right)
  | BagQuery_Project :
      forall select_list input,
        bag_query_admissible input ->
        query_select_list_outputs_unique select_list ->
        bag_query_admissible (@Q_Pi T relname select_list input)
  | BagQuery_Filter :
      forall formula input,
        bag_formula_admissible formula ->
        bag_query_admissible input ->
        bag_query_admissible (@Q_Sigma T relname formula input)
  | BagQuery_Aggregate :
      forall select_list group_terms having input,
        group_terms <> nil ->
        bag_formula_admissible having ->
        bag_query_admissible input ->
        query_select_list_outputs_unique select_list ->
        bag_query_admissible
          (@Q_Gamma T relname select_list group_terms having input)

with bag_formula_admissible :
    @sql_formula T (@query T relname) -> Prop :=
  | BagFormula_Conj :
      forall operation left right,
        bag_formula_admissible left ->
        bag_formula_admissible right ->
        bag_formula_admissible
          (@Sql_Conj T (@query T relname) operation left right)
  | BagFormula_Not :
      forall formula,
        bag_formula_admissible formula ->
        bag_formula_admissible
          (@Sql_Not T (@query T relname) formula)
  | BagFormula_True :
      bag_formula_admissible (@Sql_True T (@query T relname))
  | BagFormula_Pred :
      forall predicate arguments,
        length arguments = predicate_arity T predicate ->
        bag_formula_admissible
          (@Sql_Pred T (@query T relname) predicate arguments)
  | BagFormula_Quant :
      forall quantifier predicate arguments subquery,
        bag_query_admissible subquery ->
        length arguments = 1 ->
        length
          (Fset.elements (A T) (@sort T relname basesort subquery)) = 1 ->
        length arguments +
          length (Fset.elements (A T) (@sort T relname basesort subquery)) =
          predicate_arity T predicate ->
        bag_formula_admissible
          (@Sql_Quant T (@query T relname)
            quantifier predicate arguments subquery)
  | BagFormula_In :
      forall select_items subquery,
        bag_query_admissible subquery ->
        length select_items = 1 ->
        length
          (Fset.elements (A T) (@sort T relname basesort subquery)) = 1 ->
        query_in_positionally_aligned (_Select_List select_items)
          (Fset.elements (A T) (@sort T relname basesort subquery)) ->
        bag_formula_admissible
          (@Sql_In T (@query T relname) select_items subquery)
  | BagFormula_Exists :
      forall subquery,
        bag_query_admissible subquery ->
        bag_formula_admissible
          (@Sql_Exists T (@query T relname) subquery).

Fixpoint query_expr_admissible
    (source : query_expr T relname) : Prop :=
  match source with
  | QExpr_Error outputs _ =>
      query_output_attributes_unique outputs
  | QExpr_Values outputs rows =>
      query_output_attributes_unique outputs /\
      query_values_well_sorted (@query_outputs_sort T outputs) rows
  | QExpr_Bag outputs query =>
      query_output_attributes_unique outputs /\
      bag_query_admissible query /\
      @query_outputs_sort T outputs =S= @sort T relname basesort query
  | QExpr_Set _ left_query right_query =>
      query_expr_admissible left_query /\
      query_expr_admissible right_query /\
      query_expr_outputs left_query = query_expr_outputs right_query
  | QExpr_NaturalJoin left_query right_query =>
      query_expr_admissible left_query /\
      query_expr_admissible right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_admissible left_query /\
      query_expr_admissible right_query /\
      query_output_sorts_disjoint
        (query_expr_sort left_query) (query_expr_sort right_query)
  | QExpr_Join kind predicate matched_select left_select right_select
      left_query right_query =>
      formula_expr_admissible predicate /\
      query_expr_admissible left_query /\
      query_expr_admissible right_query /\
      query_join_projection_sorts_compatible
        kind matched_select left_select right_select /\
      query_join_projections_unique
        kind matched_select left_select right_select
  | QExpr_Project select_list input =>
      query_expr_admissible input /\
      query_select_list_outputs_unique select_list
  | QExpr_Distinct input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_admissible input
  | QExpr_RowMap outputs row_map input =>
      query_expr_admissible input /\
      query_output_attributes_unique outputs /\
      query_row_map_well_sorted (@query_outputs_sort T outputs) row_map
  | QExpr_Filter formula input =>
      query_expr_admissible input /\ formula_expr_admissible formula
  | QExpr_Group select_list _ having input =>
      query_expr_admissible input /\
      formula_expr_admissible having /\
      query_select_list_outputs_unique select_list
  | QExpr_GroupingSets grouping_sets input =>
      query_expr_admissible input /\
      query_grouping_sets_well_formed grouping_sets
  | QExpr_Rank partition_keys order_keys rank_attribute _ input =>
      query_expr_admissible input /\
      query_sort_keys_in_scope
        (query_expr_sort input) partition_keys /\
      query_sort_keys_in_scope
        (query_expr_sort input) order_keys /\
      ~ rank_attribute inS query_expr_sort input
  | QExpr_Window partition_keys order_keys items input =>
      query_expr_admissible input /\
      query_sort_keys_in_scope
        (query_expr_sort input) partition_keys /\
      query_sort_keys_in_scope
        (query_expr_sort input) order_keys /\
      Forall
        (fun item => ~ qwi_attribute item inS query_expr_sort input)
        items /\
      length (map (@qwi_attribute T) items) =
        Fset.cardinal (A T)
          (Fset.mk_set (A T) (map (@qwi_attribute T) items))
  | QExpr_OrderBy keys input =>
      query_expr_admissible input /\
      query_sort_keys_in_scope (query_expr_sort input) keys
  end

with formula_expr_admissible
    (formula : formula_expr T relname) : Prop :=
  match formula with
  | FExpr_Conj _ left_formula right_formula =>
      formula_expr_admissible left_formula /\
      formula_expr_admissible right_formula
  | FExpr_Not nested => formula_expr_admissible nested
  | FExpr_True => True
  | FExpr_Pred predicate arguments =>
      length arguments = predicate_arity T predicate
  | FExpr_Quant _ predicate arguments subquery =>
      query_expr_admissible subquery /\
      length arguments = 1 /\
      length (query_expr_outputs subquery) = 1 /\
      length arguments + length (query_expr_outputs subquery) =
        predicate_arity T predicate
  | FExpr_Exists subquery => query_expr_admissible subquery
  | FExpr_In select_items subquery =>
      query_expr_admissible subquery /\
      select_list_sort (_Select_List select_items) =S=
        query_expr_sort subquery /\
      query_in_positionally_aligned (_Select_List select_items)
        (query_expr_outputs subquery)
  end.

Lemma query_in_positionally_aligned_arity :
  forall select_list right_outputs,
    query_in_positionally_aligned select_list right_outputs ->
    length (select_list_outputs select_list) = length right_outputs.
Proof.
intros select_list right_outputs [_ [_ Haligned]].
now rewrite Haligned.
Qed.

Lemma query_in_positionally_aligned_nonempty :
  forall select_list right_outputs,
    query_in_positionally_aligned select_list right_outputs ->
    select_list_outputs select_list <> nil.
Proof.
intros select_list right_outputs [Hnonempty _]; exact Hnonempty.
Qed.

Lemma query_in_positionally_aligned_sort :
  forall select_list right_sort,
    query_in_positionally_aligned select_list
      (Fset.elements (A T) right_sort) ->
    select_list_sort select_list =S= right_sort.
Proof.
intros [select_items] right_sort [_ [_ Haligned]].
unfold select_list_sort, select_list_outputs in *.
rewrite Haligned.
apply Fset.mk_set_idem.
Qed.

Lemma formula_expr_admissible_in_positionally_aligned :
  forall select_items subquery,
    formula_expr_admissible (FExpr_In select_items subquery) ->
    query_in_positionally_aligned (_Select_List select_items)
      (query_expr_outputs subquery).
Proof.
intros select_items subquery Hadmissible; simpl in Hadmissible; tauto.
Qed.

Lemma bag_formula_admissible_in_positionally_aligned :
  forall select_items subquery,
    bag_formula_admissible
      (@Sql_In T (@query T relname) select_items subquery) ->
    query_in_positionally_aligned (_Select_List select_items)
      (Fset.elements (A T) (@sort T relname basesort subquery)).
Proof.
intros select_items subquery Hadmissible; inversion Hadmissible; subst;
  assumption.
Qed.

Lemma query_expr_admissible_join_projection_sorts :
  forall kind predicate matched_select left_select right_select left right,
    query_expr_admissible
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) ->
    query_join_projection_sorts_compatible
      kind matched_select left_select right_select.
Proof.
intros kind predicate matched_select left_select right_select left right
  Hadmissible; simpl in Hadmissible; tauto.
Qed.

Lemma query_expr_admissible_join_projection_uniqueness :
  forall kind predicate matched_select left_select right_select left right,
    query_expr_admissible
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) ->
    query_join_projections_unique
      kind matched_select left_select right_select.
Proof.
intros kind predicate matched_select left_select right_select left right
  Hadmissible; simpl in Hadmissible; tauto.
Qed.

Lemma query_expr_admissible_cross_join_disjoint :
  forall left right,
    query_expr_admissible (QExpr_CrossJoin left right) ->
    query_output_sorts_disjoint
      (query_expr_sort left) (query_expr_sort right).
Proof.
intros left right Hadmissible; simpl in Hadmissible; tauto.
Qed.

End Sec.

Arguments query_expr_admissible {T relname} basesort _.
Arguments formula_expr_admissible {T relname} basesort _.
