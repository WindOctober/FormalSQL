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
        SqlOutcome SqlOrder SqlQuerySyntax SqlQuerySemantics.

(** Query-level scalar phases.  A nested query starts its own phase analysis;
    the restrictions here apply only to expressions owned by the current query
    level. *)
Inductive scalar_phase : Type :=
  | ScalarPhaseWhere
  | ScalarPhaseOn
  | ScalarPhaseHaving
  (** Per-row SELECT adapter (ordinary projection and join target lists). *)
  | ScalarPhaseRowSelect
  (** SELECT evaluated under a logical group environment. *)
  | ScalarPhaseSelect
  | ScalarPhaseGroupBy.

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

Fixpoint prop_forall {A : Type} (predicate : A -> Prop) (values : list A) : Prop :=
  match values with
  | nil => True
  | value :: rest => predicate value /\ prop_forall predicate rest
  end.

Fixpoint aggterm_contains_aggregate (term : @aggterm T) : bool :=
  match term with
  | A_Expr _ _ => false
  | A_agg _ _ _ => true
  | A_fun _ _ arguments => existsb (@aggterm_contains_aggregate) arguments
  end.

Definition scalar_phase_allows_aggregate (phase : scalar_phase) : bool :=
  match phase with
  | ScalarPhaseHaving | ScalarPhaseSelect => true
  | ScalarPhaseWhere | ScalarPhaseOn | ScalarPhaseRowSelect
  | ScalarPhaseGroupBy => false
  end.

Definition scalar_phase_allows_subquery (phase : scalar_phase) : bool :=
  match phase with
  | ScalarPhaseGroupBy => false
  | _ => true
  end.

Definition aggterm_phase_admissible
    (phase : scalar_phase) (term : @aggterm T) : Prop :=
  scalar_phase_allows_aggregate phase = true \/
  aggterm_contains_aggregate term = false.

Definition select_list_phase_admissible
    (phase : scalar_phase) (select_list : @_select_list T) : Prop :=
  match select_list with
  | _Select_List items =>
      prop_forall
        (fun item =>
          match item with
          | Select_As term _ => aggterm_phase_admissible phase term
          end) items
  end.

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

(** SELECT expressions and grouping keys belong to different SQL phases even
    when they are stored together in one grouping-set branch. *)
Definition query_grouping_sets_phase_admissible
    (grouping_sets : list (query_grouping_set T)) : Prop :=
  prop_forall
    (fun grouping_set =>
      select_list_phase_admissible ScalarPhaseSelect (fst grouping_set) /\
      prop_forall
        (aggterm_phase_admissible ScalarPhaseGroupBy) (snd grouping_set))
    grouping_sets.

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

Definition query_join_projections_phase_admissible
    (kind : query_join_kind)
    (matched_select left_select right_select : @_select_list T) : Prop :=
  match kind with
  | QueryJoinInner =>
      select_list_phase_admissible ScalarPhaseRowSelect matched_select
  | QueryJoinLeft =>
      select_list_phase_admissible ScalarPhaseRowSelect matched_select /\
      select_list_phase_admissible ScalarPhaseRowSelect left_select
  | QueryJoinRight =>
      select_list_phase_admissible ScalarPhaseRowSelect matched_select /\
      select_list_phase_admissible ScalarPhaseRowSelect right_select
  | QueryJoinFull =>
      select_list_phase_admissible ScalarPhaseRowSelect matched_select /\
      select_list_phase_admissible ScalarPhaseRowSelect left_select /\
      select_list_phase_admissible ScalarPhaseRowSelect right_select
  | QueryJoinSemi | QueryJoinAnti =>
      select_list_phase_admissible ScalarPhaseRowSelect left_select
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

Fixpoint query_expr_admissible
    (source : query_expr T relname) : Prop :=
  match source with
  | QExpr_Error outputs _ =>
      query_output_attributes_unique outputs
  | QExpr_Values outputs rows =>
      query_output_attributes_unique outputs /\
      query_values_well_sorted (@query_outputs_sort T outputs) rows
  | QExpr_Table outputs table =>
      query_output_attributes_unique outputs /\
      @query_outputs_sort T outputs =S= basesort table
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
      formula_expr_admissible_at ScalarPhaseOn predicate /\
      query_expr_admissible left_query /\
      query_expr_admissible right_query /\
      query_join_projection_sorts_compatible
        kind matched_select left_select right_select /\
      query_join_projections_unique
        kind matched_select left_select right_select /\
      query_join_projections_phase_admissible
        kind matched_select left_select right_select
  | QExpr_Project select_list input =>
      query_expr_admissible input /\
      query_select_list_outputs_unique select_list /\
      select_list_phase_admissible ScalarPhaseRowSelect select_list
  | QExpr_ScalarProject select_list input =>
      query_expr_admissible input /\
      query_output_attributes_unique (scalar_select_outputs select_list) /\
      prop_forall
        (fun item =>
          scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list
  | QExpr_Distinct input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_admissible input
  | QExpr_RowMap outputs row_map input =>
      query_expr_admissible input /\
      query_output_attributes_unique outputs /\
      query_row_map_well_sorted (@query_outputs_sort T outputs) row_map
  | QExpr_Filter formula input =>
      query_expr_admissible input /\
      formula_expr_admissible_at ScalarPhaseWhere formula
  | QExpr_ScalarFilter expression input =>
      query_expr_admissible input /\
      scalar_expr_admissible ScalarPhaseWhere expression
  | QExpr_Group select_list group_terms having input =>
      query_expr_admissible input /\
      formula_expr_admissible_at ScalarPhaseHaving having /\
      query_select_list_outputs_unique select_list /\
      select_list_phase_admissible ScalarPhaseSelect select_list /\
      prop_forall
        (aggterm_phase_admissible ScalarPhaseGroupBy) group_terms
  | QExpr_ScalarGroup select_list group_keys having input =>
      query_expr_admissible input /\
      query_output_attributes_unique (scalar_select_outputs select_list) /\
      prop_forall
        (fun item =>
          scalar_expr_admissible ScalarPhaseSelect (fst item) /\
          scalar_expr_type (fst item) = type_of_attribute T (snd item))
        select_list /\
      scalar_expr_admissible ScalarPhaseHaving having /\
      prop_forall
        (@scalar_expr_admissible ScalarPhaseGroupBy ScalarResultValue)
        group_keys /\
      exists group_terms,
        scalar_group_key_terms group_keys = Some group_terms
  | QExpr_GroupingSets grouping_sets input =>
      query_expr_admissible input /\
      query_grouping_sets_well_formed grouping_sets /\
      query_grouping_sets_phase_admissible grouping_sets
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

with formula_expr_admissible_at
    (phase : scalar_phase) (formula : formula_expr T relname) : Prop :=
  match formula with
  | FExpr_Conj _ left_formula right_formula =>
      formula_expr_admissible_at phase left_formula /\
      formula_expr_admissible_at phase right_formula
  | FExpr_Not nested => formula_expr_admissible_at phase nested
  | FExpr_True => True
  | FExpr_Pred predicate arguments =>
      prop_forall (aggterm_phase_admissible phase) arguments /\
      length arguments = predicate_arity T predicate
  | FExpr_Quant _ predicate arguments subquery =>
      query_expr_admissible subquery /\
      prop_forall (aggterm_phase_admissible phase) arguments /\
      length arguments = 1 /\
      length (query_expr_outputs subquery) = 1 /\
      length arguments + length (query_expr_outputs subquery) =
        predicate_arity T predicate
  | FExpr_Exists subquery => query_expr_admissible subquery
  | FExpr_In select_items subquery =>
      query_expr_admissible subquery /\
      select_list_phase_admissible phase (_Select_List select_items) /\
      select_list_sort (_Select_List select_items) =S=
        query_expr_sort subquery /\
      query_in_positionally_aligned (_Select_List select_items)
        (query_expr_outputs subquery)
  | FExpr_Scalar expression =>
      scalar_expr_admissible phase expression
  end

with scalar_expr_admissible
    (phase : scalar_phase) {kind : scalar_result_kind}
    (expression : scalar_expr T relname kind) : Prop :=
  match expression with
  | SExpr_Leaf _ term => aggterm_phase_admissible phase term
  | SExpr_Call _ _ arguments =>
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments
  | SExpr_Case result_type condition then_expression else_expression =>
      scalar_expr_admissible phase condition /\
      scalar_expr_admissible phase then_expression /\
      scalar_expr_admissible phase else_expression /\
      scalar_expr_type then_expression = result_type /\
      scalar_expr_type else_expression = result_type
  | SExpr_BoolValue result_type embed inner =>
      scalar_expr_admissible phase inner /\
      forall truth, type_of_value T (embed truth) = result_type
  | SExpr_ValueBool _ inner => scalar_expr_admissible phase inner
  | SExpr_Pred predicate arguments =>
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      length arguments = predicate_arity T predicate
  | SExpr_Conj _ left_expression right_expression =>
      scalar_expr_admissible phase left_expression /\
      scalar_expr_admissible phase right_expression
  | SExpr_Not inner => scalar_expr_admissible phase inner
  | SExpr_True => True
  | SExpr_Quant _ predicate arguments subquery =>
      scalar_phase_allows_subquery phase = true /\
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      query_expr_admissible subquery /\
      length arguments + length (query_expr_outputs subquery) =
        predicate_arity T predicate
  | SExpr_In arguments subquery =>
      scalar_phase_allows_subquery phase = true /\
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      query_expr_admissible subquery /\
      arguments <> nil /\
      length arguments = length (query_expr_outputs subquery) /\
      map scalar_expr_type arguments =
        map (type_of_attribute T) (query_expr_outputs subquery)
  | SExpr_Exists subquery =>
      scalar_phase_allows_subquery phase = true /\
      query_expr_admissible subquery
  | SExpr_Subquery result_type null_value subquery =>
      scalar_phase_allows_subquery phase = true /\
      query_expr_admissible subquery /\
      type_of_value T null_value = result_type /\
      match query_expr_outputs subquery with
      | attribute :: nil => type_of_attribute T attribute = result_type
      | _ => False
      end
  end.

(** Compatibility view used by existing theorem statements about standalone
    formulas.  Query constructors above always choose their owning phase
    explicitly; a standalone formula historically denotes HAVING-capable
    aggregate evaluation. *)
Definition formula_expr_admissible
    (formula : formula_expr T relname) : Prop :=
  formula_expr_admissible_at ScalarPhaseHaving formula.

(** Semantic-side witness validation that depends on the concrete SQL NULL
    classifier.  It is kept separate from structural/phase admissibility so
    legacy generic clients need not invent a NULL operation; exact native
    scalar frontends must discharge both components through
    [query_expr_native_scalar_admissible]. *)
Fixpoint query_expr_scalar_witnesses_valid
    (value_is_null : value T -> bool)
    (query : query_expr T relname) : Prop :=
  match query with
  | QExpr_Error _ _ | QExpr_Values _ _ | QExpr_Table _ _ => True
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_scalar_witnesses_valid value_is_null left_query /\
      query_expr_scalar_witnesses_valid value_is_null right_query
  | QExpr_Join _ predicate _ _ _ left_query right_query =>
      formula_expr_scalar_witnesses_valid value_is_null predicate /\
      query_expr_scalar_witnesses_valid value_is_null left_query /\
      query_expr_scalar_witnesses_valid value_is_null right_query
  | QExpr_Project _ input
  | QExpr_RowMap _ _ input
  | QExpr_GroupingSets _ input
  | QExpr_Rank _ _ _ _ input
  | QExpr_Window _ _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input =>
      query_expr_scalar_witnesses_valid value_is_null input
  | QExpr_ScalarProject select_list input =>
      prop_forall
        (fun item => scalar_expr_witnesses_valid value_is_null (fst item))
        select_list /\
      query_expr_scalar_witnesses_valid value_is_null input
  | QExpr_Filter formula input =>
      formula_expr_scalar_witnesses_valid value_is_null formula /\
      query_expr_scalar_witnesses_valid value_is_null input
  | QExpr_ScalarFilter expression input =>
      scalar_expr_witnesses_valid value_is_null expression /\
      query_expr_scalar_witnesses_valid value_is_null input
  | QExpr_Group _ _ having input =>
      formula_expr_scalar_witnesses_valid value_is_null having /\
      query_expr_scalar_witnesses_valid value_is_null input
  | QExpr_ScalarGroup select_list group_keys having input =>
      prop_forall
        (fun item => scalar_expr_witnesses_valid value_is_null (fst item))
        select_list /\
      prop_forall (scalar_expr_witnesses_valid value_is_null) group_keys /\
      scalar_expr_witnesses_valid value_is_null having /\
      query_expr_scalar_witnesses_valid value_is_null input
  end

with formula_expr_scalar_witnesses_valid
    (value_is_null : value T -> bool)
    (formula : formula_expr T relname) : Prop :=
  match formula with
  | FExpr_Conj _ left_formula right_formula =>
      formula_expr_scalar_witnesses_valid value_is_null left_formula /\
      formula_expr_scalar_witnesses_valid value_is_null right_formula
  | FExpr_Not inner =>
      formula_expr_scalar_witnesses_valid value_is_null inner
  | FExpr_True | FExpr_Pred _ _ => True
  | FExpr_Quant _ _ _ subquery
  | FExpr_In _ subquery
  | FExpr_Exists subquery =>
      query_expr_scalar_witnesses_valid value_is_null subquery
  | FExpr_Scalar expression =>
      scalar_expr_witnesses_valid value_is_null expression
  end

with scalar_expr_witnesses_valid
    (value_is_null : value T -> bool) {kind : scalar_result_kind}
    (expression : scalar_expr T relname kind) : Prop :=
  match expression with
  | SExpr_Leaf _ _ | SExpr_True => True
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      prop_forall (scalar_expr_witnesses_valid value_is_null) arguments
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_witnesses_valid value_is_null condition /\
      scalar_expr_witnesses_valid value_is_null then_expression /\
      scalar_expr_witnesses_valid value_is_null else_expression
  | SExpr_BoolValue _ _ inner
  | SExpr_ValueBool _ inner
  | SExpr_Not inner => scalar_expr_witnesses_valid value_is_null inner
  | SExpr_Conj _ left_expression right_expression =>
      scalar_expr_witnesses_valid value_is_null left_expression /\
      scalar_expr_witnesses_valid value_is_null right_expression
  | SExpr_Quant _ _ arguments subquery
  | SExpr_In arguments subquery =>
      prop_forall (scalar_expr_witnesses_valid value_is_null) arguments /\
      query_expr_scalar_witnesses_valid value_is_null subquery
  | SExpr_Exists subquery =>
      query_expr_scalar_witnesses_valid value_is_null subquery
  | SExpr_Subquery _ null_value subquery =>
      value_is_null null_value = true /\
      query_expr_scalar_witnesses_valid value_is_null subquery
  end.

Definition query_expr_native_scalar_admissible
    (value_is_null : value T -> bool) (query : query_expr T relname) : Prop :=
  query_expr_admissible query /\
  query_expr_scalar_witnesses_valid value_is_null query /\
  query_expr_analysis_error_well_placed query.

Definition scalar_expr_native_admissible
    (value_is_null : value T -> bool) (phase : scalar_phase)
    {kind : scalar_result_kind} (expression : scalar_expr T relname kind) : Prop :=
  scalar_expr_admissible phase expression /\
  scalar_expr_witnesses_valid value_is_null expression.

(** Resolved scalar typing is supplied explicitly because the generic tuple
    interface intentionally contains no SQL signature catalog.  A concrete
    instance (TNull in Logos) owns the authoritative leaf, call, predicate,
    rank, and Boolean result types; the exact AST cannot validate a result
    witness by assertion alone. *)
Definition query_select_list_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (select_list : @_select_list T) : Prop :=
  match select_list with
  | _Select_List items =>
      prop_forall
        (fun item =>
          match item with
          | Select_As term output =>
              leaf_has_type (type_of_attribute T output) term
          end)
        items
  end.

Definition query_aggterms_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (terms : list (@aggterm T)) : Prop :=
  prop_forall
    (fun term => exists result_type, leaf_has_type result_type term) terms.

Definition query_join_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (kind : query_join_kind)
    (matched_select left_select right_select : @_select_list T) : Prop :=
  match kind with
  | QueryJoinInner =>
      query_select_list_scalar_types_valid leaf_has_type matched_select
  | QueryJoinLeft =>
      query_select_list_scalar_types_valid leaf_has_type matched_select /\
      query_select_list_scalar_types_valid leaf_has_type left_select
  | QueryJoinRight =>
      query_select_list_scalar_types_valid leaf_has_type matched_select /\
      query_select_list_scalar_types_valid leaf_has_type right_select
  | QueryJoinFull =>
      query_select_list_scalar_types_valid leaf_has_type matched_select /\
      query_select_list_scalar_types_valid leaf_has_type left_select /\
      query_select_list_scalar_types_valid leaf_has_type right_select
  | QueryJoinSemi | QueryJoinAnti =>
      query_select_list_scalar_types_valid leaf_has_type left_select
  end.

Definition query_grouping_sets_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (grouping_sets : list (query_grouping_set T)) : Prop :=
  prop_forall
    (fun grouping_set =>
      query_select_list_scalar_types_valid leaf_has_type (fst grouping_set) /\
      query_aggterms_scalar_types_valid leaf_has_type (snd grouping_set))
    grouping_sets.

Definition query_window_item_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (rank_type : type T) (item : query_window_item T) : Prop :=
  match item with
  | QueryWindowItem output function =>
      match function with
      | QueryWindowRowNumber _ => type_of_attribute T output = rank_type
      | QueryWindowAggregate term
      | QueryWindowFullPartitionAggregate term =>
          leaf_has_type (type_of_attribute T output) term
      end
  end.

Fixpoint query_expr_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (call_has_type :
      type T -> scalar_operator T -> list (type T) -> Prop)
    (predicate_has_types : predicate T -> list (type T) -> Prop)
    (rank_type boolean_type : type T)
    (query : query_expr T relname) : Prop :=
  match query with
  | QExpr_Error _ _ | QExpr_Values _ _ | QExpr_Table _ _ => True
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        left_query /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        right_query
  | QExpr_Join kind predicate matched_select left_select right_select
      left_query right_query =>
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        predicate /\
      query_join_scalar_types_valid leaf_has_type kind
        matched_select left_select right_select /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        left_query /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        right_query
  | QExpr_Project select_list input =>
      query_select_list_scalar_types_valid leaf_has_type select_list /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type input
  | QExpr_RowMap _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input =>
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  | QExpr_GroupingSets grouping_sets input =>
      query_grouping_sets_scalar_types_valid leaf_has_type grouping_sets /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type input
  | QExpr_Rank _ _ rank_attribute _ input =>
      type_of_attribute T rank_attribute = rank_type /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type input
  | QExpr_Window _ _ items input =>
      prop_forall
        (query_window_item_scalar_types_valid leaf_has_type rank_type) items /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type input
  | QExpr_ScalarProject select_list input =>
      prop_forall
        (fun item => scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type (fst item)) select_list /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  | QExpr_Filter formula input =>
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        formula /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  | QExpr_ScalarFilter expression input =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        expression /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  | QExpr_Group select_list group_terms having input =>
      query_select_list_scalar_types_valid leaf_has_type select_list /\
      query_aggterms_scalar_types_valid leaf_has_type group_terms /\
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        having /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  | QExpr_ScalarGroup select_list group_keys having input =>
      prop_forall
        (fun item => scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type (fst item)) select_list /\
      prop_forall
        (scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type)
        group_keys /\
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type having /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        input
  end

with formula_expr_scalar_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (call_has_type :
      type T -> scalar_operator T -> list (type T) -> Prop)
    (predicate_has_types : predicate T -> list (type T) -> Prop)
    (rank_type boolean_type : type T)
    (formula : formula_expr T relname) : Prop :=
  match formula with
  | FExpr_Conj _ left_formula right_formula =>
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        left_formula /\
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        right_formula
  | FExpr_Not inner =>
      formula_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        inner
  | FExpr_True => True
  | FExpr_Pred predicate arguments =>
      exists argument_types,
        Forall2
          (fun term argument_type => leaf_has_type argument_type term)
          arguments argument_types /\
        predicate_has_types predicate argument_types
  | FExpr_Quant _ predicate arguments subquery =>
      (exists argument_types,
        Forall2
          (fun term argument_type => leaf_has_type argument_type term)
          arguments argument_types /\
        predicate_has_types predicate
          (argument_types ++
            map (type_of_attribute T) (query_expr_outputs subquery))) /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type subquery
  | FExpr_In select_items subquery =>
      prop_forall
        (fun item =>
          match item with
          | Select_As term output =>
              leaf_has_type (type_of_attribute T output) term
          end)
        select_items /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type subquery
  | FExpr_Exists subquery =>
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        subquery
  | FExpr_Scalar expression =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        expression
  end

with scalar_expr_types_valid
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (call_has_type :
      type T -> scalar_operator T -> list (type T) -> Prop)
    (predicate_has_types : predicate T -> list (type T) -> Prop)
    (rank_type boolean_type : type T) {kind : scalar_result_kind}
    (expression : scalar_expr T relname kind) : Prop :=
  match expression with
  | SExpr_Leaf result_type term => leaf_has_type result_type term
  | SExpr_Call result_type operator arguments =>
      prop_forall
        (scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type)
        arguments /\
      call_has_type result_type operator (map scalar_expr_type arguments)
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        condition /\
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        then_expression /\
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        else_expression
  | SExpr_BoolValue result_type embed inner =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type inner /\
      (forall truth, type_of_value T (embed truth) = result_type)
  | SExpr_ValueBool _ inner =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type inner /\
      scalar_expr_type inner = boolean_type
  | SExpr_Pred predicate arguments =>
      prop_forall
        (scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type)
        arguments /\
      predicate_has_types predicate (map scalar_expr_type arguments)
  | SExpr_Conj _ left_expression right_expression =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        left_expression /\
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type
        right_expression
  | SExpr_Not inner =>
      scalar_expr_types_valid leaf_has_type call_has_type predicate_has_types
        rank_type boolean_type inner
  | SExpr_True => True
  | SExpr_Quant _ predicate arguments subquery =>
      prop_forall
        (scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type)
        arguments /\
      predicate_has_types predicate
        (map scalar_expr_type arguments ++
          map (type_of_attribute T) (query_expr_outputs subquery)) /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        subquery
  | SExpr_In arguments subquery =>
      prop_forall
        (scalar_expr_types_valid leaf_has_type call_has_type
          predicate_has_types rank_type boolean_type)
        arguments /\
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        subquery
  | SExpr_Exists subquery =>
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        subquery
  | SExpr_Subquery _ _ subquery =>
      query_expr_scalar_types_valid leaf_has_type call_has_type
        predicate_has_types rank_type boolean_type
        subquery
  end.

Definition query_expr_typed_native_scalar_admissible
    (leaf_has_type : type T -> @aggterm T -> Prop)
    (call_has_type :
      type T -> scalar_operator T -> list (type T) -> Prop)
    (predicate_has_types : predicate T -> list (type T) -> Prop)
    (rank_type boolean_type : type T) (value_is_null : value T -> bool)
    (query : query_expr T relname) : Prop :=
  query_expr_native_scalar_admissible value_is_null query /\
  query_expr_scalar_types_valid leaf_has_type call_has_type predicate_has_types
    rank_type boolean_type query.

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
intros select_items subquery Hadmissible.
unfold formula_expr_admissible in Hadmissible; simpl in Hadmissible; tauto.
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
Arguments formula_expr_admissible_at {T relname} basesort _ _.
Arguments formula_expr_admissible {T relname} basesort _.
Arguments scalar_expr_admissible {T relname} basesort _ {_} _.
Arguments query_expr_scalar_witnesses_valid {T relname} _ _.
Arguments formula_expr_scalar_witnesses_valid {T relname} _ _.
Arguments scalar_expr_witnesses_valid {T relname} _ {_} _.
Arguments query_expr_native_scalar_admissible {T relname} basesort _ _.
Arguments scalar_expr_native_admissible {T relname} basesort _ _ {_} _.
Arguments query_expr_scalar_types_valid {T relname} _ _ _ _ _ _.
Arguments formula_expr_scalar_types_valid {T relname} _ _ _ _ _ _.
Arguments scalar_expr_types_valid {T relname} _ _ _ _ _ {_} _.
Arguments query_expr_typed_native_scalar_admissible {T relname}
  basesort _ _ _ _ _ _ _.
