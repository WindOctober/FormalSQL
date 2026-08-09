(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                Typed contextual congruence for query expressions               *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Program.Equality.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
        ATerms Projection SqlOutcome SqlErrorSemantics SqlBagAbstraction
        SqlQuerySyntax SqlQuerySemantics SqlQueryFacts.

(** Ordered row-list outcomes are the single exact query semantics.  [alpha]
    maps them to possible bags; [gamma] forgets order by permutation closure
    and is therefore an over-approximation.  [BagClosed] is exactly where that
    abstraction is complete for equivalence.  Context substitution below is
    stated first for the exact outcomes, then bridged to possible bags. *)

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition tuple := tuple T.
Local Definition value := value T.
Local Definition setA := Fset.set (A T).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> setA.
Hypothesis instance : relname -> bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value) ->
  option sql_runtime_error.
Hypothesis value_is_null : value -> bool.
Hypothesis boolean_schedule : boolean_site -> boolean_evaluation_order.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_query_cardinality :=
  (@eval_query_cardinality_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_query_exists :=
  (@eval_query_exists_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_value :=
  (@eval_scalar_value_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_grouping_sets_bag :=
  (@eval_grouping_sets_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_row_conditions :=
  (@eval_join_row_conditions_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_conditions :=
  (@eval_join_conditions_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_join_bag :=
  (@eval_join_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Ltac transport_query_forward equivalence :=
  match goal with
  | Hsource : eval_query ?current_env _ ?source_outcome
      |- eval_query ?current_env _ ?target_outcome =>
      unify source_outcome target_outcome;
      exact (proj1 (equivalence current_env source_outcome) Hsource)
  end.

Ltac transport_query_backward equivalence :=
  match goal with
  | Hsource : eval_query ?current_env _ ?source_outcome
      |- eval_query ?current_env _ ?target_outcome =>
      unify source_outcome target_outcome;
      exact (proj2 (equivalence current_env source_outcome) Hsource)
  end.

(** Raw global equality retains errors as ordinary outcomes. *)
Definition query_expr_global_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  forall env outcome,
    eval_query env left outcome <-> eval_query env right outcome.

(** EXISTS has a deliberately weaker, target-list-eliding observation than a
    complete query result.  Ordinary row-outcome equivalence does not imply
    this relation (for example, a failing target expression is dead only to
    EXISTS), so it is tracked explicitly. *)
Definition query_expr_global_cardinality_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  forall env outcome,
    eval_query_cardinality env left outcome <->
    eval_query_cardinality env right outcome.

Definition query_expr_global_exists_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  forall env outcome,
    eval_query_exists env left outcome <-> eval_query_exists env right outcome.

Definition query_expr_global_typed_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  query_expr_global_outcome_equiv left right.

Lemma query_expr_global_outcome_equiv_refl :
  forall query, query_expr_global_outcome_equiv query query.
Proof.
intros query env outcome; tauto.
Qed.

Lemma query_expr_global_cardinality_outcome_equiv_refl :
  forall query, query_expr_global_cardinality_outcome_equiv query query.
Proof.
intros query env outcome; tauto.
Qed.

Lemma query_expr_global_exists_outcome_equiv_refl :
  forall query, query_expr_global_exists_outcome_equiv query query.
Proof.
intros query env outcome; tauto.
Qed.

Lemma query_expr_global_typed_outcome_equiv_refl :
  forall query, query_expr_global_typed_outcome_equiv query query.
Proof.
intro query; split.
- reflexivity.
- apply query_expr_global_outcome_equiv_refl.
Qed.

(** Scalar congruence is indexed by the result kind, so value and
    three-valued Boolean outcomes cannot be interchanged. *)
Definition scalar_expr_global_outcome_equiv
    {kind : scalar_result_kind}
    (left right : scalar_expr T relname kind) : Prop :=
  match kind as result_kind return
      scalar_expr T relname result_kind ->
      scalar_expr T relname result_kind -> Prop with
  | ScalarResultValue =>
      fun left_value right_value => forall env outcome,
        eval_scalar_value env left_value outcome <->
        eval_scalar_value env right_value outcome
  | ScalarResultBoolean =>
      fun left_boolean right_boolean => forall env outcome,
        eval_scalar_boolean env left_boolean outcome <->
        eval_scalar_boolean env right_boolean outcome
  end left right.

(** GROUP additionally observes eager aggregate finalization owned by the
    current query level. *)
Definition scalar_expr_global_group_outcome_equiv
    {kind : scalar_result_kind}
    (left right : scalar_expr T relname kind) : Prop :=
  scalar_expr_global_outcome_equiv left right /\
  forall env,
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env left =
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env right.

Definition scalar_value_expr_list_global_outcome_equiv
    (left right : list (scalar_expr T relname ScalarResultValue)) : Prop :=
  Forall2 scalar_expr_global_outcome_equiv left right.

Definition scalar_boolean_expr_list_global_outcome_equiv
    (left right : list (scalar_expr T relname ScalarResultBoolean)) : Prop :=
  Forall2 scalar_expr_global_outcome_equiv left right.

Definition scalar_select_list_global_outcome_equiv
    (left right : @query_select_list T relname) : Prop :=
  Forall2
    (fun left_item right_item =>
      snd left_item = snd right_item /\
      scalar_expr_global_outcome_equiv
        (fst left_item) (fst right_item))
    left right.

Lemma scalar_expr_global_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_global_outcome_equiv expression expression.
Proof.
intros [|] expression env outcome; tauto.
Qed.

Lemma scalar_expr_global_outcome_equiv_sym :
  forall kind (left right : scalar_expr T relname kind),
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv right left.
Proof.
intros [|] left right Hequiv env outcome; symmetry; apply Hequiv.
Qed.

Lemma scalar_expr_global_group_outcome_equiv_refl :
  forall kind (expression : scalar_expr T relname kind),
    scalar_expr_global_group_outcome_equiv expression expression.
Proof.
intros kind expression; split.
- apply scalar_expr_global_outcome_equiv_refl.
- reflexivity.
Qed.

Lemma scalar_expr_list_global_outcome_equiv_refl :
  forall kind (expressions : list (scalar_expr T relname kind)),
    Forall2 scalar_expr_global_outcome_equiv expressions expressions.
Proof.
intros kind expressions; induction expressions; constructor; auto using
  scalar_expr_global_outcome_equiv_refl.
Qed.

Lemma scalar_expr_list_context_global_outcome_equiv :
  forall kind prefix
      (left right : scalar_expr T relname kind) suffix,
    scalar_expr_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (prefix ++ left :: suffix) (prefix ++ right :: suffix).
Proof.
intros kind prefix left right suffix Hequiv.
apply Forall2_app.
- apply scalar_expr_list_global_outcome_equiv_refl.
- constructor; [exact Hequiv|].
  apply scalar_expr_list_global_outcome_equiv_refl.
Qed.

Lemma scalar_select_list_global_outcome_equiv_outputs :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_select_outputs left = scalar_select_outputs right.
Proof.
intros left right Hequiv; induction Hequiv as
  [|[left_expression left_attribute] [right_expression right_attribute]
    left right [Hattribute _] _ IH]; cbn in *; [reflexivity|now f_equal].
Qed.

Lemma scalar_select_list_global_outcome_equiv_values :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_value_expr_list_global_outcome_equiv
      (map fst left) (map fst right).
Proof.
intros left right Hequiv; induction Hequiv as
  [|[left_expression left_attribute] [right_expression right_attribute]
    left right [_ Hexpression] _ IH]; cbn; constructor; assumption.
Qed.

Lemma scalar_select_list_global_outcome_equiv_refl :
  forall select_list,
    scalar_select_list_global_outcome_equiv select_list select_list.
Proof.
intro select_list; induction select_list as
  [|[expression attribute] select_list IH]; constructor; auto.
split; [reflexivity|apply scalar_expr_global_outcome_equiv_refl].
Qed.

Lemma scalar_select_list_global_outcome_equiv_sym :
  forall left right,
    scalar_select_list_global_outcome_equiv left right ->
    scalar_select_list_global_outcome_equiv right left.
Proof.
intros left right Hequiv; induction Hequiv as
  [|[left_expression left_attribute] [right_expression right_attribute]
    left right [Hattribute Hexpression] _ IH]; constructor; auto.
split; [now symmetry|now apply scalar_expr_global_outcome_equiv_sym].
Qed.

Inductive query_context_demand : Type :=
  | QueryContextRows
  | QueryContextExists.

Definition query_expr_global_demand_equiv
    (demand : query_context_demand)
    (left right : query_expr T relname) : Prop :=
  match demand with
  | QueryContextRows => query_expr_global_typed_outcome_equiv left right
  | QueryContextExists => query_expr_global_exists_outcome_equiv left right
  end.

(** A result-kind-indexed scalar context contains exactly one query hole.
    Nested query paths are represented by composing this plug operation with
    [plug_query_expr_context], so the scalar grammar stays canonical instead
    of embedding a second query AST. *)
Inductive scalar_expr_context : scalar_result_kind -> Type :=
  | SCtx_CallArgument : type T -> scalar_operator T ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultValue ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultValue
  | SCtx_CaseCondition : type T ->
      scalar_expr_context ScalarResultBoolean ->
      scalar_expr T relname ScalarResultValue ->
      scalar_expr T relname ScalarResultValue ->
      scalar_expr_context ScalarResultValue
  | SCtx_CaseThen : type T ->
      scalar_expr T relname ScalarResultBoolean ->
      scalar_expr_context ScalarResultValue ->
      scalar_expr T relname ScalarResultValue ->
      scalar_expr_context ScalarResultValue
  | SCtx_CaseElse : type T ->
      scalar_expr T relname ScalarResultBoolean ->
      scalar_expr T relname ScalarResultValue ->
      scalar_expr_context ScalarResultValue ->
      scalar_expr_context ScalarResultValue
  | SCtx_BoolValue : type T -> (Bool.b (B T) -> value) ->
      scalar_expr_context ScalarResultBoolean ->
      scalar_expr_context ScalarResultValue
  | SCtx_Subquery : type T -> value ->
      scalar_expr_context ScalarResultValue
  | SCtx_ValueBool : (value -> Bool.b (B T)) ->
      scalar_expr_context ScalarResultValue ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_PredArgument : predicate T ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultValue ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_ConjListOperand : list (list boolean_site) -> and_or ->
      list (scalar_expr T relname ScalarResultBoolean) ->
      scalar_expr_context ScalarResultBoolean ->
      list (scalar_expr T relname ScalarResultBoolean) ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_Not : scalar_expr_context ScalarResultBoolean ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_QuantArgument : quantifier -> predicate T ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultValue ->
      list (scalar_expr T relname ScalarResultValue) ->
      query_expr T relname -> scalar_expr_context ScalarResultBoolean
  | SCtx_QuantSubquery : quantifier -> predicate T ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_InArgument :
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultValue ->
      list (scalar_expr T relname ScalarResultValue) ->
      query_expr T relname -> scalar_expr_context ScalarResultBoolean
  | SCtx_InSubquery :
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultBoolean
  | SCtx_ExistsSubquery : scalar_expr_context ScalarResultBoolean.

Fixpoint scalar_expr_context_demand
    {kind : scalar_result_kind} (context : scalar_expr_context kind) :
    query_context_demand :=
  match context with
  | SCtx_CallArgument _ _ _ child _ => scalar_expr_context_demand child
  | SCtx_CaseCondition _ child _ _ => scalar_expr_context_demand child
  | SCtx_CaseThen _ _ child _ => scalar_expr_context_demand child
  | SCtx_CaseElse _ _ _ child => scalar_expr_context_demand child
  | SCtx_BoolValue _ _ child => scalar_expr_context_demand child
  | SCtx_Subquery _ _ => QueryContextRows
  | SCtx_ValueBool _ child => scalar_expr_context_demand child
  | SCtx_PredArgument _ _ child _ => scalar_expr_context_demand child
  | SCtx_ConjListOperand _ _ _ child _ => scalar_expr_context_demand child
  | SCtx_Not child => scalar_expr_context_demand child
  | SCtx_QuantArgument _ _ _ child _ _ => scalar_expr_context_demand child
  | SCtx_QuantSubquery _ _ _ => QueryContextRows
  | SCtx_InArgument _ child _ _ => scalar_expr_context_demand child
  | SCtx_InSubquery _ => QueryContextRows
  | SCtx_ExistsSubquery => QueryContextExists
  end.

Fixpoint plug_scalar_expr_context
    {kind : scalar_result_kind} (context : scalar_expr_context kind)
    (replacement : query_expr T relname) : scalar_expr T relname kind :=
  match context with
  | SCtx_CallArgument result_type operator prefix child suffix =>
      SExpr_Call result_type operator
        (prefix ++ plug_scalar_expr_context child replacement :: suffix)
  | SCtx_CaseCondition result_type child then_expression else_expression =>
      SExpr_Case result_type (plug_scalar_expr_context child replacement)
        then_expression else_expression
  | SCtx_CaseThen result_type condition child else_expression =>
      SExpr_Case result_type condition
        (plug_scalar_expr_context child replacement) else_expression
  | SCtx_CaseElse result_type condition then_expression child =>
      SExpr_Case result_type condition then_expression
        (plug_scalar_expr_context child replacement)
  | SCtx_BoolValue result_type embed child =>
      SExpr_BoolValue result_type embed
        (plug_scalar_expr_context child replacement)
  | SCtx_Subquery result_type null_value =>
      SExpr_Subquery result_type null_value replacement
  | SCtx_ValueBool decode child =>
      SExpr_ValueBool decode (plug_scalar_expr_context child replacement)
  | SCtx_PredArgument predicate prefix child suffix =>
      SExpr_Pred predicate
        (prefix ++ plug_scalar_expr_context child replacement :: suffix)
  | SCtx_ConjListOperand site_rows operation prefix child suffix =>
      SExpr_ConjList site_rows operation
        (prefix ++ plug_scalar_expr_context child replacement :: suffix)
  | SCtx_Not child =>
      SExpr_Not (plug_scalar_expr_context child replacement)
  | SCtx_QuantArgument quantifier predicate prefix child suffix subquery =>
      SExpr_Quant quantifier predicate
        (prefix ++ plug_scalar_expr_context child replacement :: suffix)
        subquery
  | SCtx_QuantSubquery quantifier predicate arguments =>
      SExpr_Quant quantifier predicate arguments replacement
  | SCtx_InArgument prefix child suffix subquery =>
      SExpr_In
        (prefix ++ plug_scalar_expr_context child replacement :: suffix)
        subquery
  | SCtx_InSubquery arguments => SExpr_In arguments replacement
  | SCtx_ExistsSubquery => SExpr_Exists replacement
  end.

Record scalar_select_context : Type := ScalarSelectContext {
  scalar_select_context_prefix : @query_select_list T relname;
  scalar_select_context_expression : scalar_expr_context ScalarResultValue;
  scalar_select_context_attribute : attribute T;
  scalar_select_context_suffix : @query_select_list T relname
}.

Definition plug_scalar_select_context
    (context : scalar_select_context) (replacement : query_expr T relname) :
    @query_select_list T relname :=
  scalar_select_context_prefix context ++
  (plug_scalar_expr_context (scalar_select_context_expression context)
      replacement,
    scalar_select_context_attribute context) ::
  scalar_select_context_suffix context.

Definition scalar_select_context_demand
    (context : scalar_select_context) : query_context_demand :=
  scalar_expr_context_demand (scalar_select_context_expression context).

Record scalar_value_list_context : Type := ScalarValueListContext {
  scalar_value_list_context_prefix :
    list (scalar_expr T relname ScalarResultValue);
  scalar_value_list_context_expression :
    scalar_expr_context ScalarResultValue;
  scalar_value_list_context_suffix :
    list (scalar_expr T relname ScalarResultValue)
}.

Definition plug_scalar_value_list_context
    (context : scalar_value_list_context)
    (replacement : query_expr T relname) :
    list (scalar_expr T relname ScalarResultValue) :=
  scalar_value_list_context_prefix context ++
  plug_scalar_expr_context (scalar_value_list_context_expression context)
    replacement ::
  scalar_value_list_context_suffix context.

Definition scalar_value_list_context_demand
    (context : scalar_value_list_context) : query_context_demand :=
  scalar_expr_context_demand (scalar_value_list_context_expression context).

(** Query contexts cover both relational children and every typed scalar
    payload owned by a query operator. *)
Inductive query_expr_context : Type :=
  | QCtx_Hole : query_expr_context
  | QCtx_SetLeft : set_op -> query_expr_context -> query_expr T relname ->
      query_expr_context
  | QCtx_SetRight : set_op -> query_expr T relname -> query_expr_context ->
      query_expr_context
  | QCtx_NaturalJoinLeft : query_expr_context -> query_expr T relname ->
      query_expr_context
  | QCtx_NaturalJoinRight : query_expr T relname -> query_expr_context ->
      query_expr_context
  | QCtx_CrossJoinLeft : query_expr_context -> query_expr T relname ->
      query_expr_context
  | QCtx_CrossJoinRight : query_expr T relname -> query_expr_context ->
      query_expr_context
  | QCtx_JoinLeft : query_join_kind ->
      scalar_expr T relname ScalarResultBoolean ->
      @query_select_list T relname -> @query_select_list T relname ->
      @query_select_list T relname -> query_expr_context ->
      query_expr T relname -> query_expr_context
  | QCtx_JoinRight : query_join_kind ->
      scalar_expr T relname ScalarResultBoolean ->
      @query_select_list T relname -> @query_select_list T relname ->
      @query_select_list T relname -> query_expr T relname ->
      query_expr_context -> query_expr_context
  | QCtx_JoinPredicate : query_join_kind ->
      scalar_expr_context ScalarResultBoolean ->
      @query_select_list T relname -> @query_select_list T relname ->
      @query_select_list T relname -> query_expr T relname ->
      query_expr T relname -> query_expr_context
  | QCtx_JoinMatchedSelect : query_join_kind ->
      scalar_expr T relname ScalarResultBoolean -> scalar_select_context ->
      @query_select_list T relname -> @query_select_list T relname ->
      query_expr T relname -> query_expr T relname -> query_expr_context
  | QCtx_JoinLeftSelect : query_join_kind ->
      scalar_expr T relname ScalarResultBoolean ->
      @query_select_list T relname -> scalar_select_context ->
      @query_select_list T relname -> query_expr T relname ->
      query_expr T relname -> query_expr_context
  | QCtx_JoinRightSelect : query_join_kind ->
      scalar_expr T relname ScalarResultBoolean ->
      @query_select_list T relname -> @query_select_list T relname ->
      scalar_select_context -> query_expr T relname ->
      query_expr T relname -> query_expr_context
  | QCtx_Project : @query_select_list T relname -> query_expr_context ->
      query_expr_context
  | QCtx_ProjectSelect : scalar_select_context -> query_expr T relname ->
      query_expr_context
  | QCtx_RowMap : list (attribute T) ->
      (tuple -> sql_outcome tuple) -> query_expr_context ->
      query_expr_context
  | QCtx_FilterInput : scalar_expr T relname ScalarResultBoolean ->
      query_expr_context -> query_expr_context
  | QCtx_FilterExpression : scalar_expr_context ScalarResultBoolean ->
      query_expr T relname -> query_expr_context
  | QCtx_GroupInput : @query_select_list T relname ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr T relname ScalarResultBoolean -> query_expr_context ->
      query_expr_context
  | QCtx_GroupSelect : scalar_select_context ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr T relname ScalarResultBoolean -> query_expr T relname ->
      query_expr_context
  | QCtx_GroupKey : @query_select_list T relname ->
      scalar_value_list_context ->
      scalar_expr T relname ScalarResultBoolean -> query_expr T relname ->
      query_expr_context
  | QCtx_GroupHaving : @query_select_list T relname ->
      list (scalar_expr T relname ScalarResultValue) ->
      scalar_expr_context ScalarResultBoolean -> query_expr T relname ->
      query_expr_context
  | QCtx_GroupingSets : list (@query_grouping_set T relname) ->
      query_expr_context -> query_expr_context
  | QCtx_GroupingSetsSelect : list (@query_grouping_set T relname) ->
      scalar_select_context ->
      list (scalar_expr T relname ScalarResultValue) ->
      list (@query_grouping_set T relname) -> query_expr T relname ->
      query_expr_context
  | QCtx_GroupingSetsKey : list (@query_grouping_set T relname) ->
      @query_select_list T relname -> scalar_value_list_context ->
      list (@query_grouping_set T relname) -> query_expr T relname ->
      query_expr_context
  | QCtx_Rank : list (SqlOrder.sort_key T) ->
      list (SqlOrder.sort_key T) -> attribute T ->
      (nat -> option value) -> query_expr_context -> query_expr_context
  | QCtx_Window : list (SqlOrder.sort_key T) ->
      list (SqlOrder.sort_key T) -> list (query_window_item T) ->
      query_expr_context -> query_expr_context
  | QCtx_Distinct : query_expr_context -> query_expr_context
  | QCtx_OrderBy : list (SqlOrder.sort_key T) -> query_expr_context ->
      query_expr_context
  | QCtx_Offset : nat -> query_expr_context -> query_expr_context
  | QCtx_Fetch : nat -> query_expr_context -> query_expr_context.

Fixpoint query_expr_context_demand
    (context : query_expr_context) : query_context_demand :=
  match context with
  | QCtx_Hole => QueryContextRows
  | QCtx_SetLeft _ child _ | QCtx_SetRight _ _ child
  | QCtx_NaturalJoinLeft child _ | QCtx_NaturalJoinRight _ child
  | QCtx_CrossJoinLeft child _ | QCtx_CrossJoinRight _ child
  | QCtx_JoinLeft _ _ _ _ _ child _
  | QCtx_JoinRight _ _ _ _ _ _ child
  | QCtx_Project _ child | QCtx_RowMap _ _ child
  | QCtx_FilterInput _ child | QCtx_GroupInput _ _ _ child
  | QCtx_GroupingSets _ child | QCtx_Rank _ _ _ _ child
  | QCtx_Window _ _ _ child | QCtx_Distinct child
  | QCtx_OrderBy _ child | QCtx_Offset _ child | QCtx_Fetch _ child =>
      query_expr_context_demand child
  | QCtx_JoinPredicate _ child _ _ _ _ _ =>
      scalar_expr_context_demand child
  | QCtx_JoinMatchedSelect _ _ child _ _ _ _
  | QCtx_JoinLeftSelect _ _ _ child _ _ _
  | QCtx_JoinRightSelect _ _ _ _ child _ _
  | QCtx_ProjectSelect child _
  | QCtx_GroupSelect child _ _ _
  | QCtx_GroupingSetsSelect _ child _ _ _ =>
      scalar_select_context_demand child
  | QCtx_FilterExpression child _
  | QCtx_GroupHaving _ _ child _ => scalar_expr_context_demand child
  | QCtx_GroupKey _ child _ _
  | QCtx_GroupingSetsKey _ _ child _ _ =>
      scalar_value_list_context_demand child
  end.

Fixpoint plug_query_expr_context
    (context : query_expr_context) (replacement : query_expr T relname) :
    query_expr T relname :=
  match context with
  | QCtx_Hole => replacement
  | QCtx_SetLeft operation child fixed_query =>
      QExpr_Set operation (plug_query_expr_context child replacement) fixed_query
  | QCtx_SetRight operation fixed_query child =>
      QExpr_Set operation fixed_query (plug_query_expr_context child replacement)
  | QCtx_NaturalJoinLeft child fixed_query =>
      QExpr_NaturalJoin (plug_query_expr_context child replacement) fixed_query
  | QCtx_NaturalJoinRight fixed_query child =>
      QExpr_NaturalJoin fixed_query (plug_query_expr_context child replacement)
  | QCtx_CrossJoinLeft child fixed_query =>
      QExpr_CrossJoin (plug_query_expr_context child replacement) fixed_query
  | QCtx_CrossJoinRight fixed_query child =>
      QExpr_CrossJoin fixed_query (plug_query_expr_context child replacement)
  | QCtx_JoinLeft kind predicate matched_select left_select right_select
      child fixed_query =>
      QExpr_Join kind predicate matched_select left_select right_select
        (plug_query_expr_context child replacement) fixed_query
  | QCtx_JoinRight kind predicate matched_select left_select right_select
      fixed_query child =>
      QExpr_Join kind predicate matched_select left_select right_select
        fixed_query (plug_query_expr_context child replacement)
  | QCtx_JoinPredicate kind predicate matched_select left_select right_select
      left_query right_query =>
      QExpr_Join kind (plug_scalar_expr_context predicate replacement)
        matched_select left_select right_select left_query right_query
  | QCtx_JoinMatchedSelect kind predicate matched_select left_select
      right_select left_query right_query =>
      QExpr_Join kind predicate
        (plug_scalar_select_context matched_select replacement)
        left_select right_select left_query right_query
  | QCtx_JoinLeftSelect kind predicate matched_select left_select
      right_select left_query right_query =>
      QExpr_Join kind predicate matched_select
        (plug_scalar_select_context left_select replacement)
        right_select left_query right_query
  | QCtx_JoinRightSelect kind predicate matched_select left_select
      right_select left_query right_query =>
      QExpr_Join kind predicate matched_select left_select
        (plug_scalar_select_context right_select replacement)
        left_query right_query
  | QCtx_Project select_list child =>
      QExpr_Project select_list (plug_query_expr_context child replacement)
  | QCtx_ProjectSelect select_list input =>
      QExpr_Project (plug_scalar_select_context select_list replacement) input
  | QCtx_RowMap outputs row_map child =>
      QExpr_RowMap outputs row_map (plug_query_expr_context child replacement)
  | QCtx_FilterInput expression child =>
      QExpr_Filter expression (plug_query_expr_context child replacement)
  | QCtx_FilterExpression expression input =>
      QExpr_Filter (plug_scalar_expr_context expression replacement) input
  | QCtx_GroupInput select_list group_keys having child =>
      QExpr_Group select_list group_keys having
        (plug_query_expr_context child replacement)
  | QCtx_GroupSelect select_list group_keys having input =>
      QExpr_Group (plug_scalar_select_context select_list replacement)
        group_keys having input
  | QCtx_GroupKey select_list group_keys having input =>
      QExpr_Group select_list
        (plug_scalar_value_list_context group_keys replacement) having input
  | QCtx_GroupHaving select_list group_keys having input =>
      QExpr_Group select_list group_keys
        (plug_scalar_expr_context having replacement) input
  | QCtx_GroupingSets grouping_sets child =>
      QExpr_GroupingSets grouping_sets
        (plug_query_expr_context child replacement)
  | QCtx_GroupingSetsSelect prefix select_list group_keys suffix input =>
      QExpr_GroupingSets
        (prefix ++
          (plug_scalar_select_context select_list replacement, group_keys) ::
          suffix) input
  | QCtx_GroupingSetsKey prefix select_list group_keys suffix input =>
      QExpr_GroupingSets
        (prefix ++
          (select_list,
            plug_scalar_value_list_context group_keys replacement) :: suffix)
        input
  | QCtx_Rank partition_keys order_keys rank_attribute rank_value child =>
      QExpr_Rank partition_keys order_keys rank_attribute rank_value
        (plug_query_expr_context child replacement)
  | QCtx_Window partition_keys order_keys items child =>
      QExpr_Window partition_keys order_keys items
        (plug_query_expr_context child replacement)
  | QCtx_Distinct child =>
      QExpr_Distinct (plug_query_expr_context child replacement)
  | QCtx_OrderBy keys child =>
      QExpr_OrderBy keys (plug_query_expr_context child replacement)
  | QCtx_Offset offset child =>
      QExpr_Offset offset (plug_query_expr_context child replacement)
  | QCtx_Fetch count child =>
      QExpr_Fetch count (plug_query_expr_context child replacement)
  end.

Lemma scalar_select_context_global_outcome_equiv :
  forall context left right,
    scalar_expr_global_outcome_equiv
      (plug_scalar_expr_context
        (scalar_select_context_expression context) left)
      (plug_scalar_expr_context
        (scalar_select_context_expression context) right) ->
    scalar_select_list_global_outcome_equiv
      (plug_scalar_select_context context left)
      (plug_scalar_select_context context right).
Proof.
intros [prefix expression attribute suffix] left right Hequiv; cbn in *.
apply Forall2_app.
- induction prefix as [|[head_expression head_attribute] prefix IH];
    constructor; auto.
  split; [reflexivity|apply scalar_expr_global_outcome_equiv_refl].
- constructor.
  + split; [reflexivity|exact Hequiv].
  + induction suffix as [|[head_expression head_attribute] suffix IH];
      constructor; auto.
    split; [reflexivity|apply scalar_expr_global_outcome_equiv_refl].
Qed.

Lemma eval_scalar_values_outcome_global_congr :
  forall left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    forall env outcome,
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left outcome <->
      @eval_scalar_values_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right outcome.
Proof.
intros left right Hequiv; induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros env outcome; split; intro Heval; inversion Heval; subst.
- constructor.
- constructor.
- apply EScalarValues_HeadError.
  now apply (proj1 (Hexpression env _)).
- eapply EScalarValues_Cons.
  + now apply (proj1 (Hexpression env _)).
  + now apply (proj1 (IH env _)).
- apply EScalarValues_HeadError.
  now apply (proj2 (Hexpression env _)).
- eapply EScalarValues_Cons.
  + now apply (proj2 (Hexpression env _)).
  + now apply (proj2 (IH env _)).
Qed.

Lemma eval_scalar_boolean_operands_outcome_global_congr :
  forall left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    forall env operation outcome,
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env operation left outcome <->
      @eval_scalar_boolean_operands_outcome T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null boolean_schedule env operation right outcome.
Proof.
intros left right Hequiv; induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros env operation outcome; split; intro Heval; inversion Heval; subst.
- constructor.
- constructor.
- apply EScalarBooleanOperands_HeadError.
  now apply (proj1 (Hexpression env _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj1 (Hexpression env _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj1 (Hexpression env _)); eassumption.
  + eassumption.
  + now apply (proj1 (IH env operation _)).
- apply EScalarBooleanOperands_HeadError.
  now apply (proj2 (Hexpression env _)).
- eapply EScalarBooleanOperands_HeadDecides.
  + eapply (proj2 (Hexpression env _)); eassumption.
  + eassumption.
- eapply EScalarBooleanOperands_Continue.
  + eapply (proj2 (Hexpression env _)); eassumption.
  + eassumption.
  + now apply (proj2 (IH env operation _)).
Qed.

Lemma insert_boolean_operand_global_Forall2 :
  forall sites left_expression right_expression left right,
    scalar_expr_global_outcome_equiv left_expression right_expression ->
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (@insert_boolean_operand T relname boolean_schedule
        sites left_expression left)
      (@insert_boolean_operand T relname boolean_schedule
        sites right_expression right).
Proof.
intros sites left_expression right_expression left right
  Hexpression Hordered.
revert sites; induction Hordered as
  [|left_head right_head left_tail right_tail Hhead Htail IH];
  intros [|site sites]; cbn.
- now constructor.
- now constructor.
- constructor; [exact Hexpression|now constructor].
- destruct (boolean_schedule site); cbn.
  + constructor; [exact Hexpression|now constructor].
  + constructor; [exact Hhead|now apply IH].
Qed.

Lemma schedule_boolean_operands_aux_global_Forall2 :
  forall site_rows left right left_ordered right_ordered,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    scalar_boolean_expr_list_global_outcome_equiv
      left_ordered right_ordered ->
    Forall2 scalar_expr_global_outcome_equiv
      (@schedule_boolean_operands_aux T relname boolean_schedule
        site_rows left left_ordered)
      (@schedule_boolean_operands_aux T relname boolean_schedule
        site_rows right right_ordered).
Proof.
intros site_rows left right left_ordered right_ordered Hequiv.
revert site_rows left_ordered right_ordered.
induction Hequiv as
  [|left_expression right_expression left right Hexpression _ IH];
  intros [|sites site_rows] left_ordered right_ordered Hordered; cbn.
- exact Hordered.
- exact Hordered.
- apply IH.
  now apply Forall2_app; [exact Hordered|constructor].
- apply IH.
  now apply insert_boolean_operand_global_Forall2.
Qed.

Lemma schedule_boolean_operands_global_Forall2 :
  forall site_rows left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    Forall2 scalar_expr_global_outcome_equiv
      (@schedule_boolean_operands T relname boolean_schedule site_rows left)
      (@schedule_boolean_operands T relname boolean_schedule site_rows right).
Proof.
intros site_rows left right Hequiv.
unfold schedule_boolean_operands.
eapply schedule_boolean_operands_aux_global_Forall2;
  [exact Hequiv|constructor].
Qed.

Lemma scalar_expr_call_global_congr :
  forall result_type operator left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Call result_type operator left)
      (SExpr_Call result_type operator right).
Proof.
intros result_type operator left right Harguments env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_CallArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_CallSuccess.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_CallArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_CallSuccess.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
Qed.

Lemma scalar_expr_case_global_congr :
  forall result_type left_condition right_condition
      left_then right_then left_else right_else,
    scalar_expr_global_outcome_equiv left_condition right_condition ->
    scalar_expr_global_outcome_equiv left_then right_then ->
    scalar_expr_global_outcome_equiv left_else right_else ->
    scalar_expr_global_outcome_equiv
      (SExpr_Case result_type left_condition left_then left_else)
      (SExpr_Case result_type right_condition right_then right_else).
Proof.
intros result_type left_condition right_condition left_then right_then
  left_else right_else Hcondition Hthen Helse env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_CaseConditionError.
  now apply (proj1 (Hcondition env _)).
- eapply EScalar_CaseThen.
  + eapply (proj1 (Hcondition env _)); eassumption.
  + eassumption.
  + eapply (proj1 (Hthen env _)); eassumption.
- eapply EScalar_CaseElse.
  + eapply (proj1 (Hcondition env _)); eassumption.
  + eassumption.
  + eapply (proj1 (Helse env _)); eassumption.
- apply EScalar_CaseConditionError.
  now apply (proj2 (Hcondition env _)).
- eapply EScalar_CaseThen.
  + eapply (proj2 (Hcondition env _)); eassumption.
  + eassumption.
  + eapply (proj2 (Hthen env _)); eassumption.
- eapply EScalar_CaseElse.
  + eapply (proj2 (Hcondition env _)); eassumption.
  + eassumption.
  + eapply (proj2 (Helse env _)); eassumption.
Qed.

Lemma scalar_expr_bool_value_global_congr :
  forall result_type embed left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_BoolValue result_type embed left)
      (SExpr_BoolValue result_type embed right).
Proof.
intros result_type embed left right Hequiv env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_BoolValue.
- now apply (proj1 (Hequiv env _)).
- now apply (proj2 (Hequiv env _)).
Qed.

Lemma scalar_expr_value_bool_global_congr :
  forall decode left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_ValueBool decode left) (SExpr_ValueBool decode right).
Proof.
intros decode left right Hequiv env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_ValueBool.
- now apply (proj1 (Hequiv env _)).
- now apply (proj2 (Hequiv env _)).
Qed.

Lemma scalar_expr_pred_global_congr :
  forall predicate left right,
    scalar_value_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Pred predicate left) (SExpr_Pred predicate right).
Proof.
intros predicate left right Harguments env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_PredArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_PredSuccess.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_PredArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- apply EScalar_PredSuccess.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
Qed.

Lemma scalar_expr_conj_list_global_congr :
  forall site_rows operation left right,
    scalar_boolean_expr_list_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_ConjList site_rows operation left)
      (SExpr_ConjList site_rows operation right).
Proof.
intros site_rows operation left right Hequiv env outcome.
split; intro Heval; inversion Heval; subst; apply EScalar_ConjList.
- eapply (proj1 (eval_scalar_boolean_operands_outcome_global_congr
    (schedule_boolean_operands_global_Forall2 site_rows Hequiv)
    env operation _)); eassumption.
- eapply (proj2 (eval_scalar_boolean_operands_outcome_global_congr
    (schedule_boolean_operands_global_Forall2 site_rows Hequiv)
    env operation _)); eassumption.
Qed.

Lemma scalar_expr_not_global_congr :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv (SExpr_Not left) (SExpr_Not right).
Proof.
intros left right Hequiv env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_NotError. now apply (proj1 (Hequiv env _)).
- apply EScalar_NotSuccess. now apply (proj1 (Hequiv env _)).
- apply EScalar_NotError. now apply (proj2 (Hequiv env _)).
- apply EScalar_NotSuccess. now apply (proj2 (Hequiv env _)).
Qed.

Lemma scalar_expr_subquery_global_congr :
  forall result_type null_value left right,
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Subquery result_type null_value left)
      (SExpr_Subquery result_type null_value right).
Proof.
intros result_type null_value left right [Houtputs Hquery] env outcome.
split; intro Heval; inversion Heval; subst.
- rewrite Houtputs.
  eapply EScalar_Subquery; [eassumption|].
  eapply (proj1 (Hquery env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_Subquery; [eassumption|].
  eapply (proj2 (Hquery env _)); eassumption.
Qed.

Lemma scalar_expr_quant_global_congr :
  forall quantifier predicate left_arguments right_arguments left right,
    scalar_value_expr_list_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Quant quantifier predicate left_arguments left)
      (SExpr_Quant quantifier predicate right_arguments right).
Proof.
intros quantifier predicate left_arguments right_arguments left right
  Harguments [Houtputs Hquery] env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_QuantArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- eapply EScalar_QuantSubqueryError.
  + eapply (proj1
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj1 (Hquery env _)); eassumption.
- rewrite Houtputs.
  eapply EScalar_QuantSuccess.
  + eapply (proj1
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj1 (Hquery env _)); eassumption.
- apply EScalar_QuantArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- eapply EScalar_QuantSubqueryError.
  + eapply (proj2
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj2 (Hquery env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_QuantSuccess.
  + eapply (proj2
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj2 (Hquery env _)); eassumption.
Qed.

Lemma scalar_expr_in_global_congr :
  forall left_arguments right_arguments left right,
    scalar_value_expr_list_global_outcome_equiv
      left_arguments right_arguments ->
    query_expr_global_typed_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_In left_arguments left) (SExpr_In right_arguments right).
Proof.
intros left_arguments right_arguments left right Harguments
  [Houtputs Hquery] env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_InArgumentsError.
  now apply (proj1
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj1
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj1 (Hquery env _)); eassumption.
- rewrite Houtputs.
  eapply EScalar_InSuccess.
  + eapply (proj1
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj1 (Hquery env _)); eassumption.
- apply EScalar_InArgumentsError.
  now apply (proj2
    (eval_scalar_values_outcome_global_congr Harguments env _)).
- eapply EScalar_InSubqueryError.
  + eapply (proj2
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj2 (Hquery env _)); eassumption.
- rewrite <- Houtputs.
  eapply EScalar_InSuccess.
  + eapply (proj2
      (eval_scalar_values_outcome_global_congr Harguments env _)); eassumption.
  + eapply (proj2 (Hquery env _)); eassumption.
Qed.

Lemma scalar_expr_exists_global_congr :
  forall left right,
    query_expr_global_exists_outcome_equiv left right ->
    scalar_expr_global_outcome_equiv
      (SExpr_Exists left) (SExpr_Exists right).
Proof.
intros left right Hequiv env outcome.
split; intro Heval; inversion Heval; subst.
- apply EScalar_ExistsError.
  eapply (proj1 (Hequiv env _)); eassumption.
- apply EScalar_ExistsSuccess.
  eapply (proj1 (Hequiv env _)); eassumption.
- apply EScalar_ExistsError.
  eapply (proj2 (Hequiv env _)); eassumption.
- apply EScalar_ExistsSuccess.
  eapply (proj2 (Hequiv env _)); eassumption.
Qed.

(** Constructor congruence for queries, including ordered-output preservation. *)
Lemma query_expr_set_global_typed_congr :
  forall operation first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Set operation first second) (QExpr_Set operation first' second').
Proof.
intros operation first first' second second'
  [Hfirst_outputs Hfirst] [Hsecond_outputs Hsecond].
split; [exact Hfirst_outputs|].
pose proof
  (query_expr_outputs_eq_sort_eq first first' Hfirst_outputs)
  as Hfirst_sort.
pose proof
  (query_expr_outputs_eq_sort_eq second second' Hsecond_outputs)
  as Hsecond_sort.
assert (Hsort_test :
  (query_expr_sort first =S?= query_expr_sort second) =
  (query_expr_sort first' =S?= query_expr_sort second')).
{
  rewrite (Fset.equal_eq_1 _ _ _ _ Hfirst_sort).
  rewrite (Fset.equal_eq_2 _ _ _ _ Hsecond_sort).
  reflexivity.
}
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_SetLeftError. transport_query_forward Hfirst.
- eapply EQuery_SetRightError.
  + transport_query_forward Hfirst.
  + transport_query_forward Hsecond.
- eapply EQuery_SetSuccess.
  + transport_query_forward Hfirst.
  + transport_query_forward Hsecond.
  + rewrite <- Hsort_test; eassumption.
- apply EQuery_SetLeftError. transport_query_backward Hfirst.
- eapply EQuery_SetRightError.
  + transport_query_backward Hfirst.
  + transport_query_backward Hsecond.
- eapply EQuery_SetSuccess.
  + transport_query_backward Hfirst.
  + transport_query_backward Hsecond.
  + rewrite Hsort_test; eassumption.
Qed.

Lemma query_expr_natural_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_NaturalJoin first second) (QExpr_NaturalJoin first' second').
Proof.
intros first first' second second'
  [Hfirst_outputs Hfirst] [Hsecond_outputs Hsecond].
split.
- cbn [query_expr_outputs]. now rewrite Hfirst_outputs, Hsecond_outputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + apply EQuery_NaturalJoinLeftError. transport_query_forward Hfirst.
  + eapply EQuery_NaturalJoinRightError.
    * transport_query_forward Hfirst.
    * transport_query_forward Hsecond.
  + eapply EQuery_NaturalJoinSuccess.
    * transport_query_forward Hfirst.
    * transport_query_forward Hsecond.
    * eassumption.
  + apply EQuery_NaturalJoinLeftError. transport_query_backward Hfirst.
  + eapply EQuery_NaturalJoinRightError.
    * transport_query_backward Hfirst.
    * transport_query_backward Hsecond.
  + eapply EQuery_NaturalJoinSuccess.
    * transport_query_backward Hfirst.
    * transport_query_backward Hsecond.
    * eassumption.
Qed.

Lemma query_expr_cross_join_global_typed_congr :
  forall first first' second second',
    query_expr_global_typed_outcome_equiv first first' ->
    query_expr_global_typed_outcome_equiv second second' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_CrossJoin first second) (QExpr_CrossJoin first' second').
Proof.
intros first first' second second'
  [Hfirst_outputs Hfirst] [Hsecond_outputs Hsecond].
split.
- cbn [query_expr_outputs]. now rewrite Hfirst_outputs, Hsecond_outputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + apply EQuery_CrossJoinLeftError. transport_query_forward Hfirst.
  + eapply EQuery_CrossJoinRightError.
    * transport_query_forward Hfirst.
    * transport_query_forward Hsecond.
  + eapply EQuery_CrossJoinSuccess.
    * transport_query_forward Hfirst.
    * transport_query_forward Hsecond.
    * eassumption.
  + apply EQuery_CrossJoinLeftError. transport_query_backward Hfirst.
  + eapply EQuery_CrossJoinRightError.
    * transport_query_backward Hfirst.
    * transport_query_backward Hsecond.
  + eapply EQuery_CrossJoinSuccess.
    * transport_query_backward Hfirst.
    * transport_query_backward Hsecond.
    * eassumption.
Qed.

Lemma query_expr_join_global_typed_congr :
  forall kind predicate matched_select left_select right_select
         left left' right right',
    query_expr_global_typed_outcome_equiv left left' ->
    query_expr_global_typed_outcome_equiv right right' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind predicate matched_select left_select right_select
        left' right').
Proof.
intros kind predicate matched_select left_select right_select
  left left' right right' [_ Hleft] [_ Hright].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_JoinLeftError. transport_query_forward Hleft.
- eapply EQuery_JoinRightError.
  + transport_query_forward Hleft.
  + transport_query_forward Hright.
- eapply EQuery_JoinBagError.
  + transport_query_forward Hleft.
  + transport_query_forward Hright.
  + eassumption.
- eapply EQuery_JoinSuccess with (output_bag := output_bag).
  + transport_query_forward Hleft.
  + transport_query_forward Hright.
  + eassumption.
  + eassumption.
- apply EQuery_JoinLeftError. transport_query_backward Hleft.
- eapply EQuery_JoinRightError.
  + transport_query_backward Hleft.
  + transport_query_backward Hright.
- eapply EQuery_JoinBagError.
  + transport_query_backward Hleft.
  + transport_query_backward Hright.
  + eassumption.
- eapply EQuery_JoinSuccess with (output_bag := output_bag).
  + transport_query_backward Hleft.
  + transport_query_backward Hright.
  + eassumption.
  + eassumption.
Qed.

Lemma query_expr_project_global_typed_congr :
  forall select_list first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Project select_list first) (QExpr_Project select_list second).
Proof.
intros select_list first second [_ Hequiv].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_ProjectChildError. transport_query_forward Hequiv.
- eapply EQuery_ProjectRows.
  + transport_query_forward Hequiv.
  + eassumption.
- apply EQuery_ProjectChildError. transport_query_backward Hequiv.
- eapply EQuery_ProjectRows.
  + transport_query_backward Hequiv.
  + eassumption.
Qed.

Lemma query_expr_row_map_global_typed_congr :
  forall output_attributes row_map first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_RowMap output_attributes row_map first)
      (QExpr_RowMap output_attributes row_map second).
Proof.
intros output_attributes row_map first second [_ Hequiv].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_RowMapChildError. transport_query_forward Hequiv.
- eapply EQuery_RowMapRows. transport_query_forward Hequiv.
- apply EQuery_RowMapChildError. transport_query_backward Hequiv.
- eapply EQuery_RowMapRows. transport_query_backward Hequiv.
Qed.

Lemma query_expr_filter_global_typed_congr :
  forall expression input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter expression input) (QExpr_Filter expression input').
Proof.
intros expression input input' [Houtputs Hinput].
split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_FilterChildError. transport_query_forward Hinput.
- eapply EQuery_FilterRows.
  + transport_query_forward Hinput.
  + eassumption.
- apply EQuery_FilterChildError. transport_query_backward Hinput.
- eapply EQuery_FilterRows.
  + transport_query_backward Hinput.
  + eassumption.
Qed.

Lemma query_expr_group_global_typed_congr :
  forall select_list group_keys having input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list group_keys having input)
      (QExpr_Group select_list group_keys having input').
Proof.
intros select_list group_keys having input input' [_ Hinput].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_GroupChildError. transport_query_forward Hinput.
- eapply EQuery_GroupBagError.
  + transport_query_forward Hinput.
  + eassumption.
- eapply EQuery_GroupBagSuccess with
    (input_rows := input_rows) (output_bag := output_bag).
  + transport_query_forward Hinput.
  + eassumption.
  + eassumption.
- apply EQuery_GroupChildError. transport_query_backward Hinput.
- eapply EQuery_GroupBagError.
  + transport_query_backward Hinput.
  + eassumption.
- eapply EQuery_GroupBagSuccess with
    (input_rows := input_rows) (output_bag := output_bag).
  + transport_query_backward Hinput.
  + eassumption.
  + eassumption.
Qed.

Lemma query_expr_grouping_sets_global_typed_congr :
  forall grouping_sets input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets grouping_sets input)
      (QExpr_GroupingSets grouping_sets input').
Proof.
intros grouping_sets input input' [_ Hinput].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_GroupingSetsChildError. transport_query_forward Hinput.
- eapply EQuery_GroupingSetsBagError.
  + transport_query_forward Hinput.
  + eassumption.
- eapply EQuery_GroupingSetsSuccess with (output_bag := output_bag).
  + transport_query_forward Hinput.
  + eassumption.
  + eassumption.
- apply EQuery_GroupingSetsChildError. transport_query_backward Hinput.
- eapply EQuery_GroupingSetsBagError.
  + transport_query_backward Hinput.
  + eassumption.
- eapply EQuery_GroupingSetsSuccess with (output_bag := output_bag).
  + transport_query_backward Hinput.
  + eassumption.
  + eassumption.
Qed.

Lemma query_expr_rank_global_typed_congr :
  forall partition_keys order_keys rank_attribute rank_value input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input').
Proof.
intros partition_keys order_keys rank_attribute rank_value input input'
  [Houtputs Hinput].
split.
- cbn [query_expr_outputs]. now rewrite Houtputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + apply EQuery_RankChildError. transport_query_forward Hinput.
  + eapply EQuery_RankValueError with (input_rows := input_rows).
    * transport_query_forward Hinput.
    * eassumption.
  + eapply EQuery_RankSuccess with
      (input_rows := input_rows) (ranked_rows := ranked_rows).
    * transport_query_forward Hinput.
    * eassumption.
    * eassumption.
  + apply EQuery_RankChildError. transport_query_backward Hinput.
  + eapply EQuery_RankValueError with (input_rows := input_rows).
    * transport_query_backward Hinput.
    * eassumption.
  + eapply EQuery_RankSuccess with
      (input_rows := input_rows) (ranked_rows := ranked_rows).
    * transport_query_backward Hinput.
    * eassumption.
    * eassumption.
Qed.

Lemma query_expr_window_global_typed_congr :
  forall partition_keys order_keys items input input',
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Window partition_keys order_keys items input)
      (QExpr_Window partition_keys order_keys items input').
Proof.
intros partition_keys order_keys items input input' [Houtputs Hinput].
split.
- cbn [query_expr_outputs]. now rewrite Houtputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + apply EQuery_WindowChildError. transport_query_forward Hinput.
  + eapply EQuery_WindowRowsError with
      (input_rows := input_rows) (ordered_rows := ordered_rows).
    * transport_query_forward Hinput.
    * eassumption.
    * eassumption.
  + eapply EQuery_WindowSuccess with
      (input_rows := input_rows) (ordered_rows := ordered_rows)
      (window_rows := window_rows).
    * transport_query_forward Hinput.
    * eassumption.
    * eassumption.
    * eassumption.
  + apply EQuery_WindowChildError. transport_query_backward Hinput.
  + eapply EQuery_WindowRowsError with
      (input_rows := input_rows) (ordered_rows := ordered_rows).
    * transport_query_backward Hinput.
    * eassumption.
    * eassumption.
  + eapply EQuery_WindowSuccess with
      (input_rows := input_rows) (ordered_rows := ordered_rows)
      (window_rows := window_rows).
    * transport_query_backward Hinput.
    * eassumption.
    * eassumption.
    * eassumption.
Qed.

Lemma query_expr_distinct_global_typed_congr :
  forall first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Distinct first) (QExpr_Distinct second).
Proof.
intros first second [Houtputs Hequiv]; split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_DistinctChildError. transport_query_forward Hequiv.
- eapply EQuery_DistinctSuccess; [transport_query_forward Hequiv|eassumption].
- apply EQuery_DistinctChildError. transport_query_backward Hequiv.
- eapply EQuery_DistinctSuccess; [transport_query_backward Hequiv|eassumption].
Qed.

Lemma query_expr_order_by_global_typed_congr :
  forall keys first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_OrderBy keys first) (QExpr_OrderBy keys second).
Proof.
intros keys first second [Houtputs Hequiv]; split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_OrderByChildError. transport_query_forward Hequiv.
- eapply EQuery_OrderBySuccess; [transport_query_forward Hequiv|eassumption].
- apply EQuery_OrderByChildError. transport_query_backward Hequiv.
- eapply EQuery_OrderBySuccess; [transport_query_backward Hequiv|eassumption].
Qed.

Lemma query_expr_offset_global_typed_congr :
  forall offset first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Offset offset first) (QExpr_Offset offset second).
Proof.
intros offset first second [Houtputs Hequiv]; split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_OffsetChildError. transport_query_forward Hequiv.
- eapply EQuery_OffsetSuccess. transport_query_forward Hequiv.
- apply EQuery_OffsetChildError. transport_query_backward Hequiv.
- eapply EQuery_OffsetSuccess. transport_query_backward Hequiv.
Qed.

Lemma query_expr_fetch_global_typed_congr :
  forall count first second,
    query_expr_global_typed_outcome_equiv first second ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Fetch count first) (QExpr_Fetch count second).
Proof.
intros count first second [Houtputs Hequiv]; split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_FetchChildError. transport_query_forward Hequiv.
- eapply EQuery_FetchSuccess. transport_query_forward Hequiv.
- apply EQuery_FetchChildError. transport_query_backward Hequiv.
- eapply EQuery_FetchSuccess. transport_query_backward Hequiv.
Qed.

Lemma eval_project_rows_outcome_global_congr :
  forall left_select right_select,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    forall env rows outcome,
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_select rows outcome <->
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_select rows outcome.
Proof.
intros left_select right_select Hselect env rows.
assert (Hvalues :=
  scalar_select_list_global_outcome_equiv_values Hselect).
assert (Houtputs :=
  scalar_select_list_global_outcome_equiv_outputs Hselect).
assert (Hrow : forall values,
  @project_row T relname left_select values =
  @project_row T relname right_select values).
{
  intro values; unfold project_row; now rewrite Houtputs.
}
induction rows as [|row rows IH]; intro outcome; split; intro Heval;
  inversion Heval; subst.
- constructor.
- constructor.
- apply EProjectRows_HeadError.
  now apply (proj1 (eval_scalar_values_outcome_global_congr
    Hvalues (env_t T env row) _)).
- rewrite Hrow.
  eapply EProjectRows_Cons.
  + eapply (proj1 (eval_scalar_values_outcome_global_congr
      Hvalues (env_t T env row) _)); eassumption.
  + now apply (proj1 (IH _)).
- apply EProjectRows_HeadError.
  now apply (proj2 (eval_scalar_values_outcome_global_congr
    Hvalues (env_t T env row) _)).
- rewrite <- Hrow.
  eapply EProjectRows_Cons.
  + eapply (proj2 (eval_scalar_values_outcome_global_congr
      Hvalues (env_t T env row) _)); eassumption.
  + now apply (proj2 (IH _)).
Qed.

Lemma eval_filter_rows_expression_global_congr_forward :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left rows outcome ->
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right rows outcome.
Proof.
intros left right Hequiv env rows outcome Heval.
induction Heval.
- constructor.
- apply EFilterRows_HeadError.
  now apply (proj1 (Hequiv _ _)).
- eapply EFilterRows_Cons.
  + now apply (proj1 (Hequiv _ _)).
  + exact (IHHeval Hequiv).
Qed.

Lemma eval_filter_rows_expression_global_congr :
  forall left right,
    scalar_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left rows outcome <->
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right rows outcome.
Proof.
intros left right Hequiv env rows outcome; split; intro Heval.
- now eapply eval_filter_rows_expression_global_congr_forward.
- eapply eval_filter_rows_expression_global_congr_forward; [|exact Heval].
  intros current_env current_outcome; symmetry; apply Hequiv.
Qed.

Lemma query_expr_project_select_global_typed_congr :
  forall left_select right_select input,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Project left_select input)
      (QExpr_Project right_select input).
Proof.
intros left_select right_select input Hselect; split.
- now apply scalar_select_list_global_outcome_equiv_outputs.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows; [eassumption|].
    now apply (proj1
      (eval_project_rows_outcome_global_congr Hselect env input_rows outcome)).
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows; [eassumption|].
    now apply (proj2
      (eval_project_rows_outcome_global_congr Hselect env input_rows outcome)).
Qed.

Lemma query_expr_filter_expression_global_typed_congr :
  forall left_expression right_expression input,
    scalar_expr_global_outcome_equiv left_expression right_expression ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter left_expression input)
      (QExpr_Filter right_expression input).
Proof.
intros left_expression right_expression input Hexpression; split;
  [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- now apply EQuery_FilterChildError.
- eapply EQuery_FilterRows; [eassumption|].
  now apply (proj1 (eval_filter_rows_expression_global_congr
    Hexpression env input_rows outcome)).
- now apply EQuery_FilterChildError.
- eapply EQuery_FilterRows; [eassumption|].
  now apply (proj2 (eval_filter_rows_expression_global_congr
    Hexpression env input_rows outcome)).
Qed.

Lemma eval_join_row_conditions_expression_global_congr_forward :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_row right_rows outcome,
      eval_join_row_conditions env first left_row right_rows outcome ->
      eval_join_row_conditions env second left_row right_rows outcome.
Proof.
intros first second Hequiv env left_row right_rows outcome Heval.
induction Heval.
- constructor.
- apply EJoinRowConditions_HeadError.
  now apply (proj1 (Hequiv _ _)).
- eapply EJoinRowConditions_Cons.
  + now apply (proj1 (Hequiv _ _)).
  + exact (IHHeval Hequiv).
Qed.

Lemma eval_join_row_conditions_expression_global_congr :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_row right_rows outcome,
      eval_join_row_conditions env first left_row right_rows outcome <->
      eval_join_row_conditions env second left_row right_rows outcome.
Proof.
intros first second Hequiv env left_row right_rows outcome; split; intro Heval.
- now eapply eval_join_row_conditions_expression_global_congr_forward.
- eapply eval_join_row_conditions_expression_global_congr_forward;
    [|exact Heval].
  now apply scalar_expr_global_outcome_equiv_sym.
Qed.

Lemma eval_join_conditions_expression_global_congr_forward :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome ->
      eval_join_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome Heval.
induction Heval.
- constructor.
- apply EJoinConditions_RowError.
  now apply (proj1
    (eval_join_row_conditions_expression_global_congr Hequiv _ _ _ _)).
- eapply EJoinConditions_Cons.
  + now apply (proj1
      (eval_join_row_conditions_expression_global_congr Hequiv _ _ _ _)).
  + exact (IHHeval Hequiv).
Qed.

Lemma eval_join_conditions_expression_global_congr :
  forall first second,
    scalar_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome <->
      eval_join_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome; split; intro Heval.
- now eapply eval_join_conditions_expression_global_congr_forward.
- eapply eval_join_conditions_expression_global_congr_forward;
    [|exact Heval].
  now apply scalar_expr_global_outcome_equiv_sym.
Qed.

Lemma eval_project_join_sources_global_congr_forward :
  forall left_matched right_matched left_left right_left
      left_right right_right,
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env sources outcome,
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_matched left_left left_right sources outcome ->
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_matched right_left right_right sources outcome.
Proof.
intros left_matched right_matched left_left right_left left_right right_right
  Hmatched Hleft Hright env sources outcome Heval.
revert outcome Heval; induction sources as [|source sources IH];
  intros outcome Heval; inversion Heval; subst.
- constructor.
- apply EProjectJoinSources_HeadError.
  pose proof
    (match source as current_source return
      scalar_select_list_global_outcome_equiv
        (query_join_source_select
          left_matched left_left left_right current_source)
        (query_join_source_select
          right_matched right_left right_right current_source) with
    | @JoinSourceMatched _ _ => Hmatched
    | @JoinSourceLeft _ _ => Hleft
    | @JoinSourceRight _ _ => Hright
    end) as Hselect.
  apply (proj1 (eval_scalar_values_outcome_global_congr
    (scalar_select_list_global_outcome_equiv_values Hselect)
    (env_t T env (query_join_source_row source)) _)).
  eassumption.
- pose proof
    (match source as current_source return
      scalar_select_list_global_outcome_equiv
        (query_join_source_select
          left_matched left_left left_right current_source)
        (query_join_source_select
          right_matched right_left right_right current_source) with
    | @JoinSourceMatched _ _ => Hmatched
    | @JoinSourceLeft _ _ => Hleft
    | @JoinSourceRight _ _ => Hright
    end) as Hselect.
  pose proof
    (scalar_select_list_global_outcome_equiv_outputs Hselect) as Houtputs.
  assert (Hrow :
    project_row
      (query_join_source_select
        left_matched left_left left_right source) values =
    project_row
      (query_join_source_select
        right_matched right_left right_right source) values).
  { unfold project_row; now rewrite Houtputs. }
  rewrite Hrow.
  eapply EProjectJoinSources_Cons.
  + apply (proj1 (eval_scalar_values_outcome_global_congr
      (scalar_select_list_global_outcome_equiv_values Hselect)
      (env_t T env (query_join_source_row source)) _)).
    eassumption.
  + apply IH; eassumption.
Qed.

Lemma eval_project_join_sources_global_congr :
  forall left_matched right_matched left_left right_left
      left_right right_right,
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env sources outcome,
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env left_matched left_left left_right sources outcome <->
      @eval_project_join_sources_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        boolean_schedule env right_matched right_left right_right sources outcome.
Proof.
intros left_matched right_matched left_left right_left left_right right_right
  Hmatched Hleft Hright env sources outcome; split; intro Heval.
- eapply eval_project_join_sources_global_congr_forward;
    [exact Hmatched|exact Hleft|exact Hright|exact Heval].
- eapply eval_project_join_sources_global_congr_forward; [| | |exact Heval].
  + now apply scalar_select_list_global_outcome_equiv_sym.
  + now apply scalar_select_list_global_outcome_equiv_sym.
  + now apply scalar_select_list_global_outcome_equiv_sym.
Qed.

Lemma eval_join_bag_scalar_global_congr_forward :
  forall left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env kind left_bag right_bag outcome,
      eval_join_bag env kind left_predicate
        left_matched left_left left_right left_bag right_bag outcome ->
      eval_join_bag env kind right_predicate
        right_matched right_left right_right left_bag right_bag outcome.
Proof.
intros left_predicate right_predicate left_matched right_matched
  left_left right_left left_right right_right Hpredicate Hmatched Hleft Hright
  env kind left_bag right_bag outcome Heval.
inversion Heval; subst.
- eapply EJoinBag_ConditionError; [eassumption|eassumption|].
  now apply (proj1
    (eval_join_conditions_expression_global_congr Hpredicate _ _ _ _)).
- eapply EJoinBag_ProjectionError with (matrix := matrix);
    [eassumption|eassumption| |].
  + now apply (proj1
      (eval_join_conditions_expression_global_congr Hpredicate _ _ _ _)).
  + now apply (proj1 (eval_project_join_sources_global_congr
      Hmatched Hleft Hright _ _ _)).
- eapply EJoinBag_Success with
    (left_rows := left_rows) (right_rows := right_rows)
    (matrix := matrix) (projected := projected);
    [eassumption|eassumption| | |eassumption].
  + now apply (proj1
      (eval_join_conditions_expression_global_congr Hpredicate _ _ _ _)).
  + now apply (proj1 (eval_project_join_sources_global_congr
      Hmatched Hleft Hright _ _ _)).
Qed.

Lemma eval_join_bag_scalar_global_congr :
  forall left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    forall env kind left_bag right_bag outcome,
      eval_join_bag env kind left_predicate
        left_matched left_left left_right left_bag right_bag outcome <->
      eval_join_bag env kind right_predicate
        right_matched right_left right_right left_bag right_bag outcome.
Proof.
intros left_predicate right_predicate left_matched right_matched
  left_left right_left left_right right_right Hpredicate Hmatched Hleft Hright
  env kind left_bag right_bag outcome; split; intro Heval.
- eapply eval_join_bag_scalar_global_congr_forward;
    [exact Hpredicate|exact Hmatched|exact Hleft|exact Hright|exact Heval].
- eapply eval_join_bag_scalar_global_congr_forward; [| | | |exact Heval].
  + now apply scalar_expr_global_outcome_equiv_sym.
  + now apply scalar_select_list_global_outcome_equiv_sym.
  + now apply scalar_select_list_global_outcome_equiv_sym.
  + now apply scalar_select_list_global_outcome_equiv_sym.
Qed.

Lemma query_expr_join_scalar_global_typed_congr :
  forall kind left_predicate right_predicate
      left_matched right_matched left_left right_left left_right right_right
      left_query right_query,
    scalar_expr_global_outcome_equiv left_predicate right_predicate ->
    scalar_select_list_global_outcome_equiv left_matched right_matched ->
    scalar_select_list_global_outcome_equiv left_left right_left ->
    scalar_select_list_global_outcome_equiv left_right right_right ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind left_predicate left_matched left_left left_right
        left_query right_query)
      (QExpr_Join kind right_predicate right_matched right_left right_right
        left_query right_query).
Proof.
intros kind left_predicate right_predicate left_matched right_matched
  left_left right_left left_right right_right left_query right_query
  Hpredicate Hmatched Hleft Hright.
split.
- cbn [query_expr_outputs]; destruct kind;
    first [now apply scalar_select_list_global_outcome_equiv_outputs with
      (left := left_matched) |
      now apply scalar_select_list_global_outcome_equiv_outputs with
        (left := left_left)].
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + now apply EQuery_JoinLeftError.
  + eapply EQuery_JoinRightError; eassumption.
  + eapply EQuery_JoinBagError; [eassumption|eassumption|].
    now apply (proj1 (eval_join_bag_scalar_global_congr
      Hpredicate Hmatched Hleft Hright _ _ _ _ _)).
  + eapply EQuery_JoinSuccess with (output_bag := output_bag);
      [eassumption|eassumption| |eassumption].
    now apply (proj1 (eval_join_bag_scalar_global_congr
      Hpredicate Hmatched Hleft Hright _ _ _ _ _)).
  + now apply EQuery_JoinLeftError.
  + eapply EQuery_JoinRightError; eassumption.
  + eapply EQuery_JoinBagError; [eassumption|eassumption|].
    now apply (proj2 (eval_join_bag_scalar_global_congr
      Hpredicate Hmatched Hleft Hright _ _ _ _ _)).
  + eapply EQuery_JoinSuccess with (output_bag := output_bag);
      [eassumption|eassumption| |eassumption].
    now apply (proj2 (eval_join_bag_scalar_global_congr
      Hpredicate Hmatched Hleft Hright _ _ _ _ _)).
Qed.

Theorem scalar_expr_context_global_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand context) replacement replacement' ->
    scalar_expr_global_outcome_equiv
      (plug_scalar_expr_context context replacement)
      (plug_scalar_expr_context context replacement').
Proof.
intros kind context; induction context; cbn;
  intros replacement replacement' Hequiv.
- apply scalar_expr_call_global_congr.
  apply scalar_expr_list_context_global_outcome_equiv.
  now apply IHcontext.
- apply scalar_expr_case_global_congr.
  + now apply IHcontext.
  + apply scalar_expr_global_outcome_equiv_refl.
  + apply scalar_expr_global_outcome_equiv_refl.
- apply scalar_expr_case_global_congr.
  + apply scalar_expr_global_outcome_equiv_refl.
  + now apply IHcontext.
  + apply scalar_expr_global_outcome_equiv_refl.
- apply scalar_expr_case_global_congr.
  + apply scalar_expr_global_outcome_equiv_refl.
  + apply scalar_expr_global_outcome_equiv_refl.
  + now apply IHcontext.
- apply scalar_expr_bool_value_global_congr. now apply IHcontext.
- now apply scalar_expr_subquery_global_congr.
- apply scalar_expr_value_bool_global_congr. now apply IHcontext.
- apply scalar_expr_pred_global_congr.
  apply scalar_expr_list_context_global_outcome_equiv.
  now apply IHcontext.
- apply scalar_expr_conj_list_global_congr.
  apply scalar_expr_list_context_global_outcome_equiv.
  now apply IHcontext.
- apply scalar_expr_not_global_congr. now apply IHcontext.
- apply scalar_expr_quant_global_congr.
  + apply scalar_expr_list_context_global_outcome_equiv.
    now apply IHcontext.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply scalar_expr_quant_global_congr.
  + apply scalar_expr_list_global_outcome_equiv_refl.
  + exact Hequiv.
- apply scalar_expr_in_global_congr.
  + apply scalar_expr_list_context_global_outcome_equiv.
    now apply IHcontext.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply scalar_expr_in_global_congr.
  + apply scalar_expr_list_global_outcome_equiv_refl.
  + exact Hequiv.
- now apply scalar_expr_exists_global_congr.
Qed.

Lemma first_runtime_error_context_eq :
  forall (A : Type) (observe : A -> option sql_runtime_error)
      prefix left right suffix,
    observe left = observe right ->
    first_runtime_error observe (prefix ++ left :: suffix) =
    first_runtime_error observe (prefix ++ right :: suffix).
Proof.
intros A observe prefix; induction prefix as [|head prefix IH];
  intros left right suffix Heq; cbn.
- now rewrite Heq.
- destruct (observe head); [reflexivity|now apply IH].
Qed.

Theorem scalar_expr_context_aggregate_runtime_error_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement'
      env,
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_expr_context context replacement) =
    eval_scalar_expr_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_expr_context context replacement').
Proof.
intros kind context; induction context; intros replacement replacement' env;
  cbn.
- apply first_runtime_error_context_eq.
  exact (IHcontext replacement replacement' env).
- now rewrite (IHcontext replacement replacement' env).
- now rewrite (IHcontext replacement replacement' env).
- now rewrite (IHcontext replacement replacement' env).
- exact (IHcontext replacement replacement' env).
- reflexivity.
- exact (IHcontext replacement replacement' env).
- apply first_runtime_error_context_eq.
  exact (IHcontext replacement replacement' env).
- apply first_runtime_error_context_eq.
  exact (IHcontext replacement replacement' env).
- exact (IHcontext replacement replacement' env).
- apply first_runtime_error_context_eq.
  exact (IHcontext replacement replacement' env).
- reflexivity.
- apply first_runtime_error_context_eq.
  exact (IHcontext replacement replacement' env).
- reflexivity.
- reflexivity.
Qed.

Corollary scalar_expr_context_global_group_congr :
  forall kind (context : scalar_expr_context kind) replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand context) replacement replacement' ->
    scalar_expr_global_group_outcome_equiv
      (plug_scalar_expr_context context replacement)
      (plug_scalar_expr_context context replacement').
Proof.
intros kind context replacement replacement' Hequiv; split.
- now apply scalar_expr_context_global_congr.
- apply scalar_expr_context_aggregate_runtime_error_congr.
Qed.

Lemma scalar_select_context_aggregate_runtime_error_congr :
  forall context replacement replacement' env,
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_select_context context replacement) =
    eval_scalar_select_aggregate_runtime_error
      symbol_runtime_error aggregate_runtime_error env
      (plug_scalar_select_context context replacement').
Proof.
intros [prefix expression attribute suffix] replacement replacement' env;
  unfold plug_scalar_select_context,
    eval_scalar_select_aggregate_runtime_error; cbn.
apply first_runtime_error_context_eq; cbn.
apply scalar_expr_context_aggregate_runtime_error_congr.
Qed.

Lemma eval_groups_scalar_global_congr :
  forall left_select right_select group_terms left_having right_having,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    scalar_expr_global_outcome_equiv left_having right_having ->
    (forall current_env,
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    (forall current_env,
      eval_scalar_expr_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_having =
      eval_scalar_expr_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_having) ->
    forall env groups outcome,
      eval_groups env left_select group_terms left_having groups outcome <->
      eval_groups env right_select group_terms right_having groups outcome.
Proof.
intros left_select right_select group_terms left_having right_having
  Hselect Hhaving Hselect_aggregates Hhaving_aggregates env groups.
assert (Hvalues := scalar_select_list_global_outcome_equiv_values Hselect).
assert (Houtputs := scalar_select_list_global_outcome_equiv_outputs Hselect).
assert (Hrow : forall values,
  @project_row T relname left_select values =
  @project_row T relname right_select values).
{ intro values; unfold project_row; now rewrite Houtputs. }
induction groups as [|group groups IH]; intro outcome; split; intro Heval;
  inversion Heval; subst.
- constructor.
- constructor.
- apply EGroups_SelectAggregateError.
  rewrite <- (Hselect_aggregates
    (env_g T env (@Group_By T group_terms) group)); assumption.
- eapply EGroups_HavingAggregateError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
- eapply EGroups_HavingError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + now apply (proj1 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)).
- eapply EGroups_HavingFalse.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj1 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + now apply (proj1 (IH _)).
- eapply EGroups_SelectError.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj1 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj1 (eval_scalar_values_outcome_global_congr Hvalues
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
- rewrite Hrow.
  eapply EGroups_SelectSuccess.
  + rewrite <- (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite <- (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj1 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj1 (eval_scalar_values_outcome_global_congr Hvalues
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + now apply (proj1 (IH _)).
- apply EGroups_SelectAggregateError.
  rewrite (Hselect_aggregates
    (env_g T env (@Group_By T group_terms) group)); assumption.
- eapply EGroups_HavingAggregateError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
- eapply EGroups_HavingError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + now apply (proj2 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)).
- eapply EGroups_HavingFalse.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj2 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + now apply (proj2 (IH _)).
- eapply EGroups_SelectError.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj2 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj2 (eval_scalar_values_outcome_global_congr Hvalues
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
- rewrite <- Hrow.
  eapply EGroups_SelectSuccess.
  + rewrite (Hselect_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + rewrite (Hhaving_aggregates
      (env_g T env (@Group_By T group_terms) group)); assumption.
  + eapply (proj2 (Hhaving
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + eassumption.
  + eapply (proj2 (eval_scalar_values_outcome_global_congr Hvalues
      (env_g T env (@Group_By T group_terms) group) _)); eassumption.
  + now apply (proj2 (IH _)).
Qed.

Lemma eval_group_bag_scalar_global_congr :
  forall left_select right_select group_keys left_having right_having,
    (forall current_env group_terms groups outcome,
      eval_groups current_env left_select group_terms left_having
        groups outcome <->
      eval_groups current_env right_select group_terms right_having
        groups outcome) ->
    forall env input_bag outcome,
      eval_group_bag env left_select group_keys left_having input_bag outcome <->
      eval_group_bag env right_select group_keys right_having input_bag outcome.
Proof.
intros left_select right_select group_keys left_having right_having
  Hlocal env input_bag outcome; split; intro Heval; inversion Heval; subst.
- eapply EGroupBag_KeyError; eassumption.
- eapply EGroupBag_ProcessError; [eassumption|eassumption|eassumption|].
  now apply (proj1 (Hlocal env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_Success; [eassumption|eassumption|eassumption| |eassumption].
  now apply (proj1 (Hlocal env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_KeyError; eassumption.
- eapply EGroupBag_ProcessError; [eassumption|eassumption|eassumption|].
  now apply (proj2 (Hlocal env group_terms
    (query_make_groups env representative group_terms) _)).
- eapply EGroupBag_Success; [eassumption|eassumption|eassumption| |eassumption].
  now apply (proj2 (Hlocal env group_terms
    (query_make_groups env representative group_terms) _)).
Qed.

Lemma query_expr_group_scalar_global_typed_congr :
  forall left_select right_select group_keys left_having right_having input,
    scalar_select_list_global_outcome_equiv left_select right_select ->
    scalar_expr_global_group_outcome_equiv left_having right_having ->
    (forall current_env,
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env left_select =
      eval_scalar_select_aggregate_runtime_error
        symbol_runtime_error aggregate_runtime_error
        current_env right_select) ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group left_select group_keys left_having input)
      (QExpr_Group right_select group_keys right_having input).
Proof.
intros left_select right_select group_keys left_having right_having input
  Hselect [Hhaving Hhaving_aggregates] Hselect_aggregates.
split; [now apply scalar_select_list_global_outcome_equiv_outputs|].
assert (Hlocal : forall current_env group_terms groups outcome,
  eval_groups current_env left_select group_terms left_having groups outcome <->
  eval_groups current_env right_select group_terms right_having groups outcome).
{
  intros current_env group_terms groups outcome.
  now apply eval_groups_scalar_global_congr.
}
intros env outcome; split; intro Heval; inversion Heval; subst.
- now apply EQuery_GroupChildError.
- eapply EQuery_GroupBagError; [eassumption|].
  now apply (proj1 (eval_group_bag_scalar_global_congr
    group_keys Hlocal env (query_rows_bag input_rows) (SqlError error))).
- eapply EQuery_GroupBagSuccess; [eassumption| |eassumption].
  now apply (proj1 (eval_group_bag_scalar_global_congr
    group_keys Hlocal env (query_rows_bag input_rows)
      (SqlSuccess output_bag))).
- now apply EQuery_GroupChildError.
- eapply EQuery_GroupBagError; [eassumption|].
  now apply (proj2 (eval_group_bag_scalar_global_congr
    group_keys Hlocal env (query_rows_bag input_rows) (SqlError error))).
- eapply EQuery_GroupBagSuccess; [eassumption| |eassumption].
  now apply (proj2 (eval_group_bag_scalar_global_congr
    group_keys Hlocal env (query_rows_bag input_rows)
      (SqlSuccess output_bag))).
Qed.

Lemma scalar_expr_context_group_key_none :
  forall (context : scalar_expr_context ScalarResultValue)
      replacement suffix,
    scalar_group_key_terms
      (plug_scalar_expr_context context replacement :: suffix) = None.
Proof.
intros context replacement suffix; dependent destruction context; reflexivity.
Qed.

Lemma scalar_value_list_context_group_keys_none :
  forall context replacement,
    scalar_group_key_terms
      (plug_scalar_value_list_context context replacement) = None.
Proof.
intros [prefix expression suffix] replacement; cbn.
induction prefix as [|head prefix IH].
- apply scalar_expr_context_group_key_none.
- dependent destruction head; cbn; try reflexivity.
  now rewrite IH.
Qed.

Lemma eval_group_bag_group_keys_none :
  forall env select_list group_keys having input_bag outcome,
    scalar_group_key_terms group_keys = None ->
    ~ eval_group_bag env select_list group_keys having input_bag outcome.
Proof.
intros env select_list group_keys having input_bag outcome Hnone Heval.
inversion Heval; subst; congruence.
Qed.

Lemma query_expr_group_invalid_keys_global_typed_congr :
  forall select_list left_keys right_keys having input,
    scalar_group_key_terms left_keys = None ->
    scalar_group_key_terms right_keys = None ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list left_keys having input)
      (QExpr_Group select_list right_keys having input).
Proof.
intros select_list left_keys right_keys having input Hleft Hright; split;
  [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- now apply EQuery_GroupChildError.
- exfalso.
  eapply (eval_group_bag_group_keys_none Hleft); eassumption.
- exfalso.
  eapply (eval_group_bag_group_keys_none Hleft); eassumption.
- now apply EQuery_GroupChildError.
- exfalso.
  eapply (eval_group_bag_group_keys_none Hright); eassumption.
- exfalso.
  eapply (eval_group_bag_group_keys_none Hright); eassumption.
Qed.

Lemma eval_grouping_sets_bag_branch_congr_forward :
  forall prefix left_select right_select left_keys right_keys suffix,
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome ->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    forall env input_bag outcome,
      eval_grouping_sets_bag env
        (prefix ++ (left_select, left_keys) :: suffix) input_bag outcome ->
      eval_grouping_sets_bag env
        (prefix ++ (right_select, right_keys) :: suffix) input_bag outcome.
Proof.
intros prefix left_select right_select left_keys right_keys suffix Hbranch.
induction prefix as [|[prefix_select prefix_keys] prefix IH];
  intros env input_bag outcome Heval; cbn in *; inversion Heval; subst.
- apply EGroupingSets_HeadError. eapply Hbranch; eassumption.
- eapply EGroupingSets_TailError.
  + eapply Hbranch; eassumption.
  + eassumption.
- eapply EGroupingSets_ConsSuccess.
  + eapply Hbranch; eassumption.
  + eassumption.
- apply EGroupingSets_HeadError. eassumption.
- eapply EGroupingSets_TailError; [eassumption|].
  now apply IH.
- eapply EGroupingSets_ConsSuccess; [eassumption|].
  now apply IH.
Qed.

Lemma eval_grouping_sets_bag_branch_congr :
  forall prefix left_select right_select left_keys right_keys suffix,
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome <->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    forall env input_bag outcome,
      eval_grouping_sets_bag env
        (prefix ++ (left_select, left_keys) :: suffix) input_bag outcome <->
      eval_grouping_sets_bag env
        (prefix ++ (right_select, right_keys) :: suffix) input_bag outcome.
Proof.
intros prefix left_select right_select left_keys right_keys suffix Hbranch
  env input_bag outcome; split; intro Heval.
- eapply eval_grouping_sets_bag_branch_congr_forward; [|exact Heval].
  intros; now apply (proj1 (Hbranch _ _ _)).
- eapply eval_grouping_sets_bag_branch_congr_forward; [|exact Heval].
  intros; now apply (proj2 (Hbranch _ _ _)).
Qed.

Lemma query_expr_grouping_sets_branch_global_typed_congr :
  forall prefix left_select right_select left_keys right_keys suffix input,
    query_grouping_sets_outputs
      (prefix ++ (left_select, left_keys) :: suffix) =
    query_grouping_sets_outputs
      (prefix ++ (right_select, right_keys) :: suffix) ->
    (forall env input_bag outcome,
      eval_group_bag env left_select left_keys SExpr_True input_bag outcome <->
      eval_group_bag env right_select right_keys SExpr_True input_bag outcome) ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++ (left_select, left_keys) :: suffix) input)
      (QExpr_GroupingSets
        (prefix ++ (right_select, right_keys) :: suffix) input).
Proof.
intros prefix left_select right_select left_keys right_keys suffix input
  Houtputs Hbranch; split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- now apply EQuery_GroupingSetsChildError.
- eapply EQuery_GroupingSetsBagError; [eassumption|].
  now apply (proj1 (eval_grouping_sets_bag_branch_congr
    prefix suffix Hbranch env (query_rows_bag input_rows) (SqlError error))).
- eapply EQuery_GroupingSetsSuccess; [eassumption| |eassumption].
  now apply (proj1 (eval_grouping_sets_bag_branch_congr
    prefix suffix Hbranch env (query_rows_bag input_rows)
      (SqlSuccess output_bag))).
- now apply EQuery_GroupingSetsChildError.
- eapply EQuery_GroupingSetsBagError; [eassumption|].
  now apply (proj2 (eval_grouping_sets_bag_branch_congr
    prefix suffix Hbranch env (query_rows_bag input_rows) (SqlError error))).
- eapply EQuery_GroupingSetsSuccess; [eassumption| |eassumption].
  now apply (proj2 (eval_grouping_sets_bag_branch_congr
    prefix suffix Hbranch env (query_rows_bag input_rows)
      (SqlSuccess output_bag))).
Qed.

Lemma query_expr_grouping_sets_select_context_global_congr :
  forall prefix select_context group_keys suffix input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_select_context_demand select_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++
          (plug_scalar_select_context select_context replacement, group_keys) ::
          suffix) input)
      (QExpr_GroupingSets
        (prefix ++
          (plug_scalar_select_context select_context replacement', group_keys) ::
          suffix) input).
Proof.
intros prefix select_context group_keys suffix input replacement replacement'
  Hequiv.
pose proof (@scalar_expr_context_global_congr
  ScalarResultValue
  (scalar_select_context_expression select_context)
  replacement replacement' Hequiv)
  as Hexpression.
pose proof (scalar_select_context_global_outcome_equiv
  select_context replacement replacement' Hexpression) as Hselect.
assert (Hselect_aggregates : forall current_env,
  eval_scalar_select_aggregate_runtime_error
    symbol_runtime_error aggregate_runtime_error current_env
    (plug_scalar_select_context select_context replacement) =
  eval_scalar_select_aggregate_runtime_error
    symbol_runtime_error aggregate_runtime_error current_env
    (plug_scalar_select_context select_context replacement')).
{ intro current_env; apply scalar_select_context_aggregate_runtime_error_congr. }
assert (Hlocal : forall current_env group_terms groups outcome,
  eval_groups current_env
    (plug_scalar_select_context select_context replacement)
    group_terms SExpr_True groups outcome <->
  eval_groups current_env
    (plug_scalar_select_context select_context replacement')
    group_terms SExpr_True groups outcome).
{
  intros current_env group_terms groups outcome.
  apply eval_groups_scalar_global_congr.
  - exact Hselect.
  - apply scalar_expr_global_outcome_equiv_refl.
  - exact Hselect_aggregates.
  - reflexivity.
}
apply query_expr_grouping_sets_branch_global_typed_congr.
- destruct prefix as [|first prefix]; cbn.
  + now apply scalar_select_list_global_outcome_equiv_outputs.
  + reflexivity.
- intros current_env input_bag outcome.
  now apply eval_group_bag_scalar_global_congr.
Qed.

Lemma query_expr_grouping_sets_key_context_global_congr :
  forall prefix select_list key_context suffix input replacement replacement',
    query_expr_global_typed_outcome_equiv
      (QExpr_GroupingSets
        (prefix ++
          (select_list,
            plug_scalar_value_list_context key_context replacement) :: suffix)
        input)
      (QExpr_GroupingSets
        (prefix ++
          (select_list,
            plug_scalar_value_list_context key_context replacement') :: suffix)
        input).
Proof.
intros prefix select_list key_context suffix input replacement replacement'.
pose proof (scalar_value_list_context_group_keys_none
  key_context replacement) as Hleft.
pose proof (scalar_value_list_context_group_keys_none
  key_context replacement') as Hright.
apply query_expr_grouping_sets_branch_global_typed_congr.
- destruct prefix; reflexivity.
- intros current_env input_bag outcome; split; intro Heval.
  + exfalso; eapply (eval_group_bag_group_keys_none Hleft); eassumption.
  + exfalso; eapply (eval_group_bag_group_keys_none Hright); eassumption.
Qed.

Lemma query_expr_group_select_context_global_congr :
  forall select_context group_keys having input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_select_context_demand select_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group (plug_scalar_select_context select_context replacement)
        group_keys having input)
      (QExpr_Group (plug_scalar_select_context select_context replacement')
        group_keys having input).
Proof.
intros select_context group_keys having input replacement replacement' Hequiv.
pose proof (@scalar_expr_context_global_congr ScalarResultValue
  (scalar_select_context_expression select_context)
  replacement replacement' Hequiv) as Hexpression.
pose proof (scalar_select_context_global_outcome_equiv
  select_context replacement replacement' Hexpression) as Hselect.
apply query_expr_group_scalar_global_typed_congr.
- exact Hselect.
- apply scalar_expr_global_group_outcome_equiv_refl.
- intro current_env; apply scalar_select_context_aggregate_runtime_error_congr.
Qed.

Lemma query_expr_group_having_context_global_congr :
  forall select_list group_keys having_context input replacement replacement',
    query_expr_global_demand_equiv
      (scalar_expr_context_demand having_context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list group_keys
        (plug_scalar_expr_context having_context replacement) input)
      (QExpr_Group select_list group_keys
        (plug_scalar_expr_context having_context replacement') input).
Proof.
intros select_list group_keys having_context input replacement replacement'
  Hequiv.
apply query_expr_group_scalar_global_typed_congr.
- apply scalar_select_list_global_outcome_equiv_refl.
- now apply scalar_expr_context_global_group_congr.
- reflexivity.
Qed.

Lemma query_expr_group_key_context_global_congr :
  forall select_list key_context having input replacement replacement',
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list
        (plug_scalar_value_list_context key_context replacement) having input)
      (QExpr_Group select_list
        (plug_scalar_value_list_context key_context replacement') having input).
Proof.
intros select_list key_context having input replacement replacement'.
apply query_expr_group_invalid_keys_global_typed_congr.
- apply scalar_value_list_context_group_keys_none.
- apply scalar_value_list_context_group_keys_none.
Qed.

Theorem query_expr_context_global_congr :
  forall (context : query_expr_context) replacement replacement',
    query_expr_global_demand_equiv (query_expr_context_demand context)
      replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
Proof.
induction context; cbn; intros replacement replacement' Hequiv;
  eauto using
    query_expr_global_typed_outcome_equiv_refl,
    query_expr_set_global_typed_congr,
    query_expr_natural_join_global_typed_congr,
    query_expr_cross_join_global_typed_congr,
    query_expr_join_global_typed_congr,
    query_expr_project_global_typed_congr,
    query_expr_row_map_global_typed_congr,
    query_expr_filter_global_typed_congr,
    query_expr_project_select_global_typed_congr,
    query_expr_filter_expression_global_typed_congr,
    query_expr_join_scalar_global_typed_congr,
    scalar_expr_context_global_congr,
    scalar_select_context_global_outcome_equiv,
    scalar_select_list_global_outcome_equiv_refl,
    scalar_expr_global_outcome_equiv_refl,
    query_expr_group_global_typed_congr,
    query_expr_group_select_context_global_congr,
    query_expr_group_key_context_global_congr,
    query_expr_group_having_context_global_congr,
    query_expr_grouping_sets_global_typed_congr,
    query_expr_grouping_sets_select_context_global_congr,
    query_expr_grouping_sets_key_context_global_congr,
    query_expr_rank_global_typed_congr,
    query_expr_window_global_typed_congr,
    query_expr_distinct_global_typed_congr,
    query_expr_order_by_global_typed_congr,
    query_expr_offset_global_typed_congr,
    query_expr_fetch_global_typed_congr.
Qed.

Definition query_expr_runtime_safe
    (env : Env.env T) (query : query_expr T relname) : Prop :=
  forall error, ~ eval_query env query (SqlError error).

Definition query_expr_has_success
    (env : Env.env T) (query : query_expr T relname) : Prop :=
  exists rows, eval_query env query (SqlSuccess rows).

Lemma query_expr_observation_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_observation_equiv T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
Proof.
intros env first second Hequiv Hfirst_safe Hsecond_safe Hsuccess.
unfold query_expr_observation_equiv, successful_relation_equiv.
split; [exact Hsuccess|].
split; [exact Hfirst_safe|].
split; [exact Hsecond_safe|].
split.
- intros rows Hrows.
  exists rows; split.
  + now apply (proj1 (Hequiv (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
- intros rows Hrows.
  exists rows; split.
  + now apply (proj2 (Hequiv (SqlSuccess rows))).
  + apply ordered_rows_equiv_refl.
Qed.

Lemma query_expr_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first second.
Proof.
intros env first second Houtputs Hequiv Hfirst_safe Hsecond_safe Hsuccess.
split; [exact Houtputs|].
now apply query_expr_observation_equiv_of_outcome_rel_equiv_safe.
Qed.

Theorem query_expr_context_equiv_safe :
  forall context replacement replacement' env,
    query_expr_global_demand_equiv (query_expr_context_demand context)
      replacement replacement' ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement) ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement') ->
    query_expr_has_success env
      (plug_query_expr_context context replacement) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
Proof.
intros context replacement replacement' env Hequiv Hsafe Hsafe' Hsuccess.
destruct (query_expr_context_global_congr
  context replacement replacement' Hequiv) as [Houtputs Hraw].
apply query_expr_equiv_of_outcome_rel_equiv_safe; try assumption.
apply Hraw.
Qed.

(** Possible-bag equality can be recovered as an exact ordered-observation
    equivalence once both result relations are proved bag-closed.  The
    possible-bag equality is not by itself allowed to hide runtime failures:
    safety and existence of a successful observation remain explicit
    premises. *)
Theorem query_bag_closed_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    BagClosed T
      (fun rows => eval_query env first (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query env second (SqlSuccess rows)) ->
    rel_equiv
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
Proof.
intros env first second Houtputs Hfirst_closed Hsecond_closed Hbags
  Hfirst_safe Hsecond_safe Hsuccess.
split; [exact Houtputs|].
apply (proj2
  (@query_bag_closed_observation_equiv_iff_possible_bag_equiv
    T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
    env first second Hfirst_closed Hsecond_closed)).
unfold query_possible_bag_equiv.
apply successful_relation_equiv_intro.
- destruct Hsuccess as [rows Hrows].
  exists (rows_bag T rows); simpl.
  exists rows; split; [exact Hrows | apply bag_eq_refl].
- intros error Herror; simpl in Herror.
  exact (Hfirst_safe error Herror).
- intros error Herror; simpl in Herror.
  exact (Hsecond_safe error Herror).
- intros bag Hbag.
  exists bag; split.
  + now apply (proj1 (Hbags bag)).
  + apply bag_eq_refl.
- intros bag Hbag.
  exists bag; split.
  + now apply (proj2 (Hbags bag)).
  + apply bag_eq_refl.
Qed.

(** Direct bag-reset constructors discharge the two semantic closure premises
    above automatically.  Other constructors may use the general theorem only
    when an independent, conditional closure proof is available. *)
Corollary query_bag_reset_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_order_behavior first = BagReset ->
    query_expr_order_behavior second = BagReset ->
    rel_equiv
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first)
      (query_success_bags basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env first second.
Proof.
intros env first second Houtputs Hfirst_reset Hsecond_reset Hbags
  Hfirst_safe Hsecond_safe Hsuccess.
apply query_bag_closed_equiv_of_success_bags_safe; try assumption.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

(** Immediate [Distinct] is the canonical local reset principle.  A proof may
    establish equality of the child queries' exact ordered success lists at
    one environment, cross [alpha] once, use the lifted duplicate-elimination
    operation, and return to exact equivalence through [BagClosed]. *)
Theorem query_distinct_equiv_of_local_success_rel_equiv :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall left_rows,
      eval_query env left (SqlSuccess left_rows) ->
      exists right_rows,
        eval_query env right (SqlSuccess right_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      eval_query env right (SqlSuccess right_rows) ->
      exists left_rows,
        eval_query env left (SqlSuccess left_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    query_expr_runtime_safe env (QExpr_Distinct left) ->
    query_expr_runtime_safe env (QExpr_Distinct right) ->
    query_expr_has_success env (QExpr_Distinct left) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right Houtputs Hforward Hbackward
  Hleft_safe Hright_safe Hsuccess.
apply query_bag_reset_equiv_of_success_bags_safe.
- exact Houtputs.
- reflexivity.
- reflexivity.
- apply query_distinct_actual_success_bags_congr.
  now apply query_success_bags_of_success_rel_equiv.
- exact Hleft_safe.
- exact Hright_safe.
- exact Hsuccess.
Qed.

(** Packaged fixed-environment substitution for callers that already have the
    standard typed, safe, successful list-equivalence contract for the child.
    The preceding theorem remains available when the outer safety/success
    obligations are proved separately. *)
Theorem query_distinct_local_list_equiv_congr :
  forall env left right,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env left right ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
      env (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right [Houtputs [Hsuccess [Hleft_safe [Hright_safe Hlists]]]].
apply query_distinct_equiv_of_local_success_rel_equiv.
- exact Houtputs.
- exact (proj1 Hlists).
- exact (proj2 Hlists).
- intros error Herror; inversion Herror; subst.
  eapply Hleft_safe; eassumption.
- intros error Herror; inversion Herror; subst.
  eapply Hright_safe; eassumption.
- destruct Hsuccess as [rows Hrows].
  exists (Febag.elements BTupleT
    (query_distinct_bag (rows_bag T rows))).
  eapply EQuery_DistinctSuccess.
  + exact Hrows.
  + apply query_elements_same_rows_as_bag.
Qed.

(** Contexts over the row-only possible-bag abstract domain. *)
Inductive possible_bag_context : Type :=
  | PBC_Hole : possible_bag_context
  | PBC_Unary : unary_bag_relation T -> possible_bag_context ->
      possible_bag_context
  | PBC_BinaryLeft : binary_bag_relation T -> possible_bag_context ->
      (bagT -> Prop) -> possible_bag_context
  | PBC_BinaryRight : binary_bag_relation T -> (bagT -> Prop) ->
      possible_bag_context -> possible_bag_context.

(** A possible-bag context is well formed when every abstract operation and
    every fixed possible-bag input respects FormalSQL bag equality.  This is
    the semantic quotient discipline required of generated bag contexts. *)
Fixpoint possible_bag_context_well_formed
    (context : possible_bag_context) : Prop :=
  match context with
  | PBC_Hole => True
  | PBC_Unary operation input =>
      unary_bag_relation_extensional operation /\
      possible_bag_context_well_formed input
  | PBC_BinaryLeft operation input fixed_relation =>
      binary_bag_relation_extensional operation /\
      possible_bag_context_well_formed input /\
      possible_bag_extensional T fixed_relation
  | PBC_BinaryRight operation fixed_relation input =>
      binary_bag_relation_extensional operation /\
      possible_bag_extensional T fixed_relation /\
      possible_bag_context_well_formed input
  end.

Fixpoint plug_possible_bag_context
    (context : possible_bag_context) (replacement : bagT -> Prop) :
    bagT -> Prop :=
  match context with
  | PBC_Hole => replacement
  | PBC_Unary operation input =>
      lift_possible_bag_unary operation
        (plug_possible_bag_context input replacement)
  | PBC_BinaryLeft operation input fixed_relation =>
      lift_possible_bag_binary operation
        (plug_possible_bag_context input replacement) fixed_relation
  | PBC_BinaryRight operation fixed_relation input =>
      lift_possible_bag_binary operation fixed_relation
        (plug_possible_bag_context input replacement)
  end.

(** Plugging an extensional possible-bag relation into a well-formed context
    produces another extensional possible-bag relation. *)
Theorem plug_possible_bag_context_extensional :
  forall context replacement,
    possible_bag_context_well_formed context ->
    possible_bag_extensional T replacement ->
    possible_bag_extensional T
      (plug_possible_bag_context context replacement).
Proof.
intro context; induction context; intros replacement Hcontext Hreplacement;
  simpl in *.
- exact Hreplacement.
- destruct Hcontext as [Hoperation Hinput].
  pose proof (IHcontext replacement Hinput Hreplacement) as Hplugged.
  now apply lift_possible_bag_unary_extensional.
- destruct Hcontext as [Hoperation [Hinput Hfixed]].
  pose proof (IHcontext replacement Hinput Hreplacement) as Hplugged.
  now apply lift_possible_bag_binary_extensional.
- destruct Hcontext as [Hoperation [Hfixed Hinput]].
  pose proof (IHcontext replacement Hinput Hreplacement) as Hplugged.
  now apply lift_possible_bag_binary_extensional.
Qed.

Theorem possible_bag_context_congr :
  forall context first second,
    rel_equiv first second ->
    rel_equiv
      (plug_possible_bag_context context first)
      (plug_possible_bag_context context second).
Proof.
intro context; induction context; intros first second Hequiv; simpl.
- exact Hequiv.
- apply lift_possible_bag_unary_congr. now apply IHcontext.
- apply lift_possible_bag_binary_congr.
  + now apply IHcontext.
  + intro bag; tauto.
- apply lift_possible_bag_binary_congr.
  + intro bag; tauto.
  + now apply IHcontext.
Qed.

Lemma outcome_alpha_congr :
  forall (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv (@outcome_alpha T first) (@outcome_alpha T second).
Proof.
intros first second Hequiv [bag | error]; simpl.
- apply alpha_congr. intro rows; apply Hequiv.
- apply Hequiv.
Qed.

Definition successful_possible_bags
    (observations : sql_outcome (list tuple) -> Prop) : bagT -> Prop :=
  fun bag => @outcome_alpha T observations (SqlSuccess bag).

Lemma successful_relation_equiv_possible_bags_rel_equiv :
  forall (first second : sql_outcome (list tuple) -> Prop),
    successful_relation_equiv (@ordered_rows_equiv T) first second ->
    rel_equiv
      (successful_possible_bags first)
      (successful_possible_bags second).
Proof.
intros first second [_ [_ [_ [Hforward Hbackward]]]] bag.
unfold successful_possible_bags, outcome_alpha, alpha; simpl.
split.
- intros [left_rows [Hleft Hbag]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists right_rows; split; [exact Hright |].
  eapply bag_eq_trans.
  + exact (bag_eq_sym (ordered_rows_equiv_implies_bag_eq Hrows)).
  + exact Hbag.
- intros [right_rows [Hright Hbag]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists left_rows; split; [exact Hleft |].
  eapply bag_eq_trans.
  + exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + exact Hbag.
Qed.

Lemma successful_possible_bags_extensional :
  forall observations,
    possible_bag_extensional T (successful_possible_bags observations).
Proof.
intro observations.
unfold successful_possible_bags.
exact (outcome_alpha_extensional observations).
Qed.

Theorem possible_bag_context_successful_plug_extensional :
  forall context observations,
    possible_bag_context_well_formed context ->
    possible_bag_extensional T
      (plug_possible_bag_context context
        (successful_possible_bags observations)).
Proof.
intros context observations Hcontext.
apply plug_possible_bag_context_extensional; [exact Hcontext|].
apply successful_possible_bags_extensional.
Qed.

Lemma list_outcome_equiv_successful_possible_bags :
  forall (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv
      (successful_possible_bags first)
      (successful_possible_bags second).
Proof.
intros first second Hequiv bag.
exact (outcome_alpha_congr Hequiv (SqlSuccess bag)).
Qed.

Theorem list_outcome_equiv_possible_bag_context_congr :
  forall context (first second : sql_outcome (list tuple) -> Prop),
    rel_equiv first second ->
    rel_equiv
      (plug_possible_bag_context context (successful_possible_bags first))
      (plug_possible_bag_context context (successful_possible_bags second)).
Proof.
intros context first second Hequiv.
apply possible_bag_context_congr.
now apply list_outcome_equiv_successful_possible_bags.
Qed.

(** Sort compatibility is carried separately at the query boundary because
    possible-bag relations intentionally contain rows only. *)
Definition possible_bag_query_boundary_equiv
    (first_sort second_sort : setA)
    (first second : bagT -> Prop) : Prop :=
  first_sort =S= second_sort /\ rel_equiv first second.

Theorem list_outcome_equiv_possible_bag_query_boundary_congr :
  forall context (first second : sql_outcome (list tuple) -> Prop)
         first_sort second_sort,
    first_sort =S= second_sort ->
    rel_equiv first second ->
    possible_bag_query_boundary_equiv first_sort second_sort
      (plug_possible_bag_context context (successful_possible_bags first))
      (plug_possible_bag_context context (successful_possible_bags second)).
Proof.
intros context first second first_sort second_sort Hsort Hequiv.
split; [exact Hsort|].
now apply list_outcome_equiv_possible_bag_context_congr.
Qed.

Theorem query_expr_equiv_possible_bag_context_congr :
  forall env context first second,
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env first second ->
    possible_bag_query_boundary_equiv
      (query_expr_sort first) (query_expr_sort second)
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env first)))
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env second))).
Proof.
intros env context first second [Houtputs Hobservation].
split.
- now apply (query_expr_outputs_eq_sort_eq first second).
- apply possible_bag_context_congr.
  now apply successful_relation_equiv_possible_bags_rel_equiv.
Qed.

End Sec.

Arguments QCtx_Hole {T relname}.
Arguments plug_query_expr_context {T relname} _ _.
Arguments plug_possible_bag_context {T} _ _.

(** Error-preserving contexts over the complete possible-schedule relation.

    This layer is intentionally abstract.  In particular, independently
    lifted left and right possible-outcome relations are merely their Cartesian
    product; they do not establish that the two children can be evaluated with
    one shared Boolean schedule.  A concrete binary query constructor may use
    this layer only after proving the exact characterization required at the
    query boundary below.

    Likewise, [Project], [Filter], [RowMap], and order-consuming constructors
    cannot be plugged merely because their children have the same possible
    bags.  Their characterization must retain the constructor's exact tuple,
    order, Boolean-schedule, and error behavior. *)
Section PossibleBagOutcomeContexts.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition outcome_tuple := tuple T.
Local Definition outcome_value := value T.
Local Definition outcome_setA := Fset.set (A T).
Local Definition outcome_BTupleT := Fecol.CBag (CTuple T).
Local Definition outcome_bagT := Febag.bag outcome_BTupleT.

Hypothesis basesort : relname -> outcome_setA.
Hypothesis instance : relname -> outcome_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * outcome_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * outcome_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : outcome_value -> bool.

Local Abbreviation eval_possible_query :=
  (@eval_query_expr_possible_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

(** The complete possible query relation, with only successful ordered lists
    abstracted to bags.  Inhabitation and runtime errors remain visible because
    [outcome_alpha] leaves the outer [sql_outcome] intact. *)
Definition query_possible_bag_outcomes
    (env : Env.env T) (query : query_expr T relname) :
    sql_outcome outcome_bagT -> Prop :=
  @outcome_alpha T (eval_possible_query env query).

(** Typed equality at the possible-bag/outcome boundary.  Output-list equality
    is deliberately separate from the extensional bag comparison. *)
Definition query_expr_possible_bag_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  outcome_relation_equiv (@bag_eq T)
    (query_possible_bag_outcomes env left)
    (query_possible_bag_outcomes env right).

Lemma query_expr_possible_bag_outcome_equiv_intro :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right) ->
    query_expr_possible_bag_outcome_equiv env left right.
Proof.
intros env left right Houtputs Houtcomes; now split.
Qed.

Lemma query_expr_possible_bag_outcome_equiv_outputs :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right ->
    query_expr_outputs left = query_expr_outputs right.
Proof.
intros env left right Hequiv; exact (proj1 Hequiv).
Qed.

Lemma query_expr_possible_bag_outcome_equiv_outcomes :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right ->
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right).
Proof.
intros env left right Hequiv; exact (proj2 Hequiv).
Qed.

Lemma query_expr_possible_bag_outcome_equiv_iff :
  forall env left right,
    query_expr_possible_bag_outcome_equiv env left right <->
    query_expr_outputs left = query_expr_outputs right /\
    outcome_relation_equiv (@bag_eq T)
      (query_possible_bag_outcomes env left)
      (query_possible_bag_outcomes env right).
Proof.
intros; reflexivity.
Qed.

(** Abstraction is sound without closure: exact ordered-row matches always
    induce bag matches, while errors are copied exactly. *)
Lemma outcome_relation_equiv_implies_outcome_alpha_equiv :
  forall (left right : sql_outcome (list outcome_tuple) -> Prop),
    outcome_relation_equiv (@ordered_rows_equiv T) left right ->
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right).
Proof.
intros left right
  [Hleft_outcome [Hright_outcome [Hforward [Hbackward Herrors]]]].
apply outcome_relation_equiv_intro.
- destruct Hleft_outcome as [[left_rows | error] Hleft].
  + exists (SqlSuccess (rows_bag T left_rows)); simpl.
    exists left_rows; split; [exact Hleft | apply bag_eq_refl].
  + now exists (SqlError error).
- destruct Hright_outcome as [[right_rows | error] Hright].
  + exists (SqlSuccess (rows_bag T right_rows)); simpl.
    exists right_rows; split; [exact Hright | apply bag_eq_refl].
  + now exists (SqlError error).
- intros left_bag [left_rows [Hleft Hleft_bag]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists left_bag; split.
  + simpl. exists right_rows; split; [exact Hright |].
    eapply bag_eq_trans.
    * exact
        (bag_eq_sym
          (ordered_rows_equiv_implies_bag_eq Hrows)).
    * exact Hleft_bag.
  + apply bag_eq_refl.
- intros right_bag [right_rows [Hright Hright_bag]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists right_bag; split.
  + simpl. exists left_rows; split; [exact Hleft |].
    eapply bag_eq_trans.
    * exact (ordered_rows_equiv_implies_bag_eq Hrows).
    * exact Hright_bag.
  + apply bag_eq_refl.
- intro error; simpl; apply Herrors.
Qed.

Theorem query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv :
  forall env left right,
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    query_expr_possible_bag_outcome_equiv env left right.
Proof.
intros env left right [Houtputs Houtcomes].
apply query_expr_possible_bag_outcome_equiv_intro; [exact Houtputs |].
unfold query_possible_bag_outcomes.
now apply outcome_relation_equiv_implies_outcome_alpha_equiv.
Qed.

(** Returning from bags to ordered observations is complete only when both
    possible-success relations are [BagClosed]. *)
Theorem query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_possible_query env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env right (SqlSuccess rows)) ->
    query_expr_possible_bag_outcome_equiv env left right ->
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
Proof.
intros env left right Hleft_closed Hright_closed [Houtputs Hbags].
split; [exact Houtputs |].
unfold query_expr_possible_outcome_observation_equiv.
apply (proj2
  (@outcome_relation_equiv_iff_outcome_alpha T
    (eval_possible_query env left) (eval_possible_query env right)
    Hleft_closed Hright_closed)).
exact Hbags.
Qed.

Corollary query_expr_possible_outcome_equiv_iff_possible_bag_outcome_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_possible_query env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env right (SqlSuccess rows)) ->
    (@query_expr_possible_outcome_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_possible_bag_outcome_equiv env left right).
Proof.
intros env left right Hleft_closed Hright_closed; split.
- apply query_expr_possible_outcome_equiv_implies_possible_bag_outcome_equiv.
- now apply query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv.
Qed.

(** Abstract outcome-aware operations.  These relations may preserve, produce,
    or transform runtime errors; no eager-success convention is built in. *)
Definition possible_bag_outcome_relation : Type :=
  sql_outcome outcome_bagT -> Prop.

Definition unary_bag_outcome_relation : Type :=
  sql_outcome outcome_bagT -> sql_outcome outcome_bagT -> Prop.

Definition binary_bag_outcome_relation : Type :=
  sql_outcome outcome_bagT -> sql_outcome outcome_bagT ->
  sql_outcome outcome_bagT -> Prop.

Definition possible_bag_outcome_relation_inhabited
    (outcomes : possible_bag_outcome_relation) : Prop :=
  exists outcome, outcomes outcome.

Definition lift_possible_bag_outcome_unary
    (operation : unary_bag_outcome_relation)
    (inputs : possible_bag_outcome_relation) :
    possible_bag_outcome_relation :=
  fun output => exists input, inputs input /\ operation input output.

Definition lift_possible_bag_outcome_binary
    (operation : binary_bag_outcome_relation)
    (left_inputs right_inputs : possible_bag_outcome_relation) :
    possible_bag_outcome_relation :=
  fun output => exists left_input, exists right_input,
    left_inputs left_input /\ right_inputs right_input /\
    operation left_input right_input output.

(** Compatibility is deliberately an outcome contract, not only bag
    extensionality.  It includes inhabited output relations and equality of
    every exposed runtime-error category. *)
Definition unary_bag_outcome_relation_compatible
    (operation : unary_bag_outcome_relation) : Prop :=
  forall left_input right_input,
    outcome_equiv (@bag_eq T) left_input right_input ->
    outcome_relation_equiv (@bag_eq T)
      (operation left_input) (operation right_input).

Definition binary_bag_outcome_relation_compatible
    (operation : binary_bag_outcome_relation) : Prop :=
  forall left_input left_input' right_input right_input',
    outcome_equiv (@bag_eq T) left_input left_input' ->
    outcome_equiv (@bag_eq T) right_input right_input' ->
    outcome_relation_equiv (@bag_eq T)
      (operation left_input right_input)
      (operation left_input' right_input').

Lemma possible_bag_outcome_equiv_refl :
  forall outcome : sql_outcome outcome_bagT,
    outcome_equiv (@bag_eq T) outcome outcome.
Proof.
intros [bag | error]; simpl.
- apply bag_eq_refl.
- reflexivity.
Qed.

Lemma possible_bag_outcome_relation_equiv_match_left :
  forall first second outcome,
    outcome_relation_equiv (@bag_eq T) first second ->
    first outcome ->
    exists outcome',
      second outcome' /\ outcome_equiv (@bag_eq T) outcome outcome'.
Proof.
intros first second [bag | error]
  [_ [_ [Hforward [_ Herrors]]]] Houtcome.
- destruct (Hforward bag Houtcome) as [bag' [Hbag' Hbags]].
  exists (SqlSuccess bag'); now split.
- exists (SqlError error); split.
  + now apply (proj1 (Herrors error)).
  + reflexivity.
Qed.

Lemma possible_bag_outcome_relation_equiv_match_right :
  forall first second outcome,
    outcome_relation_equiv (@bag_eq T) first second ->
    second outcome ->
    exists outcome',
      first outcome' /\ outcome_equiv (@bag_eq T) outcome' outcome.
Proof.
intros first second [bag | error]
  [_ [_ [_ [Hbackward Herrors]]]] Houtcome.
- destruct (Hbackward bag Houtcome) as [bag' [Hbag' Hbags]].
  exists (SqlSuccess bag'); now split.
- exists (SqlError error); split.
  + now apply (proj2 (Herrors error)).
  + reflexivity.
Qed.

Theorem lift_possible_bag_outcome_unary_congr :
  forall operation first_inputs second_inputs,
    unary_bag_outcome_relation_compatible operation ->
    outcome_relation_equiv (@bag_eq T) first_inputs second_inputs ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_unary operation first_inputs)
      (lift_possible_bag_outcome_unary operation second_inputs).
Proof.
intros operation first_inputs second_inputs Hoperation Hinputs.
apply outcome_relation_equiv_intro.
- destruct (proj1 Hinputs) as [input Hinput].
  pose proof
    (Hoperation input input (possible_bag_outcome_equiv_refl input))
    as Houtputs.
  destruct (proj1 Houtputs) as [output Houtput].
  exists output; now exists input.
- destruct (proj1 (proj2 Hinputs)) as [input Hinput].
  pose proof
    (Hoperation input input (possible_bag_outcome_equiv_refl input))
    as Houtputs.
  destruct (proj1 Houtputs) as [output Houtput].
  exists output; now exists input.
- intros output [input [Hinput Houtput]].
  destruct (@possible_bag_outcome_relation_equiv_match_left
    first_inputs second_inputs input Hinputs Hinput)
    as [input' [Hinput' Hinput_equiv]].
  pose proof (Hoperation input input' Hinput_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [Hforward _]]].
  destruct (Hforward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split; [now exists input' | exact Houtput_equiv].
- intros output [input [Hinput Houtput]].
  destruct (@possible_bag_outcome_relation_equiv_match_right
    first_inputs second_inputs input Hinputs Hinput)
    as [input' [Hinput' Hinput_equiv]].
  pose proof (Hoperation input' input Hinput_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [_ [Hbackward _]]]].
  destruct (Hbackward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split; [now exists input' | exact Houtput_equiv].
- intro error; split;
    intros [input [Hinput Houtput]].
  + destruct (@possible_bag_outcome_relation_equiv_match_left
      first_inputs second_inputs input Hinputs Hinput)
      as [input' [Hinput' Hinput_equiv]].
    pose proof (Hoperation input input' Hinput_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists input'; split; [exact Hinput' |].
    now apply (proj1 (Herrors error)).
  + destruct (@possible_bag_outcome_relation_equiv_match_right
      first_inputs second_inputs input Hinputs Hinput)
      as [input' [Hinput' Hinput_equiv]].
    pose proof (Hoperation input' input Hinput_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists input'; split; [exact Hinput' |].
    now apply (proj2 (Herrors error)).
Qed.

Theorem lift_possible_bag_outcome_binary_congr :
  forall operation first_left second_left first_right second_right,
    binary_bag_outcome_relation_compatible operation ->
    outcome_relation_equiv (@bag_eq T) first_left second_left ->
    outcome_relation_equiv (@bag_eq T) first_right second_right ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_binary operation first_left first_right)
      (lift_possible_bag_outcome_binary operation second_left second_right).
Proof.
intros operation first_left second_left first_right second_right
  Hoperation Hleft Hright.
apply outcome_relation_equiv_intro.
- destruct (proj1 Hleft) as [left_input Hleft_input].
  destruct (proj1 Hright) as [right_input Hright_input].
  pose proof (Hoperation left_input left_input right_input right_input
    (possible_bag_outcome_equiv_refl left_input)
    (possible_bag_outcome_equiv_refl right_input)) as Houtputs.
  destruct (proj1 Houtputs) as [output Houtput].
  exists output; exists left_input; exists right_input; now repeat split.
- destruct (proj1 (proj2 Hleft)) as [left_input Hleft_input].
  destruct (proj1 (proj2 Hright)) as [right_input Hright_input].
  pose proof (Hoperation left_input left_input right_input right_input
    (possible_bag_outcome_equiv_refl left_input)
    (possible_bag_outcome_equiv_refl right_input)) as Houtputs.
  destruct (proj1 Houtputs) as [output Houtput].
  exists output; exists left_input; exists right_input; now repeat split.
- intros output
    [left_input [right_input [Hleft_input [Hright_input Houtput]]]].
  destruct (@possible_bag_outcome_relation_equiv_match_left
    first_left second_left left_input Hleft Hleft_input)
    as [left_input' [Hleft_input' Hleft_equiv]].
  destruct (@possible_bag_outcome_relation_equiv_match_left
    first_right second_right right_input Hright Hright_input)
    as [right_input' [Hright_input' Hright_equiv]].
  pose proof
    (Hoperation left_input left_input' right_input right_input'
      Hleft_equiv Hright_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [Hforward _]]].
  destruct (Hforward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split.
  + exists left_input'; exists right_input'; now repeat split.
  + exact Houtput_equiv.
- intros output
    [left_input [right_input [Hleft_input [Hright_input Houtput]]]].
  destruct (@possible_bag_outcome_relation_equiv_match_right
    first_left second_left left_input Hleft Hleft_input)
    as [left_input' [Hleft_input' Hleft_equiv]].
  destruct (@possible_bag_outcome_relation_equiv_match_right
    first_right second_right right_input Hright Hright_input)
    as [right_input' [Hright_input' Hright_equiv]].
  pose proof
    (Hoperation left_input' left_input right_input' right_input
      Hleft_equiv Hright_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [_ [Hbackward _]]]].
  destruct (Hbackward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split.
  + exists left_input'; exists right_input'; now repeat split.
  + exact Houtput_equiv.
- intro error; split;
    intros [left_input [right_input
      [Hleft_input [Hright_input Houtput]]]].
  + destruct (@possible_bag_outcome_relation_equiv_match_left
      first_left second_left left_input Hleft Hleft_input)
      as [left_input' [Hleft_input' Hleft_equiv]].
    destruct (@possible_bag_outcome_relation_equiv_match_left
      first_right second_right right_input Hright Hright_input)
      as [right_input' [Hright_input' Hright_equiv]].
    pose proof
      (Hoperation left_input left_input' right_input right_input'
        Hleft_equiv Hright_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists left_input'; exists right_input'; repeat split; try assumption.
    now apply (proj1 (Herrors error)).
  + destruct (@possible_bag_outcome_relation_equiv_match_right
      first_left second_left left_input Hleft Hleft_input)
      as [left_input' [Hleft_input' Hleft_equiv]].
    destruct (@possible_bag_outcome_relation_equiv_match_right
      first_right second_right right_input Hright Hright_input)
      as [right_input' [Hright_input' Hright_equiv]].
    pose proof
      (Hoperation left_input' left_input right_input' right_input
        Hleft_equiv Hright_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists left_input'; exists right_input'; repeat split; try assumption.
    now apply (proj2 (Herrors error)).
Qed.

(** A one-hole abstract context.  Fixed binary inputs must be inhabited so
    that reflexive [outcome_relation_equiv] is not obtained vacuously. *)
Inductive possible_bag_outcome_context : Type :=
  | PBOC_Hole : possible_bag_outcome_context
  | PBOC_Unary : unary_bag_outcome_relation ->
      possible_bag_outcome_context -> possible_bag_outcome_context
  | PBOC_BinaryLeft : binary_bag_outcome_relation ->
      possible_bag_outcome_context -> possible_bag_outcome_relation ->
      possible_bag_outcome_context
  | PBOC_BinaryRight : binary_bag_outcome_relation ->
      possible_bag_outcome_relation -> possible_bag_outcome_context ->
      possible_bag_outcome_context.

Fixpoint possible_bag_outcome_context_well_formed
    (context : possible_bag_outcome_context) : Prop :=
  match context with
  | PBOC_Hole => True
  | PBOC_Unary operation input =>
      unary_bag_outcome_relation_compatible operation /\
      possible_bag_outcome_context_well_formed input
  | PBOC_BinaryLeft operation input fixed =>
      binary_bag_outcome_relation_compatible operation /\
      possible_bag_outcome_context_well_formed input /\
      possible_bag_outcome_relation_inhabited fixed
  | PBOC_BinaryRight operation fixed input =>
      binary_bag_outcome_relation_compatible operation /\
      possible_bag_outcome_relation_inhabited fixed /\
      possible_bag_outcome_context_well_formed input
  end.

Fixpoint plug_possible_bag_outcome_context
    (context : possible_bag_outcome_context)
    (replacement : possible_bag_outcome_relation) :
    possible_bag_outcome_relation :=
  match context with
  | PBOC_Hole => replacement
  | PBOC_Unary operation input =>
      lift_possible_bag_outcome_unary operation
        (plug_possible_bag_outcome_context input replacement)
  | PBOC_BinaryLeft operation input fixed =>
      lift_possible_bag_outcome_binary operation
        (plug_possible_bag_outcome_context input replacement) fixed
  | PBOC_BinaryRight operation fixed input =>
      lift_possible_bag_outcome_binary operation fixed
        (plug_possible_bag_outcome_context input replacement)
  end.

Theorem possible_bag_outcome_context_congr :
  forall context first second,
    possible_bag_outcome_context_well_formed context ->
    outcome_relation_equiv (@bag_eq T) first second ->
    outcome_relation_equiv (@bag_eq T)
      (plug_possible_bag_outcome_context context first)
      (plug_possible_bag_outcome_context context second).
Proof.
intro context; induction context; intros first second Hcontext Hequiv;
  simpl in *.
- exact Hequiv.
- destruct Hcontext as [Hoperation Hinput].
  apply lift_possible_bag_outcome_unary_congr; [exact Hoperation |].
  now apply IHcontext.
- destruct Hcontext as [Hoperation [Hinput Hfixed]].
  apply lift_possible_bag_outcome_binary_congr; [exact Hoperation | |].
  + now apply IHcontext.
  + apply outcome_relation_equiv_refl.
    * apply bag_eq_refl.
    * exact Hfixed.
- destruct Hcontext as [Hoperation [Hfixed Hinput]].
  apply lift_possible_bag_outcome_binary_congr; [exact Hoperation | |].
  + apply outcome_relation_equiv_refl.
    * apply bag_eq_refl.
    * exact Hfixed.
  + now apply IHcontext.
Qed.

Lemma outcome_relation_equiv_rel_equiv_transport :
  forall first first' second second',
    rel_equiv first first' ->
    rel_equiv second second' ->
    outcome_relation_equiv (@bag_eq T) first' second' ->
    outcome_relation_equiv (@bag_eq T) first second.
Proof.
intros first first' second second' Hfirst Hsecond
  [Hfirst_outcome [Hsecond_outcome [Hforward [Hbackward Herrors]]]].
apply outcome_relation_equiv_intro.
- destruct Hfirst_outcome as [outcome Houtcome].
  exists outcome; now apply (proj2 (Hfirst outcome)).
- destruct Hsecond_outcome as [outcome Houtcome].
  exists outcome; now apply (proj2 (Hsecond outcome)).
- intros value Hvalue.
  destruct (Hforward value (proj1 (Hfirst _) Hvalue))
    as [value' [Hvalue' Hequiv]].
  exists value'; split; [now apply (proj2 (Hsecond _)) | exact Hequiv].
- intros value Hvalue.
  destruct (Hbackward value (proj1 (Hsecond _) Hvalue))
    as [value' [Hvalue' Hequiv]].
  exists value'; split; [now apply (proj2 (Hfirst _)) | exact Hequiv].
- intro error; rewrite (Hfirst (SqlError error)), (Hsecond (SqlError error)).
  apply Herrors.
Qed.

(** Query-boundary use is permitted only with exact, two-sided [rel_equiv]
    characterizations of both actual parent abstractions.  Those premises are
    where a concrete operator must justify correlated environments, shared
    schedules, NULL/Bool3 behavior, order/tie behavior, and runtime errors. *)
Theorem query_expr_possible_bag_outcome_context_boundary_congr :
  forall env context child_left child_right parent_left parent_right,
    possible_bag_outcome_context_well_formed context ->
    query_expr_possible_bag_outcome_equiv env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    rel_equiv
      (query_possible_bag_outcomes env parent_left)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_left)) ->
    rel_equiv
      (query_possible_bag_outcomes env parent_right)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_right)) ->
    query_expr_possible_bag_outcome_equiv env parent_left parent_right.
Proof.
intros env context child_left child_right parent_left parent_right
  Hcontext Hchildren Houtputs Hleft_characterization
  Hright_characterization.
apply query_expr_possible_bag_outcome_equiv_intro; [exact Houtputs |].
eapply outcome_relation_equiv_rel_equiv_transport.
- exact Hleft_characterization.
- exact Hright_characterization.
- apply possible_bag_outcome_context_congr; [exact Hcontext |].
  exact (query_expr_possible_bag_outcome_equiv_outcomes Hchildren).
Qed.

(** Final recovery remains a separate step and again requires closure for both
    actual parent success relations. *)
Theorem query_expr_possible_bag_outcome_context_boundary_final :
  forall env context child_left child_right parent_left parent_right,
    BagClosed T
      (fun rows => eval_possible_query env parent_left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_possible_query env parent_right (SqlSuccess rows)) ->
    possible_bag_outcome_context_well_formed context ->
    query_expr_possible_bag_outcome_equiv env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    rel_equiv
      (query_possible_bag_outcomes env parent_left)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_left)) ->
    rel_equiv
      (query_possible_bag_outcomes env parent_right)
      (plug_possible_bag_outcome_context context
        (query_possible_bag_outcomes env child_right)) ->
    @query_expr_possible_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
Proof.
intros env context child_left child_right parent_left parent_right
  Hleft_closed Hright_closed Hcontext Hchildren Houtputs
  Hleft_characterization Hright_characterization.
apply query_expr_possible_bag_outcome_equiv_implies_possible_outcome_equiv;
  [exact Hleft_closed | exact Hright_closed |].
eapply query_expr_possible_bag_outcome_context_boundary_congr; eassumption.
Qed.

End PossibleBagOutcomeContexts.

Arguments PBOC_Hole {T}.
Arguments plug_possible_bag_outcome_context {T} _ _.

(** Schedule-indexed contracts for validating concrete wrapper laws.  These
    contracts refine the possible-bag layer above without assigning semantics
    to any query constructor. *)
Section ScheduleAwarePossibleBagContexts.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition scheduled_tuple := tuple T.
Local Definition scheduled_value := value T.
Local Definition scheduled_setA := Fset.set (A T).
Local Definition scheduled_BTupleT := Fecol.CBag (CTuple T).
Local Definition scheduled_bagT := Febag.bag scheduled_BTupleT.

Hypothesis basesort : relname -> scheduled_setA.
Hypothesis instance : relname -> scheduled_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * scheduled_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * scheduled_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : scheduled_value -> bool.

Local Abbreviation eval_scheduled_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

(** Bag/error outcomes at one exact Boolean-site schedule. *)
Definition query_scheduled_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (query : query_expr T relname) :
    sql_outcome scheduled_bagT -> Prop :=
  @outcome_alpha T (eval_scheduled_query schedule env query).

(** The complete possible-bag relation is exactly the union of its scheduled
    bag/error relations. *)
Lemma query_possible_bag_outcomes_iff_scheduled :
  forall env query outcome,
    @query_possible_bag_outcomes T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env query outcome <->
    exists schedule,
      query_scheduled_bag_outcomes schedule env query outcome.
Proof.
intros env query [bag | error];
  unfold query_possible_bag_outcomes, query_scheduled_bag_outcomes,
    eval_query_expr_possible_outcome, outcome_alpha, alpha; simpl.
- split.
  + intros [rows [[schedule Hrows] Hbag]].
    exists schedule; exists rows; now split.
  + intros [schedule [rows [Hrows Hbag]]].
    exists rows; split; [now exists schedule | exact Hbag].
- split.
  + intros [schedule Herror]; now exists schedule.
  + intros [schedule Herror]; now exists schedule.
Qed.

(** Schedule transport is stronger than equality of the unions: every exact
    source schedule has one target schedule whose complete scheduled bag/error
    relation matches, and conversely. *)
Definition query_expr_possible_bag_schedule_transport
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  (forall left_schedule,
    exists right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left)
        (query_scheduled_bag_outcomes right_schedule env right)) /\
  (forall right_schedule,
    exists left_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left)
        (query_scheduled_bag_outcomes right_schedule env right)).

Theorem query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv :
  forall env left right,
    query_expr_possible_bag_schedule_transport env left right ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
Proof.
intros env left right [Houtputs [Hforward Hbackward]].
apply query_expr_possible_bag_outcome_equiv_intro; [exact Houtputs |].
apply outcome_relation_equiv_intro.
- destruct (Hforward (fun _ => BooleanLeftFirst))
    as [right_schedule Hscheduled].
  destruct (proj1 Hscheduled) as [outcome Houtcome].
  exists outcome.
  apply (proj2 (query_possible_bag_outcomes_iff_scheduled env left outcome)).
  now exists (fun _ => BooleanLeftFirst).
- destruct (Hforward (fun _ => BooleanLeftFirst))
    as [right_schedule Hscheduled].
  destruct (proj1 (proj2 Hscheduled)) as [outcome Houtcome].
  exists outcome.
  apply (proj2 (query_possible_bag_outcomes_iff_scheduled env right outcome)).
  now exists right_schedule.
- intros left_bag Hleft_bag.
  apply (proj1
    (query_possible_bag_outcomes_iff_scheduled
      env left (SqlSuccess left_bag))) in Hleft_bag.
  destruct Hleft_bag as [left_schedule Hleft_bag].
  destruct (Hforward left_schedule)
    as [right_schedule Hscheduled].
  destruct Hscheduled as [_ [_ [Hscheduled_forward _]]].
  destruct (Hscheduled_forward left_bag Hleft_bag)
    as [right_bag [Hright_bag Hbags]].
  exists right_bag; split; [|exact Hbags].
  apply (proj2
    (query_possible_bag_outcomes_iff_scheduled
      env right (SqlSuccess right_bag))).
  now exists right_schedule.
- intros right_bag Hright_bag.
  apply (proj1
    (query_possible_bag_outcomes_iff_scheduled
      env right (SqlSuccess right_bag))) in Hright_bag.
  destruct Hright_bag as [right_schedule Hright_bag].
  destruct (Hbackward right_schedule)
    as [left_schedule Hscheduled].
  destruct Hscheduled as [_ [_ [_ [Hscheduled_backward _]]]].
  destruct (Hscheduled_backward right_bag Hright_bag)
    as [left_bag [Hleft_bag Hbags]].
  exists left_bag; split; [|exact Hbags].
  apply (proj2
    (query_possible_bag_outcomes_iff_scheduled
      env left (SqlSuccess left_bag))).
  now exists left_schedule.
- intro error; split; intro Herror.
  + apply (proj1
      (query_possible_bag_outcomes_iff_scheduled
        env left (SqlError error))) in Herror.
    destruct Herror as [left_schedule Herror].
    destruct (Hforward left_schedule)
      as [right_schedule Hscheduled].
    destruct Hscheduled as [_ [_ [_ [_ Herrors]]]].
    apply (proj2
      (query_possible_bag_outcomes_iff_scheduled
        env right (SqlError error))).
    exists right_schedule; now apply (proj1 (Herrors error)).
  + apply (proj1
      (query_possible_bag_outcomes_iff_scheduled
        env right (SqlError error))) in Herror.
    destruct Herror as [right_schedule Herror].
    destruct (Hbackward right_schedule)
      as [left_schedule Hscheduled].
    destruct Hscheduled as [_ [_ [_ [_ Herrors]]]].
    apply (proj2
      (query_possible_bag_outcomes_iff_scheduled
        env left (SqlError error))).
    exists left_schedule; now apply (proj2 (Herrors error)).
Qed.

(** A unary wrapper law is local to one matched schedule pair.  This premise
    is where [Project], [RowMap], [Filter], [Group], [GroupingSets], [Rank],
    [Window], [Distinct], and [OrderBy] must justify their exact tuple,
    multiplicity, Bool3, aggregate-finalization, tie, schedule, and error
    behavior.  This generic theorem supplies none of those facts itself.
    [Offset] and [Fetch] additionally require a later [BagClosed]/all-list-
    representatives argument before recovering ordered observations. *)
Theorem query_expr_possible_bag_unary_wrapper_schedule_transport :
  forall env child_left child_right parent_left parent_right,
    query_expr_possible_bag_schedule_transport
      env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env child_left)
        (query_scheduled_bag_outcomes right_schedule env child_right) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    query_expr_possible_bag_schedule_transport
      env parent_left parent_right.
Proof.
intros env child_left child_right parent_left parent_right
  [_ [Hforward Hbackward]] Houtputs Hlocal.
split; [exact Houtputs |].
split.
- intro left_schedule.
  destruct (Hforward left_schedule)
    as [right_schedule Hchildren].
  exists right_schedule; now apply Hlocal.
- intro right_schedule.
  destruct (Hbackward right_schedule)
    as [left_schedule Hchildren].
  exists left_schedule; now apply Hlocal.
Qed.

Theorem query_expr_possible_bag_unary_wrapper_congr :
  forall env child_left child_right parent_left parent_right,
    query_expr_possible_bag_schedule_transport
      env child_left child_right ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env child_left)
        (query_scheduled_bag_outcomes right_schedule env child_right) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
Proof.
intros env child_left child_right parent_left parent_right
  Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport; eassumption.
Qed.

(** A binary wrapper needs joint schedule transport.  For each source
    schedule, one target schedule must simultaneously relate both child pairs,
    and conversely.  Independent marginal transports cannot establish this
    shared witness and are insufficient for [QExpr_Set], [QExpr_NaturalJoin],
    [QExpr_CrossJoin], or [QExpr_Join]. *)
Definition query_expr_possible_bag_joint_schedule_transport
    (env : Env.env T)
    (left_first left_second right_first right_second :
      query_expr T relname) : Prop :=
  query_expr_outputs left_first = query_expr_outputs right_first /\
  query_expr_outputs left_second = query_expr_outputs right_second /\
  (forall left_schedule,
    exists right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) /\
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second)) /\
  (forall right_schedule,
    exists left_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) /\
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second)).

(** The local binary law consumes the two child relations under exactly the
    same matched schedules and must prove the complete parent bag/error
    relation under those schedules. *)
Theorem query_expr_possible_bag_binary_wrapper_schedule_transport :
  forall env left_first left_second right_first right_second
         parent_left parent_right,
    query_expr_possible_bag_joint_schedule_transport env
      left_first left_second right_first right_second ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    query_expr_possible_bag_schedule_transport
      env parent_left parent_right.
Proof.
intros env left_first left_second right_first right_second
  parent_left parent_right
  [_ [_ [Hforward Hbackward]]] Houtputs Hlocal.
split; [exact Houtputs |].
split.
- intro left_schedule.
  destruct (Hforward left_schedule)
    as [right_schedule [Hfirst Hsecond]].
  exists right_schedule; now apply Hlocal.
- intro right_schedule.
  destruct (Hbackward right_schedule)
    as [left_schedule [Hfirst Hsecond]].
  exists left_schedule; now apply Hlocal.
Qed.

Theorem query_expr_possible_bag_binary_wrapper_congr :
  forall env left_first left_second right_first right_second
         parent_left parent_right,
    query_expr_possible_bag_joint_schedule_transport env
      left_first left_second right_first right_second ->
    query_expr_outputs parent_left = query_expr_outputs parent_right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_first)
        (query_scheduled_bag_outcomes right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env left_second)
        (query_scheduled_bag_outcomes right_schedule env right_second) ->
      outcome_relation_equiv (@bag_eq T)
        (query_scheduled_bag_outcomes left_schedule env parent_left)
        (query_scheduled_bag_outcomes right_schedule env parent_right)) ->
    @query_expr_possible_bag_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env parent_left parent_right.
Proof.
intros env left_first left_second right_first right_second
  parent_left parent_right
  Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_possible_bag_binary_wrapper_schedule_transport; eassumption.
Qed.

End ScheduleAwarePossibleBagContexts.

(** Constructor-facing scheduled binary laws.  The eager-left lift below is
    an abstraction of the actual query rules: a left error is exposed without
    demanding the right query, a right error is exposed only after a left
    success, and operator-local errors arise only after both children succeed.
    It is not the independent Cartesian marginal model warned about above. *)
Section ScheduledBinaryConstructorLaws.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition constructor_tuple := tuple T.
Local Definition constructor_value := value T.
Local Definition constructor_setA := Fset.set (A T).
Local Definition constructor_BTupleT := Fecol.CBag (CTuple T).
Local Definition constructor_bagT := Febag.bag constructor_BTupleT.

Hypothesis basesort : relname -> constructor_setA.
Hypothesis instance : relname -> constructor_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * constructor_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * constructor_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : constructor_value -> bool.

Local Abbreviation eval_scheduled_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Definition query_binary_bag_outcome_operation : Type :=
  constructor_bagT -> constructor_bagT ->
  sql_outcome constructor_bagT -> Prop.

(** Turn a successful bag relation into an operator outcome relation with no
    internal error outcomes. *)
Definition query_success_only_binary_bag_operation
    (operation : binary_bag_relation T) :
    query_binary_bag_outcome_operation :=
  fun left_bag right_bag outcome =>
    match outcome with
    | SqlSuccess output_bag => operation left_bag right_bag output_bag
    | SqlError _ => False
    end.

Definition query_eager_left_binary_outcome_relation
    (operation : query_binary_bag_outcome_operation) :
    binary_bag_outcome_relation T :=
  fun left_outcome right_outcome output =>
    match left_outcome with
    | SqlError error => output = SqlError error
    | SqlSuccess left_bag =>
        match right_outcome with
        | SqlError error => output = SqlError error
        | SqlSuccess right_bag => operation left_bag right_bag output
        end
    end.

(** Quotient-respecting operator semantics, including exact errors. *)
Definition query_binary_bag_outcome_operation_extensional
    (operation : query_binary_bag_outcome_operation) : Prop :=
  forall left_bag left_bag' right_bag right_bag' output output',
    bag_eq T left_bag left_bag' ->
    bag_eq T right_bag right_bag' ->
    outcome_equiv (@bag_eq T) output output' ->
    (operation left_bag right_bag output <->
     operation left_bag' right_bag' output').

(** Cross-schedule compatibility is deliberately operator-local.  For JOIN,
    the two operations below are the authoritative [eval_join_bag_outcome]
    relations at the two matched schedules. *)
Definition query_binary_bag_outcome_operations_compatible
    (left_operation right_operation :
      query_binary_bag_outcome_operation) : Prop :=
  forall left_bag left_bag' right_bag right_bag',
    bag_eq T left_bag left_bag' ->
    bag_eq T right_bag right_bag' ->
    outcome_relation_equiv (@bag_eq T)
      (left_operation left_bag right_bag)
      (right_operation left_bag' right_bag').

Definition binary_bag_outcome_relations_cross_compatible
    (left_operation right_operation : binary_bag_outcome_relation T) : Prop :=
  forall left_input left_input' right_input right_input',
    outcome_equiv (@bag_eq T) left_input left_input' ->
    outcome_equiv (@bag_eq T) right_input right_input' ->
    outcome_relation_equiv (@bag_eq T)
      (left_operation left_input right_input)
      (right_operation left_input' right_input').

Lemma query_error_singleton_outcome_relation_equiv :
  forall error,
    outcome_relation_equiv (@bag_eq T)
      (fun outcome : sql_outcome constructor_bagT =>
        outcome = SqlError error)
      (fun outcome : sql_outcome constructor_bagT =>
        outcome = SqlError error).
Proof.
intro error.
apply outcome_relation_equiv_refl.
- apply bag_eq_refl.
- exists (SqlError error); reflexivity.
Qed.

Lemma query_eager_left_binary_outcome_relation_cross_compatible :
  forall left_operation right_operation,
    query_binary_bag_outcome_operations_compatible
      left_operation right_operation ->
    binary_bag_outcome_relations_cross_compatible
      (query_eager_left_binary_outcome_relation left_operation)
      (query_eager_left_binary_outcome_relation right_operation).
Proof.
intros left_operation right_operation Hoperations
  [left_bag | left_error] [left_bag' | left_error']
  [right_bag | right_error] [right_bag' | right_error']
  Hleft Hright; simpl in Hleft, Hright; try contradiction.
- now apply Hoperations.
- subst right_error'. apply query_error_singleton_outcome_relation_equiv.
- subst left_error'. apply query_error_singleton_outcome_relation_equiv.
- subst left_error'. apply query_error_singleton_outcome_relation_equiv.
Qed.

(** Cross-operation counterpart of the ordinary binary lift congruence. *)
Theorem lift_possible_bag_outcome_binary_cross_congr :
  forall left_operation right_operation
         first_left second_left first_right second_right,
    binary_bag_outcome_relations_cross_compatible
      left_operation right_operation ->
    outcome_relation_equiv (@bag_eq T) first_left second_left ->
    outcome_relation_equiv (@bag_eq T) first_right second_right ->
    outcome_relation_equiv (@bag_eq T)
      (lift_possible_bag_outcome_binary
        left_operation first_left first_right)
      (lift_possible_bag_outcome_binary
        right_operation second_left second_right).
Proof.
intros left_operation right_operation
  first_left second_left first_right second_right
  Hoperation Hleft Hright.
apply outcome_relation_equiv_intro.
- destruct (proj1 Hleft) as [left_input Hleft_input].
  destruct (proj1 Hright) as [right_input Hright_input].
  pose proof (Hoperation left_input left_input right_input right_input
    (@possible_bag_outcome_equiv_refl T left_input)
    (@possible_bag_outcome_equiv_refl T right_input)) as Houtputs.
  destruct (proj1 Houtputs) as [output Houtput].
  exists output; exists left_input; exists right_input; now repeat split.
- destruct (proj1 (proj2 Hleft)) as [left_input Hleft_input].
  destruct (proj1 (proj2 Hright)) as [right_input Hright_input].
  pose proof (Hoperation left_input left_input right_input right_input
    (@possible_bag_outcome_equiv_refl T left_input)
    (@possible_bag_outcome_equiv_refl T right_input)) as Houtputs.
  destruct (proj1 (proj2 Houtputs)) as [output Houtput].
  exists output; exists left_input; exists right_input; now repeat split.
- intros output
    [left_input [right_input [Hleft_input [Hright_input Houtput]]]].
  destruct (@possible_bag_outcome_relation_equiv_match_left
    T first_left second_left left_input Hleft Hleft_input)
    as [left_input' [Hleft_input' Hleft_equiv]].
  destruct (@possible_bag_outcome_relation_equiv_match_left
    T first_right second_right right_input Hright Hright_input)
    as [right_input' [Hright_input' Hright_equiv]].
  pose proof
    (Hoperation left_input left_input' right_input right_input'
      Hleft_equiv Hright_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [Hforward _]]].
  destruct (Hforward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split.
  + exists left_input'; exists right_input'; now repeat split.
  + exact Houtput_equiv.
- intros output
    [left_input [right_input [Hleft_input [Hright_input Houtput]]]].
  destruct (@possible_bag_outcome_relation_equiv_match_right
    T first_left second_left left_input Hleft Hleft_input)
    as [left_input' [Hleft_input' Hleft_equiv]].
  destruct (@possible_bag_outcome_relation_equiv_match_right
    T first_right second_right right_input Hright Hright_input)
    as [right_input' [Hright_input' Hright_equiv]].
  pose proof
    (Hoperation left_input' left_input right_input' right_input
      Hleft_equiv Hright_equiv) as Houtputs.
  destruct Houtputs as [_ [_ [_ [Hbackward _]]]].
  destruct (Hbackward output Houtput)
    as [output' [Houtput' Houtput_equiv]].
  exists output'; split.
  + exists left_input'; exists right_input'; now repeat split.
  + exact Houtput_equiv.
- intro error; split;
    intros [left_input [right_input
      [Hleft_input [Hright_input Houtput]]]].
  + destruct (@possible_bag_outcome_relation_equiv_match_left
      T first_left second_left left_input Hleft Hleft_input)
      as [left_input' [Hleft_input' Hleft_equiv]].
    destruct (@possible_bag_outcome_relation_equiv_match_left
      T first_right second_right right_input Hright Hright_input)
      as [right_input' [Hright_input' Hright_equiv]].
    pose proof
      (Hoperation left_input left_input' right_input right_input'
        Hleft_equiv Hright_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists left_input'; exists right_input'; repeat split; try assumption.
    now apply (proj1 (Herrors error)).
  + destruct (@possible_bag_outcome_relation_equiv_match_right
      T first_left second_left left_input Hleft Hleft_input)
      as [left_input' [Hleft_input' Hleft_equiv]].
    destruct (@possible_bag_outcome_relation_equiv_match_right
      T first_right second_right right_input Hright Hright_input)
      as [right_input' [Hright_input' Hright_equiv]].
    pose proof
      (Hoperation left_input' left_input right_input' right_input
        Hleft_equiv Hright_equiv) as Houtputs.
    destruct Houtputs as [_ [_ [_ [_ Herrors]]]].
    exists left_input'; exists right_input'; repeat split; try assumption.
    now apply (proj2 (Herrors error)).
Qed.

(** Exact abstraction theorem for any scheduled eager-left binary parent.
    The two semantic iff premises are constructor inversion laws over the
    authoritative ordered evaluator, not assumptions of parent equivalence. *)
Theorem query_scheduled_binary_parent_bag_outcomes_characterization :
  forall schedule env parent left right operation,
    (forall output,
      eval_scheduled_query schedule env parent (SqlSuccess output) <->
      exists left_rows, exists right_rows, exists output_bag,
        eval_scheduled_query schedule env left (SqlSuccess left_rows) /\
        eval_scheduled_query schedule env right (SqlSuccess right_rows) /\
        operation (rows_bag T left_rows) (rows_bag T right_rows)
          (SqlSuccess output_bag) /\
        query_same_rows_as_bag output output_bag) ->
    (forall error,
      eval_scheduled_query schedule env parent (SqlError error) <->
      eval_scheduled_query schedule env left (SqlError error) \/
      exists left_rows,
        eval_scheduled_query schedule env left (SqlSuccess left_rows) /\
        (eval_scheduled_query schedule env right (SqlError error) \/
         exists right_rows,
           eval_scheduled_query schedule env right (SqlSuccess right_rows) /\
           operation (rows_bag T left_rows) (rows_bag T right_rows)
             (SqlError error))) ->
    query_binary_bag_outcome_operation_extensional operation ->
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env parent)
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
Proof.
intros schedule env parent left right operation
  Hsuccess Herror Hoperation Hright_inhabited [observed_bag | error].
- unfold query_scheduled_bag_outcomes, outcome_alpha, alpha,
    lift_possible_bag_outcome_binary,
    query_eager_left_binary_outcome_relation; simpl.
  split.
  + intros [output [Hparent Hobserved]].
    apply Hsuccess in Hparent.
    destruct Hparent as
      [left_rows [right_rows [output_bag
        [Hleft [Hright [Hresult Houtput]]]]]].
    apply query_same_rows_as_bag_iff_bag_eq in Houtput.
    exists (SqlSuccess (rows_bag T left_rows)).
    exists (SqlSuccess (rows_bag T right_rows)).
    repeat split.
    * exists left_rows; split; [exact Hleft | apply bag_eq_refl].
    * exists right_rows; split; [exact Hright | apply bag_eq_refl].
    * assert (Hresult_bag : bag_eq T output_bag observed_bag).
      {
        exact (bag_eq_trans (bag_eq_sym Houtput) Hobserved).
      }
      apply (proj1
        (Hoperation
          (rows_bag T left_rows) (rows_bag T left_rows)
          (rows_bag T right_rows) (rows_bag T right_rows)
          (SqlSuccess output_bag) (SqlSuccess observed_bag)
          (bag_eq_refl T _) (bag_eq_refl T _) Hresult_bag)).
      exact Hresult.
  + intros [left_outcome [right_outcome
      [Hleft [Hright Hresult]]]].
    destruct left_outcome as [left_bag | left_error];
      [|discriminate Hresult].
    destruct right_outcome as [right_bag | right_error];
      [|discriminate Hresult].
    destruct Hleft as [left_rows [Hleft Hleft_bag]].
    destruct Hright as [right_rows [Hright Hright_bag]].
    assert (Hconcrete :
      operation (rows_bag T left_rows) (rows_bag T right_rows)
        (SqlSuccess observed_bag)).
    {
      apply (proj2
        (Hoperation
          (rows_bag T left_rows) left_bag
          (rows_bag T right_rows) right_bag
          (SqlSuccess observed_bag) (SqlSuccess observed_bag)
          Hleft_bag Hright_bag (bag_eq_refl T observed_bag))).
      exact Hresult.
    }
    exists (Febag.elements constructor_BTupleT observed_bag); split.
    * apply Hsuccess.
      exists left_rows; exists right_rows; exists observed_bag.
      repeat split; try assumption.
      apply query_elements_same_rows_as_bag.
    * apply rows_bag_elements.
- unfold query_scheduled_bag_outcomes, outcome_alpha,
    lift_possible_bag_outcome_binary,
    query_eager_left_binary_outcome_relation; simpl.
  split.
  + intro Hparent; apply Herror in Hparent.
    destruct Hparent as
      [Hleft_error |
       [left_rows [Hleft [Hright_error |
        [right_rows [Hright Hresult]]]]]].
    * destruct Hright_inhabited as [right_outcome Hright].
      exists (SqlError error); exists right_outcome.
      repeat split; try assumption; reflexivity.
    * exists (SqlSuccess (rows_bag T left_rows)); exists (SqlError error).
      repeat split; try assumption.
      exists left_rows; split; [exact Hleft | apply bag_eq_refl].
    * exists (SqlSuccess (rows_bag T left_rows)).
      exists (SqlSuccess (rows_bag T right_rows)).
      repeat split; try assumption.
      -- exists left_rows; split; [exact Hleft | apply bag_eq_refl].
      -- exists right_rows; split; [exact Hright | apply bag_eq_refl].
  + intros [left_outcome [right_outcome
      [Hleft [Hright Hresult]]]].
    destruct left_outcome as [left_bag | left_error].
    * destruct right_outcome as [right_bag | right_error].
      -- destruct Hleft as [left_rows [Hleft Hleft_bag]].
         destruct Hright as [right_rows [Hright Hright_bag]].
         apply Herror; right; exists left_rows; split; [exact Hleft |].
         right; exists right_rows; split; [exact Hright |].
         apply (proj2
           (Hoperation
             (rows_bag T left_rows) left_bag
             (rows_bag T right_rows) right_bag
             (SqlError error) (SqlError error)
             Hleft_bag Hright_bag eq_refl)).
         exact Hresult.
      -- inversion Hresult; subst right_error.
         destruct Hleft as [left_rows [Hleft _]].
         apply Herror; right; exists left_rows; now split; auto.
    * inversion Hresult; subst left_error.
      apply Herror; now left.
Qed.

End ScheduledBinaryConstructorLaws.

Section ScheduledBinaryConstructorAdapters.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition adapter_tuple := tuple T.
Local Definition adapter_value := value T.
Local Definition adapter_setA := Fset.set (A T).
Local Definition adapter_BTupleT := Fecol.CBag (CTuple T).
Local Definition adapter_bagT := Febag.bag adapter_BTupleT.

Hypothesis basesort : relname -> adapter_setA.
Hypothesis instance : relname -> adapter_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * adapter_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * adapter_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : adapter_value -> bool.

Local Abbreviation eval_adapter_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).
Local Abbreviation eval_adapter_join_bag schedule :=
  (@eval_join_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Local Definition query_set_outcome_operation operation left right :=
  @query_success_only_binary_bag_operation T
    (@query_set_bag_relation T relname operation left right).

Local Definition query_natural_join_outcome_operation :=
  @query_success_only_binary_bag_operation T
    (@query_natural_join_bag_relation T value_is_null).

Local Definition query_cross_join_outcome_operation :=
  @query_success_only_binary_bag_operation T
    (@query_cross_join_bag_relation T).

Local Definition query_join_outcome_operation schedule env kind predicate
    matched_select left_select right_select :
    query_binary_bag_outcome_operation T :=
  eval_adapter_join_bag schedule env kind predicate
    matched_select left_select right_select.

Lemma query_success_only_binary_bag_operation_extensional :
  forall relation,
    binary_bag_relation_extensional relation ->
    query_binary_bag_outcome_operation_extensional
      (@query_success_only_binary_bag_operation T relation).
Proof.
intros relation Hrelation left_bag left_bag' right_bag right_bag'
  [output_bag | error] [output_bag' | error'] Hleft Hright Houtput;
  simpl in Houtput; try contradiction; simpl.
- now apply Hrelation.
- tauto.
Qed.

Lemma query_success_only_binary_bag_operations_compatible :
  forall relation,
    binary_bag_relation_extensional relation ->
    (forall left_bag right_bag,
      exists output_bag, relation left_bag right_bag output_bag) ->
    query_binary_bag_outcome_operations_compatible
      (@query_success_only_binary_bag_operation T relation)
      (@query_success_only_binary_bag_operation T relation).
Proof.
intros relation Hrelation Htotal
  left_bag left_bag' right_bag right_bag' Hleft Hright.
apply outcome_relation_equiv_intro.
- destruct (Htotal left_bag right_bag) as [output Houtput].
  now exists (SqlSuccess output).
- destruct (Htotal left_bag' right_bag') as [output Houtput].
  now exists (SqlSuccess output).
- intros output Houtput.
  exists output; split.
  + simpl in *. apply (proj1
      (Hrelation left_bag left_bag' right_bag right_bag'
        output output Hleft Hright (bag_eq_refl T output))).
    exact Houtput.
  + apply bag_eq_refl.
- intros output Houtput.
  exists output; split.
  + simpl in *. apply (proj2
      (Hrelation left_bag left_bag' right_bag right_bag'
        output output Hleft Hright (bag_eq_refl T output))).
    exact Houtput.
  + apply bag_eq_refl.
- intro error; simpl; tauto.
Qed.

Lemma query_set_outcome_operations_compatible :
  forall operation left left' right right',
    query_expr_sort left =S= query_expr_sort left' ->
    query_expr_sort right =S= query_expr_sort right' ->
    query_binary_bag_outcome_operations_compatible
      (query_set_outcome_operation operation left right)
      (query_set_outcome_operation operation left' right').
Proof.
intros operation left left' right right' Hleft_sort Hright_sort
  left_bag left_bag' right_bag right_bag' Hleft Hright.
pose proof
  (query_set_bag_relation_sort_congr operation left left' right right'
    Hleft_sort Hright_sort) as Hsyntax.
pose proof (query_set_bag_relation_extensional operation left right)
  as Hsource_ext.
pose proof (query_set_bag_relation_extensional operation left' right')
  as Htarget_ext.
apply outcome_relation_equiv_intro.
- exists (SqlSuccess
    (query_set_bag_function operation left right left_bag right_bag)).
  unfold query_set_outcome_operation,
    query_success_only_binary_bag_operation, query_set_bag_relation,
    binary_bag_graph; apply bag_eq_refl.
- exists (SqlSuccess
    (query_set_bag_function operation left' right' left_bag' right_bag')).
  unfold query_set_outcome_operation,
    query_success_only_binary_bag_operation, query_set_bag_relation,
    binary_bag_graph; apply bag_eq_refl.
- intros output Houtput.
  exists output; split.
  + unfold query_set_outcome_operation,
      query_success_only_binary_bag_operation in *.
    apply (proj1
      (Htarget_ext left_bag left_bag' right_bag right_bag'
        output output Hleft Hright (bag_eq_refl T output))).
    now apply (proj1 (Hsyntax left_bag right_bag output)).
  + apply bag_eq_refl.
- intros output Houtput.
  exists output; split.
  + unfold query_set_outcome_operation,
      query_success_only_binary_bag_operation in *.
    apply (proj2 (Hsyntax left_bag right_bag output)).
    apply (proj2
      (Htarget_ext left_bag left_bag' right_bag right_bag'
        output output Hleft Hright (bag_eq_refl T output))).
    exact Houtput.
  + apply bag_eq_refl.
- intro error; simpl; tauto.
Qed.

Lemma query_natural_join_outcome_operations_compatible :
  query_binary_bag_outcome_operations_compatible
    query_natural_join_outcome_operation
    query_natural_join_outcome_operation.
Proof.
apply query_success_only_binary_bag_operations_compatible.
- apply query_natural_join_bag_relation_extensional.
- intros left_bag right_bag.
  exists (query_natural_join_bag value_is_null left_bag right_bag).
  unfold query_natural_join_bag_relation, binary_bag_graph.
  apply bag_eq_refl.
Qed.

Lemma query_cross_join_outcome_operations_compatible :
  query_binary_bag_outcome_operations_compatible
    query_cross_join_outcome_operation
    query_cross_join_outcome_operation.
Proof.
apply query_success_only_binary_bag_operations_compatible.
- apply query_cross_join_bag_relation_extensional.
- intros left_bag right_bag.
  exists (query_cross_join_bag left_bag right_bag).
  unfold query_cross_join_bag_relation, binary_bag_graph.
  apply bag_eq_refl.
Qed.

(** The full native-join operator relation is extensional for successes and
    exact runtime errors, not merely its successful projection. *)
Lemma query_join_outcome_operation_extensional :
  forall schedule env kind predicate matched_select left_select right_select,
    query_binary_bag_outcome_operation_extensional
      (query_join_outcome_operation schedule env kind predicate
        matched_select left_select right_select).
Proof.
intros schedule env kind predicate matched_select left_select right_select
  left_bag left_bag' right_bag right_bag'
  [output_bag | error] [output_bag' | error'] Hleft Hright Houtput;
  simpl in Houtput; try contradiction.
- unfold query_join_outcome_operation.
  apply query_join_bag_relation_extensional; assumption.
- subst error'. unfold query_join_outcome_operation; split; intro Heval;
    inversion Heval; subst.
  + eapply EJoinBag_ConditionError with
      (left_rows := left_rows) (right_rows := right_rows).
    * eapply query_same_rows_as_bag_bag_transport; eassumption.
    * eapply query_same_rows_as_bag_bag_transport; eassumption.
    * eassumption.
  + eapply EJoinBag_ProjectionError with
      (left_rows := left_rows) (right_rows := right_rows) (matrix := matrix).
    * eapply query_same_rows_as_bag_bag_transport; eassumption.
    * eapply query_same_rows_as_bag_bag_transport; eassumption.
    * eassumption.
    * eassumption.
  + eapply EJoinBag_ConditionError with
      (left_rows := left_rows) (right_rows := right_rows).
    * eapply query_same_rows_as_bag_bag_transport.
      -- eassumption.
      -- now apply bag_eq_sym.
    * eapply query_same_rows_as_bag_bag_transport.
      -- eassumption.
      -- now apply bag_eq_sym.
    * eassumption.
  + eapply EJoinBag_ProjectionError with
      (left_rows := left_rows) (right_rows := right_rows) (matrix := matrix).
    * eapply query_same_rows_as_bag_bag_transport.
      -- eassumption.
      -- now apply bag_eq_sym.
    * eapply query_same_rows_as_bag_bag_transport.
      -- eassumption.
      -- now apply bag_eq_sym.
    * eassumption.
    * eassumption.
Qed.

Lemma eval_adapter_query_set_error_iff :
  forall schedule env operation left right error,
    eval_adapter_query schedule env (QExpr_Set operation left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
Proof.
intros schedule env operation left right error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hleft | [left_rows [Hleft Hright]]].
  + now apply EQuery_SetLeftError.
  + eapply EQuery_SetRightError; eassumption.
Qed.

Lemma eval_adapter_query_natural_join_error_iff :
  forall schedule env left right error,
    eval_adapter_query schedule env (QExpr_NaturalJoin left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
Proof.
intros schedule env left right error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hleft | [left_rows [Hleft Hright]]].
  + now apply EQuery_NaturalJoinLeftError.
  + eapply EQuery_NaturalJoinRightError; eassumption.
Qed.

Lemma eval_adapter_query_cross_join_error_iff :
  forall schedule env left right error,
    eval_adapter_query schedule env (QExpr_CrossJoin left right)
      (SqlError error) <->
    eval_adapter_query schedule env left (SqlError error) \/
    exists left_rows,
      eval_adapter_query schedule env left (SqlSuccess left_rows) /\
      eval_adapter_query schedule env right (SqlError error).
Proof.
intros schedule env left right error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hleft | [left_rows [Hleft Hright]]].
  + now apply EQuery_CrossJoinLeftError.
  + eapply EQuery_CrossJoinRightError; eassumption.
Qed.

Theorem query_set_scheduled_bag_outcomes_characterization :
  forall schedule env operation left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_Set operation left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          (query_set_outcome_operation operation left right))
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
Proof.
intros schedule env operation left right Hright.
eapply query_scheduled_binary_parent_bag_outcomes_characterization.
- intro output; split; intro Heval.
  + apply eval_query_expr_set_success_iff in Heval.
    destruct Heval as [left_rows [right_rows [Hleft [Hright' Houtput]]]].
    exists left_rows; exists right_rows.
    exists (query_set_bag_function operation left right
      (rows_bag T left_rows) (rows_bag T right_rows)).
    repeat split; try assumption.
    unfold query_set_outcome_operation,
      query_success_only_binary_bag_operation, query_set_bag_relation,
      binary_bag_graph; apply bag_eq_refl.
  + destruct Heval as
      [left_rows [right_rows [output_bag
        [Hleft [Hright' [Hoperation Houtput]]]]]].
    apply eval_query_expr_set_success_iff.
    exists left_rows; exists right_rows; repeat split; try assumption.
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput |].
    unfold query_set_outcome_operation,
      query_success_only_binary_bag_operation, query_set_bag_relation,
      binary_bag_graph in Hoperation.
    now apply bag_eq_sym.
- intro error; split; intro Heval.
  + apply eval_adapter_query_set_error_iff in Heval.
    destruct Heval as [Hleft | [left_rows [Hleft Hright']]].
    * now left.
    * right; exists left_rows; split; [exact Hleft | now left].
  + apply eval_adapter_query_set_error_iff.
    destruct Heval as
      [Hleft | [left_rows [Hleft [Hright' |
        [right_rows [Hright' Hoperation]]]]]].
    * now left.
    * right; now exists left_rows.
    * unfold query_set_outcome_operation,
        query_success_only_binary_bag_operation in Hoperation.
      contradiction.
- apply query_success_only_binary_bag_operation_extensional.
  apply query_set_bag_relation_extensional.
- exact Hright.
Qed.

Theorem query_natural_join_scheduled_bag_outcomes_characterization :
  forall schedule env left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_NaturalJoin left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          query_natural_join_outcome_operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
Proof.
intros schedule env left right Hright.
eapply query_scheduled_binary_parent_bag_outcomes_characterization.
- intro output; split; intro Heval.
  + apply eval_query_expr_natural_join_success_iff in Heval.
    destruct Heval as [left_rows [right_rows [Hleft [Hright' Houtput]]]].
    exists left_rows; exists right_rows.
    exists (query_natural_join_bag value_is_null
      (rows_bag T left_rows) (rows_bag T right_rows)).
    repeat split; try assumption.
    unfold query_natural_join_outcome_operation,
      query_success_only_binary_bag_operation,
      query_natural_join_bag_relation, binary_bag_graph.
    apply bag_eq_refl.
  + destruct Heval as
      [left_rows [right_rows [output_bag
        [Hleft [Hright' [Hoperation Houtput]]]]]].
    apply eval_query_expr_natural_join_success_iff.
    exists left_rows; exists right_rows; repeat split; try assumption.
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput |].
    unfold query_natural_join_outcome_operation,
      query_success_only_binary_bag_operation,
      query_natural_join_bag_relation, binary_bag_graph in Hoperation.
    now apply bag_eq_sym.
- intro error; split; intro Heval.
  + apply eval_adapter_query_natural_join_error_iff in Heval.
    destruct Heval as [Hleft | [left_rows [Hleft Hright']]].
    * now left.
    * right; exists left_rows; split; [exact Hleft | now left].
  + apply eval_adapter_query_natural_join_error_iff.
    destruct Heval as
      [Hleft | [left_rows [Hleft [Hright' |
        [right_rows [Hright' Hoperation]]]]]].
    * now left.
    * right; now exists left_rows.
    * unfold query_natural_join_outcome_operation,
        query_success_only_binary_bag_operation in Hoperation.
      contradiction.
- apply query_success_only_binary_bag_operation_extensional.
  apply query_natural_join_bag_relation_extensional.
- exact Hright.
Qed.

Theorem query_cross_join_scheduled_bag_outcomes_characterization :
  forall schedule env left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env (QExpr_CrossJoin left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          query_cross_join_outcome_operation)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
Proof.
intros schedule env left right Hright.
eapply query_scheduled_binary_parent_bag_outcomes_characterization.
- intro output; split; intro Heval.
  + apply eval_query_expr_cross_join_success_iff in Heval.
    destruct Heval as [left_rows [right_rows [Hleft [Hright' Houtput]]]].
    exists left_rows; exists right_rows.
    exists (query_cross_join_bag
      (rows_bag T left_rows) (rows_bag T right_rows)).
    repeat split; try assumption.
    unfold query_cross_join_outcome_operation,
      query_success_only_binary_bag_operation,
      query_cross_join_bag_relation, binary_bag_graph.
    apply bag_eq_refl.
  + destruct Heval as
      [left_rows [right_rows [output_bag
        [Hleft [Hright' [Hoperation Houtput]]]]]].
    apply eval_query_expr_cross_join_success_iff.
    exists left_rows; exists right_rows; repeat split; try assumption.
    eapply query_same_rows_as_bag_bag_transport; [exact Houtput |].
    unfold query_cross_join_outcome_operation,
      query_success_only_binary_bag_operation,
      query_cross_join_bag_relation, binary_bag_graph in Hoperation.
    now apply bag_eq_sym.
- intro error; split; intro Heval.
  + apply eval_adapter_query_cross_join_error_iff in Heval.
    destruct Heval as [Hleft | [left_rows [Hleft Hright']]].
    * now left.
    * right; exists left_rows; split; [exact Hleft | now left].
  + apply eval_adapter_query_cross_join_error_iff.
    destruct Heval as
      [Hleft | [left_rows [Hleft [Hright' |
        [right_rows [Hright' Hoperation]]]]]].
    * now left.
    * right; now exists left_rows.
    * unfold query_cross_join_outcome_operation,
        query_success_only_binary_bag_operation in Hoperation.
      contradiction.
- apply query_success_only_binary_bag_operation_extensional.
  apply query_cross_join_bag_relation_extensional.
- exact Hright.
Qed.

Theorem query_join_scheduled_bag_outcomes_characterization :
  forall schedule env kind predicate matched_select left_select right_select
         left right,
    possible_bag_outcome_relation_inhabited
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        schedule env right) ->
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (lift_possible_bag_outcome_binary
        (query_eager_left_binary_outcome_relation
          (query_join_outcome_operation schedule env kind predicate
            matched_select left_select right_select))
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          schedule env right)).
Proof.
intros schedule env kind predicate matched_select left_select right_select
  left right Hright.
eapply query_scheduled_binary_parent_bag_outcomes_characterization.
- apply eval_query_expr_join_success_iff.
- apply eval_query_expr_join_error_iff.
- apply query_join_outcome_operation_extensional.
- exact Hright.
Qed.

(** Fixed matched-schedule constructor laws. *)
Theorem query_set_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env operation
         left_first left_second right_first right_second,
    query_expr_sort left_first =S= query_expr_sort right_first ->
    query_expr_sort left_second =S= query_expr_sort right_second ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Set operation left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Set operation right_first right_second)).
Proof.
intros left_schedule right_schedule env operation
  left_first left_second right_first right_second
  Hfirst_sort Hsecond_sort Hfirst Hsecond.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_set_scheduled_bag_outcomes_characterization.
  exact (proj1 Hsecond).
- apply query_set_scheduled_bag_outcomes_characterization.
  exact (proj1 (proj2 Hsecond)).
- apply lift_possible_bag_outcome_binary_cross_congr.
  + apply query_eager_left_binary_outcome_relation_cross_compatible.
    now apply query_set_outcome_operations_compatible.
  + exact Hfirst.
  + exact Hsecond.
Qed.

Theorem query_natural_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
         left_first left_second right_first right_second,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_NaturalJoin left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_NaturalJoin right_first right_second)).
Proof.
intros left_schedule right_schedule env
  left_first left_second right_first right_second Hfirst Hsecond.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_natural_join_scheduled_bag_outcomes_characterization.
  exact (proj1 Hsecond).
- apply query_natural_join_scheduled_bag_outcomes_characterization.
  exact (proj1 (proj2 Hsecond)).
- apply lift_possible_bag_outcome_binary_cross_congr.
  + apply query_eager_left_binary_outcome_relation_cross_compatible.
    apply query_natural_join_outcome_operations_compatible.
  + exact Hfirst.
  + exact Hsecond.
Qed.

Theorem query_cross_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
         left_first left_second right_first right_second,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_CrossJoin left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_CrossJoin right_first right_second)).
Proof.
intros left_schedule right_schedule env
  left_first left_second right_first right_second Hfirst Hsecond.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_cross_join_scheduled_bag_outcomes_characterization.
  exact (proj1 Hsecond).
- apply query_cross_join_scheduled_bag_outcomes_characterization.
  exact (proj1 (proj2 Hsecond)).
- apply lift_possible_bag_outcome_binary_cross_congr.
  + apply query_eager_left_binary_outcome_relation_cross_compatible.
    apply query_cross_join_outcome_operations_compatible.
  + exact Hfirst.
  + exact Hsecond.
Qed.

Theorem query_join_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env kind predicate
         matched_select left_select right_select
         left_first left_second right_first right_second,
    query_binary_bag_outcome_operations_compatible
      (query_join_outcome_operation left_schedule env kind predicate
        matched_select left_select right_select)
      (query_join_outcome_operation right_schedule env kind predicate
        matched_select left_select right_select) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_first)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_first) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_second)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_second) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          left_first left_second))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Join kind predicate matched_select left_select right_select
          right_first right_second)).
Proof.
intros left_schedule right_schedule env kind predicate
  matched_select left_select right_select
  left_first left_second right_first right_second
  Hoperation Hfirst Hsecond.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_join_scheduled_bag_outcomes_characterization.
  exact (proj1 Hsecond).
- apply query_join_scheduled_bag_outcomes_characterization.
  exact (proj1 (proj2 Hsecond)).
- apply lift_possible_bag_outcome_binary_cross_congr.
  + apply query_eager_left_binary_outcome_relation_cross_compatible.
    exact Hoperation.
  + exact Hfirst.
  + exact Hsecond.
Qed.

(** Constructor adapters consume one joint schedule witness and return a
    schedule-transport contract, so their results compose through further
    nested wrappers.  The possible-bag/outcome theorems below are bridge
    corollaries. *)
Theorem query_expr_set_possible_bag_schedule_transport :
  forall env operation left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left_first left_second)
      (QExpr_Set operation right_first right_second).
Proof.
intros env operation left_first left_second right_first right_second Hjoint.
pose proof (proj1 Hjoint) as Hfirst_outputs.
pose proof (proj1 (proj2 Hjoint)) as Hsecond_outputs.
eapply query_expr_possible_bag_binary_wrapper_schedule_transport.
- exact Hjoint.
- simpl; exact Hfirst_outputs.
- intros left_schedule right_schedule Hfirst Hsecond.
  eapply query_set_scheduled_bag_outcomes_congr.
  + now apply query_expr_outputs_eq_sort_eq.
  + now apply query_expr_outputs_eq_sort_eq.
  + exact Hfirst.
  + exact Hsecond.
Qed.

Corollary query_expr_set_possible_bag_outcome_equiv :
  forall env operation left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Set operation left_first left_second)
      (QExpr_Set operation right_first right_second).
Proof.
intros env operation left_first left_second right_first right_second Hjoint.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
now apply query_expr_set_possible_bag_schedule_transport.
Qed.

Theorem query_expr_natural_join_possible_bag_schedule_transport :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_NaturalJoin left_first left_second)
      (QExpr_NaturalJoin right_first right_second).
Proof.
intros env left_first left_second right_first right_second Hjoint.
pose proof (proj1 Hjoint) as Hfirst_outputs.
pose proof (proj1 (proj2 Hjoint)) as Hsecond_outputs.
eapply query_expr_possible_bag_binary_wrapper_schedule_transport.
- exact Hjoint.
- change
    (query_natural_join_outputs T
      (query_expr_outputs left_first) (query_expr_outputs left_second) =
     query_natural_join_outputs T
      (query_expr_outputs right_first) (query_expr_outputs right_second)).
  now rewrite Hfirst_outputs, Hsecond_outputs.
- intros left_schedule right_schedule Hfirst Hsecond.
  now apply query_natural_join_scheduled_bag_outcomes_congr.
Qed.

Corollary query_expr_natural_join_possible_bag_outcome_equiv :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_NaturalJoin left_first left_second)
      (QExpr_NaturalJoin right_first right_second).
Proof.
intros env left_first left_second right_first right_second Hjoint.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
now apply query_expr_natural_join_possible_bag_schedule_transport.
Qed.

Theorem query_expr_cross_join_possible_bag_schedule_transport :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left_first left_second)
      (QExpr_CrossJoin right_first right_second).
Proof.
intros env left_first left_second right_first right_second Hjoint.
pose proof (proj1 Hjoint) as Hfirst_outputs.
pose proof (proj1 (proj2 Hjoint)) as Hsecond_outputs.
eapply query_expr_possible_bag_binary_wrapper_schedule_transport.
- exact Hjoint.
- simpl; now rewrite Hfirst_outputs, Hsecond_outputs.
- intros left_schedule right_schedule Hfirst Hsecond.
  now apply query_cross_join_scheduled_bag_outcomes_congr.
Qed.

Corollary query_expr_cross_join_possible_bag_outcome_equiv :
  forall env left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_CrossJoin left_first left_second)
      (QExpr_CrossJoin right_first right_second).
Proof.
intros env left_first left_second right_first right_second Hjoint.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
now apply query_expr_cross_join_possible_bag_schedule_transport.
Qed.

(** JOIN's predicate and projection lists are schedule-sensitive and may
    expose their own errors after both children succeed.  The explicit local
    premise below compares exactly the two authoritative
    [eval_join_bag_outcome] relations selected by the one joint schedule pair;
    it is not an assumption about either full parent query. *)
Theorem query_expr_join_possible_bag_schedule_transport :
  forall env kind predicate matched_select left_select right_select
         left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_first)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_second)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_second) ->
      query_binary_bag_outcome_operations_compatible
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env kind predicate
          matched_select left_select right_select)
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env kind predicate
          matched_select left_select right_select)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_first left_second)
      (QExpr_Join kind predicate matched_select left_select right_select
        right_first right_second).
Proof.
intros env kind predicate matched_select left_select right_select
  left_first left_second right_first right_second Hjoint Hoperation.
eapply query_expr_possible_bag_binary_wrapper_schedule_transport.
- exact Hjoint.
- simpl; destruct kind; reflexivity.
- intros left_schedule right_schedule Hfirst Hsecond.
  eapply query_join_scheduled_bag_outcomes_congr.
  + now apply Hoperation.
  + exact Hfirst.
  + exact Hsecond.
Qed.

Corollary query_expr_join_possible_bag_outcome_equiv :
  forall env kind predicate matched_select left_select right_select
         left_first left_second right_first right_second,
    @query_expr_possible_bag_joint_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left_first left_second right_first right_second ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_first)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_first) ->
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_second)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_second) ->
      query_binary_bag_outcome_operations_compatible
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env kind predicate
          matched_select left_select right_select)
        (@eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env kind predicate
          matched_select left_select right_select)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Join kind predicate matched_select left_select right_select
        left_first left_second)
      (QExpr_Join kind predicate matched_select left_select right_select
        right_first right_second).
Proof.
intros env kind predicate matched_select left_select right_select
  left_first left_second right_first right_second Hjoint Hoperation.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_join_possible_bag_schedule_transport; eassumption.
Qed.

End ScheduledBinaryConstructorAdapters.

(** Constructor-facing scheduled unary laws.  Unlike a premise that merely
    restates equivalence of two complete parent evaluators, the local contract
    below talks only about the authoritative row/bag operation reached after
    one actual successful child list has been selected. *)
Section ScheduledUnaryConstructorLaws.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition unary_tuple := tuple T.
Local Definition unary_value := value T.
Local Definition unary_setA := Fset.set (A T).
Local Definition unary_BTupleT := Fecol.CBag (CTuple T).
Local Definition unary_bagT := Febag.bag unary_BTupleT.

Hypothesis basesort : relname -> unary_setA.
Hypothesis instance : relname -> unary_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * unary_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * unary_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : unary_value -> bool.

Local Abbreviation eval_unary_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Definition query_rows_to_bag_outcome_relation : Type :=
  list unary_tuple -> sql_outcome unary_bagT -> Prop.

(** Eager unary bind over actual successful child lists.  Child errors pass
    through unchanged; local work is performed only after one concrete child
    success has been selected. *)
Definition query_actual_rows_bag_outcome_bind
    (child : sql_outcome (list unary_tuple) -> Prop)
    (local : query_rows_to_bag_outcome_relation) :
    sql_outcome unary_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        exists input_rows,
          child (SqlSuccess input_rows) /\
          local input_rows (SqlSuccess output_bag)
    | SqlError error =>
        child (SqlError error) \/
        exists input_rows,
          child (SqlSuccess input_rows) /\
          local input_rows (SqlError error)
    end.

(** The only admissible local premise.  It compares the actual local semantic
    relations on two reachable, bag-equal child lists.  Thus differing list
    orders, correlated environments, Boolean schedules, first errors, and
    multiplicities must all be justified here; no parent query occurs in the
    definition. *)
Definition scheduled_local_rows_to_bag_contract
    (left_child right_child : sql_outcome (list unary_tuple) -> Prop)
    (left_local right_local : query_rows_to_bag_outcome_relation) : Prop :=
  forall left_rows right_rows,
    left_child (SqlSuccess left_rows) ->
    right_child (SqlSuccess right_rows) ->
    bag_eq T (rows_bag T left_rows) (rows_bag T right_rows) ->
    outcome_relation_equiv (@bag_eq T)
      (left_local left_rows) (right_local right_rows).

Lemma outcome_alpha_success_match_left_rows :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) left_rows,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    left (SqlSuccess left_rows) ->
    exists right_rows,
      right (SqlSuccess right_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
Proof.
intros left right left_rows
  [_ [_ [Hforward _]]] Hleft.
assert (Hleft_bag :
  @outcome_alpha T left (SqlSuccess (rows_bag T left_rows))).
{
  simpl; exists left_rows; split; [exact Hleft | apply bag_eq_refl].
}
destruct (Hforward _ Hleft_bag)
  as [right_bag [[right_rows [Hright Hright_bag]] Hbags]].
exists right_rows; split; [exact Hright |].
eapply bag_eq_trans; [exact Hbags |].
now apply bag_eq_sym.
Qed.

Lemma outcome_alpha_success_match_right_rows :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) right_rows,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    right (SqlSuccess right_rows) ->
    exists left_rows,
      left (SqlSuccess left_rows) /\
      bag_eq T (rows_bag T left_rows) (rows_bag T right_rows).
Proof.
intros left right right_rows
  [_ [_ [_ [Hbackward _]]]] Hright.
assert (Hright_bag :
  @outcome_alpha T right (SqlSuccess (rows_bag T right_rows))).
{
  simpl; exists right_rows; split; [exact Hright | apply bag_eq_refl].
}
destruct (Hbackward _ Hright_bag)
  as [left_bag [[left_rows [Hleft Hleft_bag]] Hbags]].
exists left_rows; split; [exact Hleft |].
eapply bag_eq_trans; eassumption.
Qed.

Lemma outcome_alpha_error_iff :
  forall (left right : sql_outcome (list unary_tuple) -> Prop) error,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left) (@outcome_alpha T right) ->
    (left (SqlError error) <-> right (SqlError error)).
Proof.
intros left right error [_ [_ [_ [_ Herrors]]]].
exact (Herrors error).
Qed.

(** Congruence of the actual-row bind.  This is the reusable proof step that
    combines scheduled child bag/error equivalence with the helper-only local
    contract. *)
Theorem query_actual_rows_bag_outcome_bind_congr :
  forall left_child right_child left_local right_local,
    outcome_relation_equiv (@bag_eq T)
      (@outcome_alpha T left_child) (@outcome_alpha T right_child) ->
    scheduled_local_rows_to_bag_contract
      left_child right_child left_local right_local ->
    outcome_relation_equiv (@bag_eq T)
      (query_actual_rows_bag_outcome_bind left_child left_local)
      (query_actual_rows_bag_outcome_bind right_child right_local).
Proof.
intros left_child right_child left_local right_local Hchildren Hlocal.
apply outcome_relation_equiv_intro.
- destruct (proj1 Hchildren) as [[left_bag | error] Hchild].
  + destruct Hchild as [left_rows [Hleft _]].
    destruct (outcome_alpha_success_match_left_rows
      (left := left_child) (right := right_child)
      left_rows Hchildren Hleft)
      as [right_rows [Hright Hbags]].
    pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
    destruct (proj1 Houtputs) as [[output_bag | local_error] Houtput].
    * exists (SqlSuccess output_bag); exists left_rows; now split.
    * exists (SqlError local_error); right; exists left_rows; now split.
  + exists (SqlError error); left; exact Hchild.
- destruct (proj1 (proj2 Hchildren)) as [[right_bag | error] Hchild].
  + destruct Hchild as [right_rows [Hright _]].
    destruct (outcome_alpha_success_match_right_rows
      (left := left_child) (right := right_child)
      right_rows Hchildren Hright)
      as [left_rows [Hleft Hbags]].
    pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
    destruct (proj1 (proj2 Houtputs))
      as [[output_bag | local_error] Houtput].
    * exists (SqlSuccess output_bag); exists right_rows; now split.
    * exists (SqlError local_error); right; exists right_rows; now split.
  + exists (SqlError error); left; exact Hchild.
- intros output_bag [left_rows [Hleft Houtput]].
  destruct (outcome_alpha_success_match_left_rows
    (left := left_child) (right := right_child)
    left_rows Hchildren Hleft)
    as [right_rows [Hright Hbags]].
  pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
  destruct (proj1 (proj2 (proj2 Houtputs)) output_bag Houtput)
    as [right_bag [Hright_output Houtput_bags]].
  exists right_bag; split.
  + exists right_rows; now split.
  + exact Houtput_bags.
- intros output_bag [right_rows [Hright Houtput]].
  destruct (outcome_alpha_success_match_right_rows
    (left := left_child) (right := right_child)
    right_rows Hchildren Hright)
    as [left_rows [Hleft Hbags]].
  pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
  destruct (proj1 (proj2 (proj2 (proj2 Houtputs))) output_bag Houtput)
    as [left_bag [Hleft_output Houtput_bags]].
  exists left_bag; split.
  + exists left_rows; now split.
  + exact Houtput_bags.
- intro error; split.
  + intros [Hchild | [left_rows [Hleft Houtput]]].
    * left; now apply (proj1 (outcome_alpha_error_iff
        (left := left_child) (right := right_child) error Hchildren)).
    * destruct (outcome_alpha_success_match_left_rows
        (left := left_child) (right := right_child)
        left_rows Hchildren Hleft)
        as [right_rows [Hright Hbags]].
      pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
      right; exists right_rows; split; [exact Hright |].
      now apply (proj1 (proj2 (proj2 (proj2 (proj2 Houtputs))) error)).
  + intros [Hchild | [right_rows [Hright Houtput]]].
    * left; now apply (proj2 (outcome_alpha_error_iff
        (left := left_child) (right := right_child) error Hchildren)).
    * destruct (outcome_alpha_success_match_right_rows
        (left := left_child) (right := right_child)
        right_rows Hchildren Hright)
        as [left_rows [Hleft Hbags]].
      pose proof (Hlocal left_rows right_rows Hleft Hright Hbags) as Houtputs.
      right; exists left_rows; split; [exact Hleft |].
      now apply (proj2 (proj2 (proj2 (proj2 (proj2 Houtputs))) error)).
Qed.

End ScheduledUnaryConstructorLaws.

Section ScheduledUnaryConstructorCharacterizations.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition unary_sem_tuple := tuple T.
Local Definition unary_sem_value := value T.
Local Definition unary_sem_setA := Fset.set (A T).
Local Definition unary_sem_BTupleT := Fecol.CBag (CTuple T).
Local Definition unary_sem_bagT := Febag.bag unary_sem_BTupleT.

Hypothesis basesort : relname -> unary_sem_setA.
Hypothesis instance : relname -> unary_sem_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * unary_sem_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * unary_sem_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : unary_sem_value -> bool.

Local Abbreviation eval_unary_sem_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

(** Row-preserving helpers retain their exact list evaluator.  Only the
    explicit [outcome_alpha] at this interface forgets output order. *)
Definition query_project_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (select_list : @query_select_list T relname)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (@eval_project_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env select_list rows).

Definition query_row_map_rows_bag_outcomes
    (row_map : unary_sem_tuple -> sql_outcome unary_sem_tuple)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (fun outcome => @row_map_rows_outcome T row_map rows = outcome).

Definition query_filter_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T)
    (predicate : scalar_expr T relname ScalarResultBoolean)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  @outcome_alpha T
    (@eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null schedule
      env predicate rows).

(** Reset helpers expose their existing quotient-saturated success relation
    and their raw exact error relation.  In particular, no deterministic bag
    function is substituted for GROUP's representative-sensitive aggregate
    semantics. *)
Definition query_group_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T) (select_list : @query_select_list T relname)
    (group_keys : list (scalar_expr T relname ScalarResultValue))
    (having : scalar_expr T relname ScalarResultBoolean)
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_group_bag_relation T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having (rows_bag T rows) output_bag
    | SqlError error =>
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having (rows_bag T rows)
          (SqlError error)
    end.

Definition query_grouping_sets_rows_bag_outcomes
    (schedule : boolean_site -> boolean_evaluation_order)
    (env : Env.env T)
    (grouping_sets : list (@query_grouping_set T relname))
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_grouping_sets_bag_relation T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env grouping_sets (rows_bag T rows) output_bag
    | SqlError error =>
        @eval_grouping_sets_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env grouping_sets (rows_bag T rows) (SqlError error)
    end.

(** Window success quantifies all legal peer orders through the existing
    relation.  The error branch states that same ordering choice and the raw
    [query_window_rows_outcome] failure explicitly. *)
Definition query_window_rows_bag_outcomes
    (env : Env.env T)
    (partition_keys order_keys : list (SqlOrder.sort_key T))
    (items : list (query_window_item T))
    (rows : list unary_sem_tuple) : sql_outcome unary_sem_bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess output_bag =>
        @query_window_bag_relation T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys order_keys items (rows_bag T rows) output_bag
    | SqlError error =>
        exists ordered_rows,
          @order_by_rows T value_is_null (partition_keys ++ order_keys)
            (query_rank_bag_rows (rows_bag T rows)) ordered_rows /\
          @query_window_rows_outcome T symbol_runtime_error
            aggregate_runtime_error value_is_null env partition_keys items
            None 0 nil ordered_rows = Some (SqlError error)
    end.

(** Missing constructor inversions used only to establish the exact
    characterizations below. *)
Lemma eval_unary_project_error_iff :
  forall schedule env select_list input error,
    eval_unary_sem_query schedule env (QExpr_Project select_list input)
      (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @eval_project_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env select_list input_rows (SqlError error).
Proof.
intros schedule env select_list input error; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [Hchild | [input_rows [Hchild Hlocal]]].
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows; eassumption.
Qed.

Lemma eval_unary_row_map_error_iff :
  forall schedule env outputs row_map input error,
    eval_unary_sem_query schedule env
      (QExpr_RowMap outputs row_map input) (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @row_map_rows_outcome T row_map input_rows = SqlError error.
Proof.
intros schedule env outputs row_map input error; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [Hchild | [input_rows [Hchild Hlocal]]].
  + now apply EQuery_RowMapChildError.
  + rewrite <- Hlocal; now apply EQuery_RowMapRows.
Qed.

Lemma eval_unary_filter_error_iff :
  forall schedule env predicate input error,
    eval_unary_sem_query schedule env (QExpr_Filter predicate input)
      (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env predicate input_rows (SqlError error).
Proof.
intros schedule env predicate input error; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [Hchild | [input_rows [Hchild Hlocal]]].
  + now apply EQuery_FilterChildError.
  + eapply EQuery_FilterRows; eassumption.
Qed.

Lemma eval_unary_window_error_iff :
  forall schedule env partition_keys order_keys items input error,
    eval_unary_sem_query schedule env
      (QExpr_Window partition_keys order_keys items input) (SqlError error) <->
    eval_unary_sem_query schedule env input (SqlError error) \/
    exists input_rows ordered_rows,
      eval_unary_sem_query schedule env input (SqlSuccess input_rows) /\
      @order_by_rows T value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows (rows_bag T input_rows)) ordered_rows /\
      @query_window_rows_outcome T symbol_runtime_error
        aggregate_runtime_error value_is_null env partition_keys items
        None 0 nil ordered_rows = Some (SqlError error).
Proof.
intros schedule env partition_keys order_keys items input error;
  split; intro Heval.
- inversion Heval; subst; eauto 8.
- destruct Heval as
    [Hchild | [input_rows [ordered_rows [Hchild [Horder Hlocal]]]]].
  + now apply EQuery_WindowChildError.
  + eapply EQuery_WindowRowsError with
      (input_rows := input_rows) (ordered_rows := ordered_rows);
      eassumption.
Qed.

(** Exact scheduled abstractions for the three order-preserving row
    operators.  Their concrete output lists remain inside the helper's
    [outcome_alpha] witness; no arbitrary representative is fed back to the
    ordered evaluator. *)
Theorem query_project_scheduled_bag_outcomes_characterization :
  forall schedule env select_list input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Project select_list input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_project_rows_bag_outcomes schedule env select_list)).
Proof.
intros schedule env select_list input [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_project_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_project_success_iff in Hparent.
    destruct Hparent as [input_rows [Hchild Hlocal]].
    exists input_rows; split; [exact Hchild |].
    exists output; now split.
  + intros [input_rows [Hchild [output [Hlocal Hobserved]]]].
    exists output; split; [|exact Hobserved].
    apply eval_query_expr_project_success_iff.
    now exists input_rows.
- apply eval_unary_project_error_iff.
Qed.

Theorem query_row_map_scheduled_bag_outcomes_characterization :
  forall schedule env outputs row_map input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_RowMap outputs row_map input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_row_map_rows_bag_outcomes row_map)).
Proof.
intros schedule env outputs row_map input [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_row_map_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_row_map_success_iff in Hparent.
    destruct Hparent as [input_rows [Hchild Hlocal]].
    exists input_rows; split; [exact Hchild |].
    exists output; now split.
  + intros [input_rows [Hchild [output [Hlocal Hobserved]]]].
    exists output; split; [|exact Hobserved].
    apply eval_query_expr_row_map_success_iff.
    now exists input_rows.
- apply eval_unary_row_map_error_iff.
Qed.

Theorem query_filter_scheduled_bag_outcomes_characterization :
  forall schedule env predicate input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Filter predicate input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_unary_sem_query schedule env input)
        (query_filter_rows_bag_outcomes schedule env predicate)).
Proof.
intros schedule env predicate input [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_filter_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_filter_success_iff in Hparent.
    destruct Hparent as [input_rows [Hchild Hlocal]].
    exists input_rows; split; [exact Hchild |].
    exists output; now split.
  + intros [input_rows [Hchild [output [Hlocal Hobserved]]]].
    exists output; split; [|exact Hobserved].
    apply eval_query_expr_filter_success_iff.
    now exists input_rows.
- apply eval_unary_filter_error_iff.
Qed.

End ScheduledUnaryConstructorCharacterizations.

Section ScheduledUnaryResetCharacterizations.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition reset_value := value T.
Local Definition reset_setA := Fset.set (A T).
Local Definition reset_BTupleT := Fecol.CBag (CTuple T).
Local Definition reset_bagT := Febag.bag reset_BTupleT.

Hypothesis basesort : relname -> reset_setA.
Hypothesis instance : relname -> reset_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * reset_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * reset_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : reset_value -> bool.

Local Abbreviation eval_reset_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Theorem query_group_scheduled_bag_outcomes_characterization :
  forall schedule env select_list group_keys having input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Group select_list group_keys having input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null schedule
          env select_list group_keys having)).
Proof.
intros schedule env select_list group_keys having input
  [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_group_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_group_success_iff in Hparent.
    destruct Hparent as
      [input_rows [output_bag [Hchild [Hlocal Houtput]]]].
    apply query_same_rows_as_bag_iff_bag_eq in Houtput.
    assert (Hbags : bag_eq T output_bag observed_bag).
    { exact (bag_eq_trans (bag_eq_sym Houtput) Hobserved). }
    pose proof
      (@SqlQueryFacts.query_group_bag_relation_extensional
        T relname basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null schedule env
        select_list group_keys having
        (rows_bag T input_rows) (rows_bag T input_rows)
        output_bag observed_bag
        (bag_eq_refl T _) Hbags) as Htransport.
    exists input_rows; split; [exact Hchild |].
    now apply (proj1 Htransport).
  + intros [input_rows [Hchild Hlocal]].
    exists (Febag.elements reset_BTupleT observed_bag); split.
    * apply eval_query_expr_group_success_iff.
      exists input_rows, observed_bag; repeat split; try assumption.
      apply query_elements_same_rows_as_bag.
    * apply rows_bag_elements.
- apply eval_query_expr_group_error_iff.
Qed.

Theorem query_grouping_sets_scheduled_bag_outcomes_characterization :
  forall schedule env grouping_sets input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_GroupingSets grouping_sets input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null schedule env grouping_sets)).
Proof.
intros schedule env grouping_sets input [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_grouping_sets_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_grouping_sets_success_iff in Hparent.
    destruct Hparent as
      [input_rows [output_bag [Hchild [Hlocal Houtput]]]].
    apply query_same_rows_as_bag_iff_bag_eq in Houtput.
    assert (Hbags : bag_eq T output_bag observed_bag).
    { exact (bag_eq_trans (bag_eq_sym Houtput) Hobserved). }
    pose proof
      (@SqlQueryFacts.query_grouping_sets_bag_relation_extensional
        T relname basesort instance unknown symbol_runtime_error
        aggregate_runtime_error value_is_null schedule env grouping_sets
        (rows_bag T input_rows) (rows_bag T input_rows)
        output_bag observed_bag
        (bag_eq_refl T _) Hbags) as Htransport.
    exists input_rows; split; [exact Hchild |].
    now apply (proj1 Htransport).
  + intros [input_rows [Hchild Hlocal]].
    exists (Febag.elements reset_BTupleT observed_bag); split.
    * apply eval_query_expr_grouping_sets_success_iff.
      exists input_rows, observed_bag; repeat split; try assumption.
      apply query_elements_same_rows_as_bag.
    * apply rows_bag_elements.
- apply eval_query_expr_grouping_sets_error_iff.
Qed.

Theorem query_window_scheduled_bag_outcomes_characterization :
  forall schedule env partition_keys order_keys items input,
    rel_equiv
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null schedule
        env (QExpr_Window partition_keys order_keys items input))
      (@query_actual_rows_bag_outcome_bind T
        (eval_reset_query schedule env input)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys order_keys items)).
Proof.
intros schedule env partition_keys order_keys items input
  [observed_bag | error];
  unfold query_scheduled_bag_outcomes,
    query_actual_rows_bag_outcome_bind,
    query_window_rows_bag_outcomes, outcome_alpha, alpha; simpl.
- split.
  + intros [output [Hparent Hobserved]].
    apply eval_query_expr_window_success_iff in Hparent.
    destruct Hparent as
      [input_rows [output_bag [Hchild [Hlocal Houtput]]]].
    apply query_same_rows_as_bag_iff_bag_eq in Houtput.
    assert (Hbags : bag_eq T output_bag observed_bag).
    { exact (bag_eq_trans (bag_eq_sym Houtput) Hobserved). }
    pose proof
      (@SqlQueryFacts.query_window_bag_relation_extensional
        T symbol_runtime_error aggregate_runtime_error value_is_null env
        partition_keys order_keys items
        (rows_bag T input_rows) (rows_bag T input_rows)
        output_bag observed_bag
        (bag_eq_refl T _) Hbags) as Htransport.
    exists input_rows; split; [exact Hchild |].
    now apply (proj1 Htransport).
  + intros [input_rows [Hchild Hlocal]].
    exists (Febag.elements reset_BTupleT observed_bag); split.
    * apply eval_query_expr_window_success_iff.
      exists input_rows, observed_bag; repeat split; try assumption.
      apply query_elements_same_rows_as_bag.
    * apply rows_bag_elements.
- split; intro Herror.
  + apply eval_unary_window_error_iff in Herror.
    destruct Herror as
      [Hchild |
       [input_rows [ordered_rows [Hchild [Horder Hlocal]]]]].
    * now left.
    * right; exists input_rows; split; [exact Hchild |].
      exists ordered_rows; now split.
  + apply eval_unary_window_error_iff.
    destruct Herror as
      [Hchild | [input_rows [Hchild [ordered_rows [Horder Hlocal]]]]].
    * now left.
    * right; exists input_rows, ordered_rows; split; [exact Hchild |].
      now split.
Qed.

End ScheduledUnaryResetCharacterizations.

Section ScheduledUnaryConstructorCongruence.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition unary_congr_value := value T.
Local Definition unary_congr_setA := Fset.set (A T).
Local Definition unary_congr_BTupleT := Fecol.CBag (CTuple T).
Local Definition unary_congr_bagT := Febag.bag unary_congr_BTupleT.

Hypothesis basesort : relname -> unary_congr_setA.
Hypothesis instance : relname -> unary_congr_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * unary_congr_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * unary_congr_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : unary_congr_value -> bool.

Local Abbreviation eval_congr_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Theorem query_project_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env left_select right_select left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_project_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_select)
      (@query_project_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_select) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Project left_select left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Project right_select right)).
Proof.
intros left_schedule right_schedule env left_select right_select left right
  Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_project_scheduled_bag_outcomes_characterization.
- apply query_project_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

Theorem query_row_map_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_outputs right_outputs left_map right_map left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_row_map_rows_bag_outcomes T left_map)
      (@query_row_map_rows_bag_outcomes T right_map) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_RowMap left_outputs left_map left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_RowMap right_outputs right_map right)).
Proof.
intros left_schedule right_schedule env
  left_outputs right_outputs left_map right_map left right Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_row_map_scheduled_bag_outcomes_characterization.
- apply query_row_map_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

Theorem query_filter_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_predicate right_predicate left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_filter_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_predicate)
      (@query_filter_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_predicate) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_Filter left_predicate left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_Filter right_predicate right)).
Proof.
intros left_schedule right_schedule env
  left_predicate right_predicate left right Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_filter_scheduled_bag_outcomes_characterization.
- apply query_filter_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

Theorem query_group_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_group_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left_select left_keys left_having)
      (@query_group_rows_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right_select right_keys right_having) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Group left_select left_keys left_having left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Group right_select right_keys right_having right)).
Proof.
intros left_schedule right_schedule env
  left_select left_keys left_having right_select right_keys right_having
  left right Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_group_scheduled_bag_outcomes_characterization.
- apply query_group_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

Theorem query_grouping_sets_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env left_sets right_sets left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_grouping_sets_rows_bag_outcomes T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null left_schedule env left_sets)
      (@query_grouping_sets_rows_bag_outcomes T relname
        basesort instance unknown symbol_runtime_error aggregate_runtime_error
        value_is_null right_schedule env right_sets) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env (QExpr_GroupingSets left_sets left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env (QExpr_GroupingSets right_sets right)).
Proof.
intros left_schedule right_schedule env left_sets right_sets left right
  Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_grouping_sets_scheduled_bag_outcomes_characterization.
- apply query_grouping_sets_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

Theorem query_window_scheduled_bag_outcomes_congr :
  forall left_schedule right_schedule env
      left_partition left_order left_items
      right_partition right_order right_items left right,
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env left)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env right) ->
    scheduled_local_rows_to_bag_contract
      (eval_congr_query left_schedule env left)
      (eval_congr_query right_schedule env right)
      (@query_window_rows_bag_outcomes T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        left_partition left_order left_items)
      (@query_window_rows_bag_outcomes T symbol_runtime_error
        aggregate_runtime_error value_is_null env
        right_partition right_order right_items) ->
    outcome_relation_equiv (@bag_eq T)
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        left_schedule env
        (QExpr_Window left_partition left_order left_items left))
      (@query_scheduled_bag_outcomes T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        right_schedule env
        (QExpr_Window right_partition right_order right_items right)).
Proof.
intros left_schedule right_schedule env
  left_partition left_order left_items right_partition right_order right_items
  left right Hchildren Hlocal.
eapply outcome_relation_equiv_rel_equiv_transport.
- apply query_window_scheduled_bag_outcomes_characterization.
- apply query_window_scheduled_bag_outcomes_characterization.
- now apply query_actual_rows_bag_outcome_bind_congr.
Qed.

End ScheduledUnaryConstructorCongruence.

Section ScheduledUnaryConstructorAdapters.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition unary_adapter_value := value T.
Local Definition unary_adapter_setA := Fset.set (A T).
Local Definition unary_adapter_BTupleT := Fecol.CBag (CTuple T).
Local Definition unary_adapter_bagT := Febag.bag unary_adapter_BTupleT.

Hypothesis basesort : relname -> unary_adapter_setA.
Hypothesis instance : relname -> unary_adapter_bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * unary_adapter_value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * unary_adapter_value) ->
  option sql_runtime_error.
Hypothesis value_is_null : unary_adapter_value -> bool.

Local Abbreviation eval_adapter_unary_query schedule :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null schedule).

Theorem query_expr_project_possible_bag_schedule_transport :
  forall env left_select right_select left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_select)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_select)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select left) (QExpr_Project right_select right).
Proof.
intros env left_select right_select left right Hchildren Houtputs Hlocal.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; exact Houtputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_project_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_project_possible_bag_outcome_equiv :
  forall env left_select right_select left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_select)
        (@query_project_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_select)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Project left_select left) (QExpr_Project right_select right).
Proof.
intros env left_select right_select left right Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_project_possible_bag_schedule_transport; eassumption.
Qed.

Theorem query_expr_row_map_possible_bag_schedule_transport :
  forall env left_outputs right_outputs left_map right_map left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    left_outputs = right_outputs ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_row_map_rows_bag_outcomes T left_map)
        (@query_row_map_rows_bag_outcomes T right_map)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_RowMap left_outputs left_map left)
      (QExpr_RowMap right_outputs right_map right).
Proof.
intros env left_outputs right_outputs left_map right_map left right
  Hchildren Houtputs Hlocal.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; exact Houtputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_row_map_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_row_map_possible_bag_outcome_equiv :
  forall env left_outputs right_outputs left_map right_map left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    left_outputs = right_outputs ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_row_map_rows_bag_outcomes T left_map)
        (@query_row_map_rows_bag_outcomes T right_map)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_RowMap left_outputs left_map left)
      (QExpr_RowMap right_outputs right_map right).
Proof.
intros env left_outputs right_outputs left_map right_map left right
  Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_row_map_possible_bag_schedule_transport; eassumption.
Qed.

Theorem query_expr_filter_possible_bag_schedule_transport :
  forall env left_predicate right_predicate left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_predicate)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_predicate)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate left) (QExpr_Filter right_predicate right).
Proof.
intros env left_predicate right_predicate left right Hchildren Hlocal.
pose proof (proj1 Hchildren) as Houtputs.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; exact Houtputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_filter_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_filter_possible_bag_outcome_equiv :
  forall env left_predicate right_predicate left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_predicate)
        (@query_filter_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_predicate)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Filter left_predicate left) (QExpr_Filter right_predicate right).
Proof.
intros env left_predicate right_predicate left right Hchildren Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_filter_possible_bag_schedule_transport; eassumption.
Qed.

Theorem query_expr_group_possible_bag_schedule_transport :
  forall env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_select left_keys left_having)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_select right_keys right_having)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_keys left_having left)
      (QExpr_Group right_select right_keys right_having right).
Proof.
intros env left_select left_keys left_having
  right_select right_keys right_having left right
  Hchildren Houtputs Hlocal.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; exact Houtputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_group_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_group_possible_bag_outcome_equiv :
  forall env
      left_select left_keys left_having right_select right_keys right_having
      left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    scalar_select_outputs left_select = scalar_select_outputs right_select ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left_select left_keys left_having)
        (@query_group_rows_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right_select right_keys right_having)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Group left_select left_keys left_having left)
      (QExpr_Group right_select right_keys right_having right).
Proof.
intros env left_select left_keys left_having
  right_select right_keys right_having left right
  Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_group_possible_bag_schedule_transport; eassumption.
Qed.

Theorem query_expr_grouping_sets_possible_bag_schedule_transport :
  forall env left_sets right_sets left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_grouping_sets_outputs T relname left_sets =
      @query_grouping_sets_outputs T relname right_sets ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_sets)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_sets)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_GroupingSets left_sets left)
      (QExpr_GroupingSets right_sets right).
Proof.
intros env left_sets right_sets left right Hchildren Houtputs Hlocal.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; exact Houtputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_grouping_sets_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_grouping_sets_possible_bag_outcome_equiv :
  forall env left_sets right_sets left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    @query_grouping_sets_outputs T relname left_sets =
      @query_grouping_sets_outputs T relname right_sets ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          left_schedule env left_sets)
        (@query_grouping_sets_rows_bag_outcomes T relname
          basesort instance unknown symbol_runtime_error
          aggregate_runtime_error value_is_null
          right_schedule env right_sets)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_GroupingSets left_sets left)
      (QExpr_GroupingSets right_sets right).
Proof.
intros env left_sets right_sets left right Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_grouping_sets_possible_bag_schedule_transport; eassumption.
Qed.

Theorem query_expr_window_possible_bag_schedule_transport :
  forall env
      left_partition left_order left_items
      right_partition right_order right_items left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    map (@qwi_attribute T) left_items = map (@qwi_attribute T) right_items ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          left_partition left_order left_items)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          right_partition right_order right_items)) ->
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window left_partition left_order left_items left)
      (QExpr_Window right_partition right_order right_items right).
Proof.
intros env left_partition left_order left_items
  right_partition right_order right_items left right
  Hchildren Hitem_outputs Hlocal.
pose proof (proj1 Hchildren) as Hchild_outputs.
eapply query_expr_possible_bag_unary_wrapper_schedule_transport.
- exact Hchildren.
- simpl; now rewrite Hchild_outputs, Hitem_outputs.
- intros left_schedule right_schedule Hscheduled.
  eapply query_window_scheduled_bag_outcomes_congr.
  + exact Hscheduled.
  + now apply Hlocal.
Qed.

Corollary query_expr_window_possible_bag_outcome_equiv :
  forall env
      left_partition left_order left_items
      right_partition right_order right_items left right,
    @query_expr_possible_bag_schedule_transport T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env left right ->
    map (@qwi_attribute T) left_items = map (@qwi_attribute T) right_items ->
    (forall left_schedule right_schedule,
      outcome_relation_equiv (@bag_eq T)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          left_schedule env left)
        (@query_scheduled_bag_outcomes T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null
          right_schedule env right) ->
      scheduled_local_rows_to_bag_contract
        (eval_adapter_unary_query left_schedule env left)
        (eval_adapter_unary_query right_schedule env right)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          left_partition left_order left_items)
        (@query_window_rows_bag_outcomes T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          right_partition right_order right_items)) ->
    @query_expr_possible_bag_outcome_equiv T relname
      basesort instance unknown symbol_runtime_error aggregate_runtime_error
      value_is_null env
      (QExpr_Window left_partition left_order left_items left)
      (QExpr_Window right_partition right_order right_items right).
Proof.
intros env left_partition left_order left_items
  right_partition right_order right_items left right
  Hchildren Houtputs Hlocal.
apply query_expr_possible_bag_schedule_transport_implies_possible_bag_outcome_equiv.
eapply query_expr_window_possible_bag_schedule_transport; eassumption.
Qed.

End ScheduledUnaryConstructorAdapters.
