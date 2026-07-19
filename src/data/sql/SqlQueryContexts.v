(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                Typed contextual congruence for query expressions               *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
        ATerms Projection SqlOutcome SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics
        SqlQueryFacts.

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
Hypothesis contains_nulls : tuple -> bool.
Hypothesis symbol_runtime_error :
  scalar_operator T -> list (option sql_runtime_error * value) ->
  option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate T -> list (option sql_runtime_error * value) ->
  option sql_runtime_error.
Hypothesis value_is_null : value -> bool.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_formula :=
  (@eval_formula_expr_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_formula_aggregates :=
  (@eval_formula_expr_aggregate_runtime_error T relname
    symbol_runtime_error aggregate_runtime_error).
Local Abbreviation eval_filter_rows :=
  (@eval_filter_rows_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_groups :=
  (@eval_groups_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_join_row_conditions :=
  (@eval_join_row_conditions_outcome T relname basesort instance unknown
    contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_join_conditions :=
  (@eval_join_conditions_outcome T relname basesort instance unknown
    contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null).
Local Abbreviation eval_join_bag :=
  (@eval_join_bag_outcome T relname basesort instance unknown contains_nulls
    symbol_runtime_error aggregate_runtime_error value_is_null).

Ltac transport_formula_forward equivalence :=
  match goal with
  | Hsource : eval_formula ?current_env _ ?source_outcome
      |- eval_formula ?current_env _ ?target_outcome =>
      unify source_outcome target_outcome;
      exact (proj1 (equivalence current_env source_outcome) Hsource)
  end.

Ltac transport_formula_backward equivalence :=
  match goal with
  | Hsource : eval_formula ?current_env _ ?source_outcome
      |- eval_formula ?current_env _ ?target_outcome =>
      unify source_outcome target_outcome;
      exact (proj2 (equivalence current_env source_outcome) Hsource)
  end.

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

Definition formula_expr_global_outcome_equiv
    (left right : formula_expr T relname) : Prop :=
  forall env outcome,
    eval_formula env left outcome <-> eval_formula env right outcome.

(** Group substitution additionally preserves the query-level aggregate
    finalization observation of HAVING.  Scalar formula outcome equivalence
    alone is insufficient because lazy CASE may hide an aggregate error from
    ordinary expression evaluation. *)
Definition formula_expr_global_group_outcome_equiv
    (left right : formula_expr T relname) : Prop :=
  formula_expr_global_outcome_equiv left right /\
  forall env,
    eval_formula_aggregates env left = eval_formula_aggregates env right.

(** Positional consumers consult the syntax-directed ordered outputs.  Raw
    outcome equality alone is therefore not substitutive in every context:
    differently shaped empty relations and swapped projection lists can have
    the same raw row outcomes.  This relation is the exact complete-context
    interface. *)
Definition query_expr_global_typed_outcome_equiv
    (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  query_expr_global_outcome_equiv left right.

Lemma query_expr_global_outcome_equiv_refl :
  forall query, query_expr_global_outcome_equiv query query.
Proof.
intros query env outcome; tauto.
Qed.

(** Constructor congruence for formulas. *)
Lemma formula_expr_conj_global_congr :
  forall operation first first' second second',
    formula_expr_global_outcome_equiv first first' ->
    formula_expr_global_outcome_equiv second second' ->
    formula_expr_global_outcome_equiv
      (FExpr_Conj operation first second) (FExpr_Conj operation first' second').
Proof.
intros operation first first' second second' Hfirst Hsecond env outcome.
split; intro Heval; inversion Heval; subst.
- apply EFormula_ConjLeftError. transport_formula_forward Hfirst.
- eapply EFormula_ConjRightError;
    first [transport_formula_forward Hfirst | transport_formula_forward Hsecond].
- eapply EFormula_ConjSuccess;
    first [transport_formula_forward Hfirst | transport_formula_forward Hsecond].
- apply EFormula_ConjLeftError. transport_formula_backward Hfirst.
- eapply EFormula_ConjRightError;
    first [transport_formula_backward Hfirst | transport_formula_backward Hsecond].
- eapply EFormula_ConjSuccess;
    first [transport_formula_backward Hfirst | transport_formula_backward Hsecond].
Qed.

Lemma formula_expr_not_global_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    formula_expr_global_outcome_equiv (FExpr_Not first) (FExpr_Not second).
Proof.
intros first second Hequiv env outcome; split; intro Heval; inversion Heval; subst.
- apply EFormula_NotError. transport_formula_forward Hequiv.
- apply EFormula_NotSuccess. transport_formula_forward Hequiv.
- apply EFormula_NotError. transport_formula_backward Hequiv.
- apply EFormula_NotSuccess. transport_formula_backward Hequiv.
Qed.

Lemma formula_expr_quant_global_congr :
  forall quantifier predicate arguments first second,
    query_expr_global_typed_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_Quant quantifier predicate arguments first)
      (FExpr_Quant quantifier predicate arguments second).
Proof.
intros quantifier predicate arguments first second [Houtputs Hequiv] env outcome.
split; intro Heval; inversion Heval; subst.
- now apply EFormula_QuantArgumentsError.
- eapply EFormula_QuantSubqueryError; [eassumption|].
  transport_query_forward Hequiv.
- rewrite Houtputs.
  eapply EFormula_QuantSuccess; [eassumption|].
  transport_query_forward Hequiv.
- now apply EFormula_QuantArgumentsError.
- eapply EFormula_QuantSubqueryError; [eassumption|].
  transport_query_backward Hequiv.
- rewrite <- Houtputs.
  eapply EFormula_QuantSuccess; [eassumption|].
  transport_query_backward Hequiv.
Qed.

Lemma formula_expr_in_global_congr :
  forall select_items first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_In select_items first) (FExpr_In select_items second).
Proof.
intros select_items first second Hequiv env outcome.
split; intro Heval; inversion Heval; subst.
- now apply EFormula_InArgumentsError.
- eapply EFormula_InSubqueryError; [eassumption|].
  transport_query_forward Hequiv.
- eapply EFormula_InSuccess; [eassumption|].
  transport_query_forward Hequiv.
- now apply EFormula_InArgumentsError.
- eapply EFormula_InSubqueryError; [eassumption|].
  transport_query_backward Hequiv.
- eapply EFormula_InSuccess; [eassumption|].
  transport_query_backward Hequiv.
Qed.

Lemma formula_expr_exists_global_congr :
  forall first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_outcome_equiv
      (FExpr_Exists first) (FExpr_Exists second).
Proof.
intros first second Hequiv env outcome; split; intro Heval; inversion Heval; subst.
- apply EFormula_ExistsError. transport_query_forward Hequiv.
- apply EFormula_ExistsSuccessEmpty. transport_query_forward Hequiv.
- eapply EFormula_ExistsSuccessNonempty. transport_query_forward Hequiv.
- apply EFormula_ExistsError. transport_query_backward Hequiv.
- apply EFormula_ExistsSuccessEmpty. transport_query_backward Hequiv.
- eapply EFormula_ExistsSuccessNonempty. transport_query_backward Hequiv.
Qed.

Lemma formula_expr_global_outcome_equiv_refl :
  forall formula, formula_expr_global_outcome_equiv formula formula.
Proof.
intros formula env outcome; tauto.
Qed.

Lemma formula_expr_global_group_outcome_equiv_refl :
  forall formula, formula_expr_global_group_outcome_equiv formula formula.
Proof.
intro formula; split.
- apply formula_expr_global_outcome_equiv_refl.
- reflexivity.
Qed.

Lemma formula_expr_conj_global_group_congr :
  forall operation first first' second second',
    formula_expr_global_group_outcome_equiv first first' ->
    formula_expr_global_group_outcome_equiv second second' ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Conj operation first second)
      (FExpr_Conj operation first' second').
Proof.
intros operation first first' second second'
  [Hfirst Hfirst_aggregates] [Hsecond Hsecond_aggregates].
split.
- now apply formula_expr_conj_global_congr.
- intro env; simpl [eval_formula_expr_aggregate_runtime_error].
  now rewrite Hfirst_aggregates, Hsecond_aggregates.
Qed.

Lemma formula_expr_not_global_group_congr :
  forall first second,
    formula_expr_global_group_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Not first) (FExpr_Not second).
Proof.
intros first second [Hequiv Haggregates]; split.
- now apply formula_expr_not_global_congr.
- intro env; simpl [eval_formula_expr_aggregate_runtime_error].
  now rewrite Haggregates.
Qed.

Lemma formula_expr_quant_global_group_congr :
  forall quantifier predicate arguments first second,
    query_expr_global_typed_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Quant quantifier predicate arguments first)
      (FExpr_Quant quantifier predicate arguments second).
Proof.
intros; split.
- now apply formula_expr_quant_global_congr.
- reflexivity.
Qed.

Lemma formula_expr_in_global_group_congr :
  forall select_items first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_In select_items first) (FExpr_In select_items second).
Proof.
intros; split.
- now apply formula_expr_in_global_congr.
- reflexivity.
Qed.

Lemma formula_expr_exists_global_group_congr :
  forall first second,
    query_expr_global_outcome_equiv first second ->
    formula_expr_global_group_outcome_equiv
      (FExpr_Exists first) (FExpr_Exists second).
Proof.
intros; split.
- now apply formula_expr_exists_global_congr.
- reflexivity.
Qed.

Lemma query_expr_global_typed_outcome_equiv_refl :
  forall query, query_expr_global_typed_outcome_equiv query query.
Proof.
intro query; split.
- reflexivity.
- apply query_expr_global_outcome_equiv_refl.
Qed.

(** One query hole may occur under every compositional relational child and
    under every formula nesting/subquery position. *)
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
  | QCtx_JoinLeft : query_join_kind -> formula_expr T relname ->
      _select_list T -> _select_list T -> _select_list T ->
      query_expr_context -> query_expr T relname -> query_expr_context
  | QCtx_JoinRight : query_join_kind -> formula_expr T relname ->
      _select_list T -> _select_list T -> _select_list T ->
      query_expr T relname -> query_expr_context -> query_expr_context
  | QCtx_JoinPredicate : query_join_kind -> formula_expr_context ->
      _select_list T -> _select_list T -> _select_list T ->
      query_expr T relname -> query_expr T relname -> query_expr_context
  | QCtx_Project : _select_list T -> query_expr_context -> query_expr_context
  | QCtx_RowMap : list (attribute T) -> (tuple -> sql_outcome tuple) ->
      query_expr_context -> query_expr_context
  | QCtx_FilterInput : formula_expr T relname -> query_expr_context ->
      query_expr_context
  | QCtx_FilterFormula : formula_expr_context -> query_expr T relname ->
      query_expr_context
  | QCtx_GroupInput : _select_list T -> list (@aggterm T) ->
      formula_expr T relname -> query_expr_context -> query_expr_context
  | QCtx_GroupHaving : _select_list T -> list (@aggterm T) ->
      formula_expr_context -> query_expr T relname -> query_expr_context
  | QCtx_GroupingSets : list (query_grouping_set T) ->
      query_expr_context -> query_expr_context
  | QCtx_Rank : list (SqlOrder.sort_key T) -> list (SqlOrder.sort_key T) ->
      attribute T -> (nat -> option value) -> query_expr_context ->
      query_expr_context
  | QCtx_Window : list (SqlOrder.sort_key T) ->
      list (SqlOrder.sort_key T) -> list (query_window_item T) ->
      query_expr_context -> query_expr_context
  | QCtx_Distinct : query_expr_context -> query_expr_context
  | QCtx_OrderBy : list (SqlOrder.sort_key T) -> query_expr_context ->
      query_expr_context
  | QCtx_Offset : nat -> query_expr_context -> query_expr_context
  | QCtx_Fetch : nat -> query_expr_context -> query_expr_context

with formula_expr_context : Type :=
  | FCtx_ConjLeft : and_or -> formula_expr_context ->
      formula_expr T relname -> formula_expr_context
  | FCtx_ConjRight : and_or -> formula_expr T relname ->
      formula_expr_context -> formula_expr_context
  | FCtx_Not : formula_expr_context -> formula_expr_context
  | FCtx_Quant : quantifier -> predicate T -> list (@aggterm T) ->
      query_expr_context -> formula_expr_context
  | FCtx_In : list (@select T) -> query_expr_context -> formula_expr_context
  | FCtx_Exists : query_expr_context -> formula_expr_context.

Fixpoint plug_query_expr_context
    (context : query_expr_context) (replacement : query_expr T relname)
    {struct context} : query_expr T relname :=
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
      fixed_left fixed_right =>
      QExpr_Join kind (plug_formula_expr_context predicate replacement)
        matched_select left_select right_select fixed_left fixed_right
  | QCtx_Project select_list input =>
      QExpr_Project select_list (plug_query_expr_context input replacement)
  | QCtx_RowMap output_attributes row_map input =>
      QExpr_RowMap output_attributes row_map
        (plug_query_expr_context input replacement)
  | QCtx_FilterInput formula input =>
      QExpr_Filter formula (plug_query_expr_context input replacement)
  | QCtx_FilterFormula formula input =>
      QExpr_Filter (plug_formula_expr_context formula replacement) input
  | QCtx_GroupInput select_list group_terms having input =>
      QExpr_Group select_list group_terms having
        (plug_query_expr_context input replacement)
  | QCtx_GroupHaving select_list group_terms having input =>
      QExpr_Group select_list group_terms
        (plug_formula_expr_context having replacement) input
  | QCtx_GroupingSets grouping_sets input =>
      QExpr_GroupingSets grouping_sets
        (plug_query_expr_context input replacement)
  | QCtx_Rank partition_keys order_keys rank_attribute rank_value input =>
      QExpr_Rank partition_keys order_keys rank_attribute rank_value
        (plug_query_expr_context input replacement)
  | QCtx_Window partition_keys order_keys items input =>
      QExpr_Window partition_keys order_keys items
        (plug_query_expr_context input replacement)
  | QCtx_Distinct input =>
      QExpr_Distinct (plug_query_expr_context input replacement)
  | QCtx_OrderBy keys input =>
      QExpr_OrderBy keys (plug_query_expr_context input replacement)
  | QCtx_Offset offset input =>
      QExpr_Offset offset (plug_query_expr_context input replacement)
  | QCtx_Fetch count input =>
      QExpr_Fetch count (plug_query_expr_context input replacement)
  end

with plug_formula_expr_context
    (context : formula_expr_context) (replacement : query_expr T relname)
    {struct context} : formula_expr T relname :=
  match context with
  | FCtx_ConjLeft operation child fixed_formula =>
      FExpr_Conj operation (plug_formula_expr_context child replacement) fixed_formula
  | FCtx_ConjRight operation fixed_formula child =>
      FExpr_Conj operation fixed_formula (plug_formula_expr_context child replacement)
  | FCtx_Not formula =>
      FExpr_Not (plug_formula_expr_context formula replacement)
  | FCtx_Quant quantifier predicate arguments subquery =>
      FExpr_Quant quantifier predicate arguments
        (plug_query_expr_context subquery replacement)
  | FCtx_In select_items subquery =>
      FExpr_In select_items (plug_query_expr_context subquery replacement)
  | FCtx_Exists subquery =>
      FExpr_Exists (plug_query_expr_context subquery replacement)
  end.

(** Auxiliary relational traversals are congruent in their formula index. *)
Lemma eval_filter_rows_formula_congr_forward :
  forall left right,
    formula_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome ->
      eval_filter_rows env right rows outcome.
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

Lemma eval_filter_rows_formula_congr :
  forall left right,
    formula_expr_global_outcome_equiv left right ->
    forall env rows outcome,
      eval_filter_rows env left rows outcome <->
      eval_filter_rows env right rows outcome.
Proof.
intros left right Hequiv env rows outcome; split; intro Heval.
- now eapply eval_filter_rows_formula_congr_forward.
- eapply eval_filter_rows_formula_congr_forward; [|exact Heval].
  intros current_env current_outcome; symmetry; apply Hequiv.
Qed.

Lemma eval_groups_formula_congr_forward :
  forall left right,
    formula_expr_global_group_outcome_equiv left right ->
    forall env select_list group_terms groups outcome,
      eval_groups env select_list group_terms left groups outcome ->
      eval_groups env select_list group_terms right groups outcome.
Proof.
intros left right [Hequiv Haggregates]
  env select_list group_terms groups outcome Heval.
induction Heval.
- constructor.
- apply EGroups_AggregateError; eassumption.
- apply EGroups_HavingAggregateError.
  + eassumption.
  + rewrite <- Haggregates; eassumption.
- apply EGroups_HavingError.
  + eassumption.
  + rewrite <- Haggregates; eassumption.
  + now apply (proj1 (Hequiv _ _)).
- eapply EGroups_HavingFalse.
  + eassumption.
  + rewrite <- Haggregates; eassumption.
  + apply (proj1 (Hequiv _ _)).
    match goal with
    | Hsource : eval_formula _ _ (SqlSuccess _) |- _ => exact Hsource
    end.
  + eassumption.
  + exact (IHHeval Hequiv Haggregates).
- eapply EGroups_SelectError.
  + eassumption.
  + rewrite <- Haggregates; eassumption.
  + apply (proj1 (Hequiv _ _)).
    match goal with
    | Hsource : eval_formula _ _ (SqlSuccess _) |- _ => exact Hsource
    end.
  + eassumption.
  + eassumption.
- eapply EGroups_SelectSuccess.
  + eassumption.
  + rewrite <- Haggregates; eassumption.
  + apply (proj1 (Hequiv _ _)).
    match goal with
    | Hsource : eval_formula _ _ (SqlSuccess _) |- _ => exact Hsource
    end.
  + eassumption.
  + eassumption.
  + exact (IHHeval Hequiv Haggregates).
Qed.

Lemma eval_groups_formula_congr :
  forall left right,
    formula_expr_global_group_outcome_equiv left right ->
    forall env select_list group_terms groups outcome,
      eval_groups env select_list group_terms left groups outcome <->
      eval_groups env select_list group_terms right groups outcome.
Proof.
intros left right Hequiv env select_list group_terms groups outcome; split; intro Heval.
- eapply eval_groups_formula_congr_forward; [exact Hequiv | exact Heval].
- eapply eval_groups_formula_congr_forward; [|exact Heval].
  destruct Hequiv as [Houtcomes Haggregates]; split.
  + intros current_env current_outcome; symmetry; apply Houtcomes.
  + intro current_env; symmetry; apply Haggregates.
Qed.

Lemma eval_group_bag_formula_congr_forward :
  forall left right,
    formula_expr_global_group_outcome_equiv left right ->
    forall env select_list group_terms input_bag outcome,
      eval_group_bag env select_list group_terms left input_bag outcome ->
      eval_group_bag env select_list group_terms right input_bag outcome.
Proof.
intros left right Hequiv env select_list group_terms input_bag outcome Heval.
inversion Heval; subst.
- eapply EGroupBag_KeyError; eassumption.
- eapply EGroupBag_ProcessError.
  + eassumption.
  + eassumption.
  + now apply (proj1
      (eval_groups_formula_congr Hequiv env select_list group_terms _ _)).
- eapply EGroupBag_Success with
    (representative := representative) (grouped_rows := grouped_rows).
  + eassumption.
  + eassumption.
  + now apply (proj1
      (eval_groups_formula_congr Hequiv env select_list group_terms _ _)).
  + eassumption.
Qed.

Lemma eval_group_bag_formula_congr :
  forall left right,
    formula_expr_global_group_outcome_equiv left right ->
    forall env select_list group_terms input_bag outcome,
      eval_group_bag env select_list group_terms left input_bag outcome <->
      eval_group_bag env select_list group_terms right input_bag outcome.
Proof.
intros left right Hequiv env select_list group_terms input_bag outcome;
  split; intro Heval.
- eapply eval_group_bag_formula_congr_forward; [exact Hequiv | exact Heval].
- eapply eval_group_bag_formula_congr_forward; [|exact Heval].
  destruct Hequiv as [Houtcomes Haggregates]; split.
  + intros current_env current_outcome; symmetry; apply Houtcomes.
  + intro current_env; symmetry; apply Haggregates.
Qed.

Lemma eval_join_row_conditions_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_row_conditions env first left_rows right_rows outcome ->
      eval_join_row_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome Heval.
induction Heval.
- constructor.
- apply EJoinRowConditions_HeadError.
  now apply (proj1 (Hequiv _ _)).
- eapply EJoinRowConditions_Cons.
  + now apply (proj1 (Hequiv _ _)).
  + exact (IHHeval Hequiv).
Qed.

Lemma eval_join_row_conditions_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_row_conditions env first left_rows right_rows outcome <->
      eval_join_row_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome; split; intro Heval.
- now eapply eval_join_row_conditions_formula_congr_forward.
- eapply eval_join_row_conditions_formula_congr_forward; [|exact Heval].
  intros current_env current_outcome; symmetry; apply Hequiv.
Qed.

Lemma eval_join_conditions_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome ->
      eval_join_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome Heval.
induction Heval.
- constructor.
- apply EJoinConditions_RowError.
  now apply (proj1
    (eval_join_row_conditions_formula_congr Hequiv _ _ _ _)).
- eapply EJoinConditions_Cons.
  + now apply (proj1
      (eval_join_row_conditions_formula_congr Hequiv _ _ _ _)).
  + exact (IHHeval Hequiv).
Qed.

Lemma eval_join_conditions_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env left_rows right_rows outcome,
      eval_join_conditions env first left_rows right_rows outcome <->
      eval_join_conditions env second left_rows right_rows outcome.
Proof.
intros first second Hequiv env left_rows right_rows outcome; split; intro Heval.
- now eapply eval_join_conditions_formula_congr_forward.
- eapply eval_join_conditions_formula_congr_forward; [|exact Heval].
  intros current_env current_outcome; symmetry; apply Hequiv.
Qed.

Lemma eval_join_bag_formula_congr_forward :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env kind matched_select left_select right_select
           left_bag right_bag outcome,
      eval_join_bag env kind first matched_select left_select right_select
        left_bag right_bag outcome ->
      eval_join_bag env kind second matched_select left_select right_select
        left_bag right_bag outcome.
Proof.
intros first second Hequiv env kind matched_select left_select right_select
  left_bag right_bag outcome Heval.
inversion Heval; subst.
- eapply EJoinBag_ConditionError.
  + eassumption.
  + eassumption.
  + now apply (proj1
      (eval_join_conditions_formula_congr Hequiv _ _ _ _)).
- eapply EJoinBag_ProjectionError with (matrix := matrix).
  + eassumption.
  + eassumption.
  + now apply (proj1
      (eval_join_conditions_formula_congr Hequiv _ _ _ _)).
  + eassumption.
- eapply EJoinBag_Success with
    (left_rows := left_rows) (right_rows := right_rows)
    (matrix := matrix) (projected := projected).
  + eassumption.
  + eassumption.
  + now apply (proj1
      (eval_join_conditions_formula_congr Hequiv _ _ _ _)).
  + eassumption.
  + eassumption.
Qed.

Lemma eval_join_bag_formula_congr :
  forall first second,
    formula_expr_global_outcome_equiv first second ->
    forall env kind matched_select left_select right_select
           left_bag right_bag outcome,
      eval_join_bag env kind first matched_select left_select right_select
        left_bag right_bag outcome <->
      eval_join_bag env kind second matched_select left_select right_select
        left_bag right_bag outcome.
Proof.
intros first second Hequiv env kind matched_select left_select right_select
  left_bag right_bag outcome; split; intro Heval.
- now eapply eval_join_bag_formula_congr_forward.
- eapply eval_join_bag_formula_congr_forward; [|exact Heval].
  intros current_env current_outcome; symmetry; apply Hequiv.
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
  forall kind predicate predicate' matched_select left_select right_select
         left left' right right',
    formula_expr_global_outcome_equiv predicate predicate' ->
    query_expr_global_typed_outcome_equiv left left' ->
    query_expr_global_typed_outcome_equiv right right' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Join kind predicate matched_select left_select right_select
        left right)
      (QExpr_Join kind predicate' matched_select left_select right_select
        left' right').
Proof.
intros kind predicate predicate' matched_select left_select right_select
  left left' right right' Hpredicate [_ Hleft] [_ Hright].
split.
- reflexivity.
- intros env outcome; split; intro Heval; inversion Heval; subst.
  + apply EQuery_JoinLeftError. transport_query_forward Hleft.
  + eapply EQuery_JoinRightError.
    * transport_query_forward Hleft.
    * transport_query_forward Hright.
  + eapply EQuery_JoinBagError.
    * transport_query_forward Hleft.
    * transport_query_forward Hright.
    * now apply (proj1
        (eval_join_bag_formula_congr Hpredicate _ _ _ _ _ _ _ _)).
  + eapply EQuery_JoinSuccess with (output_bag := output_bag).
    * transport_query_forward Hleft.
    * transport_query_forward Hright.
    * now apply (proj1
        (eval_join_bag_formula_congr Hpredicate _ _ _ _ _ _ _ _)).
    * eassumption.
  + apply EQuery_JoinLeftError. transport_query_backward Hleft.
  + eapply EQuery_JoinRightError.
    * transport_query_backward Hleft.
    * transport_query_backward Hright.
  + eapply EQuery_JoinBagError.
    * transport_query_backward Hleft.
    * transport_query_backward Hright.
    * now apply (proj2
        (eval_join_bag_formula_congr Hpredicate _ _ _ _ _ _ _ _)).
  + eapply EQuery_JoinSuccess with (output_bag := output_bag).
    * transport_query_backward Hleft.
    * transport_query_backward Hright.
    * now apply (proj2
        (eval_join_bag_formula_congr Hpredicate _ _ _ _ _ _ _ _)).
    * eassumption.
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
- eapply EQuery_ProjectRows. transport_query_forward Hequiv.
- apply EQuery_ProjectChildError. transport_query_backward Hequiv.
- eapply EQuery_ProjectRows. transport_query_backward Hequiv.
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
  forall formula formula' input input',
    formula_expr_global_outcome_equiv formula formula' ->
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Filter formula input) (QExpr_Filter formula' input').
Proof.
intros formula formula' input input' Hformula [Houtputs Hinput].
split; [exact Houtputs|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_FilterChildError. transport_query_forward Hinput.
- eapply EQuery_FilterRows.
  + transport_query_forward Hinput.
  + now apply (proj1 (eval_filter_rows_formula_congr Hformula _ _ _)).
- apply EQuery_FilterChildError. transport_query_backward Hinput.
- eapply EQuery_FilterRows.
  + transport_query_backward Hinput.
  + now apply (proj2 (eval_filter_rows_formula_congr Hformula _ _ _)).
Qed.

Lemma query_expr_group_global_typed_congr :
  forall select_list group_terms having having' input input',
    formula_expr_global_group_outcome_equiv having having' ->
    query_expr_global_typed_outcome_equiv input input' ->
    query_expr_global_typed_outcome_equiv
      (QExpr_Group select_list group_terms having input)
      (QExpr_Group select_list group_terms having' input').
Proof.
intros select_list group_terms having having' input input' Hhaving [_ Hinput].
split; [reflexivity|].
intros env outcome; split; intro Heval; inversion Heval; subst.
- apply EQuery_GroupChildError. transport_query_forward Hinput.
- eapply EQuery_GroupBagError.
  + transport_query_forward Hinput.
  + now apply (proj1
      (eval_group_bag_formula_congr Hhaving env select_list group_terms _ _)).
- eapply EQuery_GroupBagSuccess with
    (input_rows := input_rows) (output_bag := output_bag).
  + transport_query_forward Hinput.
  + now apply (proj1
      (eval_group_bag_formula_congr Hhaving env select_list group_terms _ _)).
  + eassumption.
- apply EQuery_GroupChildError. transport_query_backward Hinput.
- eapply EQuery_GroupBagError.
  + transport_query_backward Hinput.
  + now apply (proj2
      (eval_group_bag_formula_congr Hhaving env select_list group_terms _ _)).
- eapply EQuery_GroupBagSuccess with
    (input_rows := input_rows) (output_bag := output_bag).
  + transport_query_backward Hinput.
  + now apply (proj2
      (eval_group_bag_formula_congr Hhaving env select_list group_terms _ _)).
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

Scheme query_expr_context_ind' := Induction for query_expr_context Sort Prop
with formula_expr_context_ind' := Induction for formula_expr_context Sort Prop.

Combined Scheme query_context_mutind
  from query_expr_context_ind', formula_expr_context_ind'.

(** Contextual congruence for the complete compositional context grammar. *)
Theorem query_context_global_congr :
  (forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement')) /\
  (forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    formula_expr_global_group_outcome_equiv
      (plug_formula_expr_context context replacement)
      (plug_formula_expr_context context replacement')).
Proof.
apply query_context_mutind; intros; simpl.
- assumption.
- apply query_expr_set_global_typed_congr.
  + now apply H.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_set_global_typed_congr.
  + apply query_expr_global_typed_outcome_equiv_refl.
  + now apply H.
- apply query_expr_natural_join_global_typed_congr.
  + now apply H.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_natural_join_global_typed_congr.
  + apply query_expr_global_typed_outcome_equiv_refl.
  + now apply H.
- apply query_expr_cross_join_global_typed_congr.
  + now apply H.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_cross_join_global_typed_congr.
  + apply query_expr_global_typed_outcome_equiv_refl.
  + now apply H.
- apply query_expr_join_global_typed_congr.
  + apply formula_expr_global_outcome_equiv_refl.
  + now apply H.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_join_global_typed_congr.
  + apply formula_expr_global_outcome_equiv_refl.
  + apply query_expr_global_typed_outcome_equiv_refl.
  + now apply H.
- apply query_expr_join_global_typed_congr.
  + exact (proj1 (H _ _ H0)).
  + apply query_expr_global_typed_outcome_equiv_refl.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_project_global_typed_congr. now apply H.
- apply query_expr_row_map_global_typed_congr. now apply H.
- apply query_expr_filter_global_typed_congr.
  + apply formula_expr_global_outcome_equiv_refl.
  + now apply H.
- apply query_expr_filter_global_typed_congr.
  + exact (proj1 (H _ _ H0)).
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_group_global_typed_congr.
  + apply formula_expr_global_group_outcome_equiv_refl.
  + now apply H.
- apply query_expr_group_global_typed_congr.
  + now apply H.
  + apply query_expr_global_typed_outcome_equiv_refl.
- apply query_expr_grouping_sets_global_typed_congr. now apply H.
- apply query_expr_rank_global_typed_congr. now apply H.
- apply query_expr_window_global_typed_congr. now apply H.
- apply query_expr_distinct_global_typed_congr. now apply H.
- apply query_expr_order_by_global_typed_congr. now apply H.
- apply query_expr_offset_global_typed_congr. now apply H.
- apply query_expr_fetch_global_typed_congr. now apply H.
- apply formula_expr_conj_global_group_congr.
  + now apply H.
  + apply formula_expr_global_group_outcome_equiv_refl.
- apply formula_expr_conj_global_group_congr.
  + apply formula_expr_global_group_outcome_equiv_refl.
  + now apply H.
- apply formula_expr_not_global_group_congr. now apply H.
- apply formula_expr_quant_global_group_congr. now apply H.
- apply formula_expr_in_global_group_congr. now apply H.
- apply formula_expr_exists_global_group_congr. now apply H.
Qed.

Theorem query_expr_context_global_congr :
  forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_global_typed_outcome_equiv
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
Proof.
exact (proj1 query_context_global_congr).
Qed.

Theorem formula_expr_context_global_congr :
  forall context replacement replacement',
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    formula_expr_global_outcome_equiv
      (plug_formula_expr_context context replacement)
      (plug_formula_expr_context context replacement').
Proof.
intros context replacement replacement' Hequiv.
exact (proj1 (proj2 query_context_global_congr
  context replacement replacement' Hequiv)).
Qed.

(** Safety remains explicit when raw equality is converted to the
    success-only observation contract. *)
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
    @query_expr_observation_equiv T relname basesort instance unknown
      contains_nulls symbol_runtime_error aggregate_runtime_error value_is_null
      env first second.
Proof.
intros env first second Hequiv Hfirst_safe Hsecond_safe Hsuccess.
unfold query_expr_observation_equiv, successful_relation_equiv.
split; [exact Hsuccess|].
split; [exact Hfirst_safe|].
split; [exact Hsecond_safe|].
intro rows; apply Hequiv.
Qed.

Lemma query_expr_equiv_of_outcome_rel_equiv_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    (forall outcome, eval_query env first outcome <-> eval_query env second outcome) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env first second.
Proof.
intros env first second Houtputs Hequiv Hfirst_safe Hsecond_safe Hsuccess.
split; [exact Houtputs|].
now apply query_expr_observation_equiv_of_outcome_rel_equiv_safe.
Qed.

Theorem query_expr_context_equiv_safe :
  forall context replacement replacement' env,
    query_expr_global_typed_outcome_equiv replacement replacement' ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement) ->
    query_expr_runtime_safe env
      (plug_query_expr_context context replacement') ->
    query_expr_has_success env
      (plug_query_expr_context context replacement) ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env
      (plug_query_expr_context context replacement)
      (plug_query_expr_context context replacement').
Proof.
intros context replacement replacement' env Hequiv Hsafe Hsafe' Hsuccess.
destruct (query_expr_context_global_congr context Hequiv) as [Houtputs Hraw].
apply query_expr_equiv_of_outcome_rel_equiv_safe; try assumption.
apply Hraw.
Qed.

(** A bag-reset result can be recovered as an exact ordered-observation
    equivalence once both result relations are known to be bag-closed.  The
    possible-bag equality is not by itself allowed to hide runtime failures:
    safety and existence of a successful observation remain explicit
    premises. *)
Theorem query_bag_effect_equiv_of_success_bags_safe :
  forall env first second,
    query_expr_outputs first = query_expr_outputs second ->
    query_expr_effect first = BagEffect ->
    query_expr_effect second = BagEffect ->
    rel_equiv
      (query_success_bags basesort instance unknown contains_nulls
        symbol_runtime_error aggregate_runtime_error value_is_null env first)
      (query_success_bags basesort instance unknown contains_nulls
        symbol_runtime_error aggregate_runtime_error value_is_null env second) ->
    query_expr_runtime_safe env first ->
    query_expr_runtime_safe env second ->
    query_expr_has_success env first ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env first second.
Proof.
intros env first second Houtputs Hfirst_effect Hsecond_effect Hbags
  Hfirst_safe Hsecond_safe Hsuccess.
split; [exact Houtputs|].
unfold query_expr_observation_equiv.
apply successful_relation_equiv_intro.
- exact Hsuccess.
- exact Hfirst_safe.
- exact Hsecond_safe.
- apply (proj2
    (bag_closed_rel_equiv_iff_alpha_rel_equiv
      (@query_expr_effect_sound T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env first Hfirst_effect)
      (@query_expr_effect_sound T relname basesort instance unknown
        contains_nulls symbol_runtime_error aggregate_runtime_error
        value_is_null env second Hsecond_effect))).
  exact Hbags.
Qed.

(** Immediate [Distinct] is the canonical local reset principle.  A proof may
    establish equality of the child queries' exact ordered success lists at
    one environment, cross [alpha] once, use the lifted duplicate-elimination
    operation, and return to exact equivalence through [BagClosed]. *)
Theorem query_distinct_equiv_of_local_success_rel_equiv :
  forall env left right,
    query_expr_outputs left = query_expr_outputs right ->
    (forall rows,
      eval_query env left (SqlSuccess rows) <->
      eval_query env right (SqlSuccess rows)) ->
    query_expr_runtime_safe env (QExpr_Distinct left) ->
    query_expr_runtime_safe env (QExpr_Distinct right) ->
    query_expr_has_success env (QExpr_Distinct left) ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right Houtputs Hlists Hleft_safe Hright_safe Hsuccess.
apply query_bag_effect_equiv_of_success_bags_safe.
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
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right ->
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null
      env (QExpr_Distinct left) (QExpr_Distinct right).
Proof.
intros env left right [Houtputs [Hsuccess [Hleft_safe [Hright_safe Hlists]]]].
apply query_distinct_equiv_of_local_success_rel_equiv.
- exact Houtputs.
- exact Hlists.
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

Lemma successful_relation_equiv_rel_equiv :
  forall (first second : sql_outcome (list tuple) -> Prop),
    successful_relation_equiv first second ->
    rel_equiv first second.
Proof.
intros first second [_ [Hfirst_error [Hsecond_error Hsuccess]]] [rows | error].
- apply Hsuccess.
- split; intro Herror.
  + contradiction (Hfirst_error error Herror).
  + contradiction (Hsecond_error error Herror).
Qed.

Definition successful_possible_bags
    (observations : sql_outcome (list tuple) -> Prop) : bagT -> Prop :=
  fun bag => @outcome_alpha T observations (SqlSuccess bag).

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
    @query_expr_equiv T relname basesort instance unknown contains_nulls
      symbol_runtime_error aggregate_runtime_error value_is_null env first second ->
    possible_bag_query_boundary_equiv
      (query_expr_sort first) (query_expr_sort second)
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env first)))
      (plug_possible_bag_context context
        (successful_possible_bags (eval_query env second))).
Proof.
intros env context first second [Houtputs Hobservation].
apply list_outcome_equiv_possible_bag_query_boundary_congr.
- now apply (query_expr_outputs_eq_sort_eq first second).
-
apply successful_relation_equiv_rel_equiv.
exact Hobservation.
Qed.

End Sec.

Arguments QCtx_Hole {T relname}.
Arguments plug_query_expr_context {T relname} _ _.
Arguments plug_formula_expr_context {T relname} _ _.
Arguments plug_possible_bag_context {T} _ _.
