(************************************************************************************)
(**                                                                                **)
(**                         The SQLFormalSemantics Library                         **)
(**                                                                                **)
(**        Collision-safe attribute renaming through exact query outcomes         **)
(**                                                                                **)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Sorting.Permutation.

Require Import ListPermut OrderedSet FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
        ATerms Projection SqlOutcome SqlOrder SqlBagAbstraction SqlQuerySyntax
        SqlQuerySemantics SqlRenameFacts SqlQueryWellFormed SqlQueryFacts
        SqlQueryContexts.

(** This module deliberately does not define a second query AST.  It relates two
    existing [query_expr] values through their mapped ordered schemas and exact
    success/error observations.  Each attribute-observing constructor below has
    a local semantic compatibility premise.  Such a premise must be discharged
    only after predicates, projections, grouping terms, sort/window keys, join
    conditions, aliases, nested subqueries, and reachable environments have all
    been renamed consistently.

    In particular, output-only tuple renaming is not full query alpha-renaming.
    [QExpr_Table] also needs a transported database, and [QExpr_RowMap] needs a
    conjugacy proof for its opaque callback.  The conditional theorems make those
    fail-closed boundaries explicit. *)

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
Hypothesis leaf_has_type : type T -> @aggterm T -> Prop.
Hypothesis call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Hypothesis predicate_has_types : predicate T -> list (type T) -> Prop.
Hypothesis rank_type boolean_type : type T.

Local Abbreviation eval_query :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_boolean :=
  (@eval_scalar_boolean_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule).
Local Abbreviation eval_scalar_boolean_aggregates :=
  (@eval_scalar_expr_aggregate_runtime_error T relname
    symbol_runtime_error aggregate_runtime_error).

(** Exact order and multiplicity are retained, and the mapping reflects tuple
    equivalence across every pair of actual source rows.  This successful-row
    contract deliberately does not trust a declared VALUES/Table schema: even
    malformed source bags must supply collision and type safety on their real
    labels before they can participate in query alpha-renaming. *)
Definition query_rows_rename
    (rho : attribute T -> attribute T)
    (left right : list tuple) : Prop :=
  rows_rename_sound rho left right.

(** Reachable scalar environments are paired explicitly.  These relations are
    used by exact expression contracts below; they do not assume that evaluating a
    renamed correlated subquery in the original outer environment is sound. *)
Definition query_row_environment_rename
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_env right_env : Env.env T) : Prop :=
  exists left_outer right_outer left_row right_row,
    environment_relation left_outer right_outer /\
    rename_tuple T rho left_row =t= right_row /\
    left_env = env_t T left_outer left_row /\
    right_env = env_t T right_outer right_row.

Definition query_join_environment_rename
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_env right_env : Env.env T) : Prop :=
  exists left_outer right_outer
      left_source right_source left_target right_target,
    environment_relation left_outer right_outer /\
    rename_tuple T rho left_source =t= left_target /\
    rename_tuple T rho right_source =t= right_target /\
    left_env = env_t T left_outer (join_tuple T left_source right_source) /\
    right_env = env_t T right_outer (join_tuple T left_target right_target).

Definition query_group_environment_rename
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_terms right_terms : list (@aggterm T))
    (left_env right_env : Env.env T) : Prop :=
  exists left_outer right_outer left_group right_group,
    environment_relation left_outer right_outer /\
    query_rows_rename rho left_group right_group /\
    left_env = env_g T left_outer (@Group_By T left_terms) left_group /\
    right_env = env_g T right_outer (@Group_By T right_terms) right_group.

Definition query_group_reachable
    (env : Env.env T) (terms : list (@aggterm T))
    (input_rows group : list tuple) : Prop :=
  exists representative,
    query_same_rows_as_bag representative (query_rows_bag input_rows) /\
    In group
      (query_make_groups env representative terms).

(** GROUP consumes arbitrary representatives of its input bag.  This coverage
    premise pairs every group reachable from either endpoint before the exact
    HAVING contract is applied, so a local final-output scheduler cannot hide a
    FALSE/UNKNOWN swap in an unpaired intermediate group. *)
Definition query_group_formation_rename_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_terms right_terms : list (@aggterm T)) : Prop :=
  forall left_env right_env left_rows right_rows,
    environment_relation left_env right_env ->
    query_rows_rename rho left_rows right_rows ->
    (forall left_group,
      query_group_reachable left_env left_terms left_rows left_group ->
      exists right_group,
        query_group_reachable right_env right_terms right_rows right_group /\
        query_rows_rename rho left_group right_group) /\
    (forall right_group,
      query_group_reachable right_env right_terms right_rows right_group ->
      exists left_group,
        query_group_reachable left_env left_terms left_rows left_group /\
        query_rows_rename rho left_group right_group).

(** Exact three-valued compatibility.  [outcome_relation_equiv eq] retains
    TRUE, FALSE, and UNKNOWN separately and compares every SQL error category;
    quantified/correlated subqueries are included by [eval_scalar_boolean]. *)
Definition query_scalar_expr_outcome_rename_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (left right : scalar_expr T relname ScalarResultBoolean) : Prop :=
  forall left_env right_env,
    environment_relation left_env right_env ->
    outcome_relation_equiv eq
      (eval_scalar_boolean left_env left) (eval_scalar_boolean right_env right).

Lemma query_scalar_expr_outcome_rename_compatible_success_iff :
  forall environment_relation left right left_env right_env,
    query_scalar_expr_outcome_rename_compatible
      environment_relation left right ->
    environment_relation left_env right_env ->
    forall truth,
      (eval_scalar_boolean left_env left (SqlSuccess truth) <->
       eval_scalar_boolean right_env right (SqlSuccess truth)).
Proof.
intros environment_relation left right left_env right_env
  Hexpression Henvironment truth.
destruct (Hexpression left_env right_env Henvironment)
  as [_ [_ [Hforward [Hbackward _]]]].
split; intro Heval.
- destruct (Hforward truth Heval) as [right_truth [Hright Hequal]].
  now subst right_truth.
- destruct (Hbackward truth Heval) as [left_truth [Hleft Hequal]].
  now subst left_truth.
Qed.

Lemma query_scalar_expr_outcome_rename_compatible_error_iff :
  forall environment_relation left right left_env right_env,
    query_scalar_expr_outcome_rename_compatible
      environment_relation left right ->
    environment_relation left_env right_env ->
    forall error,
      (eval_scalar_boolean left_env left (SqlError error) <->
       eval_scalar_boolean right_env right (SqlError error)).
Proof.
intros environment_relation left right left_env right_env
  Hexpression Henvironment error.
exact (proj2 (proj2 (proj2 (proj2
  (Hexpression left_env right_env Henvironment)))) error).
Qed.

(** GROUP observes aggregate finalization before its lazy HAVING result, so the
    aggregate precheck must also agree exactly. *)
Definition query_group_scalar_expr_outcome_rename_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (left right : scalar_expr T relname ScalarResultBoolean) : Prop :=
  query_scalar_expr_outcome_rename_compatible environment_relation left right /\
  forall left_env right_env,
    environment_relation left_env right_env ->
    eval_scalar_boolean_aggregates left_env left =
    eval_scalar_boolean_aggregates right_env right.

(** A support-local injection is the collision side condition actually needed
    by tuple renaming.  Pair-list uniqueness alone is insufficient when a
    renamed target collides with an untouched label. *)
Definition query_attribute_rename_injective_on
    (rho : attribute T -> attribute T) (scope : setA) : Prop :=
  attribute_rename_injective_on scope rho.

(** Attribute types include the concrete model's type parameters.  A generic
    transport proof must retain them on every observed label; instance-specific
    TNull conformance adapters may strengthen this to the full typmod contract. *)
Definition query_attribute_rename_type_preserving_on
    (rho : attribute T -> attribute T) (scope : setA) : Prop :=
  attribute_rename_type_preserving_on scope rho.

(** Ordered schema compatibility is intentionally separate from ordinary query
    equivalence, whose schemas must be literally equal.  Both endpoint schemas
    must be unique and admissible, and the source mapping must be collision- and
    type-safe.  Keeping admissibility here makes every constructor transport
    fail closed, including VALUES/Table sources and all context compositions. *)
Definition query_rename_schema_compatible
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  @query_output_attributes_unique T (query_expr_outputs left) /\
  @query_output_attributes_unique T (query_expr_outputs right) /\
  map rho (query_expr_outputs left) = query_expr_outputs right /\
  query_attribute_rename_injective_on rho (query_expr_sort left) /\
  query_attribute_rename_type_preserving_on rho (query_expr_sort left) /\
  @query_expr_admissible T relname basesort leaf_has_type call_has_type
    predicate_has_types rank_type boolean_type value_is_null left /\
  @query_expr_admissible T relname basesort leaf_has_type call_has_type
    predicate_has_types rank_type boolean_type value_is_null right.

(** Bidirectional exact-outcome transport.  Successes retain order and bag
    multiplicity through [query_rows_rename]; every runtime error category is
    present on one side exactly when it is present on the other.  Unlike
    [outcome_relation_equiv], this compositional interface does not silently
    assert that an arbitrary relation is inhabited. *)
Definition query_outcome_rename_transport
    (rho : attribute T -> attribute T)
    (left right : sql_outcome (list tuple) -> Prop) : Prop :=
  (forall left_rows,
    left (SqlSuccess left_rows) ->
    exists right_rows,
      right (SqlSuccess right_rows) /\
      query_rows_rename rho left_rows right_rows) /\
  (forall right_rows,
    right (SqlSuccess right_rows) ->
    exists left_rows,
      left (SqlSuccess left_rows) /\
      query_rows_rename rho left_rows right_rows) /\
  (forall error,
    left (SqlError error) <-> right (SqlError error)).

Lemma query_outcome_rename_transport_identity :
  forall outcomes,
    query_outcome_rename_transport
      (fun attribute => attribute) outcomes outcomes.
Proof.
intro outcomes; split.
- intros rows Hrows; exists rows; split.
  + exact Hrows.
  + unfold query_rows_rename; apply rows_rename_sound_identity.
- split.
  + intros rows Hrows; exists rows; split.
    * exact Hrows.
    * unfold query_rows_rename; apply rows_rename_sound_identity.
  + intro error; reflexivity.
Qed.

(** [environment_relation] is explicit because correlated subqueries cannot be
    transported soundly by evaluating renamed [F_Dot] references in the same
    old outer environment.  Callers may use closed [nil]/[nil] environments or
    supply a reachable-environment relation preserved by their renamed scalar,
    aggregate, grouping, and subquery metadata. *)
Definition query_rename_transport_under
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  query_rename_schema_compatible rho left right /\
  forall left_env right_env,
    environment_relation left_env right_env ->
    query_outcome_rename_transport rho
      (eval_query left_env left) (eval_query right_env right).

Lemma query_rename_schema_compatible_identity :
  forall query,
    @query_output_attributes_unique T (query_expr_outputs query) ->
    @query_expr_admissible T relname basesort leaf_has_type call_has_type
      predicate_has_types rank_type boolean_type value_is_null query ->
    query_rename_schema_compatible
      (fun attribute => attribute) query query.
Proof.
intros query Houtputs Hadmissible.
unfold query_rename_schema_compatible.
split; [exact Houtputs |].
split; [exact Houtputs |].
split; [apply map_id |].
split; [apply attribute_rename_injective_on_identity |].
split; [apply attribute_rename_type_preserving_on_identity |].
now split.
Qed.

Lemma query_rename_transport_under_identity :
  forall query,
    @query_output_attributes_unique T (query_expr_outputs query) ->
    @query_expr_admissible T relname basesort leaf_has_type call_has_type
      predicate_has_types rank_type boolean_type value_is_null query ->
    query_rename_transport_under eq
      (fun attribute => attribute) query query.
Proof.
intros query Houtputs Hadmissible; split.
- now apply query_rename_schema_compatible_identity.
- intros left_env right_env Hequal; subst right_env.
  apply query_outcome_rename_transport_identity.
Qed.

Definition query_closed_rename_transport
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  query_rename_schema_compatible rho left right /\
  query_outcome_rename_transport rho
    (eval_query nil left) (eval_query nil right).

Lemma query_rename_transport_under_closed :
  forall rho left right,
    query_rename_transport_under
      (fun left_env right_env => left_env = nil /\ right_env = nil)
      rho left right ->
    query_closed_rename_transport rho left right.
Proof.
intros rho left right [Hschema Htransport].
split; [exact Hschema|].
apply Htransport; now split.
Qed.

(** Abstract error-propagating operator schedulers.  These are proof devices,
    not query syntax.  They factor the common parent/child reasoning shared by
    all current constructors while leaving each constructor's local semantics
    visible below. *)
Inductive query_unary_outcome_lift
    (child : sql_outcome (list tuple) -> Prop)
    (local : list tuple -> sql_outcome (list tuple) -> Prop) :
    sql_outcome (list tuple) -> Prop :=
  | QueryUnaryLiftChildError :
      forall error,
        child (SqlError error) ->
        query_unary_outcome_lift child local (SqlError error)
  | QueryUnaryLiftLocal :
      forall rows outcome,
        child (SqlSuccess rows) ->
        local rows outcome ->
        query_unary_outcome_lift child local outcome.

Inductive query_binary_outcome_lift
    (left_child right_child : sql_outcome (list tuple) -> Prop)
    (local : list tuple -> list tuple ->
      sql_outcome (list tuple) -> Prop) :
    sql_outcome (list tuple) -> Prop :=
  | QueryBinaryLiftLeftError :
      forall error,
        left_child (SqlError error) ->
        query_binary_outcome_lift left_child right_child local
          (SqlError error)
  | QueryBinaryLiftRightError :
      forall left_rows error,
        left_child (SqlSuccess left_rows) ->
        right_child (SqlError error) ->
        query_binary_outcome_lift left_child right_child local
          (SqlError error)
  | QueryBinaryLiftLocal :
      forall left_rows right_rows outcome,
        left_child (SqlSuccess left_rows) ->
        right_child (SqlSuccess right_rows) ->
        local left_rows right_rows outcome ->
        query_binary_outcome_lift left_child right_child local outcome.

Lemma query_unary_outcome_lift_transport :
  forall rho left_child right_child left_local right_local,
    query_outcome_rename_transport rho left_child right_child ->
    (forall left_rows right_rows,
      query_rows_rename rho left_rows right_rows ->
      query_outcome_rename_transport rho
        (left_local left_rows) (right_local right_rows)) ->
    query_outcome_rename_transport rho
      (query_unary_outcome_lift left_child left_local)
      (query_unary_outcome_lift right_child right_local).
Proof.
intros rho left_child right_child left_local right_local
  [Hchild_forward [Hchild_backward Hchild_errors]] Hlocal.
split.
- intros left_rows Hleft; inversion Hleft; subst.
  destruct (Hchild_forward _ H) as [right_input [Hright_input Hrows]].
  destruct (proj1 (Hlocal _ _ Hrows) _ H0)
    as [right_rows [Hright_rows Hrenamed]].
  exists right_rows; split; [|exact Hrenamed].
  now apply QueryUnaryLiftLocal with (rows := right_input).
- split.
  + intros right_rows Hright; inversion Hright; subst.
    destruct (Hchild_backward _ H) as [left_input [Hleft_input Hrows]].
    destruct (proj1 (proj2 (Hlocal _ _ Hrows)) _ H0)
      as [left_rows [Hleft_rows Hrenamed]].
    exists left_rows; split; [|exact Hrenamed].
    now apply QueryUnaryLiftLocal with (rows := left_input).
  + intro error; split; intro Herror; inversion Herror; subst.
    * apply QueryUnaryLiftChildError.
      now apply (proj1 (Hchild_errors error)).
    * destruct (Hchild_forward _ H)
        as [right_rows [Hright_rows Hrenamed]].
      apply QueryUnaryLiftLocal with (rows := right_rows); [exact Hright_rows|].
      exact (proj1 ((proj2 (proj2 (Hlocal _ _ Hrenamed))) error) H0).
    * apply QueryUnaryLiftChildError.
      now apply (proj2 (Hchild_errors error)).
    * destruct (Hchild_backward _ H)
        as [left_rows [Hleft_rows Hrenamed]].
      apply QueryUnaryLiftLocal with (rows := left_rows); [exact Hleft_rows|].
      exact (proj2 ((proj2 (proj2 (Hlocal _ _ Hrenamed))) error) H0).
Qed.

Lemma query_binary_outcome_lift_error_iff :
  forall left_child right_child local error,
    query_binary_outcome_lift left_child right_child local
      (SqlError error) <->
    left_child (SqlError error) \/
    (exists left_rows,
      left_child (SqlSuccess left_rows) /\
      right_child (SqlError error)) \/
    (exists left_rows right_rows,
      left_child (SqlSuccess left_rows) /\
      right_child (SqlSuccess right_rows) /\
      local left_rows right_rows (SqlError error)).
Proof.
intros left_child right_child local error; split; intro Herror.
- inversion Herror; subst.
  + now left.
  + right; left; eauto.
  + right; right; eauto.
- destruct Herror as
    [Hleft
    | [[left_rows [Hleft Hright]]
      | [left_rows [right_rows [Hleft [Hright Hlocal]]]]]].
  + now apply QueryBinaryLiftLeftError.
  + now apply QueryBinaryLiftRightError with (left_rows := left_rows).
  + now apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows).
Qed.

Lemma query_binary_outcome_lift_transport :
  forall rho left_child left_child' right_child right_child'
      left_local right_local,
    query_outcome_rename_transport rho left_child left_child' ->
    query_outcome_rename_transport rho right_child right_child' ->
    (forall left_rows left_rows' right_rows right_rows',
      query_rows_rename rho left_rows left_rows' ->
      query_rows_rename rho right_rows right_rows' ->
      query_outcome_rename_transport rho
        (left_local left_rows right_rows)
        (right_local left_rows' right_rows')) ->
    query_outcome_rename_transport rho
      (query_binary_outcome_lift left_child right_child left_local)
      (query_binary_outcome_lift left_child' right_child' right_local).
Proof.
intros rho left_child left_child' right_child right_child'
  left_local right_local
  [Hleft_forward [Hleft_backward Hleft_errors]]
  [Hright_forward [Hright_backward Hright_errors]] Hlocal.
split.
- intros output Houtput; inversion Houtput; subst.
  destruct (Hleft_forward _ H) as [left_rows' [Hleft' Hleft_rows]].
  destruct (Hright_forward _ H0) as [right_rows' [Hright' Hright_rows]].
  destruct (proj1 (Hlocal _ _ _ _ Hleft_rows Hright_rows) _ H1)
    as [output' [Houtput' Hrenamed]].
  exists output'; split; [|exact Hrenamed].
  now apply QueryBinaryLiftLocal with
    (left_rows := left_rows') (right_rows := right_rows').
- split.
  + intros output Houtput; inversion Houtput; subst.
    destruct (Hleft_backward _ H)
      as [source_left_rows [Hleft Hleft_rows]].
    destruct (Hright_backward _ H0)
      as [source_right_rows [Hright Hright_rows]].
    destruct (proj1 (proj2
      (Hlocal _ _ _ _ Hleft_rows Hright_rows)) _ H1)
      as [output' [Houtput' Hrenamed]].
    exists output'; split; [|exact Hrenamed].
    now apply QueryBinaryLiftLocal with
      (left_rows := source_left_rows) (right_rows := source_right_rows).
  + intro error; rewrite 2 query_binary_outcome_lift_error_iff.
    split; intro Herror.
    * destruct Herror as
        [Hleft_error
        | [[left_rows [Hleft Hright_error]]
          | [left_rows [right_rows [Hleft [Hright Hlocal_error]]]]]].
      -- left. now apply (proj1 (Hleft_errors error)).
      -- right; left.
         destruct (Hleft_forward _ Hleft) as [left_rows' [Hleft' _]].
         exists left_rows'; split; [exact Hleft'|].
         now apply (proj1 (Hright_errors error)).
      -- right; right.
         destruct (Hleft_forward _ Hleft)
           as [left_rows' [Hleft' Hleft_rows]].
         destruct (Hright_forward _ Hright)
           as [right_rows' [Hright' Hright_rows]].
         exists left_rows', right_rows'; repeat split; try assumption.
         exact (proj1 ((proj2 (proj2
           (Hlocal _ _ _ _ Hleft_rows Hright_rows))) error) Hlocal_error).
    * destruct Herror as
        [Hleft_error
        | [[left_rows' [Hleft' Hright_error]]
          | [left_rows' [right_rows' [Hleft' [Hright' Hlocal_error]]]]]].
      -- left. now apply (proj2 (Hleft_errors error)).
      -- right; left.
         destruct (Hleft_backward _ Hleft') as [left_rows [Hleft _]].
         exists left_rows; split; [exact Hleft|].
         now apply (proj2 (Hright_errors error)).
      -- right; right.
         destruct (Hleft_backward _ Hleft')
           as [left_rows [Hleft Hleft_rows]].
         destruct (Hright_backward _ Hright')
           as [right_rows [Hright Hright_rows]].
         exists left_rows, right_rows; repeat split; try assumption.
         exact (proj2 ((proj2 (proj2
           (Hlocal _ _ _ _ Hleft_rows Hright_rows))) error) Hlocal_error).
Qed.

Lemma query_outcome_rename_transport_congr :
  forall rho left left' right right',
    (forall outcome, left outcome <-> left' outcome) ->
    (forall outcome, right outcome <-> right' outcome) ->
    query_outcome_rename_transport rho left right ->
    query_outcome_rename_transport rho left' right'.
Proof.
intros rho left left' right right' Hleft Hright
  [Hforward [Hbackward Herrors]].
split.
- intros rows Hrows.
  destruct (Hforward rows (proj2 (Hleft _) Hrows))
    as [rows' [Hrows' Hrenamed]].
  exists rows'; split; [now apply (proj1 (Hright _))|exact Hrenamed].
- split.
  + intros rows Hrows.
    destruct (Hbackward rows (proj2 (Hright _) Hrows))
      as [rows' [Hrows' Hrenamed]].
    exists rows'; split; [now apply (proj1 (Hleft _))|exact Hrenamed].
  + intro error; rewrite <- Hleft, <- Hright; apply Herrors.
Qed.

Definition query_unary_local_rename_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_local right_local :
      Env.env T -> list tuple -> sql_outcome (list tuple) -> Prop) : Prop :=
  forall left_env right_env left_rows right_rows,
    environment_relation left_env right_env ->
    query_rows_rename rho left_rows right_rows ->
    query_outcome_rename_transport rho
      (left_local left_env left_rows)
      (right_local right_env right_rows).

Definition query_binary_local_rename_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_local right_local :
      Env.env T -> list tuple -> list tuple ->
      sql_outcome (list tuple) -> Prop) : Prop :=
  forall left_env right_env left_rows left_rows' right_rows right_rows',
    environment_relation left_env right_env ->
    query_rows_rename rho left_rows left_rows' ->
    query_rows_rename rho right_rows right_rows' ->
    query_outcome_rename_transport rho
      (left_local left_env left_rows right_rows)
      (right_local right_env left_rows' right_rows').

Lemma query_unary_constructor_rename_transport :
  forall environment_relation rho child child' outer outer'
      left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_rename_transport_under environment_relation rho child child' ->
    query_unary_local_rename_compatible
      environment_relation rho left_local right_local ->
    (forall env outcome,
      eval_query env outer outcome <->
      query_unary_outcome_lift
        (eval_query env child) (left_local env) outcome) ->
    (forall env outcome,
      eval_query env outer' outcome <->
      query_unary_outcome_lift
        (eval_query env child') (right_local env) outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
Proof.
intros environment_relation rho child child' outer outer'
  left_local right_local Hschema [Hchild_schema Hchild]
  Hlocal Hleft_eval Hright_eval.
split; [exact Hschema|].
intros left_env right_env Henvironment.
eapply query_outcome_rename_transport_congr.
- intro outcome; symmetry; apply Hleft_eval.
- intro outcome; symmetry; apply Hright_eval.
- eapply query_unary_outcome_lift_transport.
  + exact (Hchild _ _ Henvironment).
  + intros left_rows right_rows Hrows.
    exact (Hlocal _ _ _ _ Henvironment Hrows).
Qed.

Lemma query_binary_constructor_rename_transport :
  forall environment_relation rho
      left left' right right' outer outer' left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible
      environment_relation rho left_local right_local ->
    (forall env outcome,
      eval_query env outer outcome <->
      query_binary_outcome_lift
        (eval_query env left) (eval_query env right)
        (left_local env) outcome) ->
    (forall env outcome,
      eval_query env outer' outcome <->
      query_binary_outcome_lift
        (eval_query env left') (eval_query env right')
        (right_local env) outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
Proof.
intros environment_relation rho left left' right right' outer outer'
  left_local right_local Hschema [_ Hleft] [_ Hright]
  Hlocal Hleft_eval Hright_eval.
split; [exact Hschema|].
intros left_env right_env Henvironment.
eapply query_outcome_rename_transport_congr.
- intro outcome; symmetry; apply Hleft_eval.
- intro outcome; symmetry; apply Hright_eval.
- eapply query_binary_outcome_lift_transport.
  + exact (Hleft _ _ Henvironment).
  + exact (Hright _ _ Henvironment).
  + intros left_rows left_rows' right_rows right_rows' Hleft_rows Hright_rows.
    exact (Hlocal _ _ _ _ _ _ Henvironment Hleft_rows Hright_rows).
Qed.

(** Constructor-local semantics.  These relations expose exactly the metadata
    that must be transported together.  Proving a local compatibility premise
    is therefore the fail-closed obligation for attribute-observing operators. *)

Definition query_bag_source_local
    (bag : bagT) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess rows => query_same_rows_as_bag rows bag
  | SqlError _ => False
  end.

(** Mapping the concrete rows before bag construction agrees with FormalSQL's
    existing finite-bag map.  This is the reusable source law used by VALUES
    and by table transports whose database bag is explicitly renamed. *)
Lemma query_rows_bag_rename_rows :
  forall rho rows,
    bag_eq T (query_rows_bag (rename_rows rho rows))
      (rename_bag rho (query_rows_bag rows)).
Proof.
intros rho rows.
unfold bag_eq, query_rows_bag, rename_bag, rename_rows, Febag.map.
rewrite Febag.nb_occ_equal; intro target.
rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
apply _permut_map with
  (fun left right => Oeset.compare (OTuple T) left right = Eq).
- intros left right _ _ Hequal.
  now apply rename_tuple_equivalence_transport.
- apply Oeset.nb_occ_permut; intro source.
  rewrite <- Febag.nb_occ_elements, Febag.nb_occ_mk_bag.
  reflexivity.
Qed.

Lemma query_rename_bag_congr :
  forall rho left right,
    bag_eq T left right ->
    bag_eq T (rename_bag rho left) (rename_bag rho right).
Proof.
intros rho left right Hequal.
unfold bag_eq, rename_bag, Febag.map in *.
rewrite Febag.nb_occ_equal in Hequal |- *; intro target.
rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
apply _permut_map with
  (fun left_row right_row =>
    Oeset.compare (OTuple T) left_row right_row = Eq).
- intros left_row right_row _ _ Hrow.
  now apply rename_tuple_equivalence_transport.
- apply Oeset.nb_occ_permut; intro source.
  rewrite <- 2 Febag.nb_occ_elements.
  exact (Hequal source).
Qed.

(** Bag sources may expose any list representative.  Requiring every such
    source representative to satisfy actual-row collision/type safety makes
    the mapped-bag law usable without trusting declared output metadata. *)
Definition query_bag_source_rename_safe
    (rho : attribute T -> attribute T) (bag : bagT) : Prop :=
  forall rows,
    query_same_rows_as_bag rows bag ->
    rows_rename_collision_safe rho rows /\
    rows_rename_type_safe rho rows.

Lemma query_same_rows_as_bag_rename_rows :
  forall (rho : attribute T -> attribute T)
      (rows : list tuple) (bag : bagT),
    query_same_rows_as_bag rows bag ->
    query_same_rows_as_bag (rename_rows rho rows) (rename_bag rho bag).
Proof.
intros rho rows bag Hrows.
unfold query_same_rows_as_bag in Hrows |- *.
change (bag_eq T (query_rows_bag rows) bag) in Hrows.
change (bag_eq T (query_rows_bag (rename_rows rho rows))
  (rename_bag rho bag)).
eapply bag_eq_trans.
- apply query_rows_bag_rename_rows.
- now apply query_rename_bag_congr.
Qed.

Lemma query_bag_source_renamed_rows_preimage :
  forall (rho : attribute T -> attribute T)
      (bag : bagT) (right_rows : list tuple),
    query_same_rows_as_bag right_rows (rename_bag rho bag) ->
    exists left_rows,
      query_same_rows_as_bag left_rows bag /\
      rows_rename_equiv rho left_rows right_rows.
Proof.
intros rho bag right_rows Hright.
set (source := Febag.elements BTupleT bag).
assert (Hsource : query_same_rows_as_bag source bag).
{ unfold source; apply query_elements_same_rows_as_bag. }
apply query_same_rows_as_bag_iff_bag_eq in Hright.
assert (Hbags : bag_eq T
  (rows_bag T (rename_rows rho source)) (rows_bag T right_rows)).
{
  eapply bag_eq_trans.
  - unfold rows_bag.
    apply query_rows_bag_rename_rows.
  - eapply bag_eq_trans.
    + apply query_rename_bag_congr.
      unfold source; apply rows_bag_elements.
    + now apply bag_eq_sym.
}
destruct (bag_eq_rows_has_concrete_alignment
  (rename_rows rho source) right_rows Hbags)
  as [aligned [Hpermutation Hordered]].
unfold rename_rows in Hpermutation.
destruct (Permutation_map_inv (rename_tuple T rho) source
  (Permutation_sym Hpermutation))
  as [left_rows [Haligned Hleft_permutation]].
exists left_rows; split.
- eapply query_same_rows_as_bag_transport.
  + exact Hsource.
  + now apply concrete_permutation_rows_bag_eq.
- apply rows_rename_equiv_of_canonical_ordered.
  unfold rename_rows; rewrite <- Haligned.
  now apply ordered_rows_equiv_sym.
Qed.

Theorem query_bag_source_local_rename_transport :
  forall rho left_bag right_bag,
    query_bag_source_rename_safe rho left_bag ->
    bag_eq T right_bag (rename_bag rho left_bag) ->
    query_outcome_rename_transport rho
      (query_bag_source_local left_bag)
      (query_bag_source_local right_bag).
Proof.
intros rho left_bag right_bag Hsafe Hbags.
split.
- intros left_rows Hleft.
  exists (rename_rows rho left_rows); split.
  + eapply query_same_rows_as_bag_bag_transport with
      (first := rename_bag rho left_bag).
    * exact (@query_same_rows_as_bag_rename_rows
        rho left_rows left_bag Hleft).
    * now apply bag_eq_sym.
  + unfold query_rows_rename.
    destruct (Hsafe left_rows Hleft) as [Hcollision Htypes].
    now apply rows_rename_sound_canonical.
- split.
  + intros right_rows Hright.
    assert (Hmapped :
      query_same_rows_as_bag right_rows (rename_bag rho left_bag)).
    {
      eapply query_same_rows_as_bag_bag_transport;
        [exact Hright | exact Hbags].
    }
    destruct (@query_bag_source_renamed_rows_preimage rho left_bag
      right_rows Hmapped) as [left_rows [Hleft Hrows]].
    exists left_rows; split; [exact Hleft|].
    unfold query_rows_rename.
    destruct (Hsafe left_rows Hleft) as [Hcollision Htypes].
    now repeat split.
  + intro error; reflexivity.
Qed.

Definition query_error_source_local
    (error : sql_runtime_error)
    (outcome : sql_outcome (list tuple)) : Prop :=
  outcome = SqlError error.

Lemma query_source_constructor_rename_transport :
  forall environment_relation rho outer outer' left_local right_local,
    query_rename_schema_compatible rho outer outer' ->
    query_outcome_rename_transport rho left_local right_local ->
    (forall env outcome, eval_query env outer outcome <-> left_local outcome) ->
    (forall env outcome, eval_query env outer' outcome <-> right_local outcome) ->
    query_rename_transport_under environment_relation rho outer outer'.
Proof.
intros environment_relation rho outer outer' left_local right_local
  Hschema Hlocal Hleft Hright.
split; [exact Hschema|].
intros left_env right_env _.
eapply query_outcome_rename_transport_congr.
- intro outcome; symmetry; apply Hleft.
- intro outcome; symmetry; apply Hright.
- exact Hlocal.
Qed.

Lemma eval_query_error_source_iff :
  forall env outputs error outcome,
    eval_query env (QExpr_Error outputs error) outcome <->
    query_error_source_local error outcome.
Proof.
intros env outputs error outcome; split; intro Heval.
- inversion Heval; reflexivity.
- unfold query_error_source_local in Heval; subst outcome; constructor.
Qed.

Lemma eval_query_values_source_iff :
  forall env outputs values outcome,
    eval_query env (QExpr_Values outputs values) outcome <->
    query_bag_source_local values outcome.
Proof.
intros env outputs values [rows | error]; split; intro Heval.
- inversion Heval; assumption.
- now constructor.
- inversion Heval.
- contradiction.
Qed.

Lemma eval_query_table_source_iff :
  forall env outputs table outcome,
    eval_query env (QExpr_Table outputs table) outcome <->
    query_bag_source_local (query_table_bag basesort instance outputs table)
      outcome.
Proof.
intros env outputs table [rows | error]; split; intro Heval.
- inversion Heval; assumption.
- now constructor.
- inversion Heval.
- contradiction.
Qed.

(** [QExpr_Error] is unconditional once its mapped schema is proved.  The
    opaque error category is retained exactly. *)
Theorem QExpr_Error_rename_transport :
  forall environment_relation rho left_outputs right_outputs error,
    query_rename_schema_compatible rho
      (QExpr_Error left_outputs error) (QExpr_Error right_outputs error) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Error left_outputs error) (QExpr_Error right_outputs error).
Proof.
intros environment_relation rho left_outputs right_outputs error Hschema.
eapply query_source_constructor_rename_transport with
  (left_local := query_error_source_local error)
  (right_local := query_error_source_local error);
  [exact Hschema| | |].
- unfold query_outcome_rename_transport, query_error_source_local.
  split.
  + intros rows H; change (SqlSuccess rows = SqlError error) in H;
      discriminate H.
  + split.
    * intros rows H; change (SqlSuccess rows = SqlError error) in H;
        discriminate H.
    * intro observed_error; reflexivity.
- intros env outcome; apply eval_query_error_source_iff.
- intros env outcome; apply eval_query_error_source_iff.
Qed.

(** VALUES transport requires every occurrence of the source bag to be mapped;
    this premise is where collision-free multiplicity preservation is used. *)
Theorem QExpr_Values_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_values right_values,
    query_rename_schema_compatible rho
      (QExpr_Values left_outputs left_values)
      (QExpr_Values right_outputs right_values) ->
    query_bag_source_rename_safe rho left_values ->
    bag_eq T right_values (rename_bag rho left_values) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Values left_outputs left_values)
      (QExpr_Values right_outputs right_values).
Proof.
intros environment_relation rho left_outputs right_outputs
  left_values right_values Hschema Hsafe Hbags.
pose proof (@query_bag_source_local_rename_transport
  rho left_values right_values Hsafe Hbags) as Hvalues.
eapply query_source_constructor_rename_transport with
  (left_local := query_bag_source_local left_values)
  (right_local := query_bag_source_local right_values); try eassumption;
  intros env outcome; apply eval_query_values_source_iff.
Qed.

(** A table scan is conditional on a transported database relation.  Relabeling
    [outputs] while retaining the same [basesort]/[instance] is not asserted to
    commute: [query_table_bag] would otherwise change its schema check or leave
    instance rows unrenamed. *)
Theorem QExpr_Table_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_table right_table,
    query_rename_schema_compatible rho
      (QExpr_Table left_outputs left_table)
      (QExpr_Table right_outputs right_table) ->
    query_bag_source_rename_safe rho
      (query_table_bag basesort instance left_outputs left_table) ->
    bag_eq T
      (query_table_bag basesort instance right_outputs right_table)
      (rename_bag rho
        (query_table_bag basesort instance left_outputs left_table)) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Table left_outputs left_table)
      (QExpr_Table right_outputs right_table).
Proof.
intros environment_relation rho left_outputs right_outputs
  left_table right_table Hschema Hsafe Hbags.
pose proof (@query_bag_source_local_rename_transport rho
  (query_table_bag basesort instance left_outputs left_table)
  (query_table_bag basesort instance right_outputs right_table)
  Hsafe Hbags) as Htables.
eapply query_source_constructor_rename_transport with
  (left_local := query_bag_source_local
    (query_table_bag basesort instance left_outputs left_table))
  (right_local := query_bag_source_local
    (query_table_bag basesort instance right_outputs right_table));
  try eassumption; intros env outcome; apply eval_query_table_source_iff.
Qed.

Definition query_set_local
    (operation : set_op) (left right : query_expr T relname)
    (left_rows right_rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess output =>
      query_same_rows_as_bag output
        (if query_expr_sort left =S?= query_expr_sort right
         then query_set_bag operation
                (query_rows_bag left_rows) (query_rows_bag right_rows)
         else Febag.empty BTupleT)
  | SqlError _ => False
  end.

Definition query_natural_join_local
    (left_rows right_rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess output =>
      query_same_rows_as_bag output
        (query_natural_join_bag value_is_null
          (query_rows_bag left_rows) (query_rows_bag right_rows))
  | SqlError _ => False
  end.

Definition query_cross_join_local
    (left_rows right_rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess output =>
      query_same_rows_as_bag output
        (query_cross_join_bag
          (query_rows_bag left_rows) (query_rows_bag right_rows))
  | SqlError _ => False
  end.

Definition query_join_local
    (env : Env.env T) (kind : query_join_kind)
    (predicate : scalar_expr T relname ScalarResultBoolean)
    (matched_select left_select right_select : @query_select_list T relname)
    (left_rows right_rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlError error =>
      @eval_join_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
        kind predicate matched_select left_select right_select
        (query_rows_bag left_rows) (query_rows_bag right_rows)
        (SqlError error)
  | SqlSuccess output =>
      exists output_bag,
        @eval_join_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
          kind predicate matched_select left_select right_select
          (query_rows_bag left_rows) (query_rows_bag right_rows)
          (SqlSuccess output_bag) /\
        query_same_rows_as_bag output output_bag
  end.

Definition query_project_local
    (env : Env.env T) (select_list : @query_select_list T relname)
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  @eval_project_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null
    boolean_schedule env select_list rows outcome.

Definition query_row_map_local
    (row_map : tuple -> sql_outcome tuple)
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  outcome = row_map_rows_outcome row_map rows.

Definition query_filter_local
    (env : Env.env T) (expression : scalar_expr T relname ScalarResultBoolean)
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  @eval_filter_rows_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule
    env expression rows outcome.

Definition query_group_local
    (env : Env.env T) (select_list : @query_select_list T relname)
    (group_keys : list (scalar_expr T relname ScalarResultValue))
    (having : scalar_expr T relname ScalarResultBoolean)
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlError error =>
      @eval_group_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
        select_list group_keys having (query_rows_bag rows)
        (SqlError error)
  | SqlSuccess output =>
      exists output_bag,
        @eval_group_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
          select_list group_keys having (query_rows_bag rows)
          (SqlSuccess output_bag) /\
        query_same_rows_as_bag output output_bag
  end.

Definition query_grouping_sets_local
    (env : Env.env T)
    (grouping_sets : list (@query_grouping_set T relname))
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlError error =>
      @eval_grouping_sets_bag_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
        grouping_sets (query_rows_bag rows) (SqlError error)
  | SqlSuccess output =>
      exists output_bag,
        @eval_grouping_sets_bag_outcome T relname basesort instance unknown
          symbol_runtime_error aggregate_runtime_error value_is_null boolean_schedule env
          grouping_sets (query_rows_bag rows) (SqlSuccess output_bag) /\
        query_same_rows_as_bag output output_bag
  end.

Definition query_rank_local
    (partition_keys order_keys : list (sort_key T))
    (rank_attribute : attribute T)
    (rank_value : nat -> option value)
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  let canonical := query_rank_bag_rows (query_rows_bag rows) in
  match outcome with
  | SqlError (DataException NumericValueOutOfRange) =>
      @query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute
        rank_value canonical canonical = None
  | SqlError _ => False
  | SqlSuccess output =>
      exists ranked_rows,
        @query_rank_rows_outcome T value_is_null
          partition_keys order_keys rank_attribute
          rank_value canonical canonical = Some ranked_rows /\
        query_same_rows_as_bag output (query_rows_bag ranked_rows)
  end.

Definition query_window_local
    (env : Env.env T)
    (partition_keys order_keys : list (sort_key T))
    (items : list (query_window_item T))
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlError error =>
      exists ordered_rows,
        order_by_rows value_is_null (partition_keys ++ order_keys)
          (query_rank_bag_rows (query_rows_bag rows)) ordered_rows /\
        @query_window_rows_outcome T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys items None 0 nil ordered_rows =
          Some (SqlError error)
  | SqlSuccess output =>
      exists ordered_rows window_rows,
        order_by_rows value_is_null (partition_keys ++ order_keys)
          (query_rank_bag_rows (query_rows_bag rows)) ordered_rows /\
        @query_window_rows_outcome T symbol_runtime_error
          aggregate_runtime_error value_is_null env
          partition_keys items None 0 nil ordered_rows =
          Some (SqlSuccess window_rows) /\
        query_same_rows_as_bag output (query_rows_bag window_rows)
  end.

Definition query_distinct_local
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess output =>
      query_same_rows_as_bag output
        (query_distinct_bag (query_rows_bag rows))
  | SqlError _ => False
  end.

Definition query_order_by_local
    (keys : list (sort_key T))
    (rows : list tuple) (outcome : sql_outcome (list tuple)) : Prop :=
  match outcome with
  | SqlSuccess output => order_by_rows value_is_null keys rows output
  | SqlError _ => False
  end.

Definition query_offset_local
    (offset : nat) (rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  outcome = SqlSuccess (skipn offset rows).

Definition query_fetch_local
    (count : nat) (rows : list tuple)
    (outcome : sql_outcome (list tuple)) : Prop :=
  outcome = SqlSuccess (firstn count rows).

Lemma eval_query_set_binary_lift_iff :
  forall env operation left right outcome,
    eval_query env (QExpr_Set operation left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      (query_set_local operation left right) outcome.
Proof.
intros env operation left right outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryBinaryLiftLeftError.
  + now apply QueryBinaryLiftRightError with (left_rows := left_rows).
  + apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows); try assumption.
- inversion Heval; subst.
  + now apply EQuery_SetLeftError.
  + now apply EQuery_SetRightError with (left_rows := left_rows).
  + destruct outcome as [output | error];
      unfold query_set_local in H1; [|contradiction].
    now apply EQuery_SetSuccess with
      (left_rows := left_rows) (right_rows := right_rows).
Qed.

Lemma eval_query_natural_join_binary_lift_iff :
  forall env left right outcome,
    eval_query env (QExpr_NaturalJoin left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      query_natural_join_local outcome.
Proof.
intros env left right outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryBinaryLiftLeftError.
  + now apply QueryBinaryLiftRightError with (left_rows := left_rows).
  + apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows); try assumption.
- inversion Heval; subst.
  + now apply EQuery_NaturalJoinLeftError.
  + now apply EQuery_NaturalJoinRightError with (left_rows := left_rows).
  + destruct outcome as [output | error];
      unfold query_natural_join_local in H1; [|contradiction].
    now apply EQuery_NaturalJoinSuccess with
      (left_rows := left_rows) (right_rows := right_rows).
Qed.

Lemma eval_query_cross_join_binary_lift_iff :
  forall env left right outcome,
    eval_query env (QExpr_CrossJoin left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      query_cross_join_local outcome.
Proof.
intros env left right outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryBinaryLiftLeftError.
  + now apply QueryBinaryLiftRightError with (left_rows := left_rows).
  + apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows); try assumption.
- inversion Heval; subst.
  + now apply EQuery_CrossJoinLeftError.
  + now apply EQuery_CrossJoinRightError with (left_rows := left_rows).
  + destruct outcome as [output | error];
      unfold query_cross_join_local in H1; [|contradiction].
    now apply EQuery_CrossJoinSuccess with
      (left_rows := left_rows) (right_rows := right_rows).
Qed.

Lemma eval_query_join_binary_lift_iff :
  forall env kind predicate matched_select left_select right_select
      left right outcome,
    eval_query env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) outcome <->
    query_binary_outcome_lift
      (eval_query env left) (eval_query env right)
      (query_join_local env kind predicate
        matched_select left_select right_select) outcome.
Proof.
intros env kind predicate matched_select left_select right_select
  left right outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryBinaryLiftLeftError.
  + now apply QueryBinaryLiftRightError with (left_rows := left_rows).
  + apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows); try assumption.
  + apply QueryBinaryLiftLocal with
      (left_rows := left_rows) (right_rows := right_rows); try assumption.
    exists output_bag; now split.
- inversion Heval; subst.
  + now apply EQuery_JoinLeftError.
  + now apply EQuery_JoinRightError with (left_rows := left_rows).
  + destruct outcome as [output | error].
    * unfold query_join_local in H1.
      destruct H1 as [output_bag [Hbag Houtput]].
      now apply EQuery_JoinSuccess with
        (left_rows := left_rows) (right_rows := right_rows)
        (output_bag := output_bag).
    * unfold query_join_local in H1.
      now apply EQuery_JoinBagError with
        (left_rows := left_rows) (right_rows := right_rows).
Qed.

(** Set operations observe both child schemas before applying the bag operator.
    Declared-sort injection is required, but malformed source bags can contain
    additional cross-child labels; the exact binary-local premise is therefore
    the explicit fail-closed proof of their UNION/INTERSECT/EXCEPT behavior. *)
Theorem QExpr_Set_rename_transport :
  forall environment_relation rho operation left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_set_local operation left right)
      (fun _ => query_set_local operation left' right') ->
    query_rename_transport_under environment_relation rho
      (QExpr_Set operation left right)
      (QExpr_Set operation left' right').
Proof.
intros environment_relation rho operation left left' right right'
  _ Hschema Hleft Hright Hlocal.
eapply query_binary_constructor_rename_transport with
  (left := left) (left' := left') (right := right) (right' := right')
  (left_local := fun _ => query_set_local operation left right)
  (right_local := fun _ => query_set_local operation left' right');
  try eassumption;
  intros env outcome; apply eval_query_set_binary_lift_iff.
Qed.

(** The local premise is the current NULL-aware NATURAL JOIN contract, not the
    older raw-value [rename_join] lemma.  It must prove common-label matching,
    NULL rejection, output order, and actual-row cross-input collision safety;
    declared union injection alone is not used as a database-row invariant. *)
Theorem QExpr_NaturalJoin_rename_transport :
  forall environment_relation rho left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_NaturalJoin left right) (QExpr_NaturalJoin left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_natural_join_local)
      (fun _ => query_natural_join_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_NaturalJoin left right) (QExpr_NaturalJoin left' right').
Proof.
intros environment_relation rho left left' right right'
  _ Hschema Hleft Hright Hlocal.
eapply query_binary_constructor_rename_transport with
  (left := left) (left' := left') (right := right) (right' := right')
  (left_local := fun _ => query_natural_join_local)
  (right_local := fun _ => query_natural_join_local);
  try eassumption;
  intros env outcome; apply eval_query_natural_join_binary_lift_iff.
Qed.

(** CROSS JOIN additionally exposes left-biased tuple construction.  Source
    and target schemas remain disjoint and union-injective, while the exact
    local premise separately fails closed on malformed actual rows whose labels
    are not covered by those declared schemas. *)
Theorem QExpr_CrossJoin_rename_transport :
  forall environment_relation rho left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    @query_output_sorts_disjoint T
      (query_expr_sort left) (query_expr_sort right) ->
    @query_output_sorts_disjoint T
      (query_expr_sort left') (query_expr_sort right') ->
    query_rename_schema_compatible rho
      (QExpr_CrossJoin left right) (QExpr_CrossJoin left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_binary_local_rename_compatible environment_relation rho
      (fun _ => query_cross_join_local)
      (fun _ => query_cross_join_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_CrossJoin left right) (QExpr_CrossJoin left' right').
Proof.
intros environment_relation rho left left' right right'
  _ _ _ Hschema Hleft Hright Hlocal.
eapply query_binary_constructor_rename_transport with
  (left := left) (left' := left') (right := right) (right' := right')
  (left_local := fun _ => query_cross_join_local)
  (right_local := fun _ => query_cross_join_local);
  try eassumption;
  intros env outcome; apply eval_query_cross_join_binary_lift_iff.
Qed.

(** Shared-child joins are conditional on one compatibility proof for the predicate,
    all three kind-dependent projection lists and aliases, both child bags,
    exact Bool3 decisions, projected rows, and every local runtime error. *)
Theorem QExpr_Join_rename_transport :
  forall environment_relation rho kind
      left_predicate right_predicate
      left_matched left_left_select left_right_select
      right_matched right_left_select right_right_select
      left left' right right',
    attribute_rename_injective_on
      (query_expr_sort left unionS query_expr_sort right) rho ->
    query_rename_schema_compatible rho
      (QExpr_Join kind left_predicate
        left_matched left_left_select left_right_select left right)
      (QExpr_Join kind right_predicate
        right_matched right_left_select right_right_select left' right') ->
    query_rename_transport_under environment_relation rho left left' ->
    query_rename_transport_under environment_relation rho right right' ->
    query_scalar_expr_outcome_rename_compatible
      (query_join_environment_rename environment_relation rho)
      left_predicate right_predicate ->
    query_binary_local_rename_compatible environment_relation rho
      (fun env => query_join_local env kind left_predicate
        left_matched left_left_select left_right_select)
      (fun env => query_join_local env kind right_predicate
        right_matched right_left_select right_right_select) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Join kind left_predicate
        left_matched left_left_select left_right_select left right)
      (QExpr_Join kind right_predicate
        right_matched right_left_select right_right_select left' right').
Proof.
intros environment_relation rho kind
  left_predicate right_predicate
  left_matched left_left_select left_right_select
  right_matched right_left_select right_right_select
  left left' right right' _ Hschema Hleft Hright _ Hlocal.
eapply query_binary_constructor_rename_transport with
  (left := left) (left' := left') (right := right) (right' := right')
  (left_local := fun env => query_join_local env kind left_predicate
    left_matched left_left_select left_right_select)
  (right_local := fun env => query_join_local env kind right_predicate
    right_matched right_left_select right_right_select);
  try eassumption;
  intros env outcome; apply eval_query_join_binary_lift_iff.
Qed.

Lemma eval_query_project_unary_lift_iff :
  forall env select_list input outcome,
    eval_query env (QExpr_Project select_list input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_project_local env select_list) outcome.
Proof.
intros env select_list input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + apply QueryUnaryLiftLocal with (rows := input_rows); assumption.
- inversion Heval; subst.
  + now apply EQuery_ProjectChildError.
  + eapply EQuery_ProjectRows with (input_rows := rows); eassumption.
Qed.

Lemma eval_query_row_map_unary_lift_iff :
  forall env outputs row_map input outcome,
    eval_query env (QExpr_RowMap outputs row_map input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_row_map_local row_map rows) outcome.
Proof.
intros env outputs row_map input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|reflexivity].
- inversion Heval; subst.
  + now apply EQuery_RowMapChildError.
  + unfold query_row_map_local in H0; subst outcome.
    now apply EQuery_RowMapRows.
Qed.

Lemma eval_query_filter_unary_lift_iff :
  forall env expression input outcome,
    eval_query env (QExpr_Filter expression input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_filter_local env expression) outcome.
Proof.
intros env expression input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
- inversion Heval; subst.
  + now apply EQuery_FilterChildError.
  + now apply EQuery_FilterRows with (input_rows := rows).
Qed.

Lemma eval_query_group_unary_lift_iff :
  forall env select_list group_terms having input outcome,
    eval_query env (QExpr_Group select_list group_terms having input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_group_local env select_list group_terms having) outcome.
Proof.
intros env select_list group_terms having input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|].
    exists output_bag; now split.
- inversion Heval; subst.
  + now apply EQuery_GroupChildError.
  + destruct outcome as [output | error].
    * unfold query_group_local in H0.
      destruct H0 as [output_bag [Hbag Houtput]].
      now apply EQuery_GroupBagSuccess with
        (input_rows := rows) (output_bag := output_bag).
    * unfold query_group_local in H0.
      now apply EQuery_GroupBagError with (input_rows := rows).
Qed.

Lemma eval_query_grouping_sets_unary_lift_iff :
  forall env grouping_sets input outcome,
    eval_query env (QExpr_GroupingSets grouping_sets input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_grouping_sets_local env grouping_sets) outcome.
Proof.
intros env grouping_sets input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|].
    exists output_bag; now split.
- inversion Heval; subst.
  + now apply EQuery_GroupingSetsChildError.
  + destruct outcome as [output | error].
    * unfold query_grouping_sets_local in H0.
      destruct H0 as [output_bag [Hbag Houtput]].
      now apply EQuery_GroupingSetsSuccess with
        (input_rows := rows) (output_bag := output_bag).
    * unfold query_grouping_sets_local in H0.
      now apply EQuery_GroupingSetsBagError with (input_rows := rows).
Qed.

Lemma eval_query_rank_unary_lift_iff :
  forall env partition_keys order_keys rank_attribute rank_value input outcome,
    eval_query env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_rank_local partition_keys order_keys rank_attribute rank_value)
      outcome.
Proof.
intros env partition_keys order_keys rank_attribute rank_value input outcome;
  split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|].
    exists ranked_rows; now split.
- inversion Heval; subst.
  + now apply EQuery_RankChildError.
  + destruct outcome as [output | error].
    * unfold query_rank_local in H0.
      destruct H0 as [ranked_rows [Hrank Houtput]].
      now apply EQuery_RankSuccess with
        (input_rows := rows) (ranked_rows := ranked_rows).
    * destruct error as
        [| | | | | [| | | | | | |]];
        unfold query_rank_local in H0; try contradiction.
      now apply EQuery_RankValueError with (input_rows := rows).
Qed.

Lemma eval_query_window_unary_lift_iff :
  forall env partition_keys order_keys items input outcome,
    eval_query env (QExpr_Window partition_keys order_keys items input)
      outcome <->
    query_unary_outcome_lift (eval_query env input)
      (query_window_local env partition_keys order_keys items) outcome.
Proof.
intros env partition_keys order_keys items input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|].
    exists ordered_rows; now split.
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|].
    unfold query_window_local.
    exists ordered_rows, window_rows.
    split; [eassumption|].
    split; eassumption.
- inversion Heval; subst.
  + now apply EQuery_WindowChildError.
  + destruct outcome as [output | error].
    * unfold query_window_local in H0.
      destruct H0 as
        [ordered_rows [window_rows [Horder [Hwindow Houtput]]]].
      now apply EQuery_WindowSuccess with
        (input_rows := rows) (ordered_rows := ordered_rows)
        (window_rows := window_rows).
    * unfold query_window_local in H0.
      destruct H0 as [ordered_rows [Horder Hwindow]].
      now apply EQuery_WindowRowsError with
        (input_rows := rows) (ordered_rows := ordered_rows).
Qed.

Lemma eval_query_distinct_unary_lift_iff :
  forall env input outcome,
    eval_query env (QExpr_Distinct input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      query_distinct_local outcome.
Proof.
intros env input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
- inversion Heval; subst.
  + now apply EQuery_DistinctChildError.
  + destruct outcome as [output | error];
      unfold query_distinct_local in H0; [|contradiction].
    now apply EQuery_DistinctSuccess with (input_rows := rows).
Qed.

Lemma eval_query_order_by_unary_lift_iff :
  forall env keys input outcome,
    eval_query env (QExpr_OrderBy keys input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_order_by_local keys rows) outcome.
Proof.
intros env keys input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + now apply QueryUnaryLiftLocal with (rows := input_rows).
- inversion Heval; subst.
  + now apply EQuery_OrderByChildError.
  + destruct outcome as [output | error];
      unfold query_order_by_local in H0; [|contradiction].
    now apply EQuery_OrderBySuccess with (input_rows := rows).
Qed.

Lemma eval_query_offset_unary_lift_iff :
  forall env offset input outcome,
    eval_query env (QExpr_Offset offset input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_offset_local offset rows) outcome.
Proof.
intros env offset input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|reflexivity].
- inversion Heval; subst.
  + now apply EQuery_OffsetChildError.
  + unfold query_offset_local in H0; subst outcome.
    now apply EQuery_OffsetSuccess.
Qed.

Lemma eval_query_fetch_unary_lift_iff :
  forall env count input outcome,
    eval_query env (QExpr_Fetch count input) outcome <->
    query_unary_outcome_lift (eval_query env input)
      (fun rows => query_fetch_local count rows) outcome.
Proof.
intros env count input outcome; split; intro Heval.
- inversion Heval; subst.
  + now apply QueryUnaryLiftChildError.
  + apply QueryUnaryLiftLocal with (rows := input_rows); [assumption|reflexivity].
- inversion Heval; subst.
  + now apply EQuery_FetchChildError.
  + unfold query_fetch_local in H0; subst outcome.
    now apply EQuery_FetchSuccess.
Qed.

(** The deterministic specialization retains query-level actual-row collision
    and type safety, rather than weakening successes back to the raw pointwise
    collection relation. *)
Definition query_deterministic_outcome_rename_equiv
    (rho : attribute T -> attribute T)
    (left right : sql_outcome (list tuple)) : Prop :=
  match left, right with
  | SqlSuccess left_rows, SqlSuccess right_rows =>
      query_rows_rename rho left_rows right_rows
  | SqlError left_error, SqlError right_error => left_error = right_error
  | _, _ => False
  end.

(** A single lossless deterministic pair of outcomes induces the relational
    transport interface.  Mismatched success/error shapes are rejected and
    equal SQL errors remain exact. *)
Lemma outcome_rename_equiv_deterministic_transport :
  forall rho left right,
    query_deterministic_outcome_rename_equiv rho left right ->
    query_outcome_rename_transport rho
      (fun outcome => outcome = left)
      (fun outcome => outcome = right).
Proof.
intros rho [left_rows | left_error] [right_rows | right_error] Hequiv;
  simpl in Hequiv; try contradiction.
- split.
  + intros rows Hrows; inversion Hrows; subst rows.
    exists right_rows; now split.
  + split.
    * intros rows Hrows; inversion Hrows; subst rows.
      exists left_rows; now split.
    * intro error; split; intro Herror; discriminate Herror.
- subst right_error.
  split.
  + intros rows Hrows; discriminate Hrows.
  + split.
    * intros rows Hrows; discriminate Hrows.
    * intro error; reflexivity.
Qed.

Definition query_row_map_callback_rename_compatible
    (rho : attribute T -> attribute T)
    (left_map right_map : tuple -> sql_outcome tuple) : Prop :=
  forall left_row right_row,
    rename_tuple T rho left_row =t= right_row ->
    match left_map left_row, right_map right_row with
    | SqlSuccess left_output, SqlSuccess right_output =>
        rename_tuple T rho left_output =t= right_output
    | SqlError left_error, SqlError right_error => left_error = right_error
    | _, _ => False
    end.

Lemma row_map_rows_outcome_callback_rename_equiv :
  forall rho left_map right_map,
    query_row_map_callback_rename_compatible rho left_map right_map ->
    forall left_rows right_rows,
      rows_rename_equiv rho left_rows right_rows ->
      outcome_rename_equiv rho
        (row_map_rows_outcome left_map left_rows)
        (row_map_rows_outcome right_map right_rows).
Proof.
intros rho left_map right_map Hcallback left_rows right_rows Hrows.
induction Hrows as
  [|left_row right_row left_rows right_rows Hrow Hrows IH].
- constructor.
- specialize (Hcallback left_row right_row Hrow).
  cbn [row_map_rows_outcome].
  destruct (left_map left_row) as [left_output | left_error] eqn:Hleft;
    destruct (right_map right_row) as [right_output | right_error] eqn:Hright;
    simpl in Hcallback;
    try contradiction.
  + destruct (row_map_rows_outcome left_map left_rows)
      as [left_outputs | left_tail_error] eqn:Hleft_tail;
    destruct (row_map_rows_outcome right_map right_rows)
      as [right_outputs | right_tail_error] eqn:Hright_tail;
    simpl in IH; try contradiction.
    * constructor; assumption.
    * exact IH.
  + exact Hcallback.
Qed.

(** A pointwise callback cannot by itself rule out collisions between outputs
    of two different input rows.  This separate premise is the exact fail-closed
    obligation on every successful source output list. *)
Definition query_row_map_success_rename_safe
    (rho : attribute T -> attribute T)
    (row_map : tuple -> sql_outcome tuple) : Prop :=
  forall input_rows output_rows,
    row_map_rows_outcome row_map input_rows = SqlSuccess output_rows ->
    rows_rename_collision_safe rho output_rows /\
    rows_rename_type_safe rho output_rows.

Definition query_row_map_scheduler_rename_compatible
    (rho : attribute T -> attribute T)
    (left_map right_map : tuple -> sql_outcome tuple) : Prop :=
  forall left_rows right_rows,
    query_rows_rename rho left_rows right_rows ->
    query_deterministic_outcome_rename_equiv rho
      (row_map_rows_outcome left_map left_rows)
      (row_map_rows_outcome right_map right_rows).

Lemma query_row_map_callback_rename_compatible_scheduler :
  forall rho left_map right_map,
    query_row_map_callback_rename_compatible rho left_map right_map ->
    query_row_map_success_rename_safe rho left_map ->
    query_row_map_scheduler_rename_compatible rho left_map right_map.
Proof.
intros rho left_map right_map Hcallback Hsafe
  left_rows right_rows [Hrows _].
pose proof (@row_map_rows_outcome_callback_rename_equiv
  rho left_map right_map Hcallback left_rows right_rows Hrows) as Houtcome.
destruct (row_map_rows_outcome left_map left_rows)
  as [left_output | left_error] eqn:Hleft;
destruct (row_map_rows_outcome right_map right_rows)
  as [right_output | right_error] eqn:Hright;
simpl in Houtcome |- *; try contradiction.
- split; [exact Houtcome|].
  now apply (Hsafe left_rows left_output).
- exact Houtcome.
Qed.

Lemma query_row_map_local_rename_compatible_of_scheduler :
  forall environment_relation rho left_map right_map,
    query_row_map_scheduler_rename_compatible rho left_map right_map ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_row_map_local left_map rows)
      (fun _ rows => query_row_map_local right_map rows).
Proof.
intros environment_relation rho left_map right_map Hmap
  left_env right_env left_rows right_rows _ Hrows.
unfold query_row_map_local.
apply outcome_rename_equiv_deterministic_transport.
now apply Hmap.
Qed.

Lemma query_offset_local_rename_compatible :
  forall environment_relation rho offset,
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_offset_local offset rows)
      (fun _ rows => query_offset_local offset rows).
Proof.
intros environment_relation rho offset
  left_env right_env left_rows right_rows _ Hrows.
unfold query_offset_local.
apply outcome_rename_equiv_deterministic_transport; simpl.
now apply rows_rename_sound_skipn.
Qed.

Lemma query_fetch_local_rename_compatible :
  forall environment_relation rho count,
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_fetch_local count rows)
      (fun _ rows => query_fetch_local count rows).
Proof.
intros environment_relation rho count
  left_env right_env left_rows right_rows _ Hrows.
unfold query_fetch_local.
apply outcome_rename_equiv_deterministic_transport; simpl.
now apply rows_rename_sound_firstn.
Qed.

(** Sort-key metadata is transported only when the referenced attribute is
    renamed and direction, NULL placement, and the semantic value comparator
    are retained.  Proof fields are intentionally not compared. *)
Definition query_sort_key_rename_compatible
    (rho : attribute T -> attribute T)
    (left right : sort_key T) : Prop :=
  sort_key_attribute right = rho (sort_key_attribute left) /\
  sort_key_direction right = sort_key_direction left /\
  sort_key_null_direction right = sort_key_null_direction left /\
  forall left_value right_value,
    sort_key_value_compare right left_value right_value =
    sort_key_value_compare left left_value right_value.

Definition query_sort_keys_rename_compatible
    (rho : attribute T -> attribute T)
    (left right : list (sort_key T)) : Prop :=
  Forall2 (query_sort_key_rename_compatible rho) left right.

Lemma query_sort_key_rename_compatible_identity :
  forall key,
    query_sort_key_rename_compatible
      (fun attribute => attribute) key key.
Proof.
intro key; repeat split; reflexivity.
Qed.

Lemma query_sort_keys_rename_compatible_identity :
  forall keys,
    query_sort_keys_rename_compatible
      (fun attribute => attribute) keys keys.
Proof.
intro keys; induction keys as [|key keys IH].
- constructor.
- constructor; [apply query_sort_key_rename_compatible_identity | exact IH].
Qed.

(** Projection compatibility covers every canonical typed selected-expression
    and output-alias pair, aggregate finalization, left-to-right error, and
    reachable renamed row environment.  Renaming aliases alone is
    insufficient. *)
Theorem QExpr_Project_rename_transport :
  forall environment_relation rho left_select right_select input input',
    query_rename_schema_compatible rho
      (QExpr_Project left_select input)
      (QExpr_Project right_select input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_project_local env left_select)
      (fun env => query_project_local env right_select) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Project left_select input)
      (QExpr_Project right_select input').
Proof.
intros environment_relation rho left_select right_select input input'
  Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun env => query_project_local env left_select)
  (right_local := fun env => query_project_local env right_select);
  try eassumption; intros env outcome; apply eval_query_project_unary_lift_iff.
Qed.

(** [QExpr_RowMap] is intentionally opaque, but a pointwise callback proof is
    lifted to the list scheduler above.  Cross-output collision/type safety is
    separate because no pointwise contract can compare outputs of two distinct
    source rows. *)
Theorem QExpr_RowMap_rename_transport :
  forall environment_relation rho left_outputs right_outputs
      left_map right_map input input',
    query_rename_schema_compatible rho
      (QExpr_RowMap left_outputs left_map input)
      (QExpr_RowMap right_outputs right_map input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_row_map_callback_rename_compatible rho left_map right_map ->
    query_row_map_success_rename_safe rho left_map ->
    query_rename_transport_under environment_relation rho
      (QExpr_RowMap left_outputs left_map input)
      (QExpr_RowMap right_outputs right_map input').
Proof.
intros environment_relation rho left_outputs right_outputs
  left_map right_map input input' Hschema Hinput Hcallback Hsafe.
pose proof (@query_row_map_callback_rename_compatible_scheduler
  rho left_map right_map Hcallback Hsafe) as Hscheduler.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ rows => query_row_map_local left_map rows)
  (right_local := fun _ rows => query_row_map_local right_map rows);
  try eassumption.
- now apply query_row_map_local_rename_compatible_of_scheduler.
- intros env outcome; apply eval_query_row_map_unary_lift_iff.
- intros env outcome; apply eval_query_row_map_unary_lift_iff.
Qed.

(** Filter transport requires exact expression outcomes in row-extended paired
    environments in addition to the final row scheduler.  Therefore FALSE and
    UNKNOWN cannot be exchanged merely because both fail [Bool.is_true]. *)
Theorem QExpr_Filter_rename_transport :
  forall environment_relation rho left_formula right_formula input input',
    query_rename_schema_compatible rho
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_scalar_expr_outcome_rename_compatible
      (query_row_environment_rename environment_relation rho)
      left_formula right_formula ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_filter_local env left_formula)
      (fun env => query_filter_local env right_formula) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Filter left_formula input)
      (QExpr_Filter right_formula input').
Proof.
intros environment_relation rho left_formula right_formula input input'
  Hschema Hinput _ Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun env => query_filter_local env left_formula)
  (right_local := fun env => query_filter_local env right_formula);
  try eassumption; intros env outcome; apply eval_query_filter_unary_lift_iff.
Qed.

(** GROUP transports projection aliases, group keys, and bags through its local
    scheduler, while the separate HAVING contract preserves exact Bool3
    outcomes, correlated subqueries, and the eager aggregate-error precheck. *)
Theorem QExpr_Group_rename_transport :
  forall environment_relation rho
      left_select right_select left_keys right_keys left_terms right_terms
      left_having right_having input input',
    query_rename_schema_compatible rho
      (QExpr_Group left_select left_keys left_having input)
      (QExpr_Group right_select right_keys right_having input') ->
    query_rename_transport_under environment_relation rho input input' ->
    scalar_group_key_terms left_keys = Some left_terms ->
    scalar_group_key_terms right_keys = Some right_terms ->
    query_group_formation_rename_compatible
      environment_relation rho left_terms right_terms ->
    query_group_scalar_expr_outcome_rename_compatible
      (query_group_environment_rename
        environment_relation rho left_terms right_terms)
      left_having right_having ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_group_local env left_select left_keys left_having)
      (fun env => query_group_local env right_select right_keys right_having) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Group left_select left_keys left_having input)
      (QExpr_Group right_select right_keys right_having input').
Proof.
intros environment_relation rho
  left_select right_select left_keys right_keys left_terms right_terms
  left_having right_having input input' Hschema Hinput _ _ _ _ Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun env =>
    query_group_local env left_select left_keys left_having)
  (right_local := fun env =>
    query_group_local env right_select right_keys right_having);
  try eassumption; intros env outcome; apply eval_query_group_unary_lift_iff.
Qed.

(** Every grouping-set branch must be transformed; well-formedness retains a
    nonempty branch list, identical ordered branch outputs, and unique aliases. *)
Theorem QExpr_GroupingSets_rename_transport :
  forall environment_relation rho left_sets right_sets input input',
    query_rename_schema_compatible rho
      (QExpr_GroupingSets left_sets input)
      (QExpr_GroupingSets right_sets input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_grouping_sets_local env left_sets)
      (fun env => query_grouping_sets_local env right_sets) ->
    query_rename_transport_under environment_relation rho
      (QExpr_GroupingSets left_sets input)
      (QExpr_GroupingSets right_sets input').
Proof.
intros environment_relation rho left_sets right_sets input input'
  Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun env => query_grouping_sets_local env left_sets)
  (right_local := fun env => query_grouping_sets_local env right_sets);
  try eassumption;
  intros env outcome; apply eval_query_grouping_sets_unary_lift_iff.
Qed.

(** RANK changes every partition/order key and the fresh result alias together;
    the local contract also preserves the embedding callback's [None] outcome
    as exactly [NumericValueOutOfRange]. *)
Theorem QExpr_Rank_rename_transport :
  forall environment_relation rho
      left_partition right_partition left_order right_order
      left_rank right_rank left_value right_value input input',
    query_sort_keys_rename_compatible rho left_partition right_partition ->
    query_sort_keys_rename_compatible rho left_order right_order ->
    right_rank = rho left_rank ->
    attribute_rename_fresh_for (query_expr_sort input) rho left_rank ->
    query_rename_schema_compatible rho
      (QExpr_Rank left_partition left_order left_rank left_value input)
      (QExpr_Rank right_partition right_order right_rank right_value input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ => query_rank_local
        left_partition left_order left_rank left_value)
      (fun _ => query_rank_local
        right_partition right_order right_rank right_value) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Rank left_partition left_order left_rank left_value input)
      (QExpr_Rank right_partition right_order right_rank right_value input').
Proof.
intros environment_relation rho
  left_partition right_partition left_order right_order
  left_rank right_rank left_value right_value input input'
  _ _ _ _ Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ => query_rank_local
    left_partition left_order left_rank left_value)
  (right_local := fun _ => query_rank_local
    right_partition right_order right_rank right_value);
  try eassumption; intros env outcome; apply eval_query_rank_unary_lift_iff.
Qed.

(** WINDOW changes key metadata and every item alias/aggregate together.  The
    local premise preserves every legal peer ordering, partition prefix,
    attached value, aggregate error, and output bag. *)
Theorem QExpr_Window_rename_transport :
  forall environment_relation rho
      left_partition right_partition left_order right_order
      left_items right_items input input',
    query_sort_keys_rename_compatible rho left_partition right_partition ->
    query_sort_keys_rename_compatible rho left_order right_order ->
    map rho (map (@qwi_attribute T) left_items) =
      map (@qwi_attribute T) right_items ->
    query_rename_schema_compatible rho
      (QExpr_Window left_partition left_order left_items input)
      (QExpr_Window right_partition right_order right_items input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun env => query_window_local env
        left_partition left_order left_items)
      (fun env => query_window_local env
        right_partition right_order right_items) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Window left_partition left_order left_items input)
      (QExpr_Window right_partition right_order right_items input').
Proof.
intros environment_relation rho
  left_partition right_partition left_order right_order
  left_items right_items input input'
  _ _ _ Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun env =>
    query_window_local env left_partition left_order left_items)
  (right_local := fun env =>
    query_window_local env right_partition right_order right_items);
  try eassumption; intros env outcome; apply eval_query_window_unary_lift_iff.
Qed.

(** DISTINCT is collision-sensitive.  Successful child rows now carry actual
    equality reflection, but the exact local premise is retained to certify the
    concrete finite-bag duplicate elimination and its output safety. *)
Theorem QExpr_Distinct_rename_transport :
  forall environment_relation rho input input',
    attribute_rename_injective_on (query_expr_sort input) rho ->
    query_rename_schema_compatible rho
      (QExpr_Distinct input) (QExpr_Distinct input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ => query_distinct_local)
      (fun _ => query_distinct_local) ->
    query_rename_transport_under environment_relation rho
      (QExpr_Distinct input) (QExpr_Distinct input').
Proof.
intros environment_relation rho input input'
  _ Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ => query_distinct_local)
  (right_local := fun _ => query_distinct_local);
  try eassumption; intros env outcome; apply eval_query_distinct_unary_lift_iff.
Qed.

(** ORDER BY transports attributes only with the whole sort-key record shape.
    The exact local scheduler retains NULL placement, comparator results, tie
    nondeterminism, list order, multiplicity, and child errors. *)
Theorem QExpr_OrderBy_rename_transport :
  forall environment_relation rho left_keys right_keys input input',
    query_sort_keys_rename_compatible rho left_keys right_keys ->
    query_rename_schema_compatible rho
      (QExpr_OrderBy left_keys input) (QExpr_OrderBy right_keys input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_unary_local_rename_compatible environment_relation rho
      (fun _ rows => query_order_by_local left_keys rows)
      (fun _ rows => query_order_by_local right_keys rows) ->
    query_rename_transport_under environment_relation rho
      (QExpr_OrderBy left_keys input) (QExpr_OrderBy right_keys input').
Proof.
intros environment_relation rho left_keys right_keys input input'
  _ Hschema Hinput Hlocal.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ rows => query_order_by_local left_keys rows)
  (right_local := fun _ rows => query_order_by_local right_keys rows);
  try eassumption; intros env outcome; apply eval_query_order_by_unary_lift_iff.
Qed.

(** Positional slicing has no attribute-bearing local metadata.  [skipn]
    commutes with the exact ordered row relation, so nested OFFSET transport
    follows directly from child transport. *)
Theorem QExpr_Offset_rename_transport :
  forall environment_relation rho offset input input',
    query_rename_schema_compatible rho
      (QExpr_Offset offset input) (QExpr_Offset offset input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_rename_transport_under environment_relation rho
      (QExpr_Offset offset input) (QExpr_Offset offset input').
Proof.
intros environment_relation rho offset input input' Hschema Hinput.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ rows => query_offset_local offset rows)
  (right_local := fun _ rows => query_offset_local offset rows);
  try eassumption.
- apply query_offset_local_rename_compatible.
- intros env outcome; apply eval_query_offset_unary_lift_iff.
- intros env outcome; apply eval_query_offset_unary_lift_iff.
Qed.

(** FETCH is the analogous [firstn] law and therefore preserves exact order,
    multiplicity, and runtime outcomes without a metadata premise. *)
Theorem QExpr_Fetch_rename_transport :
  forall environment_relation rho count input input',
    query_rename_schema_compatible rho
      (QExpr_Fetch count input) (QExpr_Fetch count input') ->
    query_rename_transport_under environment_relation rho input input' ->
    query_rename_transport_under environment_relation rho
      (QExpr_Fetch count input) (QExpr_Fetch count input').
Proof.
intros environment_relation rho count input input' Hschema Hinput.
eapply query_unary_constructor_rename_transport with
  (child := input) (child' := input')
  (left_local := fun _ rows => query_fetch_local count rows)
  (right_local := fun _ rows => query_fetch_local count rows);
  try eassumption.
- apply query_fetch_local_rename_compatible.
- intros env outcome; apply eval_query_fetch_unary_lift_iff.
- intros env outcome; apply eval_query_fetch_unary_lift_iff.
Qed.

(** Output-only relabeling uses the existing [QExpr_RowMap] constructor.  It is
    useful at an observation boundary, but it does not rename any predicate,
    projection input, grouping key, join condition, sort key, window item, or
    nested subquery and therefore is not by itself full alpha-renaming. *)
Definition query_output_rename_adapter
    (rho : attribute T -> attribute T)
    (query : query_expr T relname) : query_expr T relname :=
  QExpr_RowMap
    (map rho (query_expr_outputs query))
    (fun row => SqlSuccess (rename_tuple T rho row))
    query.

Lemma row_map_rows_output_rename :
  forall rho rows,
    row_map_rows_outcome
      (fun row => SqlSuccess (rename_tuple T rho row)) rows =
    SqlSuccess (rename_rows rho rows).
Proof.
intros rho rows; induction rows as [|row rows IH]; simpl; now rewrite ?IH.
Qed.

Lemma query_output_rename_adapter_outputs :
  forall rho query,
    query_expr_outputs (query_output_rename_adapter rho query) =
    map rho (query_expr_outputs query).
Proof.
intros; reflexivity.
Qed.

Lemma eval_query_output_rename_adapter_success_iff :
  forall env rho query output,
    eval_query env (query_output_rename_adapter rho query)
      (SqlSuccess output) <->
    exists input,
      eval_query env query (SqlSuccess input) /\
      output = rename_rows rho input.
Proof.
intros env rho query output; split; intro Heval.
- apply eval_query_row_map_unary_lift_iff in Heval.
  inversion Heval; subst.
  unfold query_row_map_local in H0.
  rewrite row_map_rows_output_rename in H0.
  inversion H0; subst output.
  now exists rows.
- destruct Heval as [input [Hinput Houtput]]; subst output.
  unfold query_output_rename_adapter.
  rewrite <- row_map_rows_output_rename.
  apply EQuery_RowMapRows with (input_rows := input).
  exact Hinput.
Qed.

Lemma eval_query_output_rename_adapter_error_iff :
  forall env rho query error,
    eval_query env (query_output_rename_adapter rho query)
      (SqlError error) <->
    eval_query env query (SqlError error).
Proof.
intros env rho query error; split; intro Heval.
- apply eval_query_row_map_unary_lift_iff in Heval.
  inversion Heval; subst; [assumption|].
  unfold query_row_map_local in H0.
  rewrite row_map_rows_output_rename in H0; discriminate H0.
- now apply EQuery_RowMapChildError.
Qed.

(** Mapped-schema outcome equivalence is the exact *observational* relation.
    It is deliberately not called full alpha-renaming: the output-only adapter
    above can satisfy this relation without renaming a predicate, key, alias,
    or nested subquery.  Full alpha-renaming is certified constructor by
    constructor by the metadata and reachable-environment premises of the
    [QExpr_*_rename_transport] theorems.  Ordinary [query_expr_outcome_equiv]
    remains stricter in a different direction: its ordered schemas are
    literally equal. *)
Definition query_mapped_schema_outcome_equiv
    (left_env right_env : Env.env T)
    (rho : attribute T -> attribute T)
    (left right : query_expr T relname) : Prop :=
  query_rename_schema_compatible rho left right /\
  outcome_relation_equiv (query_rows_rename rho)
    (eval_query left_env left) (eval_query right_env right).

Lemma query_mapped_schema_outcome_equiv_mapped_schema :
  forall left_env right_env rho left right,
    query_mapped_schema_outcome_equiv
      left_env right_env rho left right ->
    map rho (query_expr_outputs left) = query_expr_outputs right.
Proof.
intros left_env right_env rho left right
  [[_ [_ [Houtputs _]]] _].
exact Houtputs.
Qed.

Theorem query_rename_transport_under_implies_mapped_schema_outcome_equiv :
  forall environment_relation left_env right_env rho left right,
    environment_relation left_env right_env ->
    query_rename_transport_under environment_relation rho left right ->
    (exists outcome, eval_query left_env left outcome) ->
    (exists outcome, eval_query right_env right outcome) ->
    query_mapped_schema_outcome_equiv
      left_env right_env rho left right.
Proof.
intros environment_relation left_env right_env rho left right
  Henvironment [Hschema Htransport] Hleft_inhabited Hright_inhabited.
split; [exact Hschema|].
destruct (Htransport left_env right_env Henvironment)
  as [Hforward [Hbackward Herrors]].
unfold outcome_relation_equiv.
split; [exact Hleft_inhabited|].
split; [exact Hright_inhabited|].
split; [exact Hforward|].
split; [exact Hbackward|exact Herrors].
Qed.

(** A paired context compatibility relation reuses the existing complete
    [query_expr_context] grammar; it is a theorem interface, not another AST.
    Child contexts are certified from the matching constructor theorem.  The
    expression-hole forms for JOIN, FILTER, and GROUP remain deliberately
    fail-closed until their exact Bool3/subquery/aggregate environment premises
    are supplied; query transport of the nested subquery alone is insufficient. *)
Definition query_rename_context_compatible
    (environment_relation : Env.env T -> Env.env T -> Prop)
    (rho : attribute T -> attribute T)
    (left_context right_context : query_expr_context T relname) : Prop :=
  forall left right,
    query_rename_transport_under environment_relation rho left right ->
    query_rename_transport_under environment_relation rho
      (plug_query_expr_context left_context left)
      (plug_query_expr_context right_context right).

Lemma query_rename_hole_context_compatible :
  forall environment_relation rho,
    query_rename_context_compatible environment_relation rho
      (@QCtx_Hole T relname) (@QCtx_Hole T relname).
Proof.
intros environment_relation rho left right Htransport; exact Htransport.
Qed.

Theorem query_rename_context_transport :
  forall environment_relation rho left_context right_context left right,
    query_rename_context_compatible environment_relation rho
      left_context right_context ->
    query_rename_transport_under environment_relation rho left right ->
    query_rename_transport_under environment_relation rho
      (plug_query_expr_context left_context left)
      (plug_query_expr_context right_context right).
Proof.
intros; now apply H.
Qed.

Fixpoint plug_query_rename_contexts
    (contexts : list (query_expr_context T relname))
    (replacement : query_expr T relname) : query_expr T relname :=
  match contexts with
  | nil => replacement
  | context :: rest =>
      plug_query_expr_context context
        (plug_query_rename_contexts rest replacement)
  end.

(** Arbitrarily deep unary/binary/order-sensitive/bag-sensitive combinations
    follow from a [Forall2] chain of locally compatible paired contexts.  No
    benchmark topology or fixed operator pair occurs in the theorem. *)
Theorem query_rename_context_chain_transport :
  forall environment_relation rho left_contexts right_contexts,
    Forall2
      (query_rename_context_compatible environment_relation rho)
      left_contexts right_contexts ->
    forall left right,
      query_rename_transport_under environment_relation rho left right ->
      query_rename_transport_under environment_relation rho
        (plug_query_rename_contexts left_contexts left)
        (plug_query_rename_contexts right_contexts right).
Proof.
intros environment_relation rho left_contexts right_contexts Hcontexts.
induction Hcontexts as
  [|left_context right_context left_contexts right_contexts
    Hcontext Hcontexts IH]; intros left right Htransport; simpl.
- exact Htransport.
- apply Hcontext. now apply IH.
Qed.

End Sec.

Arguments query_rows_rename {T} _ _ _.
Arguments query_attribute_rename_injective_on {T} _ _.
Arguments query_attribute_rename_type_preserving_on {T} _ _.
