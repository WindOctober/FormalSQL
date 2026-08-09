(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                 Compositional exact query and scalar syntax                    *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List String.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Bool3 Formula Projection ATerms
        SqlOutcome SqlOrder.

(** Exact-query scalar expressions distinguish SQL values from three-valued
    Boolean results in their Rocq type.  Value expressions additionally carry
    their resolved SQL result type at each value-producing constructor; this
    witness is used for typed NULL production by scalar subqueries and checked
    against projection aliases by query admissibility. *)
Inductive scalar_result_kind : Type :=
  | ScalarResultValue
  | ScalarResultBoolean.

(** A Boolean site identifies one syntactic AND/OR occurrence in a normalized
    query.  PostgreSQL chooses one compiled operand order for that occurrence
    and reuses it for every row; the exact evaluator therefore indexes its
    schedule by sites instead of choosing an order independently per row. *)
Definition boolean_site : Type := string.

Inductive boolean_evaluation_order : Type :=
  | BooleanLeftFirst
  | BooleanRightFirst.

(** Ordered row-list outcomes are the single exact query semantics.  [alpha]
    maps them to possible bags; [gamma] forgets order by permutation closure
    and is therefore an over-approximation.  [BagClosed] is exactly where that
    abstraction is complete for equivalence; it is only an abstraction of the
    exact observations. *)

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

(** SQL join modes for the shared-child join operator.  Unlike a syntactic
    desugaring into unions and correlated EXISTS predicates, [QExpr_Join]
    below denotes one choice of each exact child outcome and reuses those
    chosen row lists throughout matching and unmatched-row production. *)
Inductive query_join_kind : Type :=
  | QueryJoinInner
  | QueryJoinLeft
  | QueryJoinRight
  | QueryJoinFull
  | QueryJoinSemi
  | QueryJoinAnti.

(** A cumulative SQL window item.  [QueryWindowRowNumber] embeds the
    one-based position in the concrete value domain; [QueryWindowAggregate]
    evaluates its aggregate term over the current partition prefix.  A list
    of items is evaluated against one shared legal ordering, which preserves
    the correlation between peer-sensitive window expressions in the same
    SELECT list. *)
Inductive query_window_function : Type :=
  | QueryWindowRowNumber : (nat -> option (value T)) -> query_window_function
  | QueryWindowAggregate : @aggterm T -> query_window_function
  (** Aggregate over the complete current partition.  Unlike a lowering that
      replays the child beside its original rows, this item is evaluated from
      the same one legal child observation selected by [QExpr_Window]. *)
  | QueryWindowFullPartitionAggregate :
      @aggterm T -> query_window_function.

Record query_window_item : Type := QueryWindowItem {
  qwi_attribute : attribute T;
  qwi_function : query_window_function
}.

(**
  [query_expr] is the exact relational syntax shared by the ordered-observation
  semantics and generated Logos problems.  Every relational operator consumes
  another query expression, so order-sensitive regions may occur at arbitrary
  depth.  Bag reasoning is a proved abstraction of this one syntax; it is not a
  second embedded query language.

  Scalar expressions are defined mutually with queries because quantified,
  IN, EXISTS, and scalar-value expressions contain full query subqueries.  This
  is essential for correlated and nested uses: no scalar constructor silently
  selects one deterministic result for its child query.  Scalar value
  subqueries have explicit one-row/cardinality-error semantics.
  [QExpr_Error] records a closed, externally attested PostgreSQL query-analysis
  outcome together with the already resolved ordered output schema.  It is not a way to
  turn parse failures or unsupported lowering into semantic errors.

 *)
Inductive query_expr : Type :=
  | QExpr_Error : list (attribute T) -> sql_runtime_error -> query_expr
  | QExpr_Values : list (attribute T) -> bagT -> query_expr
  (** A table scan carries the resolved SQL ordinal output schema because the
      set-valued base sort cannot recover column order.  Its observations are
      every list representative of the database instance bag. *)
  | QExpr_Table : list (attribute T) -> relname -> query_expr
  | QExpr_Set : set_op -> query_expr -> query_expr -> query_expr
  | QExpr_NaturalJoin : query_expr -> query_expr -> query_expr
  | QExpr_CrossJoin : query_expr -> query_expr -> query_expr
  | QExpr_Join :
      query_join_kind -> scalar_expr ScalarResultBoolean ->
      list (scalar_expr ScalarResultValue * attribute T) ->
      list (scalar_expr ScalarResultValue * attribute T) ->
      list (scalar_expr ScalarResultValue * attribute T) ->
      query_expr -> query_expr -> query_expr
  (** Every projection item is one value-typed scalar expression paired with
      its resolved output attribute. *)
  | QExpr_Project :
      list (scalar_expr ScalarResultValue * attribute T) ->
      query_expr -> query_expr
  (** Declarative, order-preserving application of one deterministic SQL row
      adapter.  The explicit list is the resolved ordered output schema; the callback
      returns either the exact output row or the SQL runtime error raised while
      computing that row. *)
  | QExpr_RowMap :
      list (attribute T) ->
      (tuple T -> sql_outcome (tuple T)) -> query_expr -> query_expr
  | QExpr_Filter :
      scalar_expr ScalarResultBoolean -> query_expr -> query_expr
  (** A grouped SELECT evaluates its SELECT and HAVING expressions
      once per logical group under the group environment, so aggregate leaves
      observe the complete group rather than one input row. *)
  | QExpr_Group :
      list (scalar_expr ScalarResultValue * attribute T) ->
      list (scalar_expr ScalarResultValue) ->
      scalar_expr ScalarResultBoolean ->
      query_expr -> query_expr
  (** Every grouping-set branch owns a typed output projection (including
      typed NULLs for keys absent from that branch) and typed grouping keys.
      The enclosing constructor owns the one shared input observation. *)
  | QExpr_GroupingSets :
      list
        (list (scalar_expr ScalarResultValue * attribute T) *
         list (scalar_expr ScalarResultValue)) ->
      query_expr -> query_expr
  (** PostgreSQL [rank()] over already-evaluated partition and ordering key
      attributes.  The adapter embeds the one-based natural rank in the
      concrete SQL value domain (BIGINT for the TNull instance).  This is a
      bag reset: the rank attached to a row depends only on its partition and
      the multiset of strictly preceding ordering keys, never on the child
      representative list. *)
  | QExpr_Rank :
      list (sort_key T) -> list (sort_key T) -> attribute T ->
      (nat -> option (value T)) -> query_expr -> query_expr
  (** Declarative SQL [ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW]
      window evaluation.  The semantics chooses every ordering permitted by
      the partition/order keys, so peers expose exactly the SQL-level
      nondeterminism without depending on a physical WindowAgg schedule. *)
  | QExpr_Window :
      list (sort_key T) -> list (sort_key T) ->
      list query_window_item -> query_expr -> query_expr
  | QExpr_Distinct : query_expr -> query_expr
  | QExpr_OrderBy : list (sort_key T) -> query_expr -> query_expr
  | QExpr_Offset : nat -> query_expr -> query_expr
  | QExpr_Fetch : nat -> query_expr -> query_expr
with scalar_expr : scalar_result_kind -> Type :=
(** One typed scalar AST is shared by projections, predicates, functions,
    CASE, IN/EXISTS, and scalar subqueries.  Flat [aggterm] is retained only as
    a value leaf so existing aggregate interpretation and bag facts remain
    authoritative.  [SExpr_Call] is strict; lazy SQL CASE has its own
    constructor so an unchosen arm is not evaluated. *)
  | SExpr_Leaf :
      type T -> @aggterm T -> scalar_expr ScalarResultValue
  | SExpr_Call :
      type T -> scalar_operator T ->
      list (scalar_expr ScalarResultValue) ->
      scalar_expr ScalarResultValue
  | SExpr_Case :
      type T -> scalar_expr ScalarResultBoolean ->
      scalar_expr ScalarResultValue -> scalar_expr ScalarResultValue ->
      scalar_expr ScalarResultValue
  | SExpr_BoolValue :
      type T -> (Bool.b (B T) -> value T) ->
      scalar_expr ScalarResultBoolean -> scalar_expr ScalarResultValue
  (** Interpret a nullable SQL BOOLEAN value as three-valued truth.  The
      instance callback preserves UNKNOWN for NULL; unlike an IS TRUE
      predicate this conversion is suitable below NOT/AND/OR. *)
  | SExpr_ValueBool :
      (value T -> Bool.b (B T)) -> scalar_expr ScalarResultValue ->
      scalar_expr ScalarResultBoolean
  | SExpr_Pred :
      predicate T -> list (scalar_expr ScalarResultValue) ->
      scalar_expr ScalarResultBoolean
  (** PostgreSQL may reorder every operand of one flattened AND/OR expression.
      Row [i] of the insertion-site matrix contains exactly [i] sites and
      inserts operand [i] into the order chosen for the preceding operands.
      Distinct stable sites therefore encode every permutation while reusing
      one compiled order for every row evaluated by the query. *)
  | SExpr_ConjList :
      list (list boolean_site) -> and_or ->
      list (scalar_expr ScalarResultBoolean) ->
      scalar_expr ScalarResultBoolean
  | SExpr_Not :
      scalar_expr ScalarResultBoolean -> scalar_expr ScalarResultBoolean
  | SExpr_True : scalar_expr ScalarResultBoolean
  | SExpr_Quant :
      quantifier -> predicate T -> list (scalar_expr ScalarResultValue) ->
      query_expr -> scalar_expr ScalarResultBoolean
  | SExpr_In :
      list (scalar_expr ScalarResultValue) -> query_expr ->
      scalar_expr ScalarResultBoolean
  | SExpr_Exists : query_expr -> scalar_expr ScalarResultBoolean
  | SExpr_Subquery :
      type T -> value T -> query_expr -> scalar_expr ScalarResultValue.

Definition query_select_list : Type :=
  list (scalar_expr ScalarResultValue * attribute T).

Definition query_grouping_set : Type :=
  (query_select_list * list (scalar_expr ScalarResultValue))%type.

(** Resolved SQL type of a typed value expression. *)
Definition scalar_expr_type
    (expression : scalar_expr ScalarResultValue) : type T :=
  match expression with
  | SExpr_Leaf result_type _
  | SExpr_Call result_type _ _
  | SExpr_Case result_type _ _ _
  | SExpr_BoolValue result_type _ _
  | SExpr_Subquery result_type _ _ => result_type
  end.

Definition scalar_select_outputs
    (select_list : list (scalar_expr ScalarResultValue * attribute T)) :
    list (attribute T) :=
  map snd select_list.

(** [QExpr_Error] denotes a query-analysis outcome, not an executable child.
    This structural checker is used by the typed admission boundary to ensure
    that such an outcome occurs only as the root query.  In particular, target
    elimination and FETCH 0 may not hide an undefined column/function in a
    nested query or scalar subquery. *)
Fixpoint query_expr_contains_analysis_error
    (query : query_expr) : bool :=
  match query with
  | QExpr_Error _ _ => true
  | QExpr_Values _ _ | QExpr_Table _ _ => false
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_contains_analysis_error left_query ||
      query_expr_contains_analysis_error right_query
  | QExpr_Join _ predicate matched_select left_select right_select
      left_query right_query =>
      scalar_expr_contains_analysis_error predicate ||
      existsb
        (fun item => scalar_expr_contains_analysis_error (fst item))
        matched_select ||
      existsb
        (fun item => scalar_expr_contains_analysis_error (fst item))
        left_select ||
      existsb
        (fun item => scalar_expr_contains_analysis_error (fst item))
        right_select ||
      query_expr_contains_analysis_error left_query ||
      query_expr_contains_analysis_error right_query
  | QExpr_RowMap _ _ input
  | QExpr_Rank _ _ _ _ input
  | QExpr_Window _ _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_contains_analysis_error input
  | QExpr_Project select_list input =>
      existsb
        (fun item => scalar_expr_contains_analysis_error (fst item))
        select_list || query_expr_contains_analysis_error input
  | QExpr_Filter expression input =>
      scalar_expr_contains_analysis_error expression ||
      query_expr_contains_analysis_error input
  | QExpr_Group select_list group_keys having input =>
      existsb
        (fun item => scalar_expr_contains_analysis_error (fst item))
        select_list ||
      existsb scalar_expr_contains_analysis_error group_keys ||
      scalar_expr_contains_analysis_error having ||
      query_expr_contains_analysis_error input
  | QExpr_GroupingSets grouping_sets input =>
      existsb
        (fun grouping_set =>
          orb
            (existsb
              (fun item => scalar_expr_contains_analysis_error (fst item))
              (fst grouping_set))
            (existsb scalar_expr_contains_analysis_error (snd grouping_set)))
        grouping_sets ||
      query_expr_contains_analysis_error input
  end
with scalar_expr_contains_analysis_error
    {kind : scalar_result_kind} (expression : scalar_expr kind) : bool :=
  match expression with
  | SExpr_Leaf _ _ | SExpr_True => false
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      existsb scalar_expr_contains_analysis_error arguments
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_contains_analysis_error condition ||
      scalar_expr_contains_analysis_error then_expression ||
      scalar_expr_contains_analysis_error else_expression
  | SExpr_BoolValue _ _ inner
  | SExpr_ValueBool _ inner
  | SExpr_Not inner => scalar_expr_contains_analysis_error inner
  | SExpr_ConjList _ _ expressions =>
      existsb scalar_expr_contains_analysis_error expressions
  | SExpr_Quant _ _ arguments subquery
  | SExpr_In arguments subquery =>
      existsb scalar_expr_contains_analysis_error arguments ||
      query_expr_contains_analysis_error subquery
  | SExpr_Exists subquery
  | SExpr_Subquery _ _ subquery =>
      query_expr_contains_analysis_error subquery
  end.

Definition query_expr_analysis_error_well_placed
    (query : query_expr) : Prop :=
  match query with
  | QExpr_Error _ _ => True
  | _ => query_expr_contains_analysis_error query = false
  end.

(** Boolean schedule sites are statement-wide identities, not local labels.
    Collecting them through scalar subqueries makes distinctness an explicit
    property of the one canonical query tree. *)
Fixpoint query_expr_boolean_sites
    (query : query_expr) : list boolean_site :=
  match query with
  | QExpr_Error _ _ | QExpr_Values _ _ | QExpr_Table _ _ => nil
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_boolean_sites left_query ++
        query_expr_boolean_sites right_query
  | QExpr_Join _ predicate matched_select left_select right_select
      left_query right_query =>
      scalar_expr_boolean_sites predicate ++
      flat_map (fun item => scalar_expr_boolean_sites (fst item))
        matched_select ++
      flat_map (fun item => scalar_expr_boolean_sites (fst item))
        left_select ++
      flat_map (fun item => scalar_expr_boolean_sites (fst item))
        right_select ++
      query_expr_boolean_sites left_query ++
      query_expr_boolean_sites right_query
  | QExpr_Project select_list input =>
      flat_map (fun item => scalar_expr_boolean_sites (fst item))
        select_list ++ query_expr_boolean_sites input
  | QExpr_RowMap _ _ input
  | QExpr_Rank _ _ _ _ input
  | QExpr_Window _ _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_boolean_sites input
  | QExpr_Filter expression input =>
      scalar_expr_boolean_sites expression ++
        query_expr_boolean_sites input
  | QExpr_Group select_list group_keys having input =>
      flat_map (fun item => scalar_expr_boolean_sites (fst item))
        select_list ++
      flat_map scalar_expr_boolean_sites group_keys ++
      scalar_expr_boolean_sites having ++
      query_expr_boolean_sites input
  | QExpr_GroupingSets grouping_sets input =>
      flat_map
        (fun grouping_set =>
          flat_map (fun item => scalar_expr_boolean_sites (fst item))
            (fst grouping_set) ++
          flat_map scalar_expr_boolean_sites (snd grouping_set))
        grouping_sets ++ query_expr_boolean_sites input
  end
with scalar_expr_boolean_sites
    {kind : scalar_result_kind}
    (expression : scalar_expr kind) : list boolean_site :=
  match expression with
  | SExpr_Leaf _ _ | SExpr_True => nil
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      flat_map scalar_expr_boolean_sites arguments
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_boolean_sites condition ++
      scalar_expr_boolean_sites then_expression ++
      scalar_expr_boolean_sites else_expression
  | SExpr_BoolValue _ _ inner
  | SExpr_ValueBool _ inner
  | SExpr_Not inner => scalar_expr_boolean_sites inner
  | SExpr_ConjList site_rows _ expressions =>
      flat_map (fun sites => sites) site_rows ++
        flat_map scalar_expr_boolean_sites expressions
  | SExpr_Quant _ _ arguments subquery
  | SExpr_In arguments subquery =>
      flat_map scalar_expr_boolean_sites arguments ++
        query_expr_boolean_sites subquery
  | SExpr_Exists subquery
  | SExpr_Subquery _ _ subquery =>
      query_expr_boolean_sites subquery
  end.

Definition boolean_sites_well_formed
    (sites : list boolean_site) : Prop :=
  NoDup sites /\ Forall (fun site => site <> EmptyString) sites.

Fixpoint boolean_site_mem
    (candidate : boolean_site) (sites : list boolean_site) : bool :=
  match sites with
  | nil => false
  | site :: rest =>
      String.eqb candidate site || boolean_site_mem candidate rest
  end.

Fixpoint boolean_sites_well_formedb
    (sites : list boolean_site) : bool :=
  match sites with
  | nil => true
  | site :: rest =>
      negb (String.eqb site EmptyString) &&
        (negb (boolean_site_mem site rest) &&
          boolean_sites_well_formedb rest)
  end.

Lemma boolean_site_mem_false_not_in :
  forall candidate sites,
    boolean_site_mem candidate sites = false ->
    ~ In candidate sites.
Proof.
intros candidate sites; induction sites as [|site rest IH]; cbn.
- intuition.
- destruct (String.eqb candidate site) eqn:Hhead; cbn; try discriminate.
  destruct (boolean_site_mem candidate rest) eqn:Hrest; cbn; try discriminate.
  intro Hfalse.
  intros [Hequal | Hin].
  + subst; now rewrite String.eqb_refl in Hhead.
  + exact (IH eq_refl Hin).
Qed.

Lemma boolean_sites_well_formedb_sound :
  forall sites,
    boolean_sites_well_formedb sites = true ->
    boolean_sites_well_formed sites.
Proof.
intro sites; induction sites as [|site rest IH]; cbn.
- intro; split; constructor.
- destruct (String.eqb site EmptyString) eqn:Hnonempty; cbn;
    try discriminate.
  destruct (boolean_site_mem site rest) eqn:Hfresh; cbn;
    try discriminate.
  intro Hrest.
  split.
  + constructor.
    * apply boolean_site_mem_false_not_in.
      exact Hfresh.
    * exact (proj1 (IH Hrest)).
  + constructor.
    * intro Hequal; subst; now rewrite String.eqb_refl in Hnonempty.
    * exact (proj2 (IH Hrest)).
Qed.

Definition query_expr_boolean_sites_well_formed
    (query : query_expr) : Prop :=
  boolean_sites_well_formed (query_expr_boolean_sites query).

Definition scalar_expr_boolean_sites_well_formed
    {kind : scalar_result_kind} (expression : scalar_expr kind) : Prop :=
  boolean_sites_well_formed (scalar_expr_boolean_sites expression).

(** Query-local dependency checks use the same complete traversal, including
    table references reached through scalar and quantified subqueries.  Keep
    each scan's ordered output list: base sorts are sets and therefore cannot
    validate the positional contract of a query-local relation on their own. *)
Definition query_table_reference : Type :=
  (relname * list (attribute T))%type.

Fixpoint query_expr_table_references
    (query : query_expr) : list query_table_reference :=
  match query with
  | QExpr_Table outputs relation => (relation, outputs) :: nil
  | QExpr_Error _ _ | QExpr_Values _ _ => nil
  | QExpr_Set _ left_query right_query
  | QExpr_NaturalJoin left_query right_query
  | QExpr_CrossJoin left_query right_query =>
      query_expr_table_references left_query ++
        query_expr_table_references right_query
  | QExpr_Join _ predicate matched_select left_select right_select
      left_query right_query =>
      scalar_expr_table_references predicate ++
      flat_map (fun item => scalar_expr_table_references (fst item))
        matched_select ++
      flat_map (fun item => scalar_expr_table_references (fst item))
        left_select ++
      flat_map (fun item => scalar_expr_table_references (fst item))
        right_select ++
      query_expr_table_references left_query ++
      query_expr_table_references right_query
  | QExpr_Project select_list input =>
      flat_map (fun item => scalar_expr_table_references (fst item))
        select_list ++ query_expr_table_references input
  | QExpr_RowMap _ _ input
  | QExpr_Rank _ _ _ _ input
  | QExpr_Window _ _ _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_table_references input
  | QExpr_Filter expression input =>
      scalar_expr_table_references expression ++
        query_expr_table_references input
  | QExpr_Group select_list group_keys having input =>
      flat_map (fun item => scalar_expr_table_references (fst item))
        select_list ++
      flat_map scalar_expr_table_references group_keys ++
      scalar_expr_table_references having ++
      query_expr_table_references input
  | QExpr_GroupingSets grouping_sets input =>
      flat_map
        (fun grouping_set =>
          flat_map (fun item => scalar_expr_table_references (fst item))
            (fst grouping_set) ++
          flat_map scalar_expr_table_references (snd grouping_set))
        grouping_sets ++ query_expr_table_references input
  end
with scalar_expr_table_references
    {kind : scalar_result_kind}
    (expression : scalar_expr kind) : list query_table_reference :=
  match expression with
  | SExpr_Leaf _ _ | SExpr_True => nil
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      flat_map scalar_expr_table_references arguments
  | SExpr_Case _ condition then_expression else_expression =>
      scalar_expr_table_references condition ++
      scalar_expr_table_references then_expression ++
      scalar_expr_table_references else_expression
  | SExpr_BoolValue _ _ inner
  | SExpr_ValueBool _ inner
  | SExpr_Not inner => scalar_expr_table_references inner
  | SExpr_ConjList _ _ expressions =>
      flat_map scalar_expr_table_references expressions
  | SExpr_Quant _ _ arguments subquery
  | SExpr_In arguments subquery =>
      flat_map scalar_expr_table_references arguments ++
        query_expr_table_references subquery
  | SExpr_Exists subquery
  | SExpr_Subquery _ _ subquery =>
      query_expr_table_references subquery
  end.

(** The mature grouping/environment kernel consumes aggregate terms.  The
    canonical GROUP BY constructor crosses that boundary through the scalar
    AST using value-leaf keys.  Concrete instances separately restrict which
    leaf payloads are admissible.  Returning [None] makes every richer key form
    fail closed until its grouping semantics is proved. *)
Fixpoint scalar_group_key_terms
    (keys : list (scalar_expr ScalarResultValue)) :
    option (list (@aggterm T)) :=
  match keys with
  | nil => Some nil
  | SExpr_Leaf _ term :: rest =>
      match scalar_group_key_terms rest with
      | Some terms => Some (term :: terms)
      | None => None
      end
  | _ :: _ => None
  end.

(** The local order behavior of one query constructor.  This is deliberately
    not a whole-query [BagClosed] classifier:

    - [BagReset] denotes a bag-closed source or a constructor that consumes
      child outcomes through bags and re-concretizes every bag-equivalent list;
    - [OrderPreserving] constructors retain the relative order chosen by their
      child while mapping or discarding rows pointwise;
    - [OrderEstablishing] constructors restrict the legal output orders;
    - [OrderConsuming] constructors use row positions to choose the result.

    Keeping behavior separate from semantic closure avoids the unsound
    inference that an order-preserving constructor is itself a reset. *)
Inductive query_order_behavior : Type :=
  | BagReset
  | OrderPreserving
  | OrderEstablishing
  | OrderConsuming.

(**
  Sources already expose permutation-closed observations. Set operations,
  joins, grouping, window resets, and duplicate elimination are semantic reset
  points. Projection, deterministic row
  mapping, and filtering preserve relative child order. ORDER BY establishes
  the legal order (while leaving peers nondeterministic); OFFSET and FETCH
  consume positions in that order.

  This function classifies the outer constructor only.  In particular,
  [QExpr_Project _ (QExpr_Group ...)] is [OrderPreserving], not [BagReset],
  even though a separate concrete-permutation certificate composes through
  the projection and then proves the whole expression [BagClosed].
 *)
Definition query_expr_order_behavior (q : query_expr) : query_order_behavior :=
  match q with
  | QExpr_Error _ _
  | QExpr_Values _ _
  | QExpr_Table _ _
  | QExpr_Set _ _ _
  | QExpr_NaturalJoin _ _
  | QExpr_CrossJoin _ _
  | QExpr_Join _ _ _ _ _ _ _
  | QExpr_Group _ _ _ _
  | QExpr_GroupingSets _ _
  | QExpr_Rank _ _ _ _ _
  | QExpr_Window _ _ _ _
  | QExpr_Distinct _ => BagReset
  | QExpr_Project _ _
  | QExpr_RowMap _ _ _
  | QExpr_Filter _ _ => OrderPreserving
  | QExpr_OrderBy _ _ => OrderEstablishing
  | QExpr_Offset _ _
  | QExpr_Fetch _ _ => OrderConsuming
  end.

(** A syntax-directed certificate candidate for concrete permutation closure
    of successful observations.  Reset constructors establish the certificate;
    deterministic row mapping may pass it through from its child.  Typed
    projection and filtering are relational because scalar subqueries may have
    several legal exact observations, so this conservative certificate does
    not guess closure for them.  The classifier is also intentionally false
    across order-establishing or order-consuming nodes. *)
Fixpoint query_expr_permutation_closure_certified
    (q : query_expr) : bool :=
  match q with
  | QExpr_RowMap _ _ input =>
      query_expr_permutation_closure_certified input
  | QExpr_Project _ _ | QExpr_Filter _ _ => false
  | _ =>
      match query_expr_order_behavior q with
      | BagReset => true
      | OrderPreserving | OrderEstablishing | OrderConsuming => false
      end
  end.

End Sec.

Arguments QExpr_Error {T relname} _ _.
Arguments QExpr_Values {T relname} _ _.
Arguments QExpr_Table {T relname} _ _.
Arguments QExpr_Set {T relname} _ _ _.
Arguments QExpr_NaturalJoin {T relname} _ _.
Arguments QExpr_CrossJoin {T relname} _ _.
Arguments QExpr_Join {T relname} _ _ _ _ _ _ _.
Arguments QExpr_Project {T relname} _ _.
Arguments QExpr_RowMap {T relname} _ _ _.
Arguments QExpr_Filter {T relname} _ _.
Arguments QExpr_Group {T relname} _ _ _ _.
Arguments QExpr_GroupingSets {T relname} _ _.
Arguments QExpr_Rank {T relname} _ _ _ _ _.
Arguments QExpr_Window {T relname} _ _ _ _.
Arguments QExpr_Distinct {T relname} _.
Arguments QExpr_OrderBy {T relname} _ _.
Arguments QExpr_Offset {T relname} _ _.
Arguments QExpr_Fetch {T relname} _ _.
Arguments QueryWindowRowNumber {T} _.
Arguments QueryWindowAggregate {T} _.
Arguments QueryWindowFullPartitionAggregate {T} _.
Arguments QueryWindowItem {T} _ _.
Arguments qwi_attribute {T} _.
Arguments qwi_function {T} _.

Arguments SExpr_Leaf {T relname} _ _.
Arguments SExpr_Call {T relname} _ _ _.
Arguments SExpr_Case {T relname} _ _ _ _.
Arguments SExpr_BoolValue {T relname} _ _ _.
Arguments SExpr_ValueBool {T relname} _ _.
Arguments SExpr_Pred {T relname} _ _.
Arguments SExpr_ConjList {T relname} _ _ _.
Arguments SExpr_Not {T relname} _.
Arguments SExpr_True {T relname}.
Arguments SExpr_Quant {T relname} _ _ _ _.
Arguments SExpr_In {T relname} _ _.
Arguments SExpr_Exists {T relname} _.
Arguments SExpr_Subquery {T relname} _ _ _.

Arguments scalar_expr_type {T relname} _.
Arguments scalar_select_outputs {T relname} _.
Arguments scalar_group_key_terms {T relname} _.

Arguments query_expr_order_behavior {T relname} _.
Arguments query_expr_permutation_closure_certified {T relname} _.
