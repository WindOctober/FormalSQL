(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                Compositional exact query and formula syntax                    *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Formula Projection ATerms
        SqlAlgebra SqlOutcome SqlOrder.

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

(** One native grouping-set branch has its own output projection (including
    typed NULLs for grouping keys absent from that branch) and its own list of
    grouping terms.  The enclosing query constructor owns the input, so no
    branch can select an independent child outcome. *)
Definition query_grouping_set : Type :=
  (@_select_list T * list (@aggterm T))%type.

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
  | QueryWindowAggregate : @aggterm T -> query_window_function.

Record query_window_item : Type := QueryWindowItem {
  qwi_attribute : attribute T;
  qwi_function : query_window_function
}.

(**
  [query_expr] is the exact relational syntax shared by the ordered-observation
  semantics and generated Logos problems.  Every relational
  constructor consumes another query expression, so order-sensitive regions
  may occur at arbitrary depth.  [QExpr_Bag] retains a compact bag-algebra
  query when lowering has established that the whole subtree
  belongs to the deterministic bag fragment.

  Formulas are defined mutually with queries because quantified, IN, and
  EXISTS predicates contain full query subqueries.  This is essential for
  correlated and nested uses: no formula constructor silently selects one
  deterministic result for its child query.  Scalar value subqueries are not
  part of this core: they require a separate one-row/cardinality error
  semantics and are rejected by lowering rather than encoded as predicates.
  [QExpr_Error] records a closed, externally attested PostgreSQL query-analysis
  outcome together with the already resolved ordered output schema.  It is not a way to
  turn parse failures or unsupported lowering into semantic errors.

 *)
Inductive query_expr : Type :=
  | QExpr_Error : list (attribute T) -> sql_runtime_error -> query_expr
  | QExpr_Values : list (attribute T) -> bagT -> query_expr
  | QExpr_Bag : list (attribute T) -> @query T relname -> query_expr
  | QExpr_Set : set_op -> query_expr -> query_expr -> query_expr
  | QExpr_NaturalJoin : query_expr -> query_expr -> query_expr
  | QExpr_CrossJoin : query_expr -> query_expr -> query_expr
  | QExpr_Join :
      query_join_kind -> formula_expr ->
      @_select_list T -> @_select_list T -> @_select_list T ->
      query_expr -> query_expr -> query_expr
  | QExpr_Project : @_select_list T -> query_expr -> query_expr
  (** Declarative, order-preserving application of one deterministic SQL row
      adapter.  The explicit list is the resolved ordered output schema; the callback
      returns either the exact output row or the SQL runtime error raised while
      computing that row. *)
  | QExpr_RowMap :
      list (attribute T) ->
      (tuple T -> sql_outcome (tuple T)) -> query_expr -> query_expr
  | QExpr_Filter : formula_expr -> query_expr -> query_expr
  | QExpr_Group :
      @_select_list T -> list (@aggterm T) -> formula_expr ->
      query_expr -> query_expr
  | QExpr_GroupingSets :
      list query_grouping_set -> query_expr -> query_expr
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
with formula_expr : Type :=
  | FExpr_Conj : and_or -> formula_expr -> formula_expr -> formula_expr
  | FExpr_Not : formula_expr -> formula_expr
  | FExpr_True : formula_expr
  | FExpr_Pred : predicate T -> list (@aggterm T) -> formula_expr
  | FExpr_Quant :
      quantifier -> predicate T -> list (@aggterm T) ->
      query_expr -> formula_expr
  | FExpr_In : list (@select T) -> query_expr -> formula_expr
  | FExpr_Exists : query_expr -> formula_expr.

(** A deliberately conservative static observation effect. *)
Inductive query_order_effect : Type :=
  | BagEffect
  | ListEffect.

(**
  Sources and deterministic [QExpr_Bag] leaves begin in a permutation-closed
  bag region. Set operations, joins, grouping, and duplicate elimination are
  semantic reset points: their observation semantics first consumes every
  possible child outcome, applies the corresponding bag operation, and then
  permits every permutation of each resulting bag.  Their effect is therefore
  [BagEffect] even when a child is list-sensitive.

  Projection, deterministic row mapping, and filtering preserve relative
  order, but classifying them unconditionally as [ListEffect] is a sound
  conservative choice.  A later analysis may recover [BagEffect] when their
  child is known BagClosed.  Ordering and slicing are always classified
  [ListEffect].  This analysis is intended to prove bag classifications sound,
  not to recognize every accidentally permutation-insensitive query.
 *)
Definition query_expr_effect (q : query_expr) : query_order_effect :=
  match q with
  | QExpr_Error _ _
  | QExpr_Values _ _
  | QExpr_Bag _ _
  | QExpr_Set _ _ _
  | QExpr_NaturalJoin _ _
  | QExpr_CrossJoin _ _
  | QExpr_Join _ _ _ _ _ _ _
  | QExpr_Group _ _ _ _
  | QExpr_GroupingSets _ _
  | QExpr_Rank _ _ _ _ _
  | QExpr_Window _ _ _ _
  | QExpr_Distinct _ => BagEffect
  | QExpr_Project _ _
  | QExpr_RowMap _ _ _
  | QExpr_Filter _ _
  | QExpr_OrderBy _ _
  | QExpr_Offset _ _
  | QExpr_Fetch _ _ => ListEffect
  end.

End Sec.

Arguments QExpr_Error {T relname} _ _.
Arguments QExpr_Values {T relname} _ _.
Arguments QExpr_Bag {T relname} _ _.
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
Arguments QueryWindowItem {T} _ _.
Arguments qwi_attribute {T} _.
Arguments qwi_function {T} _.

Arguments FExpr_Conj {T relname} _ _ _.
Arguments FExpr_Not {T relname} _.
Arguments FExpr_True {T relname}.
Arguments FExpr_Pred {T relname} _ _.
Arguments FExpr_Quant {T relname} _ _ _ _.
Arguments FExpr_In {T relname} _ _.
Arguments FExpr_Exists {T relname} _.

Arguments query_expr_effect {T relname} _.
