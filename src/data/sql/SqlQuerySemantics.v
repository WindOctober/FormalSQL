(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**             Exact ordered-outcome semantics for normalized SQL queries         *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Bool List Arith Sorting.Permutation ZArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet
        FiniteSet FiniteBag FiniteCollection Join FlatData Env Bool3 Formula
        FTerms ATerms Projection SqlOutcome SqlErrorSemantics SqlOrder
        SqlBagAbstraction SqlQuerySyntax.

(** Ordered row-list outcomes are the single exact query semantics.  [alpha]
    maps them to possible bags; [gamma] forgets order by permutation closure
    and is therefore an over-approximation.  [BagClosed] is exactly where that
    abstraction is complete for equivalence.

    Runtime errors are expression-level SQL observations evaluated from the
    logical query structure.  They do not depend on optimizer or executor
    scheduling choices. *)

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Arguments Select_As {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_By {T}.
Arguments F_Dot {T}.
Arguments A_Expr {T}.

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

Definition query_grouping_sets_outputs
    (grouping_sets : list (query_grouping_set T)) : list (attribute T) :=
  match grouping_sets with
  | nil => nil
  | (select_list, _) :: _ => select_list_outputs select_list
  end.

Definition query_outputs_sort (outputs : list (attribute T)) : setA :=
  Fset.mk_set (A T) outputs.

(** Ordered NATURAL JOIN output follows PostgreSQL's visible-column rule.
    Attribute identity is the same ordered-set identity used by
    [query_natural_join_compatible] for the intersection of row labels: common
    attributes occur first in left-child order, followed by left-only and
    right-only attributes in their respective child orders. *)
Definition query_natural_join_outputs
    (left_outputs right_outputs : list (attribute T)) : list (attribute T) :=
  filter
    (fun attribute => attribute inS? query_outputs_sort right_outputs)
    left_outputs ++
  filter
    (fun attribute => negb (attribute inS? query_outputs_sort right_outputs))
    left_outputs ++
  filter
    (fun attribute => negb (attribute inS? query_outputs_sort left_outputs))
    right_outputs.

(** Syntax-directed result order.  Projection and grouping preserve their
    select-list order, set operations use their left operand, and transparent
    unary operators preserve child order.  CROSS JOIN concatenates its child
    witnesses, while NATURAL JOIN applies PostgreSQL's common/left/right rule.
    Every leaf and row adapter carries its resolved order explicitly, so no
    finite-set enumeration is used as an ordinal authority. *)
Fixpoint query_expr_outputs
    (source : query_expr T relname) : list (attribute T) :=
  match source with
  | QExpr_Error outputs _ => outputs
  | QExpr_Values outputs _ => outputs
  | QExpr_Table outputs _ => outputs
  | QExpr_Set _ left_query _ => query_expr_outputs left_query
  | QExpr_NaturalJoin left_query right_query =>
      query_natural_join_outputs
        (query_expr_outputs left_query) (query_expr_outputs right_query)
  | QExpr_CrossJoin left_query right_query =>
      query_expr_outputs left_query ++ query_expr_outputs right_query
  | QExpr_Join kind _ matched_select left_select _ _ _ =>
      match kind with
      | QueryJoinSemi | QueryJoinAnti => select_list_outputs left_select
      | _ => select_list_outputs matched_select
      end
  | QExpr_Project select_list _
  | QExpr_Group select_list _ _ _ => select_list_outputs select_list
  | QExpr_ScalarProject select_list _ =>
      scalar_select_outputs select_list
  | QExpr_ScalarGroup select_list _ _ _ =>
      scalar_select_outputs select_list
  | QExpr_RowMap outputs _ _ => outputs
  | QExpr_GroupingSets grouping_sets _ =>
      query_grouping_sets_outputs grouping_sets
  | QExpr_Rank _ _ rank_attribute _ input =>
      query_expr_outputs input ++ rank_attribute :: nil
  | QExpr_Window _ _ items input =>
      query_expr_outputs input ++ map (@qwi_attribute T) items
  | QExpr_Filter _ input
  | QExpr_ScalarFilter _ input
  | QExpr_Distinct input
  | QExpr_OrderBy _ input
  | QExpr_Offset _ input
  | QExpr_Fetch _ input => query_expr_outputs input
  end.

(** Set-valued schema consumers intentionally forget only order and duplicate
    labels from the authoritative ordered output list. *)
Definition query_expr_sort (q : query_expr T relname) : setA :=
  query_outputs_sort (query_expr_outputs q).

Lemma query_expr_outputs_eq_sort_eq :
  forall left right,
    query_expr_outputs left = query_expr_outputs right ->
    query_expr_sort left =S= query_expr_sort right.
Proof.
intros left right Houtputs.
unfold query_expr_sort.
now rewrite Houtputs; apply Fset.equal_refl.
Qed.

(** Aggregate finalization owned by the current formula query level.  This
    traverses scalar formula/function structure but treats relational
    subqueries as opaque: their aggregate errors arise from their own query
    outcome. *)
Fixpoint eval_formula_expr_aggregate_runtime_error
    (env : Env.env T) (formula : formula_expr T relname) :
    option sql_runtime_error :=
  match formula with
  | FExpr_Conj _ left_formula right_formula =>
      first_error
        (eval_formula_expr_aggregate_runtime_error env left_formula)
        (eval_formula_expr_aggregate_runtime_error env right_formula)
  | FExpr_Not inner => eval_formula_expr_aggregate_runtime_error env inner
  | FExpr_True => None
  | FExpr_Pred _ arguments
  | FExpr_Quant _ _ arguments _ =>
      first_runtime_error
        (@eval_aggterm_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error env) arguments
  | FExpr_In select_items _ =>
      first_runtime_error
        (@eval_select_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error env) select_items
  | FExpr_Exists _ => None
  | FExpr_Scalar expression =>
      eval_scalar_expr_aggregate_runtime_error env expression
  end

with eval_scalar_expr_aggregate_runtime_error
    {kind : scalar_result_kind}
    (env : Env.env T) (expression : scalar_expr T relname kind) :
    option sql_runtime_error :=
  match expression with
  | SExpr_Leaf _ term =>
      @eval_aggterm_aggregate_runtime_error T
        symbol_runtime_error aggregate_runtime_error env term
  | SExpr_Call _ _ arguments
  | SExpr_Pred _ arguments =>
      first_runtime_error
        (@eval_scalar_expr_aggregate_runtime_error ScalarResultValue env)
        arguments
  | SExpr_Case _ condition then_expression else_expression =>
      first_error
        (eval_scalar_expr_aggregate_runtime_error env condition)
        (first_error
          (eval_scalar_expr_aggregate_runtime_error env then_expression)
          (eval_scalar_expr_aggregate_runtime_error env else_expression))
  | SExpr_BoolValue _ _ expression
  | SExpr_Not expression =>
      eval_scalar_expr_aggregate_runtime_error env expression
  | SExpr_ValueBool _ expression =>
      eval_scalar_expr_aggregate_runtime_error env expression
  | SExpr_Conj _ left_expression right_expression =>
      first_error
        (eval_scalar_expr_aggregate_runtime_error env left_expression)
        (eval_scalar_expr_aggregate_runtime_error env right_expression)
  | SExpr_True => None
  | SExpr_Quant _ _ arguments _
  | SExpr_In arguments _ =>
      first_runtime_error
        (@eval_scalar_expr_aggregate_runtime_error ScalarResultValue env)
        arguments
  | SExpr_Exists _
  | SExpr_Subquery _ _ _ => None
  end.

Definition eval_scalar_select_aggregate_runtime_error
    (env : Env.env T)
    (select_list : list
      (scalar_expr T relname ScalarResultValue * attribute T)) :
    option sql_runtime_error :=
  first_runtime_error
    (fun item => eval_scalar_expr_aggregate_runtime_error env (fst item))
    select_list.

(** Concrete bag operations used at the permutation-closing operators. *)
Definition query_rows_bag (rows : list tuple) : bagT :=
  Febag.mk_bag BTupleT rows.

(** Total table-scan denotation.  Exact generated programs separately prove
    admissibility, so the first branch is the only observable one there.  The
    empty fallback follows the existing total treatment of malformed set
    operations and, importantly, keeps the schema component of the database in
    the semantic interpretation rather than treating ordered scan metadata as
    an unchecked annotation. *)
Definition query_table_bag
    (outputs : list (attribute T)) (table : relname) : bagT :=
  if query_outputs_sort outputs =S?= basesort table
  then instance table
  else Febag.empty BTupleT.

(** Operators whose mathematical result is permutation-invariant may use this
    canonical representative.  Quantified predicates are one such consumer.
    GROUP deliberately does not use it, because floating-point SUM/AVG can
    observe the fold order of the selected input-bag representative. *)
Definition query_canonical_rows (rows : list tuple) : list tuple :=
  Febag.elements BTupleT (query_rows_bag rows).

(** Ranking observes only the child bag, but it subsequently reads arbitrary
    attributes from the chosen canonical rows.  [Febag.elements] is canonical
    only up to [OTuple] equality, whose representatives may differ outside
    their labels.  Canonizing every tuple turns equal bag elements into
    Leibniz-equal rows, so the ranking computation is a well-defined function
    of the semantic input bag rather than of an implementation representative. *)
Definition query_rank_bag_rows (input : bagT) : list tuple :=
  map (@canonized_tuple T) (Febag.elements BTupleT input).

(** [rank()] is the one-based row number of the first peer in a partition.
    Partition NULLs compare equal, as required by PostgreSQL window
    partitioning, because [compare_order_keys] returns [Eq] for two NULL key
    values.  Only strictly earlier ordering keys contribute to the count, so
    peer multiplicity creates the standard gaps without changing peer ranks. *)
Definition query_rank_precedes
    (partition_keys order_keys : list (sort_key T))
    (candidate row : tuple) : bool :=
  match compare_order_keys value_is_null partition_keys candidate row with
  | Eq =>
      match compare_order_keys value_is_null order_keys candidate row with
      | Lt => true
      | Eq | Gt => false
      end
  | Lt | Gt => false
  end.

Definition query_rank_nat
    (partition_keys order_keys : list (sort_key T))
    (rows : list tuple) (row : tuple) : nat :=
  S (length (filter
    (fun candidate =>
      query_rank_precedes partition_keys order_keys candidate row) rows)).

Definition query_rank_row_outcome
    (partition_keys order_keys : list (sort_key T))
    (rank_attribute : attribute T)
    (rank_value : nat -> option value)
    (all_rows : list tuple) (row : tuple) : option tuple :=
  match rank_value (query_rank_nat partition_keys order_keys all_rows row) with
  | None => None
  | Some value =>
      Some
        (mk_tuple T
          (Fset.union (A T) (labels T row)
            (Fset.mk_set (A T) (rank_attribute :: nil)))
          (fun attribute =>
            if Oset.eq_bool (OAtt T) attribute rank_attribute
            then value
            else dot T row attribute))
  end.

Fixpoint query_rank_rows_outcome
    (partition_keys order_keys : list (sort_key T))
    (rank_attribute : attribute T)
    (rank_value : nat -> option value)
    (all_rows rows : list tuple) : option (list tuple) :=
  match rows with
  | nil => Some nil
  | row :: rows' =>
      match query_rank_row_outcome partition_keys order_keys rank_attribute
              rank_value all_rows row with
      | None => None
      | Some ranked_row =>
          match query_rank_rows_outcome partition_keys order_keys rank_attribute
                  rank_value all_rows rows' with
          | None => None
          | Some ranked_rows => Some (ranked_row :: ranked_rows)
          end
      end
  end.

(** Attach one concrete value while preserving every existing field.  Window
    output aliases are required to be fresh by the lowering boundary. *)
Definition query_window_attach_value
    (attribute : attribute T) (value : value) (row : tuple) : tuple :=
  mk_tuple T
    (Fset.union (A T) (labels T row)
      (Fset.mk_set (A T) (attribute :: nil)))
    (fun candidate =>
      if Oset.eq_bool (OAtt T) candidate attribute
      then value
      else dot T row candidate).

(** Evaluate one cumulative item against the exact current partition prefix.
    Aggregate errors are the ordinary SQL expression-level errors of the
    aggregate term.  ROW_NUMBER has SQL type BIGINT, so a position outside
    that concrete carrier is a numeric-value-out-of-range language error. *)
Definition query_window_item_value_outcome
    (env : Env.env T) (position : nat)
    (prefix partition : list tuple)
    (item : query_window_item T) : option (sql_outcome value) :=
  match qwi_function item with
  | QueryWindowRowNumber embed =>
      match embed position with
      | None => Some (SqlError (DataException NumericValueOutOfRange))
      | Some value => Some (SqlSuccess value)
      end
  | QueryWindowAggregate term =>
      let aggregate_env := env_g T env (@Group_By T nil) prefix in
      match @eval_aggterm_runtime_error T
              symbol_runtime_error aggregate_runtime_error
              aggregate_env term with
      | Some error => Some (SqlError error)
      | None => Some (SqlSuccess (@interp_aggterm T aggregate_env term))
      end
  | QueryWindowFullPartitionAggregate term =>
      let aggregate_env := env_g T env (@Group_By T nil) partition in
      match @eval_aggterm_runtime_error T
              symbol_runtime_error aggregate_runtime_error
              aggregate_env term with
      | Some error => Some (SqlError error)
      | None => Some (SqlSuccess (@interp_aggterm T aggregate_env term))
      end
  end.

Fixpoint query_window_items_outcome
    (env : Env.env T) (position : nat)
    (prefix partition : list tuple)
    (items : list (query_window_item T)) (row : tuple) :
    option (sql_outcome tuple) :=
  match items with
  | nil => Some (SqlSuccess row)
  | item :: rest =>
      match query_window_item_value_outcome env position prefix partition item with
      | None => None
      | Some (SqlError error) => Some (SqlError error)
      | Some (SqlSuccess value) =>
          query_window_items_outcome env position prefix partition rest
            (query_window_attach_value (qwi_attribute item) value row)
      end
  end.

Definition query_window_same_partition
    (partition_keys : list (sort_key T)) (row candidate : tuple) : bool :=
  match compare_order_keys value_is_null partition_keys row candidate with
  | Eq => true
  | Lt | Gt => false
  end.

(** Process one legal partition/order representative.  [prefix] contains the
    original staged rows of the current partition (never previously attached
    window outputs), and [position] is one-based.  Comparing adjacent rows is
    sufficient because the representative is sorted by partition keys before
    this function is called. *)
Fixpoint query_window_rows_outcome
    (env : Env.env T) (partition_keys : list (sort_key T))
    (items : list (query_window_item T))
    (previous : option tuple) (position : nat) (prefix rows : list tuple) :
    option (sql_outcome (list tuple)) :=
  match rows with
  | nil => Some (SqlSuccess nil)
  | row :: rest =>
      let same_partition :=
        match previous with
        | None => false
        | Some previous_row =>
            match compare_order_keys value_is_null partition_keys
                    previous_row row with
            | Eq => true
            | Lt | Gt => false
            end
        end in
      let current_position := if same_partition then S position else 1 in
      let current_prefix := if same_partition then prefix ++ row :: nil
                            else row :: nil in
      let current_partition :=
        filter (query_window_same_partition partition_keys row)
          (current_prefix ++ rest) in
      match query_window_items_outcome env current_position current_prefix
              current_partition items row with
      | None => None
      | Some (SqlError error) => Some (SqlError error)
      | Some (SqlSuccess output_row) =>
          match query_window_rows_outcome env partition_keys items
                  (Some row) current_position current_prefix rest with
          | None => None
          | Some (SqlError error) => Some (SqlError error)
          | Some (SqlSuccess output_rows) =>
              Some (SqlSuccess (output_row :: output_rows))
          end
      end
  end.

Definition query_same_rows_as_bag
    (rows : list tuple) (bag : bagT) : Prop :=
  query_rows_bag rows =BE= bag.

(** A legal ORDER BY observation is an ordered representative of exactly the
    input bag.  Ties intentionally remain relational: every permutation that
    satisfies [ordered_rows] is a possible exact query outcome. *)
Definition order_by_rows
    (keys : list (sort_key T))
    (input output : list tuple) : Prop :=
  query_same_rows_as_bag output (query_rows_bag input) /\
  ordered_rows value_is_null keys output.

Definition query_set_bag
    (operation : set_op) (left right : bagT) : bagT :=
  Febag.interp_set_op BTupleT operation left right.

Definition query_cross_join_bag (left right : bagT) : bagT :=
  Febag.mk_bag BTupleT
    (brute_left_join_list tuple (join_tuple T)
      (Febag.elements BTupleT left) (Febag.elements BTupleT right)).

Definition query_distinct_bag (input : bagT) : bagT :=
  Febag.mk_bag BTupleT
    (Feset.elements (Fecol.CSet (CTuple T))
      (Feset.mk_set (Fecol.CSet (CTuple T))
        (Febag.elements BTupleT input))).

(** Runtime checking and deterministic row transforms used by relational
    query rules.  A projection checks rows and select items from left to right
    and preserves the successful input order exactly. *)
Fixpoint project_rows_outcome
    (env : Env.env T)
    (select_list : _select_list T)
    (rows : list tuple) : sql_outcome (list tuple) :=
  match rows with
  | nil => SqlSuccess nil
  | row :: rest =>
      match @eval_select_list_runtime_error T
              symbol_runtime_error aggregate_runtime_error
              (env_t T env row) select_list with
      | Some error => SqlError error
      | None =>
          match project_rows_outcome env select_list rest with
          | SqlError error => SqlError error
          | SqlSuccess output =>
              SqlSuccess
                (projection T (env_t T env row) (Select_List select_list)
                   :: output)
          end
      end
  end.

Definition group_keys_runtime_error
    (env : Env.env T)
    (group_terms : list (@aggterm T))
    (rows : list tuple) : option sql_runtime_error :=
  first_runtime_error
    (fun row =>
      first_runtime_error
        (@eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error (env_t T env row))
        group_terms)
    rows.

(** A global aggregate has one group on an empty input.  The older generic
    [FlatData.make_groups] helper predates this SQL case and returns no groups;
    the exact normalized-query semantics corrects it locally without changing
    the behavior of surface SELECT-star constructs outside this core. *)
Definition query_make_groups
    (env : Env.env T) (rows : list tuple)
    (group_terms : list (@aggterm T)) : list (list tuple) :=
  match group_terms, rows with
  | nil, nil => nil :: nil
  | _, _ => @make_groups T env rows (@Group_By T group_terms)
  end.

(** SQL row equality is componentwise three-valued equality: one definite
    mismatch makes the whole comparison FALSE even if another component is
    NULL; otherwise a NULL component makes it UNKNOWN. *)
Definition query_value_equal
    (left right : value) : Bool.b (B T) :=
  if value_is_null left || value_is_null right
  then unknown
  else
    match Oset.compare (OVal T) left right with
    | Eq => Bool.true (B T)
    | Lt | Gt => Bool.false (B T)
    end.

Fixpoint query_tuple_values_equal
    (attributes : list (attribute T)) (left right : tuple) : Bool.b (B T) :=
  match attributes with
  | nil => Bool.true (B T)
  | attribute :: rest =>
      Bool.andb (B T)
        (query_value_equal (dot T left attribute) (dot T right attribute))
        (query_tuple_values_equal rest left right)
  end.

Definition query_tuple_equal (left right : tuple) : Bool.b (B T) :=
  if labels T left =S?= labels T right
  then
    query_tuple_values_equal
      (Fset.elements (A T) (labels T left)) left right
  else Bool.false (B T).

(** SQL NATURAL JOIN retains a pair only when equality on every common
    attribute is TRUE.  In particular, NULL = NULL is UNKNOWN rather than
    TRUE, so a common NULL never matches.  This predicate computes exactly
    that TRUE test directly, while an empty common schema remains a cross
    product. *)
Definition query_natural_join_compatible
    (left right : tuple) : bool :=
  Fset.for_all (A T)
    (fun attribute =>
      andb (negb (value_is_null (dot T left attribute)))
        (andb (negb (value_is_null (dot T right attribute)))
          (match Oset.compare (OVal T)
             (dot T left attribute) (dot T right attribute) with
           | Eq => true
           | Lt | Gt => false
           end)))
    (labels T left interS labels T right).

Definition query_natural_join_bag (left right : bagT) : bagT :=
  Febag.mk_bag BTupleT
    (theta_join_list tuple (join_tuple T) query_natural_join_compatible
      (Febag.elements BTupleT left) (Febag.elements BTupleT right)).

Definition filter_cons_outcome
    (truth : Bool.b (B T)) (row : tuple)
    (tail : sql_outcome (list tuple)) : sql_outcome (list tuple) :=
  match tail with
  | SqlError error => SqlError error
  | SqlSuccess output =>
      if Bool.is_true (B T) truth
      then SqlSuccess (row :: output)
      else SqlSuccess output
  end.

Definition group_cons_outcome
    (row : tuple) (tail : sql_outcome (list tuple)) :
    sql_outcome (list tuple) :=
  match tail with
  | SqlError error => SqlError error
  | SqlSuccess output => SqlSuccess (row :: output)
  end.

(** A condition matrix records one coherent TRUE/non-TRUE choice for every
    occurrence pair from one chosen left outcome and one chosen right
    outcome.  SQL joins retain a pair exactly when the condition is TRUE;
    FALSE and UNKNOWN both record [false]. *)
Inductive query_join_source : Type :=
  | JoinSourceMatched : tuple -> query_join_source
  | JoinSourceLeft : tuple -> query_join_source
  | JoinSourceRight : tuple -> query_join_source.

Fixpoint query_join_matched_sources
    (left : tuple) (rights : list tuple) (flags : list bool) :
    list query_join_source :=
  match rights, flags with
  | right_row :: rights', flag :: flags' =>
      let tail := query_join_matched_sources left rights' flags' in
      if flag
      then JoinSourceMatched (join_tuple T left right_row) :: tail
      else tail
  | _, _ => nil
  end.

Definition query_join_row_has_match (flags : list bool) : bool :=
  existsb (fun flag => flag) flags.

Fixpoint query_join_left_sources
    (kind : query_join_kind) (lefts rights : list tuple)
    (matrix : list (list bool)) : list query_join_source :=
  match lefts, matrix with
  | left_row :: lefts', flags :: matrix' =>
      let matched := query_join_matched_sources left_row rights flags in
      let row_sources :=
        match kind with
        | QueryJoinInner | QueryJoinRight => matched
        | QueryJoinLeft | QueryJoinFull =>
            if query_join_row_has_match flags
            then matched
            else JoinSourceLeft left_row :: nil
        | QueryJoinSemi =>
            if query_join_row_has_match flags
            then JoinSourceLeft left_row :: nil
            else nil
        | QueryJoinAnti =>
            if query_join_row_has_match flags
            then nil
            else JoinSourceLeft left_row :: nil
        end in
      row_sources ++ query_join_left_sources kind lefts' rights matrix'
  | _, _ => nil
  end.

Definition query_join_column_has_match
    (index : nat) (matrix : list (list bool)) : bool :=
  existsb (fun flags => nth index flags false) matrix.

Fixpoint query_join_unmatched_right_sources_from
    (index : nat) (rights : list tuple) (matrix : list (list bool)) :
    list query_join_source :=
  match rights with
  | nil => nil
  | right_row :: rights' =>
      let tail :=
        query_join_unmatched_right_sources_from (S index) rights' matrix in
      if query_join_column_has_match index matrix
      then tail
      else JoinSourceRight right_row :: tail
  end.

Definition query_join_sources
    (kind : query_join_kind) (lefts rights : list tuple)
    (matrix : list (list bool)) : list query_join_source :=
  query_join_left_sources kind lefts rights matrix ++
  match kind with
  | QueryJoinRight | QueryJoinFull =>
      query_join_unmatched_right_sources_from O rights matrix
  | _ => nil
  end.

Definition project_join_source_outcome
    (env : Env.env T)
    (matched_select left_select right_select : _select_list T)
    (source : query_join_source) : sql_outcome tuple :=
  let '(row, select_list) :=
    match source with
    | JoinSourceMatched row => (row, matched_select)
    | JoinSourceLeft row => (row, left_select)
    | JoinSourceRight row => (row, right_select)
    end in
  match @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_t T env row) select_list with
  | Some error => SqlError error
  | None =>
      SqlSuccess
        (projection T (env_t T env row) (Select_List select_list))
  end.

(** Apply a deterministic row adapter in the exact child-list order.  The
    first row error is the result; otherwise the transformed rows retain their
    original relative order. *)
Fixpoint row_map_rows_outcome
    (row_map : tuple -> sql_outcome tuple)
    (rows : list tuple) : sql_outcome (list tuple) :=
  match rows with
  | nil => SqlSuccess nil
  | row :: rows' =>
      match row_map row with
      | SqlError error => SqlError error
      | SqlSuccess mapped_row =>
          match row_map_rows_outcome row_map rows' with
          | SqlError error => SqlError error
          | SqlSuccess mapped_rows =>
              SqlSuccess (mapped_row :: mapped_rows)
          end
      end
  end.

Fixpoint project_join_sources_outcome
    (env : Env.env T)
    (matched_select left_select right_select : _select_list T)
    (sources : list query_join_source) : sql_outcome (list tuple) :=
  match sources with
  | nil => SqlSuccess nil
  | source :: sources' =>
      match project_join_source_outcome env
              matched_select left_select right_select source with
      | SqlError error => SqlError error
      | SqlSuccess row =>
          match project_join_sources_outcome env
                  matched_select left_select right_select sources' with
          | SqlError error => SqlError error
          | SqlSuccess rows => SqlSuccess (row :: rows)
          end
      end
  end.

(** Small total combinators used by the relational scalar evaluator. *)
Definition sql_outcome_map {A C : Type}
    (f : A -> C) (outcome : sql_outcome A) : sql_outcome C :=
  match outcome with
  | SqlSuccess value => SqlSuccess (f value)
  | SqlError error => SqlError error
  end.

Definition scalar_value_cons_outcome
    (head : value) (tail : sql_outcome (list value)) :
    sql_outcome (list value) :=
  match tail with
  | SqlSuccess values => SqlSuccess (head :: values)
  | SqlError error => SqlError error
  end.

Definition scalar_project_cons_outcome
    (head : tuple) (tail : sql_outcome (list tuple)) :
    sql_outcome (list tuple) :=
  match tail with
  | SqlSuccess rows => SqlSuccess (head :: rows)
  | SqlError error => SqlError error
  end.

Definition scalar_leaf_value_outcome
    (env : Env.env T) (term : @aggterm T) : sql_outcome value :=
  match @eval_aggterm_runtime_error T
          symbol_runtime_error aggregate_runtime_error env term with
  | Some error => SqlError error
  | None => SqlSuccess (@interp_aggterm T env term)
  end.

Definition scalar_call_value_outcome
    (operator : scalar_operator T) (values : list value) : sql_outcome value :=
  match symbol_runtime_error operator
          (map (fun value => (None, value)) values) with
  | Some error => SqlError error
  | None => SqlSuccess (interp_scalar_operator T operator values)
  end.

Definition scalar_bool_value_outcome
    (embed : Bool.b (B T) -> value)
    (outcome : sql_outcome (Bool.b (B T))) : sql_outcome value :=
  sql_outcome_map embed outcome.

Definition scalar_project_row
    (select_list : list
      (scalar_expr T relname ScalarResultValue * attribute T))
    (values : list value) : tuple :=
  let attributes := scalar_select_outputs select_list in
  let fields := combine attributes values in
  mk_tuple T (Fset.mk_set (A T) attributes)
    (fun attribute =>
      match Oset.find (OAtt T) attribute fields with
      | Some value => value
      | None => default_value T (type_of_attribute T attribute)
      end).

Fixpoint query_value_lists_equal
    (left right : list value) : Bool.b (B T) :=
  match left, right with
  | nil, nil => Bool.true (B T)
  | left_value :: left', right_value :: right' =>
      Bool.andb (B T)
        (query_value_equal left_value right_value)
        (query_value_lists_equal left' right')
  | _, _ => Bool.false (B T)
  end.

Definition query_row_output_values
    (outputs : list (attribute T)) (row : tuple) : list value :=
  map (dot T row) outputs.

(** PostgreSQL scalar-subquery cardinality.  The helper is total on malformed
    output schemas, but admissibility makes only the singleton-output branch
    reachable for generated exact queries. *)
Definition scalar_subquery_value_outcome
    (null_value : value) (outputs : list (attribute T))
    (outcome : sql_outcome (list tuple)) : sql_outcome value :=
  match outcome with
  | SqlError error => SqlError error
  | SqlSuccess nil => SqlSuccess null_value
  | SqlSuccess (row :: nil) =>
      match outputs with
      | attribute :: nil => SqlSuccess (dot T row attribute)
      | _ => SqlSuccess null_value
      end
  | SqlSuccess (_ :: _ :: _) => SqlError CardinalityViolation
  end.

Definition query_rows_cardinality_outcome
    (outcome : sql_outcome (list tuple)) : sql_outcome nat :=
  sql_outcome_map (@length tuple) outcome.

Definition query_offset_cardinality_outcome
    (offset : nat) (outcome : sql_outcome nat) : sql_outcome nat :=
  sql_outcome_map (fun cardinality => cardinality - offset) outcome.

Definition query_fetch_cardinality_outcome
    (count : nat) (outcome : sql_outcome nat) : sql_outcome nat :=
  sql_outcome_map (Nat.min count) outcome.

Definition query_cardinality_cons_outcome
    (outcome : sql_outcome nat) : sql_outcome nat :=
  sql_outcome_map S outcome.

Definition query_exists_truth (cardinality : nat) : Bool.b (B T) :=
  if Nat.eqb cardinality O
  then Bool.false (B T)
  else Bool.true (B T).

Definition query_exists_rows_outcome
    (outcome : sql_outcome (list tuple)) :
    sql_outcome (Bool.b (B T)) :=
  sql_outcome_map (fun rows => query_exists_truth (length rows)) outcome.

Definition query_exists_cardinality_outcome
    (outcome : sql_outcome nat) : sql_outcome (Bool.b (B T)) :=
  sql_outcome_map query_exists_truth outcome.

(** Constructors not listed here have no target-eliding/short-circuit EXISTS
    rule and therefore demand their ordinary row outcome. *)
Definition query_exists_requires_rows
    (query : query_expr T relname) : bool :=
  match query with
  | QExpr_Project _ _
  | QExpr_ScalarProject _ _
  | QExpr_RowMap _ _ _
  | QExpr_Filter _ _
  | QExpr_ScalarFilter _ _
  | QExpr_Join _ _ _ _ _ _ _
  | QExpr_Group _ _ _ _
  | QExpr_ScalarGroup _ _ _ _
  | QExpr_GroupingSets _ _
  | QExpr_Distinct _
  | QExpr_OrderBy _ _
  | QExpr_Fetch _ _ => false
  | _ => true
  end.

Definition query_exists_uses_cardinality
    (query : query_expr T relname) : bool :=
  match query with
  | QExpr_Join _ _ _ _ _ _ _
  | QExpr_Group _ _ _ _
  | QExpr_ScalarGroup _ _ _ _
  | QExpr_GroupingSets _ _ => true
  | _ => false
  end.

(** EXISTS may discard target-only computation, but it must retain ordinary
    query evaluation at operators whose rows or values affect cardinality.
    This classifier is semantic demand routing, not a replayability claim. *)
Definition query_cardinality_requires_rows
    (query : query_expr T relname) : bool :=
  match query with
  | QExpr_Project _ _
  | QExpr_ScalarProject _ _
  | QExpr_RowMap _ _ _
  | QExpr_Join _ _ _ _ _ _ _
  | QExpr_Group _ _ _ _
  | QExpr_ScalarGroup _ _ _ _
  | QExpr_GroupingSets _ _
  | QExpr_OrderBy _ _
  | QExpr_Fetch _ _ => false
  | _ => true
  end.

(** [SExpr_Conj] gives a closed FormalSQL term deterministic left-to-right
    short-circuit semantics.  PostgreSQL may reorganize Boolean operands, so
    SQL lowering may construct this term only when every operand is pure and
    runtime-total (or when separate authoritative evaluation-order evidence is
    available).  [Bool.is_true (Bool.negb truth)] distinguishes FALSE from
    UNKNOWN in the generic three-valued Boolean interface. *)
Definition scalar_conj_requires_right
    (operation : and_or) (truth : Bool.b (B T)) : bool :=
  match operation with
  | And_F => negb (Bool.is_true (B T) (Bool.negb (B T) truth))
  | Or_F => negb (Bool.is_true (B T) truth)
  end.

Definition scalar_conj_short_result
    (operation : and_or) : Bool.b (B T) :=
  match operation with
  | And_F => Bool.false (B T)
  | Or_F => Bool.true (B T)
  end.

(**
  The relations below form one big-step semantics.  Formula and scalar
  subqueries
  are evaluated under the current (possibly correlated) environment.  Filter
  and group-processing relations are explicit members of the mutual family so
  no deterministic child bag is selected behind the relational interface.

  Errors propagate compositionally from query operands.  Successful bag
  operators re-concretize their result with [query_same_rows_as_bag], thereby
  including every permutation of each possible result bag.
 *)
Inductive eval_query_expr_outcome
    (env : Env.env T) :
    query_expr T relname -> sql_outcome (list tuple) -> Prop :=
  | EQuery_Error :
      forall outputs error,
        eval_query_expr_outcome env (QExpr_Error outputs error)
          (SqlError error)
  | EQuery_Values :
      forall outputs values rows,
        query_same_rows_as_bag rows values ->
        eval_query_expr_outcome env (QExpr_Values outputs values)
          (SqlSuccess rows)
  | EQuery_Table :
      forall outputs table rows,
        query_same_rows_as_bag rows (query_table_bag outputs table) ->
        eval_query_expr_outcome env (QExpr_Table outputs table)
          (SqlSuccess rows)
  | EQuery_SetLeftError :
      forall operation left right error,
        eval_query_expr_outcome env left (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Set operation left right)
          (SqlError error)
  | EQuery_SetRightError :
      forall operation left right left_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Set operation left right)
          (SqlError error)
  | EQuery_SetSuccess :
      forall operation left right left_rows right_rows output,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        query_same_rows_as_bag output
          (if query_expr_sort left =S?= query_expr_sort right
           then query_set_bag operation
                  (query_rows_bag left_rows) (query_rows_bag right_rows)
           else Febag.empty BTupleT) ->
        eval_query_expr_outcome env (QExpr_Set operation left right)
          (SqlSuccess output)
  | EQuery_NaturalJoinLeftError :
      forall left right error,
        eval_query_expr_outcome env left (SqlError error) ->
        eval_query_expr_outcome env (QExpr_NaturalJoin left right)
          (SqlError error)
  | EQuery_NaturalJoinRightError :
      forall left right left_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlError error) ->
        eval_query_expr_outcome env (QExpr_NaturalJoin left right)
          (SqlError error)
  | EQuery_NaturalJoinSuccess :
      forall left right left_rows right_rows output,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        query_same_rows_as_bag output
          (query_natural_join_bag
            (query_rows_bag left_rows) (query_rows_bag right_rows)) ->
        eval_query_expr_outcome env (QExpr_NaturalJoin left right)
          (SqlSuccess output)
  | EQuery_CrossJoinLeftError :
      forall left right error,
        eval_query_expr_outcome env left (SqlError error) ->
        eval_query_expr_outcome env (QExpr_CrossJoin left right)
          (SqlError error)
  | EQuery_CrossJoinRightError :
      forall left right left_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlError error) ->
        eval_query_expr_outcome env (QExpr_CrossJoin left right)
          (SqlError error)
  | EQuery_CrossJoinSuccess :
      forall left right left_rows right_rows output,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        query_same_rows_as_bag output
          (query_cross_join_bag
            (query_rows_bag left_rows) (query_rows_bag right_rows)) ->
        eval_query_expr_outcome env (QExpr_CrossJoin left right)
          (SqlSuccess output)
  | EQuery_JoinLeftError :
      forall kind predicate matched_select left_select right_select
             left right error,
        eval_query_expr_outcome env left (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error)
  | EQuery_JoinRightError :
      forall kind predicate matched_select left_select right_select
             left right left_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error)
  | EQuery_JoinBagError :
      forall kind predicate matched_select left_select right_select
             left right left_rows right_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        eval_join_bag_outcome env kind predicate
          matched_select left_select right_select
          (query_rows_bag left_rows) (query_rows_bag right_rows)
          (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error)
  | EQuery_JoinSuccess :
      forall kind predicate matched_select left_select right_select
             left right left_rows right_rows output_bag output,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        eval_join_bag_outcome env kind predicate
          matched_select left_select right_select
          (query_rows_bag left_rows) (query_rows_bag right_rows)
          (SqlSuccess output_bag) ->
        query_same_rows_as_bag output output_bag ->
        eval_query_expr_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlSuccess output)
  | EQuery_ProjectChildError :
      forall select_list input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Project select_list input)
          (SqlError error)
  | EQuery_ProjectRows :
      forall select_list input input_rows,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_query_expr_outcome env (QExpr_Project select_list input)
          (project_rows_outcome env select_list input_rows)
  | EQuery_ScalarProjectChildError :
      forall select_list input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_ScalarProject select_list input) (SqlError error)
  | EQuery_ScalarProjectRows :
      forall select_list input input_rows outcome,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_scalar_project_rows_outcome env select_list input_rows outcome ->
        eval_query_expr_outcome env
          (QExpr_ScalarProject select_list input) outcome
  | EQuery_RowMapChildError :
      forall output_attributes row_map input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_RowMap output_attributes row_map input)
          (SqlError error)
  | EQuery_RowMapRows :
      forall output_attributes row_map input input_rows,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_query_expr_outcome env
          (QExpr_RowMap output_attributes row_map input)
          (row_map_rows_outcome row_map input_rows)
  | EQuery_FilterChildError :
      forall formula input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Filter formula input)
          (SqlError error)
  | EQuery_FilterRows :
      forall formula input input_rows outcome,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_filter_rows_outcome env formula input_rows outcome ->
        eval_query_expr_outcome env (QExpr_Filter formula input) outcome
  | EQuery_ScalarFilterChildError :
      forall expression input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_ScalarFilter expression input) (SqlError error)
  | EQuery_ScalarFilterRows :
      forall expression input input_rows outcome,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_filter_rows_outcome env (FExpr_Scalar expression)
          input_rows outcome ->
        eval_query_expr_outcome env
          (QExpr_ScalarFilter expression input) outcome
  | EQuery_GroupChildError :
      forall select_list group_terms having input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Group select_list group_terms having input) (SqlError error)
  | EQuery_GroupBagError :
      forall select_list group_terms having input input_rows error,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_group_bag_outcome env select_list group_terms having
          (query_rows_bag input_rows) (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Group select_list group_terms having input) (SqlError error)
  | EQuery_GroupBagSuccess :
      forall select_list group_terms having input input_rows output_bag output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_group_bag_outcome env select_list group_terms having
          (query_rows_bag input_rows) (SqlSuccess output_bag) ->
        query_same_rows_as_bag output output_bag ->
        eval_query_expr_outcome env
          (QExpr_Group select_list group_terms having input) (SqlSuccess output)
  | EQuery_ScalarGroupChildError :
      forall select_list group_terms having input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_ScalarGroup select_list group_terms having input)
          (SqlError error)
  | EQuery_ScalarGroupBagError :
      forall select_list group_terms having input input_rows error,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_scalar_group_bag_outcome env select_list group_terms having
          (query_rows_bag input_rows) (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_ScalarGroup select_list group_terms having input)
          (SqlError error)
  | EQuery_ScalarGroupBagSuccess :
      forall select_list group_terms having input input_rows output_bag output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_scalar_group_bag_outcome env select_list group_terms having
          (query_rows_bag input_rows) (SqlSuccess output_bag) ->
        query_same_rows_as_bag output output_bag ->
        eval_query_expr_outcome env
          (QExpr_ScalarGroup select_list group_terms having input)
          (SqlSuccess output)
  | EQuery_GroupingSetsChildError :
      forall grouping_sets input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_GroupingSets grouping_sets input)
          (SqlError error)
  | EQuery_GroupingSetsBagError :
      forall grouping_sets input input_rows error,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_grouping_sets_bag_outcome env grouping_sets
          (query_rows_bag input_rows) (SqlError error) ->
        eval_query_expr_outcome env (QExpr_GroupingSets grouping_sets input)
          (SqlError error)
  | EQuery_GroupingSetsSuccess :
      forall grouping_sets input input_rows output_bag output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_grouping_sets_bag_outcome env grouping_sets
          (query_rows_bag input_rows) (SqlSuccess output_bag) ->
        query_same_rows_as_bag output output_bag ->
        eval_query_expr_outcome env (QExpr_GroupingSets grouping_sets input)
          (SqlSuccess output)
  | EQuery_RankChildError :
      forall partition_keys order_keys rank_attribute rank_value input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
          (SqlError error)
  | EQuery_RankValueError :
      forall partition_keys order_keys rank_attribute rank_value input input_rows,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        query_rank_rows_outcome partition_keys order_keys rank_attribute
          rank_value (query_rank_bag_rows (query_rows_bag input_rows))
          (query_rank_bag_rows (query_rows_bag input_rows)) = None ->
        eval_query_expr_outcome env
          (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
          (SqlError (DataException NumericValueOutOfRange))
  | EQuery_RankSuccess :
      forall partition_keys order_keys rank_attribute rank_value input
             input_rows ranked_rows output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        query_rank_rows_outcome partition_keys order_keys rank_attribute
          rank_value (query_rank_bag_rows (query_rows_bag input_rows))
          (query_rank_bag_rows (query_rows_bag input_rows)) = Some ranked_rows ->
        query_same_rows_as_bag output (query_rows_bag ranked_rows) ->
        eval_query_expr_outcome env
          (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
          (SqlSuccess output)
  | EQuery_WindowChildError :
      forall partition_keys order_keys items input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Window partition_keys order_keys items input)
          (SqlError error)
  | EQuery_WindowRowsError :
      forall partition_keys order_keys items input input_rows ordered_rows error,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        order_by_rows (partition_keys ++ order_keys)
          (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
        query_window_rows_outcome env partition_keys items None 0 nil
          ordered_rows = Some (SqlError error) ->
        eval_query_expr_outcome env
          (QExpr_Window partition_keys order_keys items input)
          (SqlError error)
  | EQuery_WindowSuccess :
      forall partition_keys order_keys items input input_rows ordered_rows
             window_rows output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        order_by_rows (partition_keys ++ order_keys)
          (query_rank_bag_rows (query_rows_bag input_rows)) ordered_rows ->
        query_window_rows_outcome env partition_keys items None 0 nil
          ordered_rows = Some (SqlSuccess window_rows) ->
        query_same_rows_as_bag output (query_rows_bag window_rows) ->
        eval_query_expr_outcome env
          (QExpr_Window partition_keys order_keys items input)
          (SqlSuccess output)
  | EQuery_DistinctChildError :
      forall input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Distinct input) (SqlError error)
  | EQuery_DistinctSuccess :
      forall input input_rows output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        query_same_rows_as_bag output
          (query_distinct_bag (query_rows_bag input_rows)) ->
        eval_query_expr_outcome env (QExpr_Distinct input) (SqlSuccess output)
  | EQuery_OrderByChildError :
      forall keys input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_OrderBy keys input) (SqlError error)
  | EQuery_OrderBySuccess :
      forall keys input input_rows output,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        order_by_rows keys input_rows output ->
        eval_query_expr_outcome env (QExpr_OrderBy keys input)
          (SqlSuccess output)
  | EQuery_OffsetChildError :
      forall offset input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Offset offset input) (SqlError error)
  | EQuery_OffsetSuccess :
      forall offset input input_rows,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_query_expr_outcome env (QExpr_Offset offset input)
          (SqlSuccess (skipn offset input_rows))
  | EQuery_FetchChildError :
      forall count input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_expr_outcome env (QExpr_Fetch count input) (SqlError error)
  | EQuery_FetchSuccess :
      forall count input input_rows,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_query_expr_outcome env (QExpr_Fetch count input)
          (SqlSuccess (firstn count input_rows))
with eval_formula_expr_outcome
    (env : Env.env T) :
    formula_expr T relname -> sql_outcome (Bool.b (B T)) -> Prop :=
  | EFormula_ConjLeftError :
      forall operation left right error,
        eval_formula_expr_outcome env left (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Conj operation left right)
          (SqlError error)
  | EFormula_ConjRightError :
      forall operation left right left_truth error,
        eval_formula_expr_outcome env left (SqlSuccess left_truth) ->
        eval_formula_expr_outcome env right (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Conj operation left right)
          (SqlError error)
  | EFormula_ConjSuccess :
      forall operation left right left_truth right_truth,
        eval_formula_expr_outcome env left (SqlSuccess left_truth) ->
        eval_formula_expr_outcome env right (SqlSuccess right_truth) ->
        eval_formula_expr_outcome env (FExpr_Conj operation left right)
          (SqlSuccess
            (interp_conj (B T) operation left_truth right_truth))
  | EFormula_NotError :
      forall formula error,
        eval_formula_expr_outcome env formula (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Not formula) (SqlError error)
  | EFormula_NotSuccess :
      forall formula truth,
        eval_formula_expr_outcome env formula (SqlSuccess truth) ->
        eval_formula_expr_outcome env (FExpr_Not formula)
          (SqlSuccess (Bool.negb (B T) truth))
  | EFormula_True :
      eval_formula_expr_outcome env FExpr_True
        (SqlSuccess (Bool.true (B T)))
  | EFormula_PredError :
      forall predicate arguments error,
        first_runtime_error
          (@eval_aggterm_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          arguments = Some error ->
        eval_formula_expr_outcome env (FExpr_Pred predicate arguments)
          (SqlError error)
  | EFormula_PredSuccess :
      forall predicate arguments,
        first_runtime_error
          (@eval_aggterm_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          arguments = None ->
        eval_formula_expr_outcome env (FExpr_Pred predicate arguments)
          (SqlSuccess
            (interp_predicate T predicate
              (map (@interp_aggterm T env) arguments)))
  | EFormula_QuantArgumentsError :
      forall quantifier predicate arguments subquery error,
        first_runtime_error
          (@eval_aggterm_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          arguments = Some error ->
        eval_formula_expr_outcome env
          (FExpr_Quant quantifier predicate arguments subquery) (SqlError error)
  | EFormula_QuantSubqueryError :
      forall quantifier predicate arguments subquery error,
        first_runtime_error
          (@eval_aggterm_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          arguments = None ->
        eval_query_expr_outcome env subquery (SqlError error) ->
        eval_formula_expr_outcome env
          (FExpr_Quant quantifier predicate arguments subquery) (SqlError error)
  | EFormula_QuantSuccess :
      forall quantifier predicate arguments subquery rows,
        first_runtime_error
          (@eval_aggterm_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          arguments = None ->
        eval_query_expr_outcome env subquery (SqlSuccess rows) ->
        eval_formula_expr_outcome env
          (FExpr_Quant quantifier predicate arguments subquery)
          (SqlSuccess
            (let interpreted_arguments := map (@interp_aggterm T env) arguments in
             interp_quant (B T) quantifier
               (fun row =>
                 interp_predicate T predicate
                   (interpreted_arguments ++
                    map (dot T row) (query_expr_outputs subquery)))
               (query_canonical_rows rows)))
  | EFormula_InArgumentsError :
      forall select_items subquery error,
        first_runtime_error
          (@eval_select_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          select_items = Some error ->
        eval_formula_expr_outcome env (FExpr_In select_items subquery)
          (SqlError error)
  | EFormula_InSubqueryError :
      forall select_items subquery error,
        first_runtime_error
          (@eval_select_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          select_items = None ->
        eval_query_expr_outcome env subquery (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_In select_items subquery)
          (SqlError error)
  | EFormula_InSuccess :
      forall select_items subquery rows,
        first_runtime_error
          (@eval_select_runtime_error T
            symbol_runtime_error aggregate_runtime_error env)
          select_items = None ->
        eval_query_expr_outcome env subquery (SqlSuccess rows) ->
        eval_formula_expr_outcome env (FExpr_In select_items subquery)
          (SqlSuccess
            (let projected :=
               projection T env (Select_List (_Select_List select_items)) in
             interp_quant (B T) Exists_F
               (query_tuple_equal projected)
               (query_canonical_rows rows)))
  | EFormula_ExistsError :
      forall subquery error,
        eval_query_exists_outcome env subquery (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery) (SqlError error)
  | EFormula_ExistsSuccessEmpty :
      forall subquery,
        eval_query_exists_outcome env subquery
          (SqlSuccess (Bool.false (B T))) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery)
          (SqlSuccess (Bool.false (B T)))
  | EFormula_ExistsSuccessNonempty :
      forall subquery,
        eval_query_exists_outcome env subquery
          (SqlSuccess (Bool.true (B T))) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery)
          (SqlSuccess (Bool.true (B T)))
  | EFormula_ScalarError :
      forall expression error,
        eval_scalar_boolean_expr_outcome env expression (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Scalar expression)
          (SqlError error)
  | EFormula_ScalarSuccess :
      forall expression truth,
        eval_scalar_boolean_expr_outcome env expression (SqlSuccess truth) ->
        eval_formula_expr_outcome env (FExpr_Scalar expression)
          (SqlSuccess truth)

with eval_scalar_value_expr_outcome
    (env : Env.env T) :
    scalar_expr T relname ScalarResultValue -> sql_outcome value -> Prop :=
  | EScalar_Leaf :
      forall result_type term,
        eval_scalar_value_expr_outcome env (SExpr_Leaf result_type term)
          (scalar_leaf_value_outcome env term)
  | EScalar_CallArgumentsError :
      forall result_type operator arguments error,
        eval_scalar_values_outcome env arguments (SqlError error) ->
        eval_scalar_value_expr_outcome env
          (SExpr_Call result_type operator arguments) (SqlError error)
  | EScalar_CallSuccess :
      forall result_type operator arguments values,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_scalar_value_expr_outcome env
          (SExpr_Call result_type operator arguments)
          (scalar_call_value_outcome operator values)
  | EScalar_CaseConditionError :
      forall result_type condition then_expression else_expression error,
        eval_scalar_boolean_expr_outcome env condition (SqlError error) ->
        eval_scalar_value_expr_outcome env
          (SExpr_Case result_type condition then_expression else_expression)
          (SqlError error)
  | EScalar_CaseThen :
      forall result_type condition then_expression else_expression truth outcome,
        eval_scalar_boolean_expr_outcome env condition (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_scalar_value_expr_outcome env then_expression outcome ->
        eval_scalar_value_expr_outcome env
          (SExpr_Case result_type condition then_expression else_expression)
          outcome
  | EScalar_CaseElse :
      forall result_type condition then_expression else_expression truth outcome,
        eval_scalar_boolean_expr_outcome env condition (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_scalar_value_expr_outcome env else_expression outcome ->
        eval_scalar_value_expr_outcome env
          (SExpr_Case result_type condition then_expression else_expression)
          outcome
  | EScalar_BoolValue :
      forall result_type embed expression outcome,
        eval_scalar_boolean_expr_outcome env expression outcome ->
        eval_scalar_value_expr_outcome env
          (SExpr_BoolValue result_type embed expression)
          (scalar_bool_value_outcome embed outcome)
  | EScalar_Subquery :
      forall result_type null_value subquery outcome,
        value_is_null null_value = true ->
        eval_query_expr_outcome env subquery outcome ->
        eval_scalar_value_expr_outcome env
          (SExpr_Subquery result_type null_value subquery)
          (scalar_subquery_value_outcome null_value
            (query_expr_outputs subquery) outcome)

with eval_scalar_boolean_expr_outcome
    (env : Env.env T) :
    scalar_expr T relname ScalarResultBoolean ->
    sql_outcome (Bool.b (B T)) -> Prop :=
  | EScalar_ValueBool :
      forall decode expression outcome,
        eval_scalar_value_expr_outcome env expression outcome ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_ValueBool decode expression)
          (sql_outcome_map decode outcome)
  | EScalar_PredArgumentsError :
      forall predicate arguments error,
        eval_scalar_values_outcome env arguments (SqlError error) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Pred predicate arguments) (SqlError error)
  | EScalar_PredSuccess :
      forall predicate arguments values,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Pred predicate arguments)
          (SqlSuccess (interp_predicate T predicate values))
  | EScalar_ConjLeftError :
      forall operation left right error,
        eval_scalar_boolean_expr_outcome env left (SqlError error) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Conj operation left right) (SqlError error)
  | EScalar_ConjShortCircuit :
      forall operation left right left_truth,
        eval_scalar_boolean_expr_outcome env left (SqlSuccess left_truth) ->
        scalar_conj_requires_right operation left_truth = false ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Conj operation left right)
          (SqlSuccess (scalar_conj_short_result operation))
  | EScalar_ConjRightError :
      forall operation left right left_truth error,
        eval_scalar_boolean_expr_outcome env left (SqlSuccess left_truth) ->
        scalar_conj_requires_right operation left_truth = true ->
        eval_scalar_boolean_expr_outcome env right (SqlError error) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Conj operation left right) (SqlError error)
  | EScalar_ConjSuccess :
      forall operation left right left_truth right_truth,
        eval_scalar_boolean_expr_outcome env left (SqlSuccess left_truth) ->
        scalar_conj_requires_right operation left_truth = true ->
        eval_scalar_boolean_expr_outcome env right (SqlSuccess right_truth) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Conj operation left right)
          (SqlSuccess
            (interp_conj (B T) operation left_truth right_truth))
  | EScalar_NotError :
      forall expression error,
        eval_scalar_boolean_expr_outcome env expression (SqlError error) ->
        eval_scalar_boolean_expr_outcome env (SExpr_Not expression)
          (SqlError error)
  | EScalar_NotSuccess :
      forall expression truth,
        eval_scalar_boolean_expr_outcome env expression (SqlSuccess truth) ->
        eval_scalar_boolean_expr_outcome env (SExpr_Not expression)
          (SqlSuccess (Bool.negb (B T) truth))
  | EScalar_True :
      eval_scalar_boolean_expr_outcome env SExpr_True
        (SqlSuccess (Bool.true (B T)))
  | EScalar_QuantArgumentsError :
      forall quantifier predicate arguments subquery error,
        eval_scalar_values_outcome env arguments (SqlError error) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Quant quantifier predicate arguments subquery)
          (SqlError error)
  | EScalar_QuantSubqueryError :
      forall quantifier predicate arguments subquery values error,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_query_expr_outcome env subquery (SqlError error) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Quant quantifier predicate arguments subquery)
          (SqlError error)
  | EScalar_QuantSuccess :
      forall quantifier predicate arguments subquery values rows,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_query_expr_outcome env subquery (SqlSuccess rows) ->
        eval_scalar_boolean_expr_outcome env
          (SExpr_Quant quantifier predicate arguments subquery)
          (SqlSuccess
            (interp_quant (B T) quantifier
              (fun row =>
                interp_predicate T predicate
                  (values ++ query_row_output_values
                    (query_expr_outputs subquery) row))
              (query_canonical_rows rows)))
  | EScalar_InArgumentsError :
      forall arguments subquery error,
        eval_scalar_values_outcome env arguments (SqlError error) ->
        eval_scalar_boolean_expr_outcome env (SExpr_In arguments subquery)
          (SqlError error)
  | EScalar_InSubqueryError :
      forall arguments subquery values error,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_query_expr_outcome env subquery (SqlError error) ->
        eval_scalar_boolean_expr_outcome env (SExpr_In arguments subquery)
          (SqlError error)
  | EScalar_InSuccess :
      forall arguments subquery values rows,
        eval_scalar_values_outcome env arguments (SqlSuccess values) ->
        eval_query_expr_outcome env subquery (SqlSuccess rows) ->
        eval_scalar_boolean_expr_outcome env (SExpr_In arguments subquery)
          (SqlSuccess
            (interp_quant (B T) Exists_F
              (fun row => query_value_lists_equal values
                (query_row_output_values (query_expr_outputs subquery) row))
              (query_canonical_rows rows)))
  | EScalar_ExistsError :
      forall subquery error,
        eval_query_exists_outcome env subquery (SqlError error) ->
        eval_scalar_boolean_expr_outcome env (SExpr_Exists subquery)
          (SqlError error)
  | EScalar_ExistsSuccess :
      forall subquery truth,
        eval_query_exists_outcome env subquery (SqlSuccess truth) ->
        eval_scalar_boolean_expr_outcome env (SExpr_Exists subquery)
          (SqlSuccess truth)

with eval_scalar_values_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue) ->
    sql_outcome (list value) -> Prop :=
  | EScalarValues_Nil :
      eval_scalar_values_outcome env nil (SqlSuccess nil)
  | EScalarValues_HeadError :
      forall expression expressions error,
        eval_scalar_value_expr_outcome env expression (SqlError error) ->
        eval_scalar_values_outcome env (expression :: expressions)
          (SqlError error)
  | EScalarValues_Cons :
      forall expression expressions value tail,
        eval_scalar_value_expr_outcome env expression (SqlSuccess value) ->
        eval_scalar_values_outcome env expressions tail ->
        eval_scalar_values_outcome env (expression :: expressions)
          (scalar_value_cons_outcome value tail)

with eval_scalar_project_rows_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue * attribute T) ->
    list tuple -> sql_outcome (list tuple) -> Prop :=
  | EScalarProjectRows_Nil :
      forall select_list,
        eval_scalar_project_rows_outcome env select_list nil
          (SqlSuccess nil)
  | EScalarProjectRows_HeadError :
      forall select_list row rows error,
        eval_scalar_values_outcome (env_t T env row)
          (map fst select_list) (SqlError error) ->
        eval_scalar_project_rows_outcome env select_list (row :: rows)
          (SqlError error)
  | EScalarProjectRows_Cons :
      forall select_list row rows values tail,
        eval_scalar_values_outcome (env_t T env row)
          (map fst select_list) (SqlSuccess values) ->
        eval_scalar_project_rows_outcome env select_list rows tail ->
        eval_scalar_project_rows_outcome env select_list (row :: rows)
          (scalar_project_cons_outcome
            (scalar_project_row select_list values) tail)

(** Native cardinality demand for EXISTS.  Transparent target-only operators
    reuse the same recursively chosen cardinality; value/cardinality-sensitive
    operators use their ordinary exact outcome once. *)
with eval_query_cardinality_outcome
    (env : Env.env T) :
    query_expr T relname -> sql_outcome nat -> Prop :=
  | ECardinality_Demanded :
      forall query outcome,
        query_cardinality_requires_rows query = true ->
        eval_query_expr_outcome env query outcome ->
        eval_query_cardinality_outcome env query
          (query_rows_cardinality_outcome outcome)
  | ECardinality_JoinLeftError :
      forall kind predicate matched_select left_select right_select
             left right error,
        eval_query_expr_outcome env left (SqlError error) ->
        eval_query_cardinality_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error)
  | ECardinality_JoinRightError :
      forall kind predicate matched_select left_select right_select
             left right left_rows error,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlError error) ->
        eval_query_cardinality_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) (SqlError error)
  | ECardinality_Join :
      forall kind predicate matched_select left_select right_select
             left right left_rows right_rows outcome,
        eval_query_expr_outcome env left (SqlSuccess left_rows) ->
        eval_query_expr_outcome env right (SqlSuccess right_rows) ->
        eval_join_cardinality_outcome env kind predicate
          (query_rows_bag left_rows) (query_rows_bag right_rows) outcome ->
        eval_query_cardinality_outcome env
          (QExpr_Join kind predicate matched_select left_select right_select
            left right) outcome
  | ECardinality_GroupChildError :
      forall select_list group_terms having input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_cardinality_outcome env
          (QExpr_Group select_list group_terms having input) (SqlError error)
  | ECardinality_Group :
      forall select_list group_terms having input input_rows outcome,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_group_cardinality_outcome env select_list group_terms having
          (query_rows_bag input_rows) outcome ->
        eval_query_cardinality_outcome env
          (QExpr_Group select_list group_terms having input) outcome
  | ECardinality_ScalarGroupChildError :
      forall select_list group_keys having input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_cardinality_outcome env
          (QExpr_ScalarGroup select_list group_keys having input)
          (SqlError error)
  | ECardinality_ScalarGroup :
      forall select_list group_keys group_terms having input input_rows outcome,
        scalar_group_key_terms group_keys = Some group_terms ->
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_scalar_group_cardinality_outcome env select_list group_terms
          having (query_rows_bag input_rows) outcome ->
        eval_query_cardinality_outcome env
          (QExpr_ScalarGroup select_list group_keys having input) outcome
  | ECardinality_GroupingSetsChildError :
      forall grouping_sets input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_cardinality_outcome env
          (QExpr_GroupingSets grouping_sets input) (SqlError error)
  | ECardinality_GroupingSets :
      forall grouping_sets input input_rows outcome,
        eval_query_expr_outcome env input (SqlSuccess input_rows) ->
        eval_grouping_sets_cardinality_outcome env grouping_sets
          (query_rows_bag input_rows) outcome ->
        eval_query_cardinality_outcome env
          (QExpr_GroupingSets grouping_sets input) outcome
  | ECardinality_Project :
      forall select_list input outcome,
        eval_query_cardinality_outcome env input outcome ->
        eval_query_cardinality_outcome env
          (QExpr_Project select_list input) outcome
  | ECardinality_ScalarProject :
      forall select_list input outcome,
        eval_query_cardinality_outcome env input outcome ->
        eval_query_cardinality_outcome env
          (QExpr_ScalarProject select_list input) outcome
  | ECardinality_RowMap :
      forall outputs row_map input outcome,
        eval_query_cardinality_outcome env input outcome ->
        eval_query_cardinality_outcome env
          (QExpr_RowMap outputs row_map input) outcome
  | ECardinality_OrderBy :
      forall keys input outcome,
        eval_query_cardinality_outcome env input outcome ->
        eval_query_cardinality_outcome env (QExpr_OrderBy keys input) outcome
  | ECardinality_Fetch :
      forall count input outcome,
        eval_query_cardinality_outcome env input outcome ->
        eval_query_cardinality_outcome env (QExpr_Fetch count input)
          (query_fetch_cardinality_outcome count outcome)

(** Capped existential demand.  Target-only operators delegate without
    executing their target computations; FETCH 0 is decided without touching
    its child; filter scanning stops at the first accepted row.  Operators
    whose values affect cardinality retain their dedicated/full demand. *)
with eval_query_exists_outcome
    (env : Env.env T) :
    query_expr T relname -> sql_outcome (Bool.b (B T)) -> Prop :=
  | EExists_Demanded :
      forall query outcome,
        query_exists_requires_rows query = true ->
        eval_query_expr_outcome env query outcome ->
        eval_query_exists_outcome env query
          (query_exists_rows_outcome outcome)
  | EExists_Cardinality :
      forall query outcome,
        query_exists_uses_cardinality query = true ->
        eval_query_cardinality_outcome env query outcome ->
        eval_query_exists_outcome env query
          (query_exists_cardinality_outcome outcome)
  | EExists_Project :
      forall select_list input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env (QExpr_Project select_list input) outcome
  | EExists_ScalarProject :
      forall select_list input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env
          (QExpr_ScalarProject select_list input) outcome
  | EExists_RowMap :
      forall outputs row_map input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env
          (QExpr_RowMap outputs row_map input) outcome
  | EExists_FilterChildError :
      forall formula input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_exists_outcome env (QExpr_Filter formula input)
          (SqlError error)
  | EExists_FilterRows :
      forall formula input rows outcome,
        eval_query_expr_outcome env input (SqlSuccess rows) ->
        eval_filter_exists_outcome env formula rows outcome ->
        eval_query_exists_outcome env (QExpr_Filter formula input) outcome
  | EExists_ScalarFilterChildError :
      forall expression input error,
        eval_query_expr_outcome env input (SqlError error) ->
        eval_query_exists_outcome env (QExpr_ScalarFilter expression input)
          (SqlError error)
  | EExists_ScalarFilterRows :
      forall expression input rows outcome,
        eval_query_expr_outcome env input (SqlSuccess rows) ->
        eval_filter_exists_outcome env (FExpr_Scalar expression) rows outcome ->
        eval_query_exists_outcome env (QExpr_ScalarFilter expression input)
          outcome
  | EExists_Distinct :
      forall input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env (QExpr_Distinct input) outcome
  | EExists_OrderBy :
      forall keys input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env (QExpr_OrderBy keys input) outcome
  | EExists_FetchZero :
      forall input,
        query_expr_contains_analysis_error input = false ->
        eval_query_exists_outcome env (QExpr_Fetch O input)
          (SqlSuccess (Bool.false (B T)))
  | EExists_FetchPositive :
      forall count input outcome,
        eval_query_exists_outcome env input outcome ->
        eval_query_exists_outcome env (QExpr_Fetch (S count) input) outcome

with eval_filter_exists_outcome
    (env : Env.env T) :
    formula_expr T relname -> list tuple ->
    sql_outcome (Bool.b (B T)) -> Prop :=
  | EFilterExists_Nil :
      forall formula,
        eval_filter_exists_outcome env formula nil
          (SqlSuccess (Bool.false (B T)))
  | EFilterExists_HeadError :
      forall formula row rows error,
        eval_formula_expr_outcome (env_t T env row) formula
          (SqlError error) ->
        eval_filter_exists_outcome env formula (row :: rows)
          (SqlError error)
  | EFilterExists_HeadTrue :
      forall formula row rows truth,
        eval_formula_expr_outcome (env_t T env row) formula
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_filter_exists_outcome env formula (row :: rows)
          (SqlSuccess (Bool.true (B T)))
  | EFilterExists_HeadFalse :
      forall formula row rows truth outcome,
        eval_formula_expr_outcome (env_t T env row) formula
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_filter_exists_outcome env formula rows outcome ->
        eval_filter_exists_outcome env formula (row :: rows) outcome

with eval_filter_rows_outcome
    (env : Env.env T) :
    formula_expr T relname -> list tuple ->
    sql_outcome (list tuple) -> Prop :=
  | EFilterRows_Nil :
      forall formula,
        eval_filter_rows_outcome env formula nil (SqlSuccess nil)
  | EFilterRows_HeadError :
      forall formula row rows error,
        eval_formula_expr_outcome (env_t T env row) formula
          (SqlError error) ->
        eval_filter_rows_outcome env formula (row :: rows)
          (SqlError error)
  | EFilterRows_Cons :
      forall formula row rows truth tail,
        eval_formula_expr_outcome (env_t T env row) formula
          (SqlSuccess truth) ->
        eval_filter_rows_outcome env formula rows tail ->
        eval_filter_rows_outcome env formula (row :: rows)
          (filter_cons_outcome truth row tail)

(** Group processing evaluates aggregate finalization, HAVING, and projection
    from the logical groups formed by the enclosing aggregate operator. *)
with eval_groups_outcome
    (env : Env.env T) :
    _select_list T -> list (@aggterm T) -> formula_expr T relname ->
    list (list tuple) -> sql_outcome (list tuple) -> Prop :=
  | EGroups_Nil :
      forall select_list group_terms having,
        eval_groups_outcome env select_list group_terms having nil
          (SqlSuccess nil)
  | EGroups_AggregateError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list =
          Some error ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroups_HavingAggregateError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = Some error ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroups_HavingError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlError error) ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroups_HavingFalse :
      forall select_list group_terms having group groups truth outcome,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_groups_outcome env select_list group_terms having
          groups outcome ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups) outcome
  | EGroups_SelectError :
      forall select_list group_terms having group groups truth error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list =
          Some error ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroups_SelectSuccess :
      forall select_list group_terms having group groups truth tail,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_groups_outcome env select_list group_terms having
          groups tail ->
        eval_groups_outcome env select_list group_terms having
          (group :: groups)
          (group_cons_outcome
            (projection T
              (env_g T env (@Group_By T group_terms) group)
              (Select_List select_list)) tail)

(** Native grouped scalar evaluation mirrors [eval_groups_outcome] but builds
    each target row from the one scalar-expression evaluation selected for
    that group.  Aggregate finalization precedes HAVING, while scalar target
    callbacks and target subqueries remain dead when HAVING rejects a group. *)
with eval_scalar_groups_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue * attribute T) ->
    list (@aggterm T) -> scalar_expr T relname ScalarResultBoolean ->
    list (list tuple) -> sql_outcome (list tuple) -> Prop :=
  | EScalarGroups_Nil :
      forall select_list group_terms having,
        eval_scalar_groups_outcome env select_list group_terms having nil
          (SqlSuccess nil)
  | EScalarGroups_SelectAggregateError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list =
          Some error ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EScalarGroups_HavingAggregateError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = Some error ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EScalarGroups_HavingError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlError error) ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EScalarGroups_HavingFalse :
      forall select_list group_terms having group groups truth outcome,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_scalar_groups_outcome env select_list group_terms having
          groups outcome ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups) outcome
  | EScalarGroups_SelectError :
      forall select_list group_terms having group groups truth error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_scalar_values_outcome
          (env_g T env (@Group_By T group_terms) group)
          (map fst select_list) (SqlError error) ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EScalarGroups_SelectSuccess :
      forall select_list group_terms having group groups truth values tail,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_scalar_values_outcome
          (env_g T env (@Group_By T group_terms) group)
          (map fst select_list) (SqlSuccess values) ->
        eval_scalar_groups_outcome env select_list group_terms having
          groups tail ->
        eval_scalar_groups_outcome env select_list group_terms having
          (group :: groups)
          (group_cons_outcome (scalar_project_row select_list values) tail)

(** Grouping is a bag-consuming reset point.  The relation existentially
    chooses a row-list representative of the input bag and evaluates that
    representative without sorting it.  Consequently, order-sensitive
    aggregate transitions expose every result obtainable from a legal input
    permutation instead of silently selecting one canonical fold order. *)
with eval_group_bag_outcome
    (env : Env.env T) :
    _select_list T -> list (@aggterm T) -> formula_expr T relname ->
    bagT -> sql_outcome bagT -> Prop :=
  | EGroupBag_KeyError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          representative = Some error ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlError error)
  | EGroupBag_ProcessError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          representative = None ->
        eval_groups_outcome env select_list group_terms having
          (query_make_groups env representative group_terms)
          (SqlError error) ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlError error)
  | EGroupBag_Success :
      forall select_list group_terms having input_bag representative
             grouped_rows output_bag,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          representative = None ->
        eval_groups_outcome env select_list group_terms having
          (query_make_groups env representative group_terms)
          (SqlSuccess grouped_rows) ->
        query_same_rows_as_bag grouped_rows output_bag ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlSuccess output_bag)

with eval_scalar_group_bag_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue * attribute T) ->
    list (scalar_expr T relname ScalarResultValue) ->
    scalar_expr T relname ScalarResultBoolean ->
    bagT -> sql_outcome bagT -> Prop :=
  | EScalarGroupBag_KeyError :
      forall select_list group_keys group_terms having input_bag
             representative error,
        scalar_group_key_terms group_keys = Some group_terms ->
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = Some error ->
        eval_scalar_group_bag_outcome env select_list group_keys having
          input_bag (SqlError error)
  | EScalarGroupBag_ProcessError :
      forall select_list group_keys group_terms having input_bag
             representative error,
        scalar_group_key_terms group_keys = Some group_terms ->
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = None ->
        eval_scalar_groups_outcome env select_list group_terms having
          (query_make_groups env representative group_terms)
          (SqlError error) ->
        eval_scalar_group_bag_outcome env select_list group_keys having
          input_bag (SqlError error)
  | EScalarGroupBag_Success :
      forall select_list group_keys group_terms having input_bag
             representative grouped_rows output_bag,
        scalar_group_key_terms group_keys = Some group_terms ->
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = None ->
        eval_scalar_groups_outcome env select_list group_terms having
          (query_make_groups env representative group_terms)
          (SqlSuccess grouped_rows) ->
        query_same_rows_as_bag grouped_rows output_bag ->
        eval_scalar_group_bag_outcome env select_list group_keys having
          input_bag (SqlSuccess output_bag)

(** EXISTS does not evaluate ordinary target expressions, but PostgreSQL
    finalizes every aggregate owned by a grouped SELECT before applying
    HAVING.  Cardinality demand therefore checks target aggregate errors while
    leaving post-HAVING scalar target computation dead. *)
with eval_groups_cardinality_outcome
    (env : Env.env T) :
    _select_list T -> list (@aggterm T) -> formula_expr T relname ->
    list (list tuple) -> sql_outcome nat -> Prop :=
  | EGroupsCardinality_Nil :
      forall select_list group_terms having,
        eval_groups_cardinality_outcome env select_list group_terms having nil
          (SqlSuccess O)
  | EGroupsCardinality_SelectAggregateError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list =
          Some error ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroupsCardinality_HavingAggregateError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = Some error ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroupsCardinality_HavingError :
      forall select_list group_terms having group groups error,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlError error) ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (group :: groups) (SqlError error)
  | EGroupsCardinality_HavingFalse :
      forall select_list group_terms having group groups truth outcome,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_groups_cardinality_outcome env select_list group_terms having
          groups outcome ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (group :: groups) outcome
  | EGroupsCardinality_HavingTrue :
      forall select_list group_terms having group groups truth tail,
        @eval_select_list_aggregate_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_formula_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_formula_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_groups_cardinality_outcome env select_list group_terms having
          groups tail ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (group :: groups) (query_cardinality_cons_outcome tail)

with eval_group_cardinality_outcome
    (env : Env.env T) :
    _select_list T -> list (@aggterm T) -> formula_expr T relname ->
    bagT -> sql_outcome nat -> Prop :=
  | EGroupCardinality_KeyError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = Some error ->
        eval_group_cardinality_outcome env select_list group_terms having
          input_bag
          (SqlError error)
  | EGroupCardinality_Process :
      forall select_list group_terms having input_bag representative outcome,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = None ->
        eval_groups_cardinality_outcome env select_list group_terms having
          (query_make_groups env representative group_terms) outcome ->
        eval_group_cardinality_outcome env select_list group_terms having
          input_bag outcome

with eval_scalar_groups_cardinality_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue * attribute T) ->
    list (@aggterm T) -> scalar_expr T relname ScalarResultBoolean ->
    list (list tuple) -> sql_outcome nat -> Prop :=
  | EScalarGroupsCardinality_Nil :
      forall select_list group_terms having,
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having nil (SqlSuccess O)
  | EScalarGroupsCardinality_SelectAggregateError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list =
          Some error ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (group :: groups) (SqlError error)
  | EScalarGroupsCardinality_HavingAggregateError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = Some error ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (group :: groups) (SqlError error)
  | EScalarGroupsCardinality_HavingError :
      forall select_list group_terms having group groups error,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlError error) ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (group :: groups) (SqlError error)
  | EScalarGroupsCardinality_HavingFalse :
      forall select_list group_terms having group groups truth outcome,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = false ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having groups outcome ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (group :: groups) outcome
  | EScalarGroupsCardinality_HavingTrue :
      forall select_list group_terms having group groups truth tail,
        eval_scalar_select_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) select_list = None ->
        eval_scalar_expr_aggregate_runtime_error
          (env_g T env (@Group_By T group_terms) group) having = None ->
        eval_scalar_boolean_expr_outcome
          (env_g T env (@Group_By T group_terms) group) having
          (SqlSuccess truth) ->
        Bool.is_true (B T) truth = true ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having groups tail ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (group :: groups) (query_cardinality_cons_outcome tail)

with eval_scalar_group_cardinality_outcome
    (env : Env.env T) :
    list (scalar_expr T relname ScalarResultValue * attribute T) ->
    list (@aggterm T) -> scalar_expr T relname ScalarResultBoolean ->
    bagT -> sql_outcome nat -> Prop :=
  | EScalarGroupCardinality_KeyError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = Some error ->
        eval_scalar_group_cardinality_outcome env select_list group_terms
          having input_bag (SqlError error)
  | EScalarGroupCardinality_Process :
      forall select_list group_terms having input_bag representative outcome,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms representative = None ->
        eval_scalar_groups_cardinality_outcome env select_list group_terms
          having (query_make_groups env representative group_terms) outcome ->
        eval_scalar_group_cardinality_outcome env select_list group_terms
          having input_bag outcome

with eval_grouping_sets_cardinality_outcome
    (env : Env.env T) :
    list (query_grouping_set T) -> bagT -> sql_outcome nat -> Prop :=
  | EGroupingSetsCardinality_Nil :
      forall input_bag,
        eval_grouping_sets_cardinality_outcome env nil input_bag
          (SqlSuccess O)
  | EGroupingSetsCardinality_HeadError :
      forall select_list group_terms grouping_sets input_bag error,
        eval_group_cardinality_outcome env select_list group_terms FExpr_True
          input_bag (SqlError error) ->
        eval_grouping_sets_cardinality_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlError error)
  | EGroupingSetsCardinality_TailError :
      forall select_list group_terms grouping_sets input_bag head error,
        eval_group_cardinality_outcome env select_list group_terms FExpr_True
          input_bag (SqlSuccess head) ->
        eval_grouping_sets_cardinality_outcome env grouping_sets input_bag
          (SqlError error) ->
        eval_grouping_sets_cardinality_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlError error)
  | EGroupingSetsCardinality_ConsSuccess :
      forall select_list group_terms grouping_sets input_bag head tail,
        eval_group_cardinality_outcome env select_list group_terms FExpr_True
          input_bag (SqlSuccess head) ->
        eval_grouping_sets_cardinality_outcome env grouping_sets input_bag
          (SqlSuccess tail) ->
        eval_grouping_sets_cardinality_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlSuccess (head + tail))

(** Every branch consumes the same chosen child bag.  Successful branches are
    combined with bag UNION ALL; an error from any branch is an error for the
    whole grouping-sets operator.  The recursive relation never
    re-evaluates, clones, or otherwise re-chooses the child query outcome. *)
with eval_grouping_sets_bag_outcome
    (env : Env.env T) :
    list (query_grouping_set T) -> bagT -> sql_outcome bagT -> Prop :=
  | EGroupingSets_Nil :
      forall input_bag,
        eval_grouping_sets_bag_outcome env nil input_bag
          (SqlSuccess (Febag.empty BTupleT))
  | EGroupingSets_HeadError :
      forall select_list group_terms grouping_sets input_bag error,
        eval_group_bag_outcome env select_list group_terms FExpr_True input_bag
          (SqlError error) ->
        eval_grouping_sets_bag_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlError error)
  | EGroupingSets_TailError :
      forall select_list group_terms grouping_sets input_bag head_bag error,
        eval_group_bag_outcome env select_list group_terms FExpr_True input_bag
          (SqlSuccess head_bag) ->
        eval_grouping_sets_bag_outcome env grouping_sets input_bag
          (SqlError error) ->
        eval_grouping_sets_bag_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlError error)
  | EGroupingSets_ConsSuccess :
      forall select_list group_terms grouping_sets input_bag head_bag tail_bag,
        eval_group_bag_outcome env select_list group_terms FExpr_True input_bag
          (SqlSuccess head_bag) ->
        eval_grouping_sets_bag_outcome env grouping_sets input_bag
          (SqlSuccess tail_bag) ->
        eval_grouping_sets_bag_outcome env
          ((select_list, group_terms) :: grouping_sets) input_bag
          (SqlSuccess (query_set_bag Union head_bag tail_bag))

(** Row-major condition evaluation.  These two relations are mutual with the
    query/formula semantics so predicate subqueries consume their complete
    exact outcome relations.  A successful derivation fixes one matrix and
    the join output is derived only from that same matrix. *)
with eval_join_row_conditions_outcome
    (env : Env.env T) :
    formula_expr T relname -> tuple -> list tuple ->
    sql_outcome (list bool) -> Prop :=
  | EJoinRowConditions_Nil :
      forall predicate left,
        eval_join_row_conditions_outcome env predicate left nil
          (SqlSuccess nil)
  | EJoinRowConditions_HeadError :
      forall predicate left right rights error,
        eval_formula_expr_outcome
          (env_t T env (join_tuple T left right)) predicate
          (SqlError error) ->
        eval_join_row_conditions_outcome env predicate left
          (right :: rights) (SqlError error)
  | EJoinRowConditions_Cons :
      forall predicate left right rights truth flags,
        eval_formula_expr_outcome
          (env_t T env (join_tuple T left right)) predicate
          (SqlSuccess truth) ->
        eval_join_row_conditions_outcome env predicate left rights
          (SqlSuccess flags) ->
        eval_join_row_conditions_outcome env predicate left
          (right :: rights)
          (SqlSuccess (Bool.is_true (B T) truth :: flags))

with eval_join_conditions_outcome
    (env : Env.env T) :
    formula_expr T relname -> list tuple -> list tuple ->
    sql_outcome (list (list bool)) -> Prop :=
  | EJoinConditions_Nil :
      forall predicate rights,
        eval_join_conditions_outcome env predicate nil rights
          (SqlSuccess nil)
  | EJoinConditions_RowError :
      forall predicate left lefts rights error,
        eval_join_row_conditions_outcome env predicate left rights
          (SqlError error) ->
        eval_join_conditions_outcome env predicate (left :: lefts) rights
          (SqlError error)
  | EJoinConditions_Cons :
      forall predicate left lefts rights flags matrix,
        eval_join_row_conditions_outcome env predicate left rights
          (SqlSuccess flags) ->
        eval_join_conditions_outcome env predicate lefts rights
          (SqlSuccess matrix) ->
        eval_join_conditions_outcome env predicate (left :: lefts) rights
          (SqlSuccess (flags :: matrix))

(** A join is an order-insensitive reset.  It consumes the two possible child
    bags selected by the parent rule, then quotient-saturates condition and
    projection evaluation over every representative of those bags.  Thus
    error order is explicit without allowing different join branches to pick
    different child outcomes. *)
with eval_join_bag_outcome
    (env : Env.env T) :
    query_join_kind -> formula_expr T relname ->
    _select_list T -> _select_list T -> _select_list T ->
    bagT -> bagT -> sql_outcome bagT -> Prop :=
  | EJoinBag_ConditionError :
      forall kind predicate matched_select left_select right_select
             left_bag right_bag left_rows right_rows error,
        query_same_rows_as_bag left_rows left_bag ->
        query_same_rows_as_bag right_rows right_bag ->
        eval_join_conditions_outcome env predicate left_rows right_rows
          (SqlError error) ->
        eval_join_bag_outcome env kind predicate
          matched_select left_select right_select left_bag right_bag
          (SqlError error)
  | EJoinBag_ProjectionError :
      forall kind predicate matched_select left_select right_select
             left_bag right_bag left_rows right_rows matrix error,
        query_same_rows_as_bag left_rows left_bag ->
        query_same_rows_as_bag right_rows right_bag ->
        eval_join_conditions_outcome env predicate left_rows right_rows
          (SqlSuccess matrix) ->
        project_join_sources_outcome env
          matched_select left_select right_select
          (query_join_sources kind left_rows right_rows matrix) =
          SqlError error ->
        eval_join_bag_outcome env kind predicate
          matched_select left_select right_select left_bag right_bag
          (SqlError error)
  | EJoinBag_Success :
      forall kind predicate matched_select left_select right_select
             left_bag right_bag left_rows right_rows matrix projected
             output_bag,
        query_same_rows_as_bag left_rows left_bag ->
        query_same_rows_as_bag right_rows right_bag ->
        eval_join_conditions_outcome env predicate left_rows right_rows
          (SqlSuccess matrix) ->
        project_join_sources_outcome env
          matched_select left_select right_select
          (query_join_sources kind left_rows right_rows matrix) =
          SqlSuccess projected ->
        query_same_rows_as_bag projected output_bag ->
        eval_join_bag_outcome env kind predicate
          matched_select left_select right_select left_bag right_bag
          (SqlSuccess output_bag)

(** Cardinality-only join evaluation retains child and ON-condition demand,
    but never evaluates the matched/unmatched target projection lists. *)
with eval_join_cardinality_outcome
    (env : Env.env T) :
    query_join_kind -> formula_expr T relname ->
    bagT -> bagT -> sql_outcome nat -> Prop :=
  | EJoinCardinality_ConditionError :
      forall kind predicate left_bag right_bag left_rows right_rows error,
        query_same_rows_as_bag left_rows left_bag ->
        query_same_rows_as_bag right_rows right_bag ->
        eval_join_conditions_outcome env predicate left_rows right_rows
          (SqlError error) ->
        eval_join_cardinality_outcome env kind predicate left_bag right_bag
          (SqlError error)
  | EJoinCardinality_Success :
      forall kind predicate left_bag right_bag left_rows right_rows matrix,
        query_same_rows_as_bag left_rows left_bag ->
        query_same_rows_as_bag right_rows right_bag ->
        eval_join_conditions_outcome env predicate left_rows right_rows
          (SqlSuccess matrix) ->
        eval_join_cardinality_outcome env kind predicate left_bag right_bag
          (SqlSuccess
            (length (query_join_sources kind left_rows right_rows matrix))).

(** Observation equivalence is success-only: both sides must have a success,
    neither may produce an error, and their legal successful lists are exactly
    the same.  It deliberately says nothing about the static result schema. *)
Definition query_expr_observation_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  successful_relation_equiv
    (@ordered_rows_equiv T)
    (eval_query_expr_outcome env left)
    (eval_query_expr_outcome env right).

(** SQL query equivalence preserves the authoritative ordered output schema.
    This is essential even for empty results and for two projections with the
    same label set in a different order: positional SQL consumers distinguish
    both cases. *)
Definition query_expr_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  query_expr_observation_equiv env left right.

(** Error-preserving observation equivalence compares the complete relation of
    legal outcomes.  Both relations must be inhabited, successful row lists
    are exact, and every runtime-error category must be exposed by both sides. *)
Definition query_expr_outcome_observation_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  outcome_relation_equiv (@ordered_rows_equiv T)
    (eval_query_expr_outcome env left)
    (eval_query_expr_outcome env right).

(** Error-preserving query equivalence retains the same authoritative output
    schema requirement as success-only equivalence. *)
Definition query_expr_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  query_expr_outcome_observation_equiv env left right.

(** Safe equivalence is a stronger certificate than error-preserving
    equivalence.  This bridge lets a proof agent choose the safe route when it
    can discharge safety; no external classifier is trusted to make that
    semantic decision. *)
Lemma query_expr_observation_equiv_implies_outcome_observation_equiv :
  forall env left right,
    query_expr_observation_equiv env left right ->
    query_expr_outcome_observation_equiv env left right.
Proof.
intros env left right Hequiv.
unfold query_expr_observation_equiv,
  query_expr_outcome_observation_equiv in *.
now apply successful_relation_equiv_implies_outcome_relation_equiv.
Qed.

Lemma query_expr_equiv_implies_outcome_equiv :
  forall env left right,
    query_expr_equiv env left right ->
    query_expr_outcome_equiv env left right.
Proof.
intros env left right [Houtputs Hobservations].
split; [exact Houtputs |].
now apply query_expr_observation_equiv_implies_outcome_observation_equiv.
Qed.

(** A query program is an ordered, stateless sequence of read-only query
    expressions evaluated against the same database and outer environment.
    Program equivalence is deliberately pointwise: it preserves statement
    count and order, keeps each statement's independent result shape, and
    inherits the success and runtime-safety requirements of
    [query_expr_equiv].  State-changing SQL statements are outside this
    syntax and must be rejected by the frontend rather than encoded here. *)
Fixpoint query_program_equiv
    (env : Env.env T)
    (left right : list (query_expr T relname)) : Prop :=
  match left, right with
  | nil, nil => True
  | left_query :: left_program, right_query :: right_program =>
      query_expr_equiv env left_query right_query /\
      query_program_equiv env left_program right_program
  | _, _ => False
  end.

(** Pointwise error-preserving equivalence for ordered read-only programs. *)
Fixpoint query_program_outcome_equiv
    (env : Env.env T)
    (left right : list (query_expr T relname)) : Prop :=
  match left, right with
  | nil, nil => True
  | left_query :: left_program, right_query :: right_program =>
      query_expr_outcome_equiv env left_query right_query /\
      query_program_outcome_equiv env left_program right_program
  | _, _ => False
  end.

Lemma query_program_equiv_nil :
  forall env,
    query_program_equiv env nil nil.
Proof.
intros; exact I.
Qed.

Lemma query_program_equiv_cons :
  forall env left_query left_program right_query right_program,
    query_program_equiv env
      (left_query :: left_program) (right_query :: right_program) <->
    query_expr_equiv env left_query right_query /\
    query_program_equiv env left_program right_program.
Proof.
reflexivity.
Qed.

Lemma query_program_outcome_equiv_nil :
  forall env,
    query_program_outcome_equiv env nil nil.
Proof.
intros; exact I.
Qed.

Lemma query_program_outcome_equiv_cons :
  forall env left_query left_program right_query right_program,
    query_program_outcome_equiv env
      (left_query :: left_program) (right_query :: right_program) <->
    query_expr_outcome_equiv env left_query right_query /\
    query_program_outcome_equiv env left_program right_program.
Proof.
reflexivity.
Qed.

Lemma query_program_equiv_implies_outcome_equiv :
  forall env left right,
    query_program_equiv env left right ->
    query_program_outcome_equiv env left right.
Proof.
intros env left; induction left as [| left_query left_program IH];
  intros [| right_query right_program] Hequiv; cbn in *; try contradiction.
- exact I.
- destruct Hequiv as [Hquery Hprogram].
  split.
  + now apply query_expr_equiv_implies_outcome_equiv.
  + now apply IH.
Qed.

Lemma query_program_equiv_length :
  forall env left right,
    query_program_equiv env left right ->
    length left = length right.
Proof.
intros env left; induction left as [| left_query left_program IH];
  intros [| right_query right_program] Hequiv; cbn in *; try contradiction.
- reflexivity.
- destruct Hequiv as [_ Hprogram].
  now rewrite (IH right_program Hprogram).
Qed.

Theorem query_program_equiv_iff_Forall2 :
  forall env left right,
    query_program_equiv env left right <->
    Forall2 (query_expr_equiv env) left right.
Proof.
intros env left; induction left as [| left_query left_program IH];
  intros [| right_query right_program]; cbn.
- split; [intro; constructor | intro; exact I].
- split; [contradiction | intro H; inversion H].
- split; [contradiction | intro H; inversion H].
- rewrite IH.
  split.
  + intros [Hquery Hprogram]. now constructor.
  + intro H; inversion H; subst; now split.
Qed.

End Sec.

Arguments query_expr_outputs {T relname} _.
Arguments query_expr_sort {T relname} _.
Arguments row_map_rows_outcome {T} _ _.
Arguments query_rows_bag {T} _.
Arguments query_table_bag {T relname} basesort instance _ _.
Arguments query_canonical_rows {T} _.
Arguments query_rank_bag_rows {T} _.
Arguments query_same_rows_as_bag {T} _ _.
Arguments order_by_rows {T} value_is_null _ _ _.
Arguments query_set_bag {T} _ _ _.
Arguments query_natural_join_compatible {T} value_is_null _ _.
Arguments query_natural_join_bag {T} value_is_null _ _.
Arguments query_cross_join_bag {T} _ _.
Arguments query_distinct_bag {T} _.
