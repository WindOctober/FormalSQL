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
        FTerms ATerms Projection SqlAlgebra SqlOutcome SqlErrorSemantics SqlOrder
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
Hypothesis contains_nulls : tuple -> bool.
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
  | QExpr_Bag outputs _ => outputs
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
  | QExpr_RowMap outputs _ _ => outputs
  | QExpr_GroupingSets grouping_sets _ =>
      query_grouping_sets_outputs grouping_sets
  | QExpr_Rank _ _ rank_attribute _ input =>
      query_expr_outputs input ++ rank_attribute :: nil
  | QExpr_Window _ _ items input =>
      query_expr_outputs input ++ map (@qwi_attribute T) items
  | QExpr_Filter _ input
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
  end.

(** Concrete bag operations used at the permutation-closing operators. *)
Definition query_rows_bag (rows : list tuple) : bagT :=
  Febag.mk_bag BTupleT rows.

(** Bag-consuming operators use this canonical representative.  In
    particular, grouping and quantified predicates must not expose the
    arbitrary representative list chosen for one possible input bag. *)
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
    (env : Env.env T) (position : nat) (prefix : list tuple)
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
  end.

Fixpoint query_window_items_outcome
    (env : Env.env T) (position : nat) (prefix : list tuple)
    (items : list (query_window_item T)) (row : tuple) :
    option (sql_outcome tuple) :=
  match items with
  | nil => Some (SqlSuccess row)
  | item :: rest =>
      match query_window_item_value_outcome env position prefix item with
      | None => None
      | Some (SqlError error) => Some (SqlError error)
      | Some (SqlSuccess value) =>
          query_window_items_outcome env position prefix rest
            (query_window_attach_value (qwi_attribute item) value row)
      end
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
      match query_window_items_outcome env current_position current_prefix
              items row with
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

(**
  The four relations below form one big-step semantics.  Formula subqueries
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
  | EQuery_BagError :
      forall outputs bag_query error,
        @eval_query_outcome T relname basesort instance unknown contains_nulls
          symbol_runtime_error aggregate_runtime_error env bag_query =
          SqlError error ->
        eval_query_expr_outcome env (QExpr_Bag outputs bag_query) (SqlError error)
  | EQuery_BagSuccess :
      forall outputs bag_query bag rows,
        @eval_query_outcome T relname basesort instance unknown contains_nulls
          symbol_runtime_error aggregate_runtime_error env bag_query =
          SqlSuccess bag ->
        query_same_rows_as_bag rows bag ->
        eval_query_expr_outcome env (QExpr_Bag outputs bag_query) (SqlSuccess rows)
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
        eval_query_expr_outcome env subquery (SqlError error) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery) (SqlError error)
  | EFormula_ExistsSuccessEmpty :
      forall subquery,
        eval_query_expr_outcome env subquery (SqlSuccess nil) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery)
          (SqlSuccess (Bool.false (B T)))
  | EFormula_ExistsSuccessNonempty :
      forall subquery row rows,
        eval_query_expr_outcome env subquery (SqlSuccess (row :: rows)) ->
        eval_formula_expr_outcome env (FExpr_Exists subquery)
          (SqlSuccess (Bool.true (B T)))

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

(** Grouping is a bag-consuming reset point.  The relation existentially
    chooses any row-list representative of the input bag before running the
    canonical grouping computation.  This quotient saturation makes every
    representation-sensitive success or error an explicit legal outcome,
    instead of silently choosing one represented bag value. *)
with eval_group_bag_outcome
    (env : Env.env T) :
    _select_list T -> list (@aggterm T) -> formula_expr T relname ->
    bagT -> sql_outcome bagT -> Prop :=
  | EGroupBag_KeyError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          (query_canonical_rows representative) = Some error ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlError error)
  | EGroupBag_ProcessError :
      forall select_list group_terms having input_bag representative error,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          (query_canonical_rows representative) = None ->
        eval_groups_outcome env select_list group_terms having
          (query_make_groups env
            (query_canonical_rows representative) group_terms)
          (SqlError error) ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlError error)
  | EGroupBag_Success :
      forall select_list group_terms having input_bag representative
             grouped_rows output_bag,
        query_same_rows_as_bag representative input_bag ->
        group_keys_runtime_error env group_terms
          (query_canonical_rows representative) = None ->
        eval_groups_outcome env select_list group_terms having
          (query_make_groups env
            (query_canonical_rows representative) group_terms)
          (SqlSuccess grouped_rows) ->
        query_same_rows_as_bag grouped_rows output_bag ->
        eval_group_bag_outcome env select_list group_terms having input_bag
          (SqlSuccess output_bag)

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
          (SqlSuccess output_bag).

(** Observation equivalence is success-only: both sides must have a success,
    neither may produce an error, and their legal successful lists are exactly
    the same.  It deliberately says nothing about the static result schema. *)
Definition query_expr_observation_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  successful_relation_equiv
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
  outcome_relation_equiv eq
    (eval_query_expr_outcome env left)
    (eval_query_expr_outcome env right).

(** Error-preserving query equivalence retains the same authoritative output
    schema requirement as success-only equivalence. *)
Definition query_expr_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  query_expr_outputs left = query_expr_outputs right /\
  query_expr_outcome_observation_equiv env left right.

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
Arguments query_program_equiv {T relname} basesort instance unknown contains_nulls
  symbol_runtime_error aggregate_runtime_error value_is_null env _ _.
Arguments query_rows_bag {T} _.
Arguments query_canonical_rows {T} _.
Arguments query_rank_bag_rows {T} _.
Arguments query_same_rows_as_bag {T} _ _.
Arguments order_by_rows {T} value_is_null _ _ _.
Arguments query_set_bag {T} _ _ _.
Arguments query_natural_join_compatible {T} value_is_null _ _.
Arguments query_natural_join_bag {T} value_is_null _ _.
Arguments query_cross_join_bag {T} _ _.
Arguments query_distinct_bag {T} _.
