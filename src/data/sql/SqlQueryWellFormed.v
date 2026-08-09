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

Arguments Group_By {T}.

Local Definition setA := Fset.set (A T).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> setA.
Hypothesis leaf_has_type : type T -> @aggterm T -> Prop.
Hypothesis call_has_type :
  type T -> scalar_operator T -> list (type T) -> Prop.
Hypothesis predicate_has_types : predicate T -> list (type T) -> Prop.
Hypothesis rank_type boolean_type : type T.
Hypothesis value_is_null : value T -> bool.

Fixpoint prop_forall {A : Type} (predicate : A -> Prop) (values : list A) : Prop :=
  match values with
  | nil => True
  | value :: rest => predicate value /\ prop_forall predicate rest
  end.

(** A flattened Boolean expression with [n] operands uses a triangular
    insertion network: operand zero needs no choice, operand one needs one
    choice, and so on.  The exact shape is part of typed admissibility rather
    than an unchecked convention of the Rust emitter. *)
Fixpoint boolean_insertion_sites_well_formed
    (expected : nat) (site_rows : list (list boolean_site)) : Prop :=
  match site_rows with
  | nil => True
  | sites :: rest =>
      length sites = expected /\
      boolean_insertion_sites_well_formed (S expected) rest
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
    (select_list : @query_select_list T relname) : Prop :=
  query_output_attributes_unique (scalar_select_outputs select_list).

Definition query_output_sorts_disjoint (left right : setA) : Prop :=
  (left interS right) =S= Fset.empty (A T).

Definition query_grouping_sets_well_formed
    (grouping_sets : list (@query_grouping_set T relname)) : Prop :=
  match grouping_sets with
  | nil => False
  | (first_select, _) :: rest =>
      query_select_list_outputs_unique first_select /\
      Forall
        (fun grouping_set =>
          scalar_select_outputs (fst grouping_set) =
            scalar_select_outputs first_select /\
          query_select_list_outputs_unique (fst grouping_set))
        rest
  end.

(** Every join source that can be emitted for a kind must project the declared
    result schema.  Projection lists unused by that join kind need no premise. *)
Definition query_join_projection_sorts_compatible
    (kind : query_join_kind)
    (matched_select left_select right_select : @query_select_list T relname) :
    Prop :=
  match kind with
  | QueryJoinInner => True
  | QueryJoinLeft =>
      @query_outputs_sort T (scalar_select_outputs matched_select) =S=
        @query_outputs_sort T (scalar_select_outputs left_select)
  | QueryJoinRight =>
      @query_outputs_sort T (scalar_select_outputs matched_select) =S=
        @query_outputs_sort T (scalar_select_outputs right_select)
  | QueryJoinFull =>
      @query_outputs_sort T (scalar_select_outputs matched_select) =S=
        @query_outputs_sort T (scalar_select_outputs left_select) /\
      @query_outputs_sort T (scalar_select_outputs matched_select) =S=
        @query_outputs_sort T (scalar_select_outputs right_select)
  | QueryJoinSemi | QueryJoinAnti => True
  end.

(** Only projection lists evaluated by a join kind carry obligations.  This
    mirrors [query_join_projection_sorts_compatible] and prevents
    [projection] from silently collapsing two output positions into one tuple
    label. *)
Definition query_join_projections_unique
    (kind : query_join_kind)
    (matched_select left_select right_select : @query_select_list T relname) :
    Prop :=
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

(** Typed IN alignment is positional: each left value expression must have
    exactly the SQL type of the corresponding subquery output. *)
Definition scalar_expr_in_positionally_aligned
    (arguments : list (scalar_expr T relname ScalarResultValue))
    (right_outputs : list (attribute T)) : Prop :=
  arguments <> nil /\
  length arguments = length right_outputs /\
  map scalar_expr_type arguments = map (type_of_attribute T) right_outputs.

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
      scalar_expr_admissible ScalarPhaseOn predicate /\
      query_expr_admissible left_query /\
      query_expr_admissible right_query /\
      query_join_projection_sorts_compatible
        kind matched_select left_select right_select /\
      query_join_projections_unique
        kind matched_select left_select right_select /\
      match kind with
      | QueryJoinInner =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            matched_select
      | QueryJoinLeft =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            matched_select /\
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            left_select
      | QueryJoinRight =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            matched_select /\
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            right_select
      | QueryJoinFull =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            matched_select /\
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            left_select /\
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            right_select
      | QueryJoinSemi | QueryJoinAnti =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseRowSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            left_select
      end
  | QExpr_Project select_list input =>
      query_expr_admissible input /\
      query_select_list_outputs_unique select_list /\
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
  | QExpr_Filter expression input =>
      query_expr_admissible input /\
      scalar_expr_admissible ScalarPhaseWhere expression
  | QExpr_Group select_list group_keys having input =>
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
      prop_forall
        (fun grouping_set =>
          prop_forall
            (fun item =>
              scalar_expr_admissible ScalarPhaseSelect (fst item) /\
              scalar_expr_type (fst item) =
                type_of_attribute T (snd item))
            (fst grouping_set) /\
          prop_forall
            (@scalar_expr_admissible ScalarPhaseGroupBy ScalarResultValue)
            (snd grouping_set) /\
          exists group_terms,
            scalar_group_key_terms (snd grouping_set) = Some group_terms)
        grouping_sets
  | QExpr_Rank partition_keys order_keys rank_attribute _ input =>
      query_expr_admissible input /\
      type_of_attribute T rank_attribute = rank_type /\
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
      prop_forall
        (fun item =>
          match item with
          | QueryWindowItem output function =>
              match function with
              | QueryWindowRowNumber _ =>
                  type_of_attribute T output = rank_type
              | QueryWindowAggregate term
              | QueryWindowFullPartitionAggregate term =>
                  leaf_has_type (type_of_attribute T output) term
              end
          end)
        items /\
      length (map (@qwi_attribute T) items) =
        Fset.cardinal (A T)
          (Fset.mk_set (A T) (map (@qwi_attribute T) items))
  | QExpr_OrderBy keys input =>
      query_expr_admissible input /\
      query_sort_keys_in_scope (query_expr_sort input) keys
  end

with scalar_expr_admissible
    (phase : scalar_phase) {kind : scalar_result_kind}
    (expression : scalar_expr T relname kind) : Prop :=
  match expression with
  | SExpr_Leaf result_type term =>
      aggterm_phase_admissible phase term /\
      leaf_has_type result_type term
  | SExpr_Call result_type operator arguments =>
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      call_has_type result_type operator (map scalar_expr_type arguments)
  | SExpr_Case result_type condition then_expression else_expression =>
      scalar_expr_admissible phase condition /\
      scalar_expr_admissible phase then_expression /\
      scalar_expr_admissible phase else_expression /\
      scalar_expr_type then_expression = result_type /\
      scalar_expr_type else_expression = result_type
  | SExpr_BoolValue result_type embed inner =>
      scalar_expr_admissible phase inner /\
      forall truth, type_of_value T (embed truth) = result_type
  | SExpr_ValueBool _ inner =>
      scalar_expr_admissible phase inner /\
      scalar_expr_type inner = boolean_type
  | SExpr_Pred predicate arguments =>
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      length arguments = predicate_arity T predicate /\
      predicate_has_types predicate (map scalar_expr_type arguments)
  | SExpr_ConjList site_rows _ expressions =>
      expressions <> nil /\
      length site_rows = length expressions /\
      boolean_insertion_sites_well_formed 0 site_rows /\
      prop_forall (@scalar_expr_admissible phase ScalarResultBoolean)
        expressions
  | SExpr_Not inner => scalar_expr_admissible phase inner
  | SExpr_True => True
  | SExpr_Quant _ predicate arguments subquery =>
      scalar_phase_allows_subquery phase = true /\
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      query_expr_admissible subquery /\
      arguments <> nil /\
      length arguments = length (query_expr_outputs subquery) /\
      length arguments + length (query_expr_outputs subquery) =
        predicate_arity T predicate /\
      predicate_has_types predicate
        (map scalar_expr_type arguments ++
          map (type_of_attribute T) (query_expr_outputs subquery))
  | SExpr_In arguments subquery =>
      scalar_phase_allows_subquery phase = true /\
      prop_forall
        (@scalar_expr_admissible phase ScalarResultValue) arguments /\
      query_expr_admissible subquery /\
      scalar_expr_in_positionally_aligned arguments
        (query_expr_outputs subquery)
  | SExpr_Exists subquery =>
      scalar_phase_allows_subquery phase = true /\
      query_expr_admissible subquery
  | SExpr_Subquery result_type null_value subquery =>
      scalar_phase_allows_subquery phase = true /\
      query_expr_admissible subquery /\
      value_is_null null_value = true /\
      type_of_value T null_value = result_type /\
      match query_expr_outputs subquery with
      | attribute :: nil => type_of_attribute T attribute = result_type
      | _ => False
      end
  end.

Lemma scalar_expr_in_positionally_aligned_arity :
  forall arguments right_outputs,
    scalar_expr_in_positionally_aligned arguments right_outputs ->
    length arguments = length right_outputs.
Proof.
intros arguments right_outputs [_ [Harity _]].
exact Harity.
Qed.

Lemma scalar_expr_in_positionally_aligned_nonempty :
  forall arguments right_outputs,
    scalar_expr_in_positionally_aligned arguments right_outputs ->
    arguments <> nil.
Proof.
intros arguments right_outputs [Hnonempty _]; exact Hnonempty.
Qed.

Lemma scalar_expr_in_positionally_aligned_types :
  forall arguments right_outputs,
    scalar_expr_in_positionally_aligned arguments right_outputs ->
    map scalar_expr_type arguments =
      map (type_of_attribute T) right_outputs.
Proof.
intros arguments right_outputs [_ [_ Htypes]].
exact Htypes.
Qed.

Lemma scalar_expr_admissible_in_positionally_aligned :
  forall phase arguments subquery,
    scalar_expr_admissible phase (SExpr_In arguments subquery) ->
    scalar_expr_in_positionally_aligned arguments
      (query_expr_outputs subquery).
Proof.
intros phase arguments subquery Hadmissible.
simpl in Hadmissible; tauto.
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

Lemma prop_forall_iff_Forall :
  forall (A : Type) (predicate : A -> Prop) values,
    prop_forall predicate values <-> Forall predicate values.
Proof.
intros A predicate values; induction values as [|value rest IH]; cbn.
- split; intro; constructor.
- rewrite IH; split.
  + intros [Hvalue Hrest]; constructor; assumption.
  + intro Hall; inversion Hall; subst; now split.
Qed.

Lemma prop_forall_firstn :
  forall (A : Type) (predicate : A -> Prop) count values,
    prop_forall predicate values ->
    prop_forall predicate (firstn count values).
Proof.
intros A predicate count; induction count as [|count IH].
- intros values Hall; cbn; exact I.
- intros [|value values] Hall.
  + cbn; exact I.
  + cbn in Hall |-; destruct Hall as [Hvalue Hvalues].
    split; [exact Hvalue | exact (IH values Hvalues)].
Qed.

Lemma prop_forall_app :
  forall (A : Type) (predicate : A -> Prop) left right,
    prop_forall predicate left ->
    prop_forall predicate right ->
    prop_forall predicate (left ++ right).
Proof.
intros A predicate left; induction left as [|value rest IH].
- intros right Hleft Hright; cbn; exact Hright.
- intros right Hleft Hright; cbn in Hleft |-.
  destruct Hleft as [Hvalue Hrest].
  split; [exact Hvalue | exact (IH right Hrest Hright)].
Qed.

Arguments query_expr_admissible {T relname}
  basesort leaf_has_type call_has_type predicate_has_types
  rank_type boolean_type value_is_null _.
Arguments scalar_expr_admissible {T relname}
  basesort leaf_has_type call_has_type predicate_has_types
  rank_type boolean_type value_is_null _ {_} _.
