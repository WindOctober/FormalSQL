(************************************************************************************)
(** Integrity constraints for generated FormalSQL base-table schemas.              *)
(************************************************************************************)

From SQLFS Require Import
  SqlSyntax GenericInstance Values FTuples FiniteBag FiniteCollection
  FiniteSet OrderedSet SqlErrorSemantics SqlOutcome Formula Interp
  Env Bool3 ValueCore ValueInteger ValueString.
From Stdlib Require Import List SetoidList String ZArith.

Import ListNotations.
Import Tuple.

Definition constraint_term : Type := @funterm TNull.
(** PostgreSQL CHECK constraints and partial-index predicates do not admit
    relational subqueries.  Instantiating the generic formula syntax with the
    empty carrier records that boundary in the type instead of retaining a
    second query language solely for schema metadata. *)
Definition constraint_query : Type := Empty_set.
Definition constraint_formula : Type :=
  @sql_formula TNull constraint_query.

Definition eliminate_constraint_query {A : Type}
    (query : constraint_query) : A :=
  match query with end.

Definition eval_constraint_query
    (_ : list (Fset.set (A TNull) * group_by TNull *
              list (tuple TNull)))
    (query : constraint_query) :
    Febag.bag (Fecol.CBag (CTuple TNull)) :=
  eliminate_constraint_query query.


Record foreign_key_constraint : Type := ForeignKeyConstraint {
  foreign_key_columns : list (attribute TNull);
  foreign_key_referenced_relation : relname;
  foreign_key_referenced_columns : list (attribute TNull)
}.

Record check_constraint : Type := CheckConstraint {
  check_constraint_formula : constraint_formula
}.

Record unique_index_constraint : Type := UniqueIndexConstraint {
  unique_index_terms : list constraint_term;
  unique_index_predicate : option constraint_formula
}.

Record table_constraint : Type := TableConstraint {
  constraint_relation : relname;
  constraint_not_null : list (attribute TNull);
  constraint_primary_key : option (list (attribute TNull));
  constraint_unique_keys : list (list (attribute TNull));
  constraint_foreign_keys : list foreign_key_constraint;
  constraint_checks : list check_constraint;
  constraint_unique_indexes : list unique_index_constraint
}.

(** PostgreSQL foreign-key equality is selected from the referenced key's
    operator family and is therefore not, in general, ordinary mixed-type SQL
    equality.  The current model admits identical declared types plus the exact
    INTEGER/BIGINT cross-type family.  In particular, heterogeneous character
    types fail closed until their directional referential-integrity casts are
    modeled explicitly. *)
Definition foreign_key_attribute_compatible
    (source referenced : attribute TNull) : Prop :=
  match source, referenced with
  | Attr_string _ source_typmod, Attr_string _ referenced_typmod =>
      source_typmod = referenced_typmod
  | Attr_Z _, Attr_Z _
  | Attr_int32 _, Attr_int32 _
  | Attr_int64 _, Attr_int64 _
  | Attr_int32 _, Attr_int64 _
  | Attr_int64 _, Attr_int32 _
  | Attr_bool _, Attr_bool _
  | Attr_float _, Attr_float _
  | Attr_double _, Attr_double _
  | Attr_numeric _, Attr_numeric _
  | Attr_date _, Attr_date _
  | Attr_time _, Attr_time _ => True
  | Attr_decimal _ source_precision source_scale,
      Attr_decimal _ referenced_precision referenced_scale =>
      source_precision = referenced_precision /\
      source_scale = referenced_scale
  | Attr_timestamp _ source_precision,
      Attr_timestamp _ referenced_precision
  | Attr_timestamptz _ source_precision,
      Attr_timestamptz _ referenced_precision =>
      source_precision = referenced_precision
  | _, _ => False
  end.

(** [Febag.elements] is intentionally used rather than a set conversion: its
    list contains one element for every bag occurrence, so duplicate stored
    rows remain observable to primary-key uniqueness. *)
Definition instance_rows
    (db : db_state) (relation : relname) : list (tuple TNull) :=
  Febag.elements
    (Fecol.CBag (CTuple TNull))
    (@_instance TNull db relation).

Definition project_row
    (attributes : list (attribute TNull))
    (row : tuple TNull) : list (value TNull) :=
  map (dot TNull row) attributes.

Definition row_attributes_not_null
    (attributes : list (attribute TNull))
    (row : tuple TNull) : Prop :=
  forall attribute,
    In attribute attributes ->
    NullValues.is_null_value (dot TNull row attribute) = false.

Definition rows_attributes_not_null
    (attributes : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  forall row,
    In row rows ->
    row_attributes_not_null attributes row.

Definition sql_value_equal_true
    (left right : value TNull) : Prop :=
  NullValues.interp_predicate PredicateEq [left; right] = true3.

Fixpoint sql_key_equal_true
    (left right : list (value TNull)) : Prop :=
  match left, right with
  | nil, nil => True
  | left_value :: left_rest, right_value :: right_rest =>
      sql_value_equal_true left_value right_value /\
      sql_key_equal_true left_rest right_rest
  | _, _ => False
  end.

(** Equality used by referential integrity is indexed by the declared source
    and referenced attributes.  Its final comparison is the FormalSQL
    PostgreSQL predicate interpreter; the surrounding premises prevent an
    accidental comparison outside the declared equality family or against an
    ill-typed cell. *)
Definition foreign_key_value_equal_true
    (source_attribute referenced_attribute : attribute TNull)
    (source_value referenced_value : value TNull) : Prop :=
  foreign_key_attribute_compatible source_attribute referenced_attribute /\
  value_conforms_attribute source_attribute source_value /\
  value_conforms_attribute referenced_attribute referenced_value /\
  sql_value_equal_true source_value referenced_value.

Fixpoint foreign_key_key_equal_true
    (source_attributes referenced_attributes : list (attribute TNull))
    (source_row referenced_row : tuple TNull) : Prop :=
  match source_attributes, referenced_attributes with
  | nil, nil => True
  | source_attribute :: source_rest,
      referenced_attribute :: referenced_rest =>
      foreign_key_value_equal_true source_attribute referenced_attribute
        (dot TNull source_row source_attribute)
        (dot TNull referenced_row referenced_attribute) /\
      foreign_key_key_equal_true source_rest referenced_rest
        source_row referenced_row
  | _, _ => False
  end.

(** [NoDupA] observes every list occurrence.  Repeated NULL-bearing keys are
    admitted because PostgreSQL equality is UNKNOWN, not TRUE, for NULL. *)
Definition unique_key_rows_conform
    (key : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  NoDupA sql_key_equal_true (map (project_row key) rows).

Definition unique_key_conforms
    (key : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  key <> nil /\ unique_key_rows_conform key rows.

Definition primary_key_conforms
    (primary_key : list (attribute TNull))
    (rows : list (tuple TNull)) : Prop :=
  primary_key <> nil /\
  rows_attributes_not_null primary_key rows /\
  unique_key_rows_conform primary_key rows.

Definition constraint_row_env (row : tuple TNull) : Env.env TNull :=
  env_t TNull nil row.

Definition eval_constraint_term
    (row : tuple TNull) (term : constraint_term) : value TNull :=
  @interp_funterm TNull (constraint_row_env row) term.

Definition constraint_term_runtime_error
    (row : tuple TNull) (term : constraint_term)
    : option sql_runtime_error :=
  @eval_funterm_runtime_error TNull
    NullValues.interp_scalar_operator_runtime_error
    (constraint_row_env row) term.

Definition eval_constraint_formula
    (_ : db_state) (row : tuple TNull) (formula : constraint_formula)
    : bool3 :=
  @eval_sql_formula TNull constraint_query
    unknown3 contains_nulls
    eval_constraint_query
    (constraint_row_env row) formula.

Definition constraint_formula_runtime_error
    (_ : db_state) (row : tuple TNull) (formula : constraint_formula)
    : option sql_runtime_error :=
  @eval_formula_runtime_error TNull
    NullValues.interp_scalar_operator_runtime_error
    NullValues.interp_aggregate_runtime_error
    constraint_query
    (fun _ query => eliminate_constraint_query query)
    (constraint_row_env row) formula.

Definition check_row_conforms
    (db : db_state) (check : check_constraint) (row : tuple TNull) : Prop :=
  constraint_formula_runtime_error db row (check_constraint_formula check) = None /\
  eval_constraint_formula db row (check_constraint_formula check) <> false3.

Definition check_constraint_conforms
    (db : db_state) (rows : list (tuple TNull))
    (check : check_constraint) : Prop :=
  Forall (check_row_conforms db check) rows.

Definition unique_index_key
    (terms : list constraint_term) (row : tuple TNull)
    : list (value TNull) :=
  map (eval_constraint_term row) terms.

Definition unique_index_predicate_error
    (db : db_state) (row : tuple TNull) (index : unique_index_constraint)
    : option sql_runtime_error :=
  match unique_index_predicate index with
  | None => None
  | Some predicate => constraint_formula_runtime_error db row predicate
  end.

Definition unique_index_predicate_truth
    (db : db_state) (row : tuple TNull) (index : unique_index_constraint)
    : bool3 :=
  match unique_index_predicate index with
  | None => true3
  | Some predicate => eval_constraint_formula db row predicate
  end.

Definition unique_index_row_participates
    (db : db_state) (index : unique_index_constraint)
    (row : tuple TNull) : bool :=
  match unique_index_predicate_error db row index,
        unique_index_predicate_truth db row index with
  | None, true3 => true
  | _, _ => false
  end.

Definition unique_index_row_terms_succeed
    (index : unique_index_constraint) (row : tuple TNull) : Prop :=
  Forall (fun term => constraint_term_runtime_error row term = None)
    (unique_index_terms index).

Definition unique_index_conforms
    (db : db_state) (rows : list (tuple TNull))
    (index : unique_index_constraint) : Prop :=
  unique_index_terms index <> nil /\
  (forall row,
    In row rows ->
    unique_index_predicate_error db row index = None) /\
  (forall row,
    In row rows ->
    unique_index_row_participates db index row = true ->
    unique_index_row_terms_succeed index row) /\
  NoDupA
    sql_key_equal_true
    (map (unique_index_key (unique_index_terms index))
      (filter (unique_index_row_participates db index) rows)).

Definition foreign_key_row_conforms_against
    (foreign_key : foreign_key_constraint)
    (referencing_row : tuple TNull)
    (referenced_rows : list (tuple TNull)) : Prop :=
  (exists attribute,
    In attribute (foreign_key_columns foreign_key) /\
    NullValues.is_null_value (dot TNull referencing_row attribute) = true) \/
  exists referenced_row,
    In referenced_row referenced_rows /\
    foreign_key_key_equal_true
      (foreign_key_columns foreign_key)
      (foreign_key_referenced_columns foreign_key)
      referencing_row referenced_row.

Definition foreign_key_conforms
    (db : db_state) (rows : list (tuple TNull))
    (foreign_key : foreign_key_constraint) : Prop :=
  foreign_key_columns foreign_key <> nil /\
  List.length (foreign_key_columns foreign_key) =
    List.length (foreign_key_referenced_columns foreign_key) /\
  forall row,
    In row rows ->
    foreign_key_row_conforms_against foreign_key row
      (instance_rows db (foreign_key_referenced_relation foreign_key)).

Definition table_declares_unique_key
    (constraint : table_constraint)
    (key : list (attribute TNull)) : Prop :=
  constraint_primary_key constraint = Some key \/
  In key (constraint_unique_keys constraint).

Definition foreign_key_reference_well_formed
    (constraints : list table_constraint)
    (foreign_key : foreign_key_constraint) : Prop :=
  foreign_key_columns foreign_key <> nil /\
  List.length (foreign_key_columns foreign_key) =
    List.length (foreign_key_referenced_columns foreign_key) /\
  Forall2 foreign_key_attribute_compatible
    (foreign_key_columns foreign_key)
    (foreign_key_referenced_columns foreign_key) /\
  exists referenced_constraint,
    In referenced_constraint constraints /\
    constraint_relation referenced_constraint =
      foreign_key_referenced_relation foreign_key /\
    table_declares_unique_key referenced_constraint
      (foreign_key_referenced_columns foreign_key).

Definition table_constraint_declarations_well_formed
    (constraints : list table_constraint)
    (constraint : table_constraint) : Prop :=
  match constraint_primary_key constraint with
  | None => True
  | Some key => key <> nil
  end /\
  Forall (fun key => key <> nil) (constraint_unique_keys constraint) /\
  Forall (foreign_key_reference_well_formed constraints)
    (constraint_foreign_keys constraint) /\
  Forall (fun index => unique_index_terms index <> nil)
    (constraint_unique_indexes constraint).

Definition schema_constraints_well_formed
    (constraints : list table_constraint) : Prop :=
  Forall (table_constraint_declarations_well_formed constraints) constraints.

Definition rows_constraint_conform
    (db : db_state)
    (not_null : list (attribute TNull))
    (primary_key : option (list (attribute TNull)))
    (unique_keys : list (list (attribute TNull)))
    (foreign_keys : list foreign_key_constraint)
    (checks : list check_constraint)
    (unique_indexes : list unique_index_constraint)
    (rows : list (tuple TNull)) : Prop :=
  rows_attributes_not_null not_null rows /\
  (match primary_key with
   | None => True
   | Some key => primary_key_conforms key rows
   end) /\
  Forall (fun key => unique_key_conforms key rows) unique_keys /\
  Forall (foreign_key_conforms db rows) foreign_keys /\
  Forall (check_constraint_conforms db rows) checks /\
  Forall (unique_index_conforms db rows) unique_indexes.

Definition table_constraint_conforms
    (db : db_state) (constraint : table_constraint) : Prop :=
  rows_constraint_conform
    db
    (constraint_not_null constraint)
    (constraint_primary_key constraint)
    (constraint_unique_keys constraint)
    (constraint_foreign_keys constraint)
    (constraint_checks constraint)
    (constraint_unique_indexes constraint)
    (instance_rows db (constraint_relation constraint)).

Definition schema_constraints_conform
    (db : db_state) (constraints : list table_constraint) : Prop :=
  schema_constraints_well_formed constraints /\
  Forall (table_constraint_conforms db) constraints.

Definition database_conforms_schema
    (expected : db_state)
    (constraints : list table_constraint)
    (actual : db_state) : Prop :=
  @_relnames TNull actual = @_relnames TNull expected /\
  (forall relation,
    @_basesort TNull actual relation =S=
    @_basesort TNull expected relation) /\
  database_values_conform actual /\
  schema_constraints_conform actual constraints.

(** Value conformance alone is insufficient when rows may later be replaced by
    arbitrary [OTuple]-equal representatives: tuple equality constrains [dot]
    only for labels which are actually present.  Keep presence and value
    conformance together at the row boundary. *)
Definition row_attribute_present_conforms
    (attribute : attribute TNull) (row : tuple TNull) : Prop :=
  attribute inS labels TNull row /\
  value_conforms_attribute attribute (dot TNull row attribute).

Definition rows_attribute_present_conform
    (attribute : attribute TNull) (rows : list (tuple TNull)) : Prop :=
  Forall (row_attribute_present_conforms attribute) rows.

Lemma row_attribute_present_conforms_eq :
  forall attribute left right,
    Oeset.compare (OTuple TNull) left right = Eq ->
    (row_attribute_present_conforms attribute left <->
     row_attribute_present_conforms attribute right).
Proof.
intros attribute left right Hequal.
assert (Hlabels : labels TNull left =S= labels TNull right).
{ now apply tuple_eq_labels. }
split.
- intros [Hpresent Hconforms].
  assert (Hright : attribute inS labels TNull right).
  {
    rewrite <- (Fset.mem_eq_2 _ _ _ Hlabels).
    exact Hpresent.
  }
  split; [exact Hright|].
  rewrite <- (tuple_eq_dot_alt TNull left right Hequal attribute Hpresent).
  exact Hconforms.
- intros [Hpresent Hconforms].
  assert (Hreverse : Oeset.compare (OTuple TNull) right left = Eq).
  { now apply Oeset.compare_eq_sym. }
  assert (Hleft : attribute inS labels TNull left).
  {
    rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
    exact Hpresent.
  }
  split; [exact Hleft|].
  rewrite <- (tuple_eq_dot_alt TNull right left Hreverse attribute Hpresent).
  exact Hconforms.
Qed.

Lemma instance_rows_nb_occ :
  forall db relation row,
    Febag.nb_occ
      (Fecol.CBag (CTuple TNull)) row
      (@_instance TNull db relation) =
    Oeset.nb_occ
      (OTuple TNull) row
      (instance_rows db relation).
Proof.
intros; apply Febag.nb_occ_elements.
Qed.

Lemma project_row_nil :
  forall row, project_row nil row = nil.
Proof.
reflexivity.
Qed.

Lemma project_row_cons :
  forall attribute attributes row,
    project_row (attribute :: attributes) row =
      dot TNull row attribute :: project_row attributes row.
Proof.
reflexivity.
Qed.

Lemma rows_attributes_not_null_member :
  forall attributes rows row,
    rows_attributes_not_null attributes rows ->
    In row rows ->
    row_attributes_not_null attributes row.
Proof.
intros attributes rows row Hrows Hrow.
now apply Hrows.
Qed.

Lemma primary_key_conforms_nonempty :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    primary_key <> nil.
Proof.
intros primary_key rows [Hnonempty _].
exact Hnonempty.
Qed.

Lemma primary_key_conforms_not_null :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    rows_attributes_not_null primary_key rows.
Proof.
intros primary_key rows [_ [Hnot_null _]].
exact Hnot_null.
Qed.

(** [NoDupA] is the semantic uniqueness statement.  It can be lowered to
    Leibniz [NoDup] only for a domain on which the SQL equality relation is
    known to be reflexive.  This premise is deliberately explicit: SQL NULL
    is not reflexive, and type/collation-specific equality must never be
    replaced by an assumed structural bridge. *)
Lemma NoDupA_implies_NoDup_for_reflexive_members :
  forall (A : Type) (relation : A -> A -> Prop) values,
    NoDupA relation values ->
    (forall value, In value values -> relation value value) ->
    NoDup values.
Proof.
intros A relation values Hnodup.
induction Hnodup as [|first rest Hfirst Hrest IH]; intro Hreflexive.
- constructor.
- constructor.
  + intro Hin.
    apply Hfirst.
    apply InA_alt.
    exists first.
    split.
    * apply Hreflexive; now left.
    * exact Hin.
  + apply IH.
    intros value Hvalue.
    apply Hreflexive; now right.
Qed.

Lemma unique_key_two_rows_conform_if_not_equal :
  forall key left right,
    key <> nil ->
    ~ sql_key_equal_true (project_row key left) (project_row key right) ->
    unique_key_conforms key [left; right].
Proof.
intros key left right Hnonempty Hdistinct.
split; [exact Hnonempty|].
constructor.
- intro Hin.
  apply InA_alt in Hin as [projected [Hequal Hin]].
  cbn in Hin.
  destruct Hin as [<- | []].
  now apply Hdistinct.
- constructor.
  + intro Hin.
    apply InA_alt in Hin as [projected [_ Hin]].
    now inversion Hin.
  + constructor.
Qed.

Lemma unique_key_two_rows_conflict :
  forall key left right,
    sql_key_equal_true (project_row key left) (project_row key right) ->
    ~ unique_key_conforms key [left; right].
Proof.
intros key left right Hequal [_ Hnodup].
inversion Hnodup as [|first rest Hnotin _].
apply Hnotin.
now apply InA_cons_hd.
Qed.

Lemma primary_key_conforms_nodup :
  forall primary_key rows,
    primary_key_conforms primary_key rows ->
    (forall key_values,
      In key_values (map (project_row primary_key) rows) ->
      sql_key_equal_true key_values key_values) ->
    NoDup (map (project_row primary_key) rows).
Proof.
intros primary_key rows [_ [_ Hnodup]] Hreflexive.
eapply NoDupA_implies_NoDup_for_reflexive_members.
- exact Hnodup.
- exact Hreflexive.
Qed.

Lemma rows_constraint_conform_not_null :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    rows_attributes_not_null not_null rows.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows [Hnot_null _].
exact Hnot_null.
Qed.

Lemma rows_constraint_conform_primary_key :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows,
    rows_constraint_conform db not_null (Some primary_key) unique_keys
      foreign_keys checks unique_indexes rows ->
    primary_key_conforms primary_key rows.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows [_ [Hprimary_key _]].
exact Hprimary_key.
Qed.

Lemma rows_constraint_conform_unique_key :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows key,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    In key unique_keys ->
    unique_key_conforms key rows.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows key [_ [_ [Hunique _]]] Hkey.
rewrite Forall_forall in Hunique.
now apply Hunique.
Qed.

Lemma rows_constraint_conform_foreign_key :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows foreign_key,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    In foreign_key foreign_keys ->
    foreign_key_conforms db rows foreign_key.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows foreign_key [_ [_ [_ [Hforeign_keys _]]]] Hforeign_key.
rewrite Forall_forall in Hforeign_keys.
now apply Hforeign_keys.
Qed.

Lemma rows_constraint_conform_check :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows check,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    In check checks ->
    check_constraint_conforms db rows check.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows check [_ [_ [_ [_ [Hchecks _]]]]] Hcheck.
rewrite Forall_forall in Hchecks.
now apply Hchecks.
Qed.

Lemma rows_constraint_conform_unique_index :
  forall db not_null primary_key unique_keys foreign_keys checks
      unique_indexes rows index,
    rows_constraint_conform db not_null primary_key unique_keys foreign_keys
      checks unique_indexes rows ->
    In index unique_indexes ->
    unique_index_conforms db rows index.
Proof.
intros db not_null primary_key unique_keys foreign_keys checks unique_indexes
  rows index [_ [_ [_ [_ [_ Hindexes]]]]] Hindex.
rewrite Forall_forall in Hindexes.
now apply Hindexes.
Qed.

Lemma unique_key_conforms_nonempty :
  forall key rows,
    unique_key_conforms key rows ->
    key <> nil.
Proof.
intros key rows [Hnonempty _]; exact Hnonempty.
Qed.

Lemma unique_key_conforms_nodupA :
  forall key rows,
    unique_key_conforms key rows ->
    NoDupA sql_key_equal_true (map (project_row key) rows).
Proof.
intros key rows [_ Hnodup]; exact Hnodup.
Qed.

(** Filtering rows cannot create a semantic duplicate. *)
Lemma InA_map_filter_in :
  forall (A B : Type) (relation : B -> B -> Prop)
      (project : A -> B) (keep : A -> bool) rows value,
    InA relation value (map project (filter keep rows)) ->
    InA relation value (map project rows).
Proof.
intros A B relation project keep rows value Hin.
apply InA_alt in Hin as [projected [Hrelated Hin]].
apply in_map_iff in Hin as [row [Hequal Hrow]].
apply filter_In in Hrow as [Hrow _].
apply InA_alt.
exists (project row).
split.
- now rewrite Hequal.
- now apply in_map.
Qed.

Lemma NoDupA_map_filter :
  forall (A B : Type) (relation : B -> B -> Prop)
      (project : A -> B) (keep : A -> bool) rows,
    NoDupA relation (map project rows) ->
    NoDupA relation (map project (filter keep rows)).
Proof.
intros A B relation project keep rows Hnodup.
induction rows as [|first rest IH].
- constructor.
- inversion Hnodup as [|projected projections Hfirst Hrest]; subst.
  cbn.
  destruct (keep first) eqn:Hkeep.
  + constructor.
    * intro Hin.
      apply Hfirst.
      eapply InA_map_filter_in; exact Hin.
    * now apply IH.
  + now apply IH.
Qed.

Lemma check_row_conforms_true :
  forall db check row,
    constraint_formula_runtime_error db row
      (check_constraint_formula check) = None ->
    eval_constraint_formula db row (check_constraint_formula check) = true3 ->
    check_row_conforms db check row.
Proof.
intros db check row Herror Htruth.
split; [exact Herror|].
now rewrite Htruth; discriminate.
Qed.

Lemma check_row_conforms_unknown :
  forall db check row,
    constraint_formula_runtime_error db row
      (check_constraint_formula check) = None ->
    eval_constraint_formula db row (check_constraint_formula check) = unknown3 ->
    check_row_conforms db check row.
Proof.
intros db check row Herror Htruth.
split; [exact Herror|].
now rewrite Htruth; discriminate.
Qed.

Lemma check_row_false_violates :
  forall db check row,
    eval_constraint_formula db row (check_constraint_formula check) = false3 ->
    ~ check_row_conforms db check row.
Proof.
intros db check row Hfalse [_ Hnot_false].
apply Hnot_false; exact Hfalse.
Qed.

Lemma check_row_error_violates :
  forall db check row error,
    constraint_formula_runtime_error db row
      (check_constraint_formula check) = Some error ->
    ~ check_row_conforms db check row.
Proof.
intros db check row error Herror [Hsucceeds _].
rewrite Herror in Hsucceeds; discriminate.
Qed.

Lemma unique_index_row_participates_true :
  forall db index row,
    unique_index_predicate_error db row index = None ->
    unique_index_predicate_truth db row index = true3 ->
    unique_index_row_participates db index row = true.
Proof.
intros db index row Herror Htruth.
unfold unique_index_row_participates.
now rewrite Herror, Htruth.
Qed.

Lemma unique_index_row_does_not_participate_false :
  forall db index row,
    unique_index_predicate_error db row index = None ->
    unique_index_predicate_truth db row index = false3 ->
    unique_index_row_participates db index row = false.
Proof.
intros db index row Herror Htruth.
unfold unique_index_row_participates.
now rewrite Herror, Htruth.
Qed.

Lemma unique_index_row_does_not_participate_unknown :
  forall db index row,
    unique_index_predicate_error db row index = None ->
    unique_index_predicate_truth db row index = unknown3 ->
    unique_index_row_participates db index row = false.
Proof.
intros db index row Herror Htruth.
unfold unique_index_row_participates.
now rewrite Herror, Htruth.
Qed.

Lemma unique_index_row_does_not_participate_error :
  forall db index row error,
    unique_index_predicate_error db row index = Some error ->
    unique_index_row_participates db index row = false.
Proof.
intros db index row error Herror.
unfold unique_index_row_participates.
rewrite Herror.
now destruct (unique_index_predicate_truth db row index).
Qed.

Lemma unique_index_conforms_predicate_succeeds :
  forall db rows index,
    unique_index_conforms db rows index ->
    forall row,
      In row rows ->
      unique_index_predicate_error db row index = None.
Proof.
intros db rows index [_ [Hpredicate _]]; exact Hpredicate.
Qed.

Lemma unique_index_conforms_participating_terms_succeed :
  forall db rows index,
    unique_index_conforms db rows index ->
    forall row,
      In row rows ->
      unique_index_row_participates db index row = true ->
      unique_index_row_terms_succeed index row.
Proof.
intros db rows index [_ [_ [Hterms _]]]; exact Hterms.
Qed.

Lemma unique_index_conforms_nodupA :
  forall db rows index,
    unique_index_conforms db rows index ->
  NoDupA
      sql_key_equal_true
      (map (unique_index_key (unique_index_terms index))
        (filter (unique_index_row_participates db index) rows)).
Proof.
intros db rows index [_ [_ [_ Hnodup]]]; exact Hnodup.
Qed.

Lemma sql_value_equal_true_string_collation :
  forall left_typmod left right_typmod right,
    sql_value_equal_true
      (NullValues.Value_string (StringValue left_typmod (Some left)))
      (NullValues.Value_string (StringValue right_typmod (Some right))) <->
    sql_string_compare left_typmod left right_typmod right = Eq.
Proof.
intros left_typmod left right_typmod right.
unfold sql_value_equal_true.
cbn.
destruct (sql_string_compare left_typmod left right_typmod right);
  cbn; intuition discriminate.
Qed.

Lemma foreign_key_attribute_compatible_int32_int64 :
  forall source_name referenced_name,
    foreign_key_attribute_compatible
      (Attr_int32 source_name) (Attr_int64 referenced_name).
Proof.
intros; exact I.
Qed.

Lemma foreign_key_attribute_compatible_int64_int32 :
  forall source_name referenced_name,
    foreign_key_attribute_compatible
      (Attr_int64 source_name) (Attr_int32 referenced_name).
Proof.
intros; exact I.
Qed.

Lemma foreign_key_value_equal_true_int32_int64 :
  forall source_name referenced_name source referenced,
    foreign_key_value_equal_true
      (Attr_int32 source_name) (Attr_int64 referenced_name)
      (NullValues.Value_int32 (Some source))
      (NullValues.Value_int64 (Some referenced)) <->
    int32_value source = int64_value referenced.
Proof.
intros source_name referenced_name source referenced.
unfold foreign_key_value_equal_true, foreign_key_attribute_compatible,
  sql_value_equal_true.
cbn.
rewrite <- Z.compare_eq_iff.
destruct (int32_value source ?= int64_value referenced)%Z;
  cbn; intuition discriminate.
Qed.

Lemma foreign_key_value_equal_true_int64_int32 :
  forall source_name referenced_name source referenced,
    foreign_key_value_equal_true
      (Attr_int64 source_name) (Attr_int32 referenced_name)
      (NullValues.Value_int64 (Some source))
      (NullValues.Value_int32 (Some referenced)) <->
    int64_value source = int32_value referenced.
Proof.
intros source_name referenced_name source referenced.
unfold foreign_key_value_equal_true, foreign_key_attribute_compatible,
  sql_value_equal_true.
cbn.
rewrite <- Z.compare_eq_iff.
destruct (int64_value source ?= int32_value referenced)%Z;
  cbn; intuition discriminate.
Qed.

Lemma foreign_key_value_equal_true_int32_int64_source_null :
  forall source_name referenced_name referenced,
    ~ foreign_key_value_equal_true
      (Attr_int32 source_name) (Attr_int64 referenced_name)
      (NullValues.Value_int32 None)
      (NullValues.Value_int64 (Some referenced)).
Proof.
intros.
unfold foreign_key_value_equal_true, foreign_key_attribute_compatible,
  sql_value_equal_true.
cbn; intuition discriminate.
Qed.

Lemma foreign_key_value_equal_true_int32_int64_referenced_null :
  forall source_name referenced_name source,
    ~ foreign_key_value_equal_true
      (Attr_int32 source_name) (Attr_int64 referenced_name)
      (NullValues.Value_int32 (Some source))
      (NullValues.Value_int64 None).
Proof.
intros.
unfold foreign_key_value_equal_true, foreign_key_attribute_compatible,
  sql_value_equal_true.
cbn; intuition discriminate.
Qed.

Lemma foreign_key_match_simple_null_component :
  forall foreign_key row referenced_rows attribute,
    In attribute (foreign_key_columns foreign_key) ->
    NullValues.is_null_value (dot TNull row attribute) = true ->
    foreign_key_row_conforms_against foreign_key row referenced_rows.
Proof.
intros foreign_key row referenced_rows attribute Hattribute Hnull.
left; now exists attribute.
Qed.

Lemma foreign_key_match_simple_referenced_row :
  forall foreign_key row referenced_rows referenced_row,
    In referenced_row referenced_rows ->
    foreign_key_key_equal_true
      (foreign_key_columns foreign_key)
      (foreign_key_referenced_columns foreign_key)
      row referenced_row ->
    foreign_key_row_conforms_against foreign_key row referenced_rows.
Proof.
intros foreign_key row referenced_rows referenced_row Hrow Hequal.
right; exists referenced_row; now split.
Qed.

Lemma foreign_key_reference_well_formed_compatible :
  forall constraints foreign_key,
    foreign_key_reference_well_formed constraints foreign_key ->
    Forall2 foreign_key_attribute_compatible
      (foreign_key_columns foreign_key)
      (foreign_key_referenced_columns foreign_key).
Proof.
intros constraints foreign_key [_ [_ [Hcompatible _]]].
exact Hcompatible.
Qed.

Lemma schema_constraints_conform_member :
  forall db constraints constraint,
    schema_constraints_conform db constraints ->
    In constraint constraints ->
    table_constraint_conforms db constraint.
Proof.
intros db constraints constraint [_ Hconstraints] Hconstraint.
rewrite Forall_forall in Hconstraints.
now apply Hconstraints.
Qed.

Lemma schema_constraints_conform_well_formed :
  forall db constraints,
    schema_constraints_conform db constraints ->
    schema_constraints_well_formed constraints.
Proof.
intros db constraints [Hwell_formed _]; exact Hwell_formed.
Qed.

Lemma database_conforms_schema_relnames :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    @_relnames TNull actual = @_relnames TNull expected.
Proof.
intros expected constraints actual [Hrelnames _].
exact Hrelnames.
Qed.

Lemma database_conforms_schema_basesort :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    forall relation,
      @_basesort TNull actual relation =S=
      @_basesort TNull expected relation.
Proof.
intros expected constraints actual [_ [Hbasesort _]].
exact Hbasesort.
Qed.

Lemma database_conforms_schema_values :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    database_values_conform actual.
Proof.
intros expected constraints actual [_ [_ [Hvalues _]]].
exact Hvalues.
Qed.

Lemma database_conforms_schema_constraints :
  forall expected constraints actual,
    database_conforms_schema expected constraints actual ->
    schema_constraints_conform actual constraints.
Proof.
intros expected constraints actual [_ [_ [_ Hconstraints]]].
exact Hconstraints.
Qed.

Lemma database_conforms_schema_rows_attribute_present :
  forall expected constraints actual relation attribute,
    database_conforms_schema expected constraints actual ->
    attribute inS (@_basesort TNull expected relation) ->
    rows_attribute_present_conform attribute (instance_rows actual relation).
Proof.
intros expected constraints actual relation attribute Hschema Hattribute.
unfold rows_attribute_present_conform.
rewrite Forall_forall.
intros row Hrow.
pose proof
  (database_conforms_schema_values expected constraints actual Hschema)
  as Hvalues.
specialize (Hvalues relation row Hrow) as [Hlabels Htyped].
pose proof
  (database_conforms_schema_basesort expected constraints actual Hschema
    relation) as Hbasesort.
assert (Hactual : attribute inS @_basesort TNull actual relation).
{
  rewrite (Fset.mem_eq_2 _ _ _ Hbasesort).
  exact Hattribute.
}
split.
- rewrite (Fset.mem_eq_2 _ _ _ Hlabels).
  exact Hactual.
- now apply Htyped.
Qed.

Lemma rows_attribute_present_conform_implies_value_conform :
  forall attribute rows,
    rows_attribute_present_conform attribute rows ->
    forall row,
      In row rows ->
      value_conforms_attribute attribute (dot TNull row attribute).
Proof.
intros attribute rows Hrows row Hrow.
unfold rows_attribute_present_conform in Hrows.
rewrite Forall_forall in Hrows.
exact (proj2 (Hrows row Hrow)).
Qed.
