(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                   Error-aware observation of SQL algebra                       *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
        FTerms ATerms Projection SqlAlgebra SqlOutcome.

Section Sec.

Hypothesis T : Tuple.Rcd.
Hypothesis relname : Type.

Import Tuple.

Local Definition value := value T.
Local Definition tuple := tuple T.
Local Definition scalar_operator := scalar_operator T.
Local Definition aggregate := aggregate T.
Local Definition funterm := @funterm T.
Local Definition aggterm := @aggterm T.
Local Definition formula := @sql_formula T (@query T relname).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.

(**
  An observation retains both the recursively detected failure and the value
  produced by the underlying total interpreter.  Keeping both lets a concrete
  value domain implement non-strict operators such as CASE: an unselected
  branch may have an error observation without making the CASE expression
  fail.
 *)
Definition argument_observation := (option sql_runtime_error * value)%type.

(** Concrete value domains classify failures and select strict arguments. *)
Hypothesis symbol_runtime_error :
  scalar_operator -> list argument_observation -> option sql_runtime_error.
Hypothesis aggregate_runtime_error :
  aggregate -> list argument_observation -> option sql_runtime_error.

Definition first_error
    (left right : option sql_runtime_error) : option sql_runtime_error :=
  match left with
  | Some error => Some error
  | None => right
  end.

Fixpoint first_runtime_error {A : Type}
    (check : A -> option sql_runtime_error)
    (values : list A) : option sql_runtime_error :=
  match values with
  | nil => None
  | value :: rest => first_error (check value) (first_runtime_error check rest)
  end.

Fixpoint eval_funterm_runtime_error
    (env : Env.env T) (term : funterm) : option sql_runtime_error :=
  match term with
  | F_Constant _ _ => None
  | F_Dot _ _ => None
  | F_Expr _ function args =>
      symbol_runtime_error function
        (map (fun argument =>
          (eval_funterm_runtime_error env argument,
           @interp_funterm T env argument)) args)
  end.

Fixpoint eval_aggterm_runtime_error
    (env : Env.env T) (term : aggterm) : option sql_runtime_error :=
  match term with
  | A_Expr _ function_term => eval_funterm_runtime_error env function_term
  | A_agg _ function function_term =>
      let selected_env :=
        if Fset.is_empty (A T) (variables_ft T function_term)
        then Some env
        else find_eval_env T env term in
      let argument_envs :=
        match selected_env with
        | None | Some nil => nil
        | Some (slice :: outer_env) =>
            map (fun inner_slice => inner_slice :: outer_env)
                (unfold_env_slice T slice)
        end in
      aggregate_runtime_error function
        (map (fun argument_env =>
          (eval_funterm_runtime_error argument_env function_term,
           @interp_funterm T argument_env function_term)) argument_envs)
  | A_fun _ function args =>
      symbol_runtime_error function
        (map (fun argument =>
          (eval_aggterm_runtime_error env argument,
           @interp_aggterm T env argument)) args)
  end.

(** Finalize only aggregate applications embedded in an aggregate term.

    Group evaluation must finalize every aggregate named by its target
    list before HAVING can discard the group.  It must not, however, execute
    scalar target operations at that point: a scalar wrapper such as division
    remains a post-HAVING expression.  Aggregate arguments are ordinary
    scalar expressions and are therefore checked when their aggregate is
    finalized; scalar wrappers around aggregate results are traversed without
    invoking their scalar-operator callback. *)
Fixpoint eval_aggterm_aggregate_runtime_error
    (env : Env.env T) (term : aggterm) : option sql_runtime_error :=
  match term with
  | A_Expr _ _ => None
  | A_agg _ function function_term =>
      let selected_env :=
        if Fset.is_empty (A T) (variables_ft T function_term)
        then Some env
        else find_eval_env T env term in
      let argument_envs :=
        match selected_env with
        | None | Some nil => nil
        | Some (slice :: outer_env) =>
            map (fun inner_slice => inner_slice :: outer_env)
                (unfold_env_slice T slice)
        end in
      aggregate_runtime_error function
        (map (fun argument_env =>
          (eval_funterm_runtime_error argument_env function_term,
           @interp_funterm T argument_env function_term)) argument_envs)
  | A_fun _ _ args =>
      first_runtime_error
        (eval_aggterm_aggregate_runtime_error env) args
  end.

Definition eval_select_runtime_error
    (env : Env.env T) (item : select T) : option sql_runtime_error :=
  match item with
  | Select_As _ term _ => eval_aggterm_runtime_error env term
  end.

Definition eval_select_list_runtime_error
    (env : Env.env T) (items : _select_list T) : option sql_runtime_error :=
  match items with
  | _Select_List _ items =>
      first_runtime_error (eval_select_runtime_error env) items
  end.

Definition eval_select_aggregate_runtime_error
    (env : Env.env T) (item : select T) : option sql_runtime_error :=
  match item with
  | Select_As _ term _ => eval_aggterm_aggregate_runtime_error env term
  end.

Definition eval_select_list_aggregate_runtime_error
    (env : Env.env T) (items : _select_list T) : option sql_runtime_error :=
  match items with
  | _Select_List _ items =>
      first_runtime_error (eval_select_aggregate_runtime_error env) items
  end.

(** Finalize aggregate applications owned by this formula's query level.
    Scalar formula/function nodes are traversed without invoking their own
    callbacks, so a lazy CASE cannot hide an aggregate transition or final
    error.  Relational subqueries are deliberately opaque here: their
    aggregates belong to, and are checked by, their own query evaluation. *)
Fixpoint eval_formula_aggregate_runtime_error
    (env : Env.env T) (sql_formula : formula) : option sql_runtime_error :=
  match sql_formula with
  | @Sql_Conj _ _ _ left_formula right_formula =>
      first_error
        (eval_formula_aggregate_runtime_error env left_formula)
        (eval_formula_aggregate_runtime_error env right_formula)
  | @Sql_Not _ _ inner => eval_formula_aggregate_runtime_error env inner
  | @Sql_True _ _ => None
  | @Sql_Pred _ _ _ args
  | @Sql_Quant _ _ _ _ args _ =>
      first_runtime_error (eval_aggterm_aggregate_runtime_error env) args
  | @Sql_In _ _ items _ =>
      first_runtime_error (eval_select_aggregate_runtime_error env) items
  | @Sql_Exists _ _ _ => None
  end.

Fixpoint eval_formula_runtime_error
    (eval_query_error : Env.env T -> @query T relname -> option sql_runtime_error)
    (env : Env.env T)
    (sql_formula : formula) : option sql_runtime_error :=
  match sql_formula with
  | @Sql_Conj _ _ _ left_formula right_formula =>
      first_error
        (eval_formula_runtime_error eval_query_error env left_formula)
        (eval_formula_runtime_error eval_query_error env right_formula)
  | @Sql_Not _ _ inner => eval_formula_runtime_error eval_query_error env inner
  | @Sql_True _ _ => None
  | @Sql_Pred _ _ _ args =>
      first_runtime_error (eval_aggterm_runtime_error env) args
  | @Sql_Quant _ _ _ _ args subquery =>
      first_error
        (first_runtime_error (eval_aggterm_runtime_error env) args)
        (eval_query_error env subquery)
  | @Sql_In _ _ items subquery =>
      first_error
        (first_runtime_error (eval_select_runtime_error env) items)
        (eval_query_error env subquery)
  | @Sql_Exists _ _ subquery => eval_query_error env subquery
  end.

Fixpoint eval_query_runtime_error
    (env : Env.env T)
    (sql_query : @query T relname) : option sql_runtime_error :=
  match sql_query with
  | @Q_Empty_Tuple _ _ | @Q_Empty_Relation _ _ _ | @Q_Table _ _ _ => None
  | @Q_Set _ _ _ left_query right_query
  | @Q_CrossJoin _ _ left_query right_query =>
      first_error
        (eval_query_runtime_error env left_query)
        (eval_query_runtime_error env right_query)
  | @Q_Pi _ _ select_list input =>
      first_error
        (eval_query_runtime_error env input)
        (first_runtime_error
          (fun row =>
            eval_select_list_runtime_error (env_t T env row) select_list)
          (Febag.elements BTupleT
            (@eval_query T relname basesort instance unknown contains_nulls env input)))
  | @Q_Sigma _ _ predicate input =>
      first_error
        (eval_query_runtime_error env input)
        (first_runtime_error
          (fun row =>
            eval_formula_runtime_error eval_query_runtime_error
              (env_t T env row) predicate)
          (Febag.elements BTupleT
            (@eval_query T relname basesort instance unknown contains_nulls env input)))
  | @Q_Gamma _ _ select_list group_terms having input =>
      let input_bag :=
        @eval_query T relname basesort instance unknown contains_nulls env input in
      let input_rows := Febag.elements BTupleT input_bag in
      let groups := @make_groups T env input_rows (@Group_By T group_terms) in
      first_error
        (eval_query_runtime_error env input)
        (first_error
          (first_runtime_error
            (fun row => first_runtime_error
              (eval_aggterm_runtime_error (env_t T env row)) group_terms)
            input_rows)
          (first_runtime_error
            (fun group =>
              let group_env := env_g T env (@Group_By T group_terms) group in
              first_error
                (eval_select_list_aggregate_runtime_error group_env select_list)
                (first_error
                  (eval_formula_aggregate_runtime_error group_env having)
                  (first_error
                    (eval_formula_runtime_error eval_query_runtime_error group_env having)
                    (if Bool.is_true (B T)
                          (@eval_sql_formula T (@query T relname)
                            unknown contains_nulls
                            (@eval_query T relname basesort instance unknown contains_nulls)
                            group_env having)
                     then eval_select_list_runtime_error group_env select_list
                     else None))))
            groups))
  end.

Definition eval_query_outcome
    (env : Env.env T)
    (sql_query : @query T relname) : sql_outcome bagT :=
  match eval_query_runtime_error env sql_query with
  | Some error => SqlError error
  | None =>
      SqlSuccess
        (@eval_query T relname basesort instance unknown contains_nulls env sql_query)
  end.

End Sec.
