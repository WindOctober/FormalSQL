(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                  Reusable SQL expression runtime-error checks                  *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Formula
        FTerms ATerms Projection SqlOutcome.

Section Sec.

Hypothesis T : Tuple.Rcd.
Import Tuple.

Local Definition value := value T.
Local Definition tuple := tuple T.
Local Definition scalar_operator := scalar_operator T.
Local Definition aggregate := aggregate T.
Local Definition funterm := @funterm T.
Local Definition aggterm := @aggterm T.
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

Fixpoint eval_formula_runtime_error {Q : Type}
    (eval_query_error : Env.env T -> Q -> option sql_runtime_error)
    (env : Env.env T)
    (sql_formula : @sql_formula T Q) : option sql_runtime_error :=
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

End Sec.
