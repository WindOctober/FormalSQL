(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**        Order-behavior soundness and observable bag-abstraction bridges         *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Bool List Arith ZArith Sorting.Permutation.

Require Import OrderedSet ListFacts FiniteSet FiniteBag FiniteCollection Join NJoinTuples
        FlatData Env Bool3 Formula
        SqlOutcome SqlErrorSemantics SqlOrder SqlListFacts
        SqlBagAbstraction SqlQuerySyntax SqlQuerySemantics.

(** Ordered row-list outcomes are the single exact query semantics.  [alpha]
    maps them to possible bags; [gamma] forgets order by permutation closure
    and is therefore an over-approximation.  [BagClosed] is exactly where that
    abstraction is complete for equivalence, allowing exact reuse of bag
    proofs in those regions. *)

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

Local Abbreviation eval_query_expr :=
  (@eval_query_expr_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_group_bag :=
  (@eval_group_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_grouping_sets_bag :=
  (@eval_grouping_sets_bag_outcome T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null).

Local Abbreviation eval_join_bag :=
  (@eval_join_bag_outcome T relname basesort instance unknown
    symbol_runtime_error aggregate_runtime_error value_is_null).

Lemma query_error_outcome_iff :
  forall env attributes error outcome,
    eval_query_expr env (QExpr_Error attributes error) outcome <->
    outcome = SqlError error.
Proof.
intros env attributes error outcome; split; intro Heval.
- inversion Heval; reflexivity.
- subst; constructor.
Qed.

Corollary query_error_has_no_success :
  forall env attributes error rows,
    ~ eval_query_expr env (QExpr_Error attributes error) (SqlSuccess rows).
Proof.
intros env attributes error rows Heval.
apply query_error_outcome_iff in Heval; discriminate.
Qed.

Lemma eval_query_expr_table_success_iff :
  forall env outputs table rows,
    eval_query_expr env (QExpr_Table outputs table) (SqlSuccess rows) <->
    query_same_rows_as_bag rows
      (@query_table_bag T relname basesort instance outputs table).
Proof.
intros env outputs table rows; split.
- intro Heval; inversion Heval; subst; assumption.
- now apply EQuery_Table.
Qed.

Corollary query_table_has_no_error :
  forall env outputs table error,
    ~ eval_query_expr env (QExpr_Table outputs table) (SqlError error).
Proof.
intros env outputs table error Heval; inversion Heval.
Qed.

Lemma query_table_has_success :
  forall env outputs table,
    exists rows,
      eval_query_expr env (QExpr_Table outputs table) (SqlSuccess rows).
Proof.
intros env outputs table.
exists (Febag.elements BTupleT
  (@query_table_bag T relname basesort instance outputs table)).
apply EQuery_Table.
unfold query_same_rows_as_bag, query_rows_bag.
apply Febag.elements_mk_bag.
Qed.

(** The row adapter is sequential over the exact child list: a head error is
    propagated immediately, while successful heads preserve their position. *)
Lemma row_map_rows_outcome_head_error :
  forall row_map row rows error,
    row_map row = SqlError error ->
    @row_map_rows_outcome T row_map (row :: rows) = SqlError error.
Proof.
intros row_map row rows error Herror; simpl; now rewrite Herror.
Qed.

Lemma row_map_rows_outcome_cons_success :
  forall row_map row rows mapped_row mapped_rows,
    row_map row = SqlSuccess mapped_row ->
    @row_map_rows_outcome T row_map rows = SqlSuccess mapped_rows ->
    @row_map_rows_outcome T row_map (row :: rows) =
      SqlSuccess (mapped_row :: mapped_rows).
Proof.
intros row_map row rows mapped_row mapped_rows Hrow Hrows.
simpl; now rewrite Hrow, Hrows.
Qed.

Lemma row_map_rows_outcome_tail_error :
  forall row_map row rows mapped_row error,
    row_map row = SqlSuccess mapped_row ->
    @row_map_rows_outcome T row_map rows = SqlError error ->
    @row_map_rows_outcome T row_map (row :: rows) = SqlError error.
Proof.
intros row_map row rows mapped_row error Hrow Hrows.
simpl; now rewrite Hrow, Hrows.
Qed.

(** Pointwise successful row mapping respects input permutations.  This does
    not turn [QExpr_RowMap] into a [BagReset]: its exact observations still
    retain the chosen child-list order. *)
Lemma row_map_rows_outcome_success_permutation :
  forall row_map left right mapped_left,
    Permutation left right ->
    @row_map_rows_outcome T row_map left = SqlSuccess mapped_left ->
    exists mapped_right,
      @row_map_rows_outcome T row_map right = SqlSuccess mapped_right /\
      Permutation mapped_left mapped_right.
Proof.
intros row_map left right mapped_left Hperm.
revert mapped_left; induction Hperm; intros mapped_left Hleft.
- simpl in Hleft; inversion Hleft; subst.
  exists nil; split; [reflexivity | constructor].
- simpl in Hleft.
  destruct (row_map x) as [mapped_x | error] eqn:Hrow; [|discriminate].
  destruct (@row_map_rows_outcome T row_map l) as [mapped_l | tail_error]
    eqn:Htail; [|discriminate].
  inversion Hleft; subst.
  destruct (IHHperm mapped_l eq_refl) as [mapped_l' [Hright Hmapped]].
  exists (mapped_x :: mapped_l'); split.
  + simpl; now rewrite Hrow, Hright.
  + now constructor.
- simpl in Hleft.
  destruct (row_map y) as [mapped_y | error_y] eqn:Hy; [|discriminate].
  destruct (row_map x) as [mapped_x | error_x] eqn:Hx; [|discriminate].
  destruct (@row_map_rows_outcome T row_map l) as [mapped_l | tail_error]
    eqn:Htail; [|discriminate].
  inversion Hleft; subst.
  exists (mapped_x :: mapped_y :: mapped_l); split.
  + simpl; now rewrite Hx, Hy, Htail.
  + apply perm_swap.
- destruct (IHHperm1 mapped_left Hleft) as [mapped_middle [Hmiddle Hlm]].
  destruct (IHHperm2 mapped_middle Hmiddle) as [mapped_right [Hright Hmr]].
  exists mapped_right; split; [exact Hright |].
  eapply Permutation_trans; eassumption.
Qed.

(** Extract the successful pointwise result selected by a row adapter.  The
    fallback branch is irrelevant under a successful list evaluation, but
    makes the extracted mapper total and lets us use the standard
    [Permutation_map_inv] lemma. *)
Definition row_map_success_value
    (row_map : tuple -> sql_outcome tuple) (row : tuple) : tuple :=
  match row_map row with
  | SqlSuccess mapped_row => mapped_row
  | SqlError _ => row
  end.

Lemma row_map_rows_outcome_success_map :
  forall row_map input output,
    @row_map_rows_outcome T row_map input = SqlSuccess output ->
    output = map (row_map_success_value row_map) input.
Proof.
intros row_map input; induction input as [|row input IH]; intros output Heval.
- simpl in Heval; now inversion Heval.
- simpl in Heval.
  destruct (row_map row) as [mapped_row | error] eqn:Hrow;
    [|discriminate].
  destruct (@row_map_rows_outcome T row_map input)
    as [mapped_input | tail_error] eqn:Hinput; [|discriminate].
  inversion Heval; subst; simpl.
  unfold row_map_success_value; rewrite Hrow.
  f_equal; now apply IH.
Qed.

(** Every concrete permutation of a successful adapter output is obtained by
    applying the adapter to a corresponding concrete permutation of its input.
    No setoid compatibility of the callback is needed: exactly the same Rocq
    rows, and therefore exactly the same callback results, are reused. *)
Lemma row_map_rows_outcome_success_output_permutation :
  forall row_map input output desired,
    @row_map_rows_outcome T row_map input = SqlSuccess output ->
    Permutation output desired ->
    exists permuted_input,
      Permutation input permuted_input /\
      @row_map_rows_outcome T row_map permuted_input = SqlSuccess desired.
Proof.
intros row_map input output desired Heval Hpermutation.
pose proof
  (row_map_rows_outcome_success_map
    row_map input (output := output) Heval) as Houtput.
assert (Hmapped :
  Permutation desired (map (row_map_success_value row_map) input)).
{
  rewrite <- Houtput; now apply Permutation_sym.
}
destruct (Permutation_map_inv
  (row_map_success_value row_map) input Hmapped)
  as [permuted_input [Hdesired Hinput]].
exists permuted_input; split; [exact Hinput |].
destruct (row_map_rows_outcome_success_permutation
  row_map Hinput Heval)
  as [mapped [Heval' _]].
pose proof
  (row_map_rows_outcome_success_map
    row_map permuted_input (output := mapped) Heval')
  as Hmapped'.
rewrite Hdesired, <- Hmapped'.
exact Heval'.
Qed.

(** Projection is the built-in row adapter obtained by pairing its runtime
    check with the ordinary projection function. *)
Definition project_row_outcome
    (env : Env.env T) (select_list : _select_list T) (row : tuple)
    : sql_outcome tuple :=
  match @eval_select_list_runtime_error T
          symbol_runtime_error aggregate_runtime_error
          (env_t T env row) select_list with
  | Some error => SqlError error
  | None =>
      SqlSuccess
        (projection T (env_t T env row) (@Select_List T select_list))
  end.

Lemma project_rows_outcome_as_row_map :
  forall env select_list rows,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list rows =
    @row_map_rows_outcome T (project_row_outcome env select_list) rows.
Proof.
intros env select_list rows; induction rows as [|row rows IH]; simpl;
  [reflexivity |].
unfold project_row_outcome.
destruct (@eval_select_list_runtime_error T
  symbol_runtime_error aggregate_runtime_error
  (env_t T env row) select_list); [reflexivity |].
now rewrite IH.
Qed.

Lemma project_rows_outcome_success_output_permutation :
  forall env select_list input output desired,
    @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
      env select_list input = SqlSuccess output ->
    Permutation output desired ->
    exists permuted_input,
      Permutation input permuted_input /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list permuted_input = SqlSuccess desired.
Proof.
intros env select_list input output desired Heval Hpermutation.
rewrite project_rows_outcome_as_row_map in Heval.
destruct (row_map_rows_outcome_success_output_permutation
  (project_row_outcome env select_list) input Heval Hpermutation)
  as [permuted_input [Hinput Hproject]].
exists permuted_input; split; [exact Hinput |].
now rewrite project_rows_outcome_as_row_map.
Qed.

(** Per-occurrence witnesses used to rearrange a successful relational filter.
    They retain the chosen formula derivation, so the argument does not assume
    formula determinism or extensionality. *)
Definition filter_row_accepts
    (env : Env.env T) (formula : formula_expr T relname) (row : tuple) : Prop :=
  exists truth,
    @eval_formula_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      (env_t T env row) formula (SqlSuccess truth) /\
    Bool.is_true (B T) truth = true.

Definition filter_row_rejects
    (env : Env.env T) (formula : formula_expr T relname) (row : tuple) : Prop :=
  exists truth,
    @eval_formula_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      (env_t T env row) formula (SqlSuccess truth) /\
    Bool.is_true (B T) truth = false.

Lemma filter_rows_all_reject_success_empty :
  forall env formula rows,
    Forall (filter_row_rejects env formula) rows ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula rows (SqlSuccess nil).
Proof.
intros env formula rows Hrows; induction Hrows as [|row rows Hrow Hrows IH].
- constructor.
- destruct Hrow as [truth [Hformula Hreject]].
  replace (SqlSuccess nil) with
    (@filter_cons_outcome T truth row (SqlSuccess nil)).
  + now eapply EFilterRows_Cons.
  + unfold filter_cons_outcome; now rewrite Hreject.
Qed.

Lemma filter_rows_accepts_then_rejects_success :
  forall env formula accepted rejected,
    Forall (filter_row_accepts env formula) accepted ->
    Forall (filter_row_rejects env formula) rejected ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula (accepted ++ rejected) (SqlSuccess accepted).
Proof.
intros env formula accepted; induction accepted as [|row accepted IH];
  intros rejected Haccepted Hrejected.
- simpl; now apply filter_rows_all_reject_success_empty.
- inversion Haccepted as [|? ? Hrow Htail]; subst.
  destruct Hrow as [truth [Hformula Haccept]].
  simpl.
  replace (SqlSuccess (row :: accepted)) with
    (@filter_cons_outcome T truth row (SqlSuccess accepted)).
  + eapply EFilterRows_Cons; [exact Hformula |].
    now apply IH.
  + unfold filter_cons_outcome; now rewrite Haccept.
Qed.

(** A successful filter derivation partitions the concrete input occurrences
    into its exact output rows and exact rejected rows. *)
Lemma eval_filter_rows_success_partition :
  forall env formula input output,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula input (SqlSuccess output) ->
    exists rejected,
      Permutation input (output ++ rejected) /\
      Forall (filter_row_accepts env formula) output /\
      Forall (filter_row_rejects env formula) rejected.
Proof.
intros env formula input; induction input as [|row input IH];
  intros output Heval.
- inversion Heval; subst.
  exists nil; repeat split; constructor.
- inversion Heval; subst.
  match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ input ?tail |- _ =>
      destruct tail as [tail_output | tail_error] eqn:Htail_outcome
  end; simpl in *; try discriminate.
  match goal with
  | truth : Bool.b (B T) |- _ =>
      destruct (Bool.is_true (B T) truth) eqn:Htruth
  end; simpl in *; subst.
  all: match goal with
  | Hresult : SqlSuccess ?result = SqlSuccess ?output |- _ =>
      inversion Hresult; subst; clear Hresult
  end.
  all: match goal with
  | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _ _ ?tail_rows
      (SqlSuccess ?tail_output) |- _ =>
      destruct (IH tail_output Htail)
        as [rejected [Hpermutation [Haccepted Hrejected]]]
  end.
  + exists rejected; repeat split.
    * simpl; now apply perm_skip.
    * constructor; [|exact Haccepted].
      eexists; split; eassumption.
    * exact Hrejected.
  + exists (row :: rejected); repeat split.
    * eapply Permutation_trans with
        (l' := row :: (output ++ rejected)).
      -- now apply perm_skip.
      -- change (Permutation ((row :: output) ++ rejected)
           (output ++ row :: rejected)).
         apply Permutation_middle.
    * exact Haccepted.
    * constructor; [|exact Hrejected].
      eexists; split; eassumption.
Qed.

Lemma eval_filter_rows_success_output_permutation :
  forall env formula input output desired,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula input (SqlSuccess output) ->
    Permutation output desired ->
    exists permuted_input,
      Permutation input permuted_input /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env formula permuted_input (SqlSuccess desired).
Proof.
intros env formula input output desired Heval Houtput.
destruct (eval_filter_rows_success_partition Heval)
  as [rejected [Hinput [Haccepted Hrejected]]].
exists (desired ++ rejected); split.
- eapply Permutation_trans; [exact Hinput |].
  now apply Permutation_app_tail.
- apply filter_rows_accepts_then_rejects_success; [|exact Hrejected].
  eapply Permutation_Forall; [exact Houtput | exact Haccepted].
Qed.

Lemma filter_rows_true_success :
  forall env rows,
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env FExpr_True rows (SqlSuccess rows).
Proof.
intros env rows; induction rows as [| row rows IH].
- constructor.
- replace (SqlSuccess (row :: rows)) with
    (@filter_cons_outcome T (Bool.true (B T)) row (SqlSuccess rows)).
  eapply EFilterRows_Cons.
  + apply EFormula_True.
  + exact IH.
  + unfold filter_cons_outcome.
    now rewrite Bool.true_is_true_alt.
Qed.

Corollary filter_rows_true_has_no_error :
  forall env rows error,
    ~ @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env FExpr_True rows (SqlError error).
Proof.
intros env rows; induction rows as [| row rows IH]; intros error Heval.
- inversion Heval.
- inversion Heval; subst.
  + match goal with
    | Htrue : @eval_formula_expr_outcome _ _ _ _ _ _ _ _ _
        FExpr_True (SqlError _) |- _ =>
        inversion Htrue
    end.
  + match goal with
    | Htail : @eval_filter_rows_outcome _ _ _ _ _ _ _ _ _
        FExpr_True rows ?tail |- _ =>
        destruct tail as [tail_rows | tail_error]
    end.
    * simpl in *.
      destruct (Bool.is_true (B T) truth); discriminate.
    * simpl in *.
      eapply (IH tail_error); exact H4.
Qed.

(** A one-row ordinary filter drops every SQL-nontrue observation, including
    FALSE and UNKNOWN. *)
Lemma filter_rows_single_nontrue_success_empty :
  forall env formula row truth,
    @eval_formula_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      (env_t T env row) formula (SqlSuccess truth) ->
    Bool.is_true (B T) truth = false ->
    @eval_filter_rows_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env formula (row :: nil) (SqlSuccess nil).
Proof.
intros env formula row truth Hformula Hnontrue.
replace (SqlSuccess nil) with
  (@filter_cons_outcome T truth row (SqlSuccess nil)).
- eapply EFilterRows_Cons.
  + exact Hformula.
  + constructor.
- unfold filter_cons_outcome; now rewrite Hnontrue.
Qed.

(** Once an ordinary lower filter is empty, an outer filter succeeds empty
    without any evaluation premise for its predicate. *)
Lemma query_nested_filter_inner_empty_skips_outer :
  forall env lower risky input,
    eval_query_expr env (QExpr_Filter lower input) (SqlSuccess nil) ->
    eval_query_expr env
      (QExpr_Filter risky (QExpr_Filter lower input)) (SqlSuccess nil).
Proof.
intros env lower risky input Hinner.
eapply EQuery_FilterRows with (input_rows := nil).
- exact Hinner.
- constructor.
Qed.

(** If the lower predicate is FALSE or UNKNOWN on the only row, logical
    selection produces an empty input and the outer predicate is consequently
    evaluated over no rows. *)
Lemma query_nested_filter_nontrue_skips_outer :
  forall env lower risky input row truth,
    eval_query_expr env input (SqlSuccess (row :: nil)) ->
    @eval_formula_expr_outcome T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      (env_t T env row) lower (SqlSuccess truth) ->
    Bool.is_true (B T) truth = false ->
    eval_query_expr env
      (QExpr_Filter risky (QExpr_Filter lower input)) (SqlSuccess nil).
Proof.
intros env lower risky input row truth Hinput Hlower Hnontrue.
eapply query_nested_filter_inner_empty_skips_outer.
eapply EQuery_FilterRows with (input_rows := row :: nil).
- exact Hinput.
- eapply filter_rows_single_nontrue_success_empty.
  + exact Hlower.
  + exact Hnontrue.
Qed.

Lemma query_same_rows_as_bag_transport :
  forall first second bag,
    query_same_rows_as_bag first bag ->
    bag_eq T (rows_bag T first) (rows_bag T second) ->
    query_same_rows_as_bag second bag.
Proof.
intros first second bag Hfirst Heq.
unfold query_same_rows_as_bag, query_rows_bag,
  bag_eq, rows_bag in *.
unfold SqlQuerySemantics.BTupleT, SqlBagAbstraction.BTupleT in *.
eapply Febag.equal_trans.
- apply Febag.equal_sym; exact Heq.
- exact Hfirst.
Qed.

Lemma query_same_rows_as_bag_iff_bag_eq :
  forall rows bag,
    query_same_rows_as_bag rows bag <->
    bag_eq T (rows_bag T rows) bag.
Proof.
intros rows bag.
unfold query_same_rows_as_bag, query_rows_bag, bag_eq, rows_bag.
unfold SqlQuerySemantics.BTupleT, SqlBagAbstraction.BTupleT.
tauto.
Qed.

Lemma query_same_rows_as_bag_bag_transport :
  forall rows first second,
    query_same_rows_as_bag rows first ->
    bag_eq T first second ->
    query_same_rows_as_bag rows second.
Proof.
intros rows first second Hrows Heq.
apply query_same_rows_as_bag_iff_bag_eq in Hrows.
apply query_same_rows_as_bag_iff_bag_eq.
eapply bag_eq_trans; [exact Hrows | exact Heq].
Qed.

Lemma concrete_permutation_rows_bag_eq :
  forall first second,
    Permutation first second ->
    bag_eq T (rows_bag T first) (rows_bag T second).
Proof.
intros first second Hpermutation.
unfold bag_eq, rows_bag.
rewrite Febag.nb_occ_equal; intro row.
rewrite 2 Febag.nb_occ_mk_bag.
now apply permutation_preserves_oeset_occurrences.
Qed.

Lemma eval_query_expr_project_success_iff :
  forall env select_list input output,
    eval_query_expr env (QExpr_Project select_list input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      @project_rows_outcome T symbol_runtime_error aggregate_runtime_error
        env select_list input_rows = SqlSuccess output.
Proof.
intros env select_list input output; split.
- intro Heval; inversion Heval; subst.
  eexists; split; [eassumption | reflexivity].
- intros [input_rows [Hinput Hproject]].
  rewrite <- Hproject.
  now apply EQuery_ProjectRows.
Qed.

Lemma eval_query_expr_row_map_success_iff :
  forall env output_attributes row_map input output,
    eval_query_expr env
      (QExpr_RowMap output_attributes row_map input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      @row_map_rows_outcome T row_map input_rows = SqlSuccess output.
Proof.
intros env output_attributes row_map input output; split.
- intro Heval; inversion Heval; subst.
  eexists; split; [eassumption | reflexivity].
- intros [input_rows [Hinput Hrow_map]].
  rewrite <- Hrow_map.
  now apply EQuery_RowMapRows.
Qed.

Lemma eval_query_expr_filter_success_iff :
  forall env formula input output,
    eval_query_expr env (QExpr_Filter formula input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      @eval_filter_rows_outcome T relname basesort instance unknown
        symbol_runtime_error aggregate_runtime_error value_is_null
        env formula input_rows (SqlSuccess output).
Proof.
intros env formula input output; split.
- intro Heval; inversion Heval; subst.
  eexists; split; eassumption.
- intros [input_rows [Hinput Hfilter]].
  eapply EQuery_FilterRows with (input_rows := input_rows).
  + exact Hinput.
  + exact Hfilter.
Qed.

Theorem query_project_preserves_concrete_permutation_closed :
  forall env select_list input,
    ConcretePermutationClosed T
      (fun rows => eval_query_expr env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query_expr env (QExpr_Project select_list input)
          (SqlSuccess rows)).
Proof.
intros env select_list input Hclosed source desired Hpermutation Hsource.
apply eval_query_expr_project_success_iff in Hsource.
destruct Hsource as [input_rows [Hinput Hproject]].
destruct (project_rows_outcome_success_output_permutation
  env select_list input_rows Hproject Hpermutation)
  as [permuted_input [Hinput_permutation Hproject']].
apply eval_query_expr_project_success_iff.
exists permuted_input; split; [|exact Hproject'].
exact (Hclosed input_rows permuted_input Hinput_permutation Hinput).
Qed.

Theorem query_row_map_preserves_concrete_permutation_closed :
  forall env output_attributes row_map input,
    ConcretePermutationClosed T
      (fun rows => eval_query_expr env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query_expr env (QExpr_RowMap output_attributes row_map input)
          (SqlSuccess rows)).
Proof.
intros env output_attributes row_map input Hclosed
  source desired Hpermutation Hsource.
apply eval_query_expr_row_map_success_iff in Hsource.
destruct Hsource as [input_rows [Hinput Hrow_map]].
destruct (row_map_rows_outcome_success_output_permutation
  row_map input_rows Hrow_map Hpermutation)
  as [permuted_input [Hinput_permutation Hrow_map']].
apply eval_query_expr_row_map_success_iff.
exists permuted_input; split; [|exact Hrow_map'].
exact (Hclosed input_rows permuted_input Hinput_permutation Hinput).
Qed.

Theorem query_filter_preserves_concrete_permutation_closed :
  forall env formula input,
    ConcretePermutationClosed T
      (fun rows => eval_query_expr env input (SqlSuccess rows)) ->
    ConcretePermutationClosed T
      (fun rows =>
        eval_query_expr env (QExpr_Filter formula input) (SqlSuccess rows)).
Proof.
intros env formula input Hclosed source desired Hpermutation Hsource.
apply eval_query_expr_filter_success_iff in Hsource.
destruct Hsource as [input_rows [Hinput Hfilter]].
destruct (eval_filter_rows_success_output_permutation
  Hfilter Hpermutation)
  as [permuted_input [Hinput_permutation Hfilter']].
apply eval_query_expr_filter_success_iff.
exists permuted_input; split; [|exact Hfilter'].
exact (Hclosed input_rows permuted_input Hinput_permutation Hinput).
Qed.

(** Every syntactic [BagReset] point is closed under changing
    a successful representative list to any bag-equal representative. *)
Lemma query_bag_reset_success_transport :
  forall env q first second,
    query_expr_order_behavior q = BagReset ->
    bag_eq T (rows_bag T first) (rows_bag T second) ->
    eval_query_expr env q (SqlSuccess first) ->
    eval_query_expr env q (SqlSuccess second).
Proof.
intros env q first second Hbehavior Heq Heval.
destruct q; simpl in Hbehavior; try discriminate;
  inversion Heval; subst;
  solve [econstructor;
         eauto using query_same_rows_as_bag_transport].
Qed.

(** [BagReset] establishes the concrete implementation certificate on
    successful observations.  This statement deliberately says nothing about
    error outcomes, whose first-error behavior remains order-sensitive. *)
Theorem query_bag_reset_concrete_permutation_closed :
  forall env q,
    query_expr_order_behavior q = BagReset ->
    ConcretePermutationClosed T
      (fun rows => eval_query_expr env q (SqlSuccess rows)).
Proof.
intros env q Hbehavior source desired Hpermutation Hsource.
eapply (query_bag_reset_success_transport
  (env := env) (q := q) (first := source) desired).
- exact Hbehavior.
- now apply concrete_permutation_rows_bag_eq.
- exact Hsource.
Qed.

Theorem query_bag_reset_sound :
  forall env q,
    query_expr_order_behavior q = BagReset ->
    BagClosed T
      (fun rows => eval_query_expr env q (SqlSuccess rows)).
Proof.
intros env q Hbehavior.
apply concrete_permutation_closed_implies_bag_closed.
now apply query_bag_reset_concrete_permutation_closed.
Qed.

(** Soundness of the recursive syntax classifier.  It recognizes a reset and
    any finite stack of the three transparent, order-preserving unary
    constructors above it. *)
Theorem query_expr_permutation_closure_certified_sound :
  forall env q,
    query_expr_permutation_closure_certified q = true ->
    ConcretePermutationClosed T
      (fun rows => eval_query_expr env q (SqlSuccess rows)).
Proof.
intro env.
fix IH 1.
intros q Hcertified.
destruct q; simpl in Hcertified;
  try discriminate;
  try solve [apply query_bag_reset_concrete_permutation_closed; reflexivity].
- apply query_project_preserves_concrete_permutation_closed.
  now apply IH.
- apply query_row_map_preserves_concrete_permutation_closed.
  now apply IH.
- apply query_filter_preserves_concrete_permutation_closed.
  now apply IH.
Qed.

Theorem query_expr_permutation_closure_certified_bag_closed :
  forall env q,
    query_expr_permutation_closure_certified q = true ->
    BagClosed T
      (fun rows => eval_query_expr env q (SqlSuccess rows)).
Proof.
intros env q Hcertified.
apply concrete_permutation_closed_implies_bag_closed.
now apply query_expr_permutation_closure_certified_sound.
Qed.

(** General introduction rule used by generated proof obligations.  Ordered
    outputs are compared positionally, while each corresponding SQL row uses
    [OTuple]'s extensional equality.  Requiring witnesses in both directions
    avoids imposing Coq representation equality on projected tuples. *)
Theorem query_expr_equiv_of_ordered_observations :
  forall env left right,
    @query_expr_outputs T relname left = @query_expr_outputs T relname right ->
    (exists rows, eval_query_expr env left (SqlSuccess rows)) ->
    (forall error, ~ eval_query_expr env left (SqlError error)) ->
    (forall error, ~ eval_query_expr env right (SqlError error)) ->
    (forall left_rows,
      eval_query_expr env left (SqlSuccess left_rows) ->
      exists right_rows,
        eval_query_expr env right (SqlSuccess right_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      eval_query_expr env right (SqlSuccess right_rows) ->
      exists left_rows,
        eval_query_expr env left (SqlSuccess left_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
Proof.
intros env left right Houtputs Hsuccess Hleft_safe Hright_safe Hforward Hbackward.
unfold query_expr_equiv; split; [exact Houtputs |].
unfold query_expr_observation_equiv.
now apply successful_relation_equiv_intro.
Qed.

(** Convenient specialization for proofs where both evaluators expose the
    exact same Rocq list representatives. *)
Theorem query_expr_equiv_of_observations :
  forall env left right,
    @query_expr_outputs T relname left = @query_expr_outputs T relname right ->
    (exists rows, eval_query_expr env left (SqlSuccess rows)) ->
    (forall error, ~ eval_query_expr env left (SqlError error)) ->
    (forall error, ~ eval_query_expr env right (SqlError error)) ->
    (forall rows,
      eval_query_expr env left (SqlSuccess rows) <->
      eval_query_expr env right (SqlSuccess rows)) ->
    @query_expr_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
Proof.
intros env left right Houtputs Hsuccess Hleft_safe Hright_safe Hobservations.
apply query_expr_equiv_of_ordered_observations; try assumption.
- intros rows Hrows.
  exists rows; split.
  + now apply (proj1 (Hobservations rows)).
  + apply ordered_rows_equiv_refl.
- intros rows Hrows.
  exists rows; split.
  + now apply (proj2 (Hobservations rows)).
  + apply ordered_rows_equiv_refl.
Qed.

(** Introduction rule for exact error-preserving equivalence.  Unlike the
    success-only rule, it permits an error-only relation, but each side must
    expose at least one outcome.  It then matches every success and every error
    in both directions. *)
Theorem query_expr_outcome_equiv_of_observations :
  forall env left right,
    @query_expr_outputs T relname left = @query_expr_outputs T relname right ->
    (exists outcome, eval_query_expr env left outcome) ->
    (exists outcome, eval_query_expr env right outcome) ->
    (forall left_rows,
      eval_query_expr env left (SqlSuccess left_rows) ->
      exists right_rows,
        eval_query_expr env right (SqlSuccess right_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      eval_query_expr env right (SqlSuccess right_rows) ->
      exists left_rows,
        eval_query_expr env left (SqlSuccess left_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall error,
      eval_query_expr env left (SqlError error) <->
      eval_query_expr env right (SqlError error)) ->
    @query_expr_outcome_equiv T relname basesort instance unknown
      symbol_runtime_error aggregate_runtime_error value_is_null
      env left right.
Proof.
intros env left right Houtputs Hleft Hright Hforward Hbackward Herrors.
unfold query_expr_outcome_equiv; split; [exact Houtputs |].
unfold query_expr_outcome_observation_equiv.
now apply outcome_relation_equiv_intro.
Qed.

Definition query_possible_bag_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  successful_relation_equiv
    (bag_eq T)
    (outcome_alpha T (eval_query_expr env left))
    (outcome_alpha T (eval_query_expr env right)).

Theorem query_bag_closed_observation_equiv_iff_possible_bag_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_query_expr env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query_expr env right (SqlSuccess rows)) ->
    (@query_expr_observation_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_possible_bag_equiv env left right).
Proof.
intros env left right Hleft_closed Hright_closed.
unfold query_expr_observation_equiv, query_possible_bag_equiv.
apply successful_relation_equiv_iff_outcome_alpha.
- exact Hleft_closed.
- exact Hright_closed.
Qed.

Corollary query_bag_reset_observation_equiv_iff_possible_bag_equiv :
  forall env left right,
    query_expr_order_behavior left = BagReset ->
    query_expr_order_behavior right = BagReset ->
    (@query_expr_observation_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_possible_bag_equiv env left right).
Proof.
intros env left right Hleft Hright.
apply query_bag_closed_observation_equiv_iff_possible_bag_equiv.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

Theorem query_bag_closed_typed_equiv_iff_possible_bag_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_query_expr env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query_expr env right (SqlSuccess rows)) ->
    (@query_expr_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_outputs left = query_expr_outputs right /\
     query_possible_bag_equiv env left right).
Proof.
intros env left right Hleft Hright.
unfold query_expr_equiv.
split; intros [Houtputs Hobservation]; split;
  [exact Houtputs | | exact Houtputs |].
- now apply (proj1
    (query_bag_closed_observation_equiv_iff_possible_bag_equiv
      (env := env) (left := left) (right := right) Hleft Hright)).
- now apply (proj2
    (query_bag_closed_observation_equiv_iff_possible_bag_equiv
      (env := env) (left := left) (right := right) Hleft Hright)).
Qed.

Corollary query_bag_reset_typed_equiv_iff_possible_bag_equiv :
  forall env left right,
    query_expr_order_behavior left = BagReset ->
    query_expr_order_behavior right = BagReset ->
    (@query_expr_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_outputs left = query_expr_outputs right /\
     query_possible_bag_equiv env left right).
Proof.
intros env left right Hleft Hright.
apply query_bag_closed_typed_equiv_iff_possible_bag_equiv.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

Definition query_possible_bag_outcome_equiv
    (env : Env.env T) (left right : query_expr T relname) : Prop :=
  outcome_relation_equiv
    (bag_eq T)
    (outcome_alpha T (eval_query_expr env left))
    (outcome_alpha T (eval_query_expr env right)).

Theorem query_bag_closed_outcome_observation_equiv_iff_possible_bag_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_query_expr env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query_expr env right (SqlSuccess rows)) ->
    (@query_expr_outcome_observation_equiv T relname basesort instance unknown symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_possible_bag_outcome_equiv env left right).
Proof.
intros env left right Hleft Hright.
unfold query_expr_outcome_observation_equiv,
  query_possible_bag_outcome_equiv.
apply outcome_relation_equiv_iff_outcome_alpha.
- exact Hleft.
- exact Hright.
Qed.

Corollary query_bag_reset_outcome_observation_equiv_iff_possible_bag_equiv :
  forall env left right,
    query_expr_order_behavior left = BagReset ->
    query_expr_order_behavior right = BagReset ->
    (@query_expr_outcome_observation_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_possible_bag_outcome_equiv env left right).
Proof.
intros env left right Hleft Hright.
apply query_bag_closed_outcome_observation_equiv_iff_possible_bag_equiv.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

Theorem query_bag_closed_typed_outcome_equiv_iff_possible_bag_equiv :
  forall env left right,
    BagClosed T
      (fun rows => eval_query_expr env left (SqlSuccess rows)) ->
    BagClosed T
      (fun rows => eval_query_expr env right (SqlSuccess rows)) ->
    (@query_expr_outcome_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_outputs left = query_expr_outputs right /\
     query_possible_bag_outcome_equiv env left right).
Proof.
intros env left right Hleft Hright.
unfold query_expr_outcome_equiv.
split; intros [Houtputs Hobservation]; split;
  [exact Houtputs | | exact Houtputs |].
- now apply (proj1
    (query_bag_closed_outcome_observation_equiv_iff_possible_bag_equiv
      (env := env) (left := left) (right := right) Hleft Hright)).
- now apply (proj2
    (query_bag_closed_outcome_observation_equiv_iff_possible_bag_equiv
      (env := env) (left := left) (right := right) Hleft Hright)).
Qed.

Corollary query_bag_reset_typed_outcome_equiv_iff_possible_bag_equiv :
  forall env left right,
    query_expr_order_behavior left = BagReset ->
    query_expr_order_behavior right = BagReset ->
    (@query_expr_outcome_equiv T relname basesort instance unknown
       symbol_runtime_error aggregate_runtime_error value_is_null
       env left right <->
     query_expr_outputs left = query_expr_outputs right /\
     query_possible_bag_outcome_equiv env left right).
Proof.
intros env left right Hleft Hright.
apply query_bag_closed_typed_outcome_equiv_iff_possible_bag_equiv.
- now apply query_bag_reset_sound.
- now apply query_bag_reset_sound.
Qed.

(** Extensional graphs of the concrete bag operations.  These are the
    operation relations consumed by [lift_possible_bag_unary] and
    [lift_possible_bag_binary]. *)
Definition unary_bag_graph
    (operation : bagT -> bagT) : unary_bag_relation T :=
  fun input output => bag_eq T (operation input) output.

Definition binary_bag_graph
    (operation : bagT -> bagT -> bagT) : binary_bag_relation T :=
  fun left_input right_input output =>
    bag_eq T (operation left_input right_input) output.

(** A graph-valued bag operator has at most one semantic output for fixed
    inputs, even though it may have many Leibniz-distinct representatives. *)
Lemma unary_bag_graph_functional :
  forall operation,
    unary_bag_relation_functional (unary_bag_graph operation).
Proof.
intros operation input first second Hfirst Hsecond.
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst | exact Hsecond].
Qed.

Lemma binary_bag_graph_functional :
  forall operation,
    binary_bag_relation_functional (binary_bag_graph operation).
Proof.
intros operation left_input right_input first second Hfirst Hsecond.
eapply bag_eq_trans; [apply bag_eq_sym; exact Hfirst | exact Hsecond].
Qed.

Lemma unary_bag_graph_extensional :
  forall operation,
    (forall left right,
      bag_eq T left right -> bag_eq T (operation left) (operation right)) ->
    unary_bag_relation_extensional (unary_bag_graph operation).
Proof.
intros operation Hoperation input_left input_right output_left output_right
  Hinput Houtput.
unfold unary_bag_graph; split; intro Hresult.
- pose proof (Hoperation _ _ Hinput) as Hoperation_eq.
  exact
    (bag_eq_trans (bag_eq_sym Hoperation_eq)
      (bag_eq_trans Hresult Houtput)).
- pose proof (Hoperation _ _ Hinput) as Hoperation_eq.
  exact
    (bag_eq_trans Hoperation_eq
      (bag_eq_trans Hresult (bag_eq_sym Houtput))).
Qed.

Lemma binary_bag_graph_extensional :
  forall operation,
    (forall left_input left_input' right_input right_input',
      bag_eq T left_input left_input' ->
      bag_eq T right_input right_input' ->
      bag_eq T
        (operation left_input right_input)
        (operation left_input' right_input')) ->
    binary_bag_relation_extensional (binary_bag_graph operation).
Proof.
intros operation Hoperation
  left_input left_input' right_input right_input' output output'
  Hleft Hright Houtput.
unfold binary_bag_graph; split; intro Hresult.
- pose proof (Hoperation _ _ _ _ Hleft Hright) as Hoperation_eq.
  exact
    (bag_eq_trans (bag_eq_sym Hoperation_eq)
      (bag_eq_trans Hresult Houtput)).
- pose proof (Hoperation _ _ _ _ Hleft Hright) as Hoperation_eq.
  exact
    (bag_eq_trans Hoperation_eq
      (bag_eq_trans Hresult (bag_eq_sym Houtput))).
Qed.

Lemma query_set_bag_congr :
  forall operation left left' right right',
    bag_eq T left left' ->
    bag_eq T right right' ->
    bag_eq T
      (query_set_bag operation left right)
      (query_set_bag operation left' right').
Proof.
intros operation left left' right right' Hleft Hright.
unfold bag_eq, query_set_bag in *.
unfold SqlBagAbstraction.BTupleT, SqlQuerySemantics.BTupleT in *.
rewrite Febag.nb_occ_equal in Hleft, Hright |- *.
intro row; destruct operation; simpl.
- rewrite 2 Febag.nb_occ_union, Hleft, Hright; reflexivity.
- rewrite 2 Febag.nb_occ_union_max, Hleft, Hright; reflexivity.
- rewrite 2 Febag.nb_occ_inter, Hleft, Hright; reflexivity.
- rewrite 2 Febag.nb_occ_diff, Hleft, Hright; reflexivity.
Qed.

Lemma query_natural_join_compatible_eq :
  forall left left' right right',
    Oeset.compare (OTuple T) left left' = Eq ->
    Oeset.compare (OTuple T) right right' = Eq ->
    query_natural_join_compatible value_is_null left right =
    query_natural_join_compatible value_is_null left' right'.
Proof.
intros left left' right right' Hleft Hright.
unfold query_natural_join_compatible.
rewrite 2 Fset.for_all_spec.
assert (Hcommon :
  (labels T left interS labels T right) =S=
  (labels T left' interS labels T right')).
{
  apply Fset.inter_eq.
  - now apply tuple_eq_labels.
  - now apply tuple_eq_labels.
}
rewrite <- (Fset.elements_spec1 _ _ _ Hcommon).
apply forallb_eq.
intros attribute Hattribute.
pose proof (Fset.in_elements_mem _ _ _ Hattribute) as Hmember.
rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Hmember.
destruct Hmember as [Hmember_left Hmember_right].
rewrite (tuple_eq_dot_alt T left left' Hleft attribute Hmember_left).
rewrite (tuple_eq_dot_alt T right right' Hright attribute Hmember_right).
reflexivity.
Qed.

Lemma query_natural_join_bag_congr :
  forall left left' right right',
    bag_eq T left left' ->
    bag_eq T right right' ->
    bag_eq T
      (query_natural_join_bag value_is_null left right)
      (query_natural_join_bag value_is_null left' right').
Proof.
intros left left' right right' Hleft Hright.
unfold bag_eq, query_natural_join_bag in *.
unfold SqlBagAbstraction.BTupleT, SqlQuerySemantics.BTupleT in *.
rewrite Febag.nb_occ_equal in Hleft, Hright |- *.
intro row; rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
apply (theta_join_list_permut_eq
  _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
  (query_natural_join_compatible value_is_null)
  (fun left_row right_row left_row' right_row' Hleft_row Hright_row =>
    query_natural_join_compatible_eq
      left_row left_row' right_row right_row' Hleft_row Hright_row)).
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- 2 Febag.nb_occ_elements; apply Hleft.
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- 2 Febag.nb_occ_elements; apply Hright.
Qed.

Lemma query_cross_join_bag_congr :
  forall left left' right right',
    bag_eq T left left' ->
    bag_eq T right right' ->
    bag_eq T
      (query_cross_join_bag left right)
      (query_cross_join_bag left' right').
Proof.
intros left left' right right' Hleft Hright.
unfold bag_eq, query_cross_join_bag in *.
unfold SqlBagAbstraction.BTupleT, SqlQuerySemantics.BTupleT in *.
rewrite Febag.nb_occ_equal in Hleft, Hright |- *.
intro row; rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.permut_nb_occ.
unfold brute_left_join_list.
apply (theta_join_list_permut_eq
  _ (OTuple T) _ (join_tuple_eq_1 T) (join_tuple_eq_2 T)
  (fun _ _ : tuple => true) (fun _ _ _ _ _ _ => refl_equal _)).
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- 2 Febag.nb_occ_elements; apply Hleft.
- apply Oeset.nb_occ_permut; intro item.
  rewrite <- 2 Febag.nb_occ_elements; apply Hright.
Qed.

Lemma query_distinct_bag_congr :
  forall input input',
    bag_eq T input input' ->
    bag_eq T (query_distinct_bag input) (query_distinct_bag input').
Proof.
intros input input' Hinput.
unfold bag_eq, query_distinct_bag in *.
unfold SqlBagAbstraction.BTupleT, SqlQuerySemantics.BTupleT in *.
rewrite Febag.nb_occ_equal in Hinput |- *.
intro row; rewrite 2 Febag.nb_occ_mk_bag.
apply Oeset.nb_occ_eq_2.
apply Feset.elements_spec1.
apply Feset.mk_set_eq_weak.
intro item; rewrite <- 2 Febag.nb_occ_elements; apply Hinput.
Qed.

(** [OTuple] equality is extensional rather than Leibniz equality.  Once each
    element is canonized, equal sorted bag-element lists therefore become
    literally equal lists.  This is the representative-independence bridge
    used by native [rank()]. *)
Lemma map_canonized_tuple_comparelA_eq :
  forall left right,
    comparelA (Oeset.compare (OTuple T)) left right = Eq ->
    map (@canonized_tuple T) left = map (@canonized_tuple T) right.
Proof.
induction left as [| x xs IH]; intros [| y ys] Hcompare;
  simpl in Hcompare |- *; try discriminate; try reflexivity.
destruct (Oeset.compare (OTuple T) x y) eqn:Hxy; try discriminate.
assert (Hcanon : canonized_tuple T x = canonized_tuple T y).
{
  unfold canonized_tuple; f_equal.
  now apply (proj1 (tuple_as_pairs_canonizes T x y)).
}
rewrite Hcanon; f_equal; now apply IH.
Qed.

Lemma query_rank_bag_rows_eq :
  forall left right,
    bag_eq T left right ->
    query_rank_bag_rows left = query_rank_bag_rows right.
Proof.
intros left right Hbags.
unfold query_rank_bag_rows, bag_eq in *.
apply map_canonized_tuple_comparelA_eq.
now apply Febag.elements_spec1.
Qed.

Definition query_set_bag_function
    (operation : set_op)
    (left right : query_expr T relname) : bagT -> bagT -> bagT :=
  fun left_bag right_bag =>
    if query_expr_sort left =S?= query_expr_sort right
    then query_set_bag operation left_bag right_bag
    else Febag.empty BTupleT.

Definition query_set_bag_relation
    (operation : set_op)
    (left right : query_expr T relname) : binary_bag_relation T :=
  binary_bag_graph (query_set_bag_function operation left right).

Definition query_natural_join_bag_relation : binary_bag_relation T :=
  binary_bag_graph (query_natural_join_bag value_is_null).

Definition query_cross_join_bag_relation : binary_bag_relation T :=
  binary_bag_graph query_cross_join_bag.

Definition query_distinct_bag_relation : unary_bag_relation T :=
  unary_bag_graph query_distinct_bag.

(** The abstract grouping operation is the successful fragment of the exact
    bag-level grouping outcome relation.  It is relational because correlated
    subqueries and representation-sensitive runtime checks may retain several
    outcomes for one semantic input bag. *)
Definition query_group_bag_relation
    (env : Env.env T) (select_list : _select_list T)
    (group_terms : list (@aggterm T)) (having : formula_expr T relname) :
    unary_bag_relation T :=
  fun input_bag output_bag =>
    eval_group_bag env select_list group_terms having input_bag
      (SqlSuccess output_bag).

(** The helper produces one concrete bag representation after UNION ALL.
    Closing that result under bag equality makes the abstract operation a
    proper relation on semantic bags without changing exact row observations. *)
Definition query_grouping_sets_bag_relation
    (env : Env.env T) (grouping_sets : list (query_grouping_set T)) :
    unary_bag_relation T :=
  fun input_bag output_bag =>
    exists evaluated_bag,
      eval_grouping_sets_bag env grouping_sets input_bag
        (SqlSuccess evaluated_bag) /\
      bag_eq T evaluated_bag output_bag.

(** Ranking is a relational reset point at the proof-abstraction boundary.
    The concrete rank computation is deterministic on the canonical input-bag
    rows; output closure records that SQL row order is not observable above a
    [BagReset] boundary. *)
Definition query_rank_bag_relation
    (partition_keys order_keys : list (sort_key T))
    (rank_attribute : attribute T) (rank_value : nat -> option value) :
    unary_bag_relation T :=
  fun input_bag output_bag =>
    exists ranked_rows,
      @query_rank_rows_outcome T value_is_null
        partition_keys order_keys rank_attribute rank_value
        (query_rank_bag_rows input_bag) (query_rank_bag_rows input_bag) =
          Some ranked_rows /\
      bag_eq T (rows_bag T ranked_rows) output_bag.

(** Cumulative windows choose one of every legal peer ordering and evaluate
    all items against that same ordering.  The output is closed under bag
    equality because a window without an enclosing ORDER BY does not expose
    its internal processing order. *)
Definition query_window_bag_relation
    (env : Env.env T) (partition_keys order_keys : list (sort_key T))
    (items : list (query_window_item T)) : unary_bag_relation T :=
  fun input_bag output_bag =>
    exists ordered_rows, exists window_rows,
      @order_by_rows T value_is_null (partition_keys ++ order_keys)
        (query_rank_bag_rows input_bag) ordered_rows /\
      query_window_rows_outcome symbol_runtime_error aggregate_runtime_error
        value_is_null env partition_keys items None 0 nil ordered_rows =
        Some (SqlSuccess window_rows) /\
      bag_eq T (rows_bag T window_rows) output_bag.

(** Successful native joins form a binary relation on possible child bags.
    The exact bag-level relation is quotient-saturated over representatives,
    so this abstraction never selects a deterministic tied child outcome. *)
Definition query_join_bag_relation
    (env : Env.env T) (kind : query_join_kind)
    (predicate : formula_expr T relname)
    (matched_select left_select right_select : _select_list T) :
    binary_bag_relation T :=
  fun left_bag right_bag output_bag =>
    eval_join_bag env kind predicate
      matched_select left_select right_select left_bag right_bag
      (SqlSuccess output_bag).

Lemma query_set_bag_function_congr :
  forall operation left right left_bag left_bag' right_bag right_bag',
    bag_eq T left_bag left_bag' ->
    bag_eq T right_bag right_bag' ->
    bag_eq T
      (query_set_bag_function operation left right left_bag right_bag)
      (query_set_bag_function operation left right left_bag' right_bag').
Proof.
intros operation left right left_bag left_bag' right_bag right_bag'
  Hleft Hright.
unfold query_set_bag_function.
destruct (query_expr_sort left =S?= query_expr_sort right).
- now apply query_set_bag_congr.
- apply bag_eq_refl.
Qed.

Lemma query_set_bag_relation_extensional :
  forall operation left right,
    binary_bag_relation_extensional
      (query_set_bag_relation operation left right).
Proof.
intros operation left right.
apply binary_bag_graph_extensional.
intros left_bag left_bag' right_bag right_bag' Hleft Hright.
now apply query_set_bag_function_congr.
Qed.

(** The relation used for a set operation contains the static compatibility
    test for its two inputs.  Replacing either input by a query of the same
    result sort therefore preserves the operation relation itself. *)
Lemma query_set_bag_relation_sort_congr :
  forall operation left left' right right',
    query_expr_sort left =S= query_expr_sort left' ->
    query_expr_sort right =S= query_expr_sort right' ->
    binary_bag_relation_equiv
      (query_set_bag_relation operation left right)
      (query_set_bag_relation operation left' right').
Proof.
intros operation left left' right right' Hleft_sort Hright_sort
  left_bag right_bag output_bag.
assert (Hcompatible :
  (query_expr_sort left =S?= query_expr_sort right) =
  (query_expr_sort left' =S?= query_expr_sort right')).
{
  rewrite (Fset.equal_eq_1 _ _ _ _ Hleft_sort).
  now rewrite (Fset.equal_eq_2 _ _ _ _ Hright_sort).
}
unfold query_set_bag_relation, binary_bag_graph,
  query_set_bag_function.
now rewrite Hcompatible.
Qed.

Lemma query_natural_join_bag_relation_extensional :
  binary_bag_relation_extensional query_natural_join_bag_relation.
Proof.
apply binary_bag_graph_extensional.
intros; now apply query_natural_join_bag_congr.
Qed.

Lemma query_cross_join_bag_relation_extensional :
  binary_bag_relation_extensional query_cross_join_bag_relation.
Proof.
apply binary_bag_graph_extensional.
intros; now apply query_cross_join_bag_congr.
Qed.

Lemma query_distinct_bag_relation_extensional :
  unary_bag_relation_extensional query_distinct_bag_relation.
Proof.
apply unary_bag_graph_extensional.
intros; now apply query_distinct_bag_congr.
Qed.

Lemma eval_group_bag_outcome_input_transport :
  forall env select_list group_terms having input_bag input_bag' outcome,
    bag_eq T input_bag input_bag' ->
    eval_group_bag env select_list group_terms having input_bag outcome ->
    eval_group_bag env select_list group_terms having input_bag' outcome.
Proof.
intros env select_list group_terms having input_bag input_bag' outcome
  Hinput Heval.
inversion Heval; subst.
- eapply EGroupBag_KeyError.
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eassumption.
- eapply EGroupBag_ProcessError.
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eassumption.
  + eassumption.
- eapply EGroupBag_Success with
    (representative := representative) (grouped_rows := grouped_rows).
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eassumption.
  + eassumption.
  + eassumption.
Qed.

Lemma eval_group_bag_outcome_input_equiv :
  forall env select_list group_terms having input_bag input_bag' outcome,
    bag_eq T input_bag input_bag' ->
    (eval_group_bag env select_list group_terms having input_bag outcome <->
     eval_group_bag env select_list group_terms having input_bag' outcome).
Proof.
intros env select_list group_terms having input_bag input_bag' outcome Hinput.
split; intro Heval.
- eapply eval_group_bag_outcome_input_transport
    with (input_bag := input_bag); eassumption.
- eapply eval_group_bag_outcome_input_transport
    with (input_bag := input_bag'); [|exact Heval].
  now apply bag_eq_sym.
Qed.

Lemma query_group_bag_relation_extensional :
  forall env select_list group_terms having,
    unary_bag_relation_extensional
      (query_group_bag_relation env select_list group_terms having).
Proof.
intros env select_list group_terms having
  input_bag input_bag' output_bag output_bag' Hinput Houtput.
unfold query_group_bag_relation.
split; intro Heval.
- inversion Heval; subst.
  eapply EGroupBag_Success with
    (representative := representative) (grouped_rows := grouped_rows).
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eassumption.
  + eassumption.
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
- inversion Heval; subst.
  eapply EGroupBag_Success with
    (representative := representative) (grouped_rows := grouped_rows).
  + eapply query_same_rows_as_bag_bag_transport.
    * eassumption.
    * now apply bag_eq_sym.
  + eassumption.
  + eassumption.
  + eapply query_same_rows_as_bag_bag_transport.
    * eassumption.
    * now apply bag_eq_sym.
Qed.

Lemma eval_grouping_sets_bag_outcome_input_transport :
  forall env grouping_sets input_bag input_bag' outcome,
    bag_eq T input_bag input_bag' ->
    eval_grouping_sets_bag env grouping_sets input_bag outcome ->
    eval_grouping_sets_bag env grouping_sets input_bag' outcome.
Proof.
intros env grouping_sets input_bag input_bag' outcome Hinput Heval.
induction Heval.
- constructor.
- apply EGroupingSets_HeadError.
  eapply eval_group_bag_outcome_input_transport; eassumption.
- eapply EGroupingSets_TailError.
  + eapply eval_group_bag_outcome_input_transport; eassumption.
  + now apply IHHeval.
- eapply EGroupingSets_ConsSuccess.
  + eapply eval_group_bag_outcome_input_transport; eassumption.
  + now apply IHHeval.
Qed.

Lemma query_grouping_sets_bag_relation_extensional :
  forall env grouping_sets,
    unary_bag_relation_extensional
      (query_grouping_sets_bag_relation env grouping_sets).
Proof.
intros env grouping_sets input_bag input_bag' output_bag output_bag'
  Hinput Houtput.
unfold query_grouping_sets_bag_relation.
split; intros [evaluated_bag [Heval Hevaluated]].
- exists evaluated_bag; split.
  + eapply eval_grouping_sets_bag_outcome_input_transport; eassumption.
  + exact (bag_eq_trans Hevaluated Houtput).
- exists evaluated_bag; split.
  + eapply eval_grouping_sets_bag_outcome_input_transport.
    * exact (bag_eq_sym Hinput).
    * exact Heval.
  + exact (bag_eq_trans Hevaluated (bag_eq_sym Houtput)).
Qed.

Lemma query_rank_bag_relation_extensional :
  forall partition_keys order_keys rank_attribute rank_value,
    unary_bag_relation_extensional
      (query_rank_bag_relation
        partition_keys order_keys rank_attribute rank_value).
Proof.
intros partition_keys order_keys rank_attribute rank_value
  input_left input_right output_left output_right Hinput Houtput.
pose proof (query_rank_bag_rows_eq Hinput) as Hrows.
unfold query_rank_bag_relation.
split; intros [ranked_rows [Hrank Hbag]].
- exists ranked_rows; split.
  + now rewrite <- Hrows.
  + exact (bag_eq_trans Hbag Houtput).
- exists ranked_rows; split.
  + now rewrite Hrows.
  + exact (bag_eq_trans Hbag (bag_eq_sym Houtput)).
Qed.

(** For a fixed semantic input bag, RANK computes over the canonical bag-row
    enumeration and is therefore functional modulo [bag_eq].  This does not
    claim that the enclosing child query has only one possible bag; that
    independent premise is required by the query-level composition theorem. *)
Lemma query_rank_bag_relation_functional :
  forall partition_keys order_keys rank_attribute rank_value,
    unary_bag_relation_functional
      (query_rank_bag_relation
        partition_keys order_keys rank_attribute rank_value).
Proof.
intros partition_keys order_keys rank_attribute rank_value
  input_bag first second
  [first_rows [Hfirst Hfirst_bag]]
  [second_rows [Hsecond Hsecond_bag]].
rewrite Hfirst in Hsecond.
inversion Hsecond; subst second_rows.
exact (bag_eq_trans (bag_eq_sym Hfirst_bag) Hsecond_bag).
Qed.

Lemma query_window_bag_relation_extensional :
  forall env partition_keys order_keys items,
    unary_bag_relation_extensional
      (query_window_bag_relation env partition_keys order_keys items).
Proof.
intros env partition_keys order_keys items
  input_left input_right output_left output_right Hinput Houtput.
pose proof (query_rank_bag_rows_eq Hinput) as Hrows.
unfold query_window_bag_relation.
split; intros [ordered_rows [window_rows [Horder [Hwindow Hbag]]]].
- exists ordered_rows, window_rows; split.
  + now rewrite <- Hrows.
  + split; [exact Hwindow | exact (bag_eq_trans Hbag Houtput)].
- exists ordered_rows, window_rows; split.
  + now rewrite Hrows.
  + split; [exact Hwindow | exact (bag_eq_trans Hbag (bag_eq_sym Houtput))].
Qed.

Lemma query_join_bag_relation_extensional :
  forall env kind predicate matched_select left_select right_select,
    binary_bag_relation_extensional
      (query_join_bag_relation env kind predicate
        matched_select left_select right_select).
Proof.
intros env kind predicate matched_select left_select right_select
  left_bag left_bag' right_bag right_bag' output_bag output_bag'
  Hleft Hright Houtput.
unfold query_join_bag_relation.
split; intro Heval; inversion Heval; subst.
- eapply EJoinBag_Success with
    (left_rows := left_rows) (right_rows := right_rows)
    (matrix := matrix) (projected := projected).
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
  + eassumption.
  + eassumption.
  + eapply query_same_rows_as_bag_bag_transport; eassumption.
- eapply EJoinBag_Success with
    (left_rows := left_rows) (right_rows := right_rows)
    (matrix := matrix) (projected := projected).
  + eapply query_same_rows_as_bag_bag_transport.
    * eassumption.
    * now apply bag_eq_sym.
  + eapply query_same_rows_as_bag_bag_transport.
    * eassumption.
    * now apply bag_eq_sym.
  + eassumption.
  + eassumption.
  + eapply query_same_rows_as_bag_bag_transport.
    * eassumption.
    * now apply bag_eq_sym.
Qed.

Definition query_success_bags
    (env : Env.env T) (q : query_expr T relname) : bagT -> Prop :=
  alpha T (fun rows => eval_query_expr env q (SqlSuccess rows)).

(** Local equality of the exact ordered success observations induces equality
    of their possible-bag abstractions.  This is the entry point for proofs
    that establish a list-sensitive subquery equivalence locally and then let
    an enclosing order-insensitive operator continue with bag reasoning. *)
Lemma query_success_bags_of_success_rel_equiv :
  forall env left right,
    (forall left_rows,
      eval_query_expr env left (SqlSuccess left_rows) ->
      exists right_rows,
        eval_query_expr env right (SqlSuccess right_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    (forall right_rows,
      eval_query_expr env right (SqlSuccess right_rows) ->
      exists left_rows,
        eval_query_expr env left (SqlSuccess left_rows) /\
        @ordered_rows_equiv T left_rows right_rows) ->
    rel_equiv
      (query_success_bags env left)
      (query_success_bags env right).
Proof.
intros env left right Hforward Hbackward bag.
unfold query_success_bags, alpha.
split.
- intros [left_rows [Hleft Hbag]].
  destruct (Hforward left_rows Hleft)
    as [right_rows [Hright Hrows]].
  exists right_rows; split; [exact Hright |].
  eapply bag_eq_trans.
  + exact (bag_eq_sym (ordered_rows_equiv_implies_bag_eq Hrows)).
  + exact Hbag.
- intros [right_rows [Hright Hbag]].
  destruct (Hbackward right_rows Hright)
    as [left_rows [Hleft Hrows]].
  exists left_rows; split; [exact Hleft |].
  eapply bag_eq_trans.
  + exact (ordered_rows_equiv_implies_bag_eq Hrows).
  + exact Hbag.
Qed.

Lemma rows_bag_elements :
  forall bag,
    bag_eq T (rows_bag T (Febag.elements BTupleT bag)) bag.
Proof.
intro bag.
unfold bag_eq, rows_bag, SqlBagAbstraction.BTupleT.
apply Febag.elements_mk_bag.
Qed.

Lemma query_elements_same_rows_as_bag :
  forall bag,
    query_same_rows_as_bag (Febag.elements BTupleT bag) bag.
Proof.
intro bag; apply query_same_rows_as_bag_iff_bag_eq.
apply rows_bag_elements.
Qed.

Lemma query_binary_reset_possible_bags :
  forall env parent left right operation,
    (forall output,
      eval_query_expr env parent (SqlSuccess output) <->
      exists left_rows, exists right_rows,
        eval_query_expr env left (SqlSuccess left_rows) /\
        eval_query_expr env right (SqlSuccess right_rows) /\
        query_same_rows_as_bag output
          (operation (rows_bag T left_rows) (rows_bag T right_rows))) ->
    (forall left_bag left_bag' right_bag right_bag',
      bag_eq T left_bag left_bag' ->
      bag_eq T right_bag right_bag' ->
      bag_eq T
        (operation left_bag right_bag)
        (operation left_bag' right_bag')) ->
    rel_equiv
      (query_success_bags env parent)
      (lift_possible_bag_binary (binary_bag_graph operation)
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env parent left right operation Heval Hoperation output_bag.
unfold query_success_bags, alpha, lift_possible_bag_binary,
  binary_bag_graph.
split.
- intros [output [Houtput Houtput_bag]].
  apply Heval in Houtput.
  destruct Houtput as
    [left_rows [right_rows [Hleft [Hright Hresult]]]].
  exists (rows_bag T left_rows); exists (rows_bag T right_rows).
  repeat split.
  + exists left_rows; split; [exact Hleft | apply bag_eq_refl].
  + exists right_rows; split; [exact Hright | apply bag_eq_refl].
  + apply query_same_rows_as_bag_iff_bag_eq in Hresult.
    exact
      (bag_eq_trans (bag_eq_sym Hresult) Houtput_bag).
- intros [left_bag [right_bag
    [[left_rows [Hleft Hleft_bag]]
     [[right_rows [Hright Hright_bag]] Hresult]]]].
  set (result_bag :=
    operation (rows_bag T left_rows) (rows_bag T right_rows)).
  exists (Febag.elements BTupleT result_bag); split.
  + apply Heval.
    exists left_rows; exists right_rows; repeat split; try assumption.
    apply query_elements_same_rows_as_bag.
  + pose proof
      (Hoperation _ _ _ _ Hleft_bag Hright_bag) as Hoperation_eq.
    exact
      (bag_eq_trans (rows_bag_elements result_bag)
        (bag_eq_trans Hoperation_eq Hresult)).
Qed.

Lemma query_unary_reset_possible_bags :
  forall env parent input operation,
    (forall output,
      eval_query_expr env parent (SqlSuccess output) <->
      exists input_rows,
        eval_query_expr env input (SqlSuccess input_rows) /\
        query_same_rows_as_bag output
          (operation (rows_bag T input_rows))) ->
    (forall input_bag input_bag',
      bag_eq T input_bag input_bag' ->
      bag_eq T (operation input_bag) (operation input_bag')) ->
    rel_equiv
      (query_success_bags env parent)
      (lift_possible_bag_unary (unary_bag_graph operation)
        (query_success_bags env input)).
Proof.
intros env parent input operation Heval Hoperation output_bag.
unfold query_success_bags, alpha, lift_possible_bag_unary,
  unary_bag_graph.
split.
- intros [output [Houtput Houtput_bag]].
  apply Heval in Houtput.
  destruct Houtput as [input_rows [Hinput Hresult]].
  exists (rows_bag T input_rows); split.
  + exists input_rows; split; [exact Hinput | apply bag_eq_refl].
  + apply query_same_rows_as_bag_iff_bag_eq in Hresult.
    exact (bag_eq_trans (bag_eq_sym Hresult) Houtput_bag).
- intros [input_bag
    [[input_rows [Hinput Hinput_bag]] Hresult]].
  set (result_bag := operation (rows_bag T input_rows)).
  exists (Febag.elements BTupleT result_bag); split.
  + apply Heval; exists input_rows; split; [exact Hinput |].
    apply query_elements_same_rows_as_bag.
  + pose proof (Hoperation _ _ Hinput_bag) as Hoperation_eq.
    exact
      (bag_eq_trans (rows_bag_elements result_bag)
        (bag_eq_trans Hoperation_eq Hresult)).
Qed.

(** Relational analogue of [query_unary_reset_possible_bags].  This is the
    form needed by grouping: the abstract operation may retain several legal
    output bags and runtime behavior for one input bag. *)
Lemma query_unary_relational_reset_possible_bags :
  forall env parent input operation,
    (forall output,
      eval_query_expr env parent (SqlSuccess output) <->
      exists input_rows, exists output_bag,
        eval_query_expr env input (SqlSuccess input_rows) /\
        operation (rows_bag T input_rows) output_bag /\
        query_same_rows_as_bag output output_bag) ->
    unary_bag_relation_extensional operation ->
    rel_equiv
      (query_success_bags env parent)
      (lift_possible_bag_unary operation (query_success_bags env input)).
Proof.
intros env parent input operation Heval Hoperation output_bag.
unfold query_success_bags, alpha, lift_possible_bag_unary.
split.
- intros [output [Hparent Houtput]].
  apply Heval in Hparent.
  destruct Hparent as
    [input_rows [result_bag [Hinput [Hresult Hrows]]]].
  exists (rows_bag T input_rows); split.
  + exists input_rows; split; [exact Hinput | apply bag_eq_refl].
  + apply query_same_rows_as_bag_iff_bag_eq in Hrows.
    pose proof
      (Hoperation (rows_bag T input_rows) (rows_bag T input_rows)
        result_bag output_bag (bag_eq_refl T (rows_bag T input_rows))
        (bag_eq_trans (bag_eq_sym Hrows) Houtput)) as Htransport.
    now apply (proj1 Htransport).
- intros [input_bag
    [[input_rows [Hinput Hinput_bag]] Hresult]].
  pose proof
    (Hoperation (rows_bag T input_rows) input_bag output_bag output_bag
      Hinput_bag (bag_eq_refl T output_bag)) as Htransport.
  exists (Febag.elements BTupleT output_bag); split.
  + apply Heval.
    exists input_rows; exists output_bag; repeat split; try assumption.
    * now apply (proj2 Htransport).
    * apply query_elements_same_rows_as_bag.
  + apply rows_bag_elements.
Qed.

(** Binary relational reset counterpart.  It applies a genuinely relational
    bag operation pointwise to one possible bag from each child, retaining
    every legal output bag. *)
Lemma query_binary_relational_reset_possible_bags :
  forall env parent left right operation,
    (forall output,
      eval_query_expr env parent (SqlSuccess output) <->
      exists left_rows, exists right_rows, exists output_bag,
        eval_query_expr env left (SqlSuccess left_rows) /\
        eval_query_expr env right (SqlSuccess right_rows) /\
        operation (rows_bag T left_rows) (rows_bag T right_rows) output_bag /\
        query_same_rows_as_bag output output_bag) ->
    binary_bag_relation_extensional operation ->
    rel_equiv
      (query_success_bags env parent)
      (lift_possible_bag_binary operation
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env parent left right operation Heval Hoperation output_bag.
unfold query_success_bags, alpha, lift_possible_bag_binary.
split.
- intros [output [Hparent Houtput]].
  apply Heval in Hparent.
  destruct Hparent as
    [left_rows [right_rows [result_bag
      [Hleft [Hright [Hresult Hrows]]]]]].
  exists (rows_bag T left_rows); exists (rows_bag T right_rows).
  repeat split.
  + exists left_rows; split; [exact Hleft | apply bag_eq_refl].
  + exists right_rows; split; [exact Hright | apply bag_eq_refl].
  + apply query_same_rows_as_bag_iff_bag_eq in Hrows.
    pose proof
      (Hoperation
        (rows_bag T left_rows) (rows_bag T left_rows)
        (rows_bag T right_rows) (rows_bag T right_rows)
        result_bag output_bag
        (bag_eq_refl T (rows_bag T left_rows))
        (bag_eq_refl T (rows_bag T right_rows))
        (bag_eq_trans (bag_eq_sym Hrows) Houtput)) as Htransport.
    now apply (proj1 Htransport).
- intros [left_bag [right_bag
    [[left_rows [Hleft Hleft_bag]]
     [[right_rows [Hright Hright_bag]] Hresult]]]].
  pose proof
    (Hoperation
      (rows_bag T left_rows) left_bag
      (rows_bag T right_rows) right_bag
      output_bag output_bag Hleft_bag Hright_bag
      (bag_eq_refl T output_bag)) as Htransport.
  exists (Febag.elements BTupleT output_bag); split.
  + apply Heval.
    exists left_rows; exists right_rows; exists output_bag.
    repeat split; try assumption.
    * now apply (proj2 Htransport).
    * apply query_elements_same_rows_as_bag.
  + apply rows_bag_elements.
Qed.

Lemma eval_query_expr_set_success_iff :
  forall env operation left right output,
    eval_query_expr env (QExpr_Set operation left right) (SqlSuccess output) <->
    exists left_rows, exists right_rows,
      eval_query_expr env left (SqlSuccess left_rows) /\
      eval_query_expr env right (SqlSuccess right_rows) /\
      query_same_rows_as_bag output
        (query_set_bag_function operation left right
          (rows_bag T left_rows) (rows_bag T right_rows)).
Proof.
intros env operation left right output; split.
- intro Heval; inversion Heval; subst; eauto 8.
- intros [left_rows [right_rows [Hleft [Hright Houtput]]]].
  eapply EQuery_SetSuccess; eassumption.
Qed.

Lemma eval_query_expr_natural_join_success_iff :
  forall env left right output,
    eval_query_expr env (QExpr_NaturalJoin left right) (SqlSuccess output) <->
    exists left_rows, exists right_rows,
      eval_query_expr env left (SqlSuccess left_rows) /\
      eval_query_expr env right (SqlSuccess right_rows) /\
      query_same_rows_as_bag output
        (query_natural_join_bag
          value_is_null
          (rows_bag T left_rows) (rows_bag T right_rows)).
Proof.
intros env left right output; split.
- intro Heval; inversion Heval; subst; eauto 8.
- intros [left_rows [right_rows [Hleft [Hright Houtput]]]].
  eapply EQuery_NaturalJoinSuccess; eassumption.
Qed.

Lemma eval_query_expr_cross_join_success_iff :
  forall env left right output,
    eval_query_expr env (QExpr_CrossJoin left right) (SqlSuccess output) <->
    exists left_rows, exists right_rows,
      eval_query_expr env left (SqlSuccess left_rows) /\
      eval_query_expr env right (SqlSuccess right_rows) /\
      query_same_rows_as_bag output
        (query_cross_join_bag
          (rows_bag T left_rows) (rows_bag T right_rows)).
Proof.
intros env left right output; split.
- intro Heval; inversion Heval; subst; eauto 8.
- intros [left_rows [right_rows [Hleft [Hright Houtput]]]].
  eapply EQuery_CrossJoinSuccess; eassumption.
Qed.

Lemma eval_query_expr_join_success_iff :
  forall env kind predicate matched_select left_select right_select
         left right output,
    eval_query_expr env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlSuccess output) <->
    exists left_rows, exists right_rows, exists output_bag,
      eval_query_expr env left (SqlSuccess left_rows) /\
      eval_query_expr env right (SqlSuccess right_rows) /\
      query_join_bag_relation env kind predicate
        matched_select left_select right_select
        (rows_bag T left_rows) (rows_bag T right_rows) output_bag /\
      query_same_rows_as_bag output output_bag.
Proof.
intros env kind predicate matched_select left_select right_select
  left right output; split.
- intro Heval; inversion Heval; subst.
  exists left_rows; exists right_rows; exists output_bag.
  repeat split; assumption.
- intros [left_rows [right_rows [output_bag
    [Hleft [Hright [Hjoin Houtput]]]]]].
  eapply EQuery_JoinSuccess; eassumption.
Qed.

Lemma eval_query_expr_join_error_iff :
  forall env kind predicate matched_select left_select right_select
         left right error,
    eval_query_expr env
      (QExpr_Join kind predicate matched_select left_select right_select
        left right) (SqlError error) <->
    eval_query_expr env left (SqlError error) \/
    exists left_rows,
      eval_query_expr env left (SqlSuccess left_rows) /\
      (eval_query_expr env right (SqlError error) \/
       exists right_rows,
         eval_query_expr env right (SqlSuccess right_rows) /\
         eval_join_bag env kind predicate
           matched_select left_select right_select
           (rows_bag T left_rows) (rows_bag T right_rows)
           (SqlError error)).
Proof.
intros env kind predicate matched_select left_select right_select
  left right error; split.
- intro Heval; inversion Heval; subst; eauto 10.
- intros [Hleft_error |
    [left_rows [Hleft [Hright_error |
      [right_rows [Hright Hjoin]]]]]].
  + now apply EQuery_JoinLeftError.
  + eapply EQuery_JoinRightError; eassumption.
  + eapply EQuery_JoinBagError; eassumption.
Qed.

Lemma eval_query_expr_distinct_success_iff :
  forall env input output,
    eval_query_expr env (QExpr_Distinct input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      query_same_rows_as_bag output
        (query_distinct_bag (rows_bag T input_rows)).
Proof.
intros env input output; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [input_rows [Hinput Houtput]].
  eapply EQuery_DistinctSuccess; eassumption.
Qed.

Lemma eval_query_expr_group_success_iff :
  forall env select_list group_terms having input output,
    eval_query_expr env
      (QExpr_Group select_list group_terms having input) (SqlSuccess output) <->
    exists input_rows, exists output_bag,
      eval_query_expr env input (SqlSuccess input_rows) /\
      query_group_bag_relation env select_list group_terms having
        (rows_bag T input_rows) output_bag /\
      query_same_rows_as_bag output output_bag.
Proof.
intros env select_list group_terms having input output; split.
- intro Heval; inversion Heval; subst.
  exists input_rows; exists output_bag; repeat split; assumption.
- intros [input_rows [output_bag [Hinput [Hgroup Houtput]]]].
  eapply EQuery_GroupBagSuccess; eassumption.
Qed.

Lemma eval_query_expr_group_error_iff :
  forall env select_list group_terms having input error,
    eval_query_expr env
      (QExpr_Group select_list group_terms having input) (SqlError error) <->
    eval_query_expr env input (SqlError error) \/
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      eval_group_bag env select_list group_terms having
        (rows_bag T input_rows) (SqlError error).
Proof.
intros env select_list group_terms having input error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hchild | [input_rows [Hinput Hgroup]]].
  + now apply EQuery_GroupChildError.
  + eapply EQuery_GroupBagError; eassumption.
Qed.

Lemma eval_query_expr_grouping_sets_success_iff :
  forall env grouping_sets input output,
    eval_query_expr env (QExpr_GroupingSets grouping_sets input)
      (SqlSuccess output) <->
    exists input_rows, exists output_bag,
      eval_query_expr env input (SqlSuccess input_rows) /\
      query_grouping_sets_bag_relation env grouping_sets
        (rows_bag T input_rows) output_bag /\
      query_same_rows_as_bag output output_bag.
Proof.
intros env grouping_sets input output; split.
- intro Heval; inversion Heval; subst.
  exists input_rows; exists output_bag; repeat split; try assumption.
  exists output_bag; split; [assumption | apply bag_eq_refl].
- intros [input_rows [output_bag [Hinput [Hsets Houtput]]]].
  destruct Hsets as [evaluated_bag [Hevaluated Heq]].
  eapply EQuery_GroupingSetsSuccess with
    (input_rows := input_rows) (output_bag := evaluated_bag).
  + exact Hinput.
  + exact Hevaluated.
  + eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput.
    * now apply bag_eq_sym.
Qed.

Lemma eval_query_expr_rank_success_iff :
  forall env partition_keys order_keys rank_attribute rank_value input output,
    eval_query_expr env
      (QExpr_Rank partition_keys order_keys rank_attribute rank_value input)
      (SqlSuccess output) <->
    exists input_rows, exists output_bag,
      eval_query_expr env input (SqlSuccess input_rows) /\
      query_rank_bag_relation
        partition_keys order_keys rank_attribute rank_value
        (rows_bag T input_rows) output_bag /\
      query_same_rows_as_bag output output_bag.
Proof.
intros env partition_keys order_keys rank_attribute rank_value input output.
split.
- intro Heval; inversion Heval; subst.
  exists input_rows; exists (rows_bag T ranked_rows).
  repeat split; try assumption.
  unfold query_rank_bag_relation.
  exists ranked_rows; split; [assumption | apply bag_eq_refl].
- intros [input_rows [output_bag [Hinput [Hrank Houtput]]]].
  destruct Hrank as [ranked_rows [Hcompute Hbag]].
  eapply EQuery_RankSuccess with
    (input_rows := input_rows) (ranked_rows := ranked_rows).
  + exact Hinput.
  + exact Hcompute.
  + eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput.
    * now apply bag_eq_sym.
Qed.

Lemma eval_query_expr_window_success_iff :
  forall env partition_keys order_keys items input output,
    eval_query_expr env
      (QExpr_Window partition_keys order_keys items input)
      (SqlSuccess output) <->
    exists input_rows, exists output_bag,
      eval_query_expr env input (SqlSuccess input_rows) /\
      query_window_bag_relation env partition_keys order_keys items
        (rows_bag T input_rows) output_bag /\
      query_same_rows_as_bag output output_bag.
Proof.
intros env partition_keys order_keys items input output; split.
- intro Heval; inversion Heval; subst.
  exists input_rows; exists (rows_bag T window_rows).
  split; [exact H4 |].
  split.
  + unfold query_window_bag_relation.
    exists ordered_rows, window_rows; split; [exact H5 |].
    split; [exact H6 | apply bag_eq_refl].
  + exact H7.
- intros [input_rows [output_bag [Hinput [Hwindow Houtput]]]].
  destruct Hwindow as
    [ordered_rows [window_rows [Horder [Hcompute Hbag]]]].
  eapply EQuery_WindowSuccess with
    (input_rows := input_rows) (ordered_rows := ordered_rows)
    (window_rows := window_rows).
  + exact Hinput.
  + exact Horder.
  + exact Hcompute.
  + eapply query_same_rows_as_bag_bag_transport.
    * exact Houtput.
    * now apply bag_eq_sym.
Qed.

Lemma eval_query_expr_grouping_sets_error_iff :
  forall env grouping_sets input error,
    eval_query_expr env (QExpr_GroupingSets grouping_sets input)
      (SqlError error) <->
    eval_query_expr env input (SqlError error) \/
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      eval_grouping_sets_bag env grouping_sets
        (rows_bag T input_rows) (SqlError error).
Proof.
intros env grouping_sets input error; split.
- intro Heval; inversion Heval; subst; eauto.
- intros [Hchild | [input_rows [Hinput Hsets]]].
  + now apply EQuery_GroupingSetsChildError.
  + eapply EQuery_GroupingSetsBagError; eassumption.
Qed.

Theorem query_set_success_bags :
  forall env operation left right,
    rel_equiv
      (query_success_bags env (QExpr_Set operation left right))
      (lift_possible_bag_binary
        (query_set_bag_relation operation left right)
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env operation left right.
apply query_binary_reset_possible_bags.
- apply eval_query_expr_set_success_iff.
- intros; now apply query_set_bag_function_congr.
Qed.

Theorem query_natural_join_success_bags :
  forall env left right,
    rel_equiv
      (query_success_bags env (QExpr_NaturalJoin left right))
      (lift_possible_bag_binary query_natural_join_bag_relation
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env left right.
apply query_binary_reset_possible_bags.
- apply eval_query_expr_natural_join_success_iff.
- intros; now apply query_natural_join_bag_congr.
Qed.

Theorem query_cross_join_success_bags :
  forall env left right,
    rel_equiv
      (query_success_bags env (QExpr_CrossJoin left right))
      (lift_possible_bag_binary query_cross_join_bag_relation
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env left right.
apply query_binary_reset_possible_bags.
- apply eval_query_expr_cross_join_success_iff.
- intros; now apply query_cross_join_bag_congr.
Qed.

Theorem query_join_success_bags :
  forall env kind predicate matched_select left_select right_select left right,
    rel_equiv
      (query_success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (lift_possible_bag_binary
        (query_join_bag_relation env kind predicate
          matched_select left_select right_select)
        (query_success_bags env left) (query_success_bags env right)).
Proof.
intros env kind predicate matched_select left_select right_select left right.
apply query_binary_relational_reset_possible_bags.
- apply eval_query_expr_join_success_iff.
- apply query_join_bag_relation_extensional.
Qed.

Theorem query_join_success_bags_congr :
  forall env kind predicate matched_select left_select right_select
         left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (query_success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left right))
      (query_success_bags env
        (QExpr_Join kind predicate matched_select left_select right_select
          left' right')).
Proof.
intros env kind predicate matched_select left_select right_select
  left left' right right' Hleft Hright output_bag.
pose proof
  (query_join_success_bags env kind predicate
    matched_select left_select right_select left right output_bag) as Hsource.
pose proof
  (query_join_success_bags env kind predicate
    matched_select left_select right_select left' right' output_bag) as Htarget.
pose proof
  (lift_possible_bag_binary_congr
    (query_join_bag_relation env kind predicate
      matched_select left_select right_select)
    Hleft Hright output_bag) as Hlift.
tauto.
Qed.

Theorem query_distinct_success_bags :
  forall env input,
    rel_equiv
      (query_success_bags env (QExpr_Distinct input))
      (lift_possible_bag_unary query_distinct_bag_relation
        (query_success_bags env input)).
Proof.
intros env input.
apply query_unary_reset_possible_bags.
- apply eval_query_expr_distinct_success_iff.
- intros; now apply query_distinct_bag_congr.
Qed.

Theorem query_group_success_bags :
  forall env select_list group_terms having input,
    rel_equiv
      (query_success_bags env
        (QExpr_Group select_list group_terms having input))
      (lift_possible_bag_unary
        (query_group_bag_relation env select_list group_terms having)
        (query_success_bags env input)).
Proof.
intros env select_list group_terms having input.
apply query_unary_relational_reset_possible_bags.
- apply eval_query_expr_group_success_iff.
- apply query_group_bag_relation_extensional.
Qed.

Theorem query_grouping_sets_success_bags :
  forall env grouping_sets input,
    rel_equiv
      (query_success_bags env (QExpr_GroupingSets grouping_sets input))
      (lift_possible_bag_unary
        (query_grouping_sets_bag_relation env grouping_sets)
        (query_success_bags env input)).
Proof.
intros env grouping_sets input.
apply query_unary_relational_reset_possible_bags.
- apply eval_query_expr_grouping_sets_success_iff.
- apply query_grouping_sets_bag_relation_extensional.
Qed.

Theorem query_rank_success_bags :
  forall env partition_keys order_keys rank_attribute rank_value input,
    rel_equiv
      (query_success_bags env
        (QExpr_Rank
          partition_keys order_keys rank_attribute rank_value input))
      (lift_possible_bag_unary
        (query_rank_bag_relation
          partition_keys order_keys rank_attribute rank_value)
        (query_success_bags env input)).
Proof.
intros env partition_keys order_keys rank_attribute rank_value input.
apply query_unary_relational_reset_possible_bags.
- apply eval_query_expr_rank_success_iff.
- apply query_rank_bag_relation_extensional.
Qed.

Theorem query_window_success_bags :
  forall env partition_keys order_keys items input,
    rel_equiv
      (query_success_bags env
        (QExpr_Window partition_keys order_keys items input))
      (lift_possible_bag_unary
        (query_window_bag_relation env partition_keys order_keys items)
        (query_success_bags env input)).
Proof.
intros env partition_keys order_keys items input.
apply query_unary_relational_reset_possible_bags.
- apply eval_query_expr_window_success_iff.
- apply query_window_bag_relation_extensional.
Qed.

Lemma query_set_lift_inputs_congr :
  forall env operation left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (lift_possible_bag_binary
        (query_set_bag_relation operation left right)
        (query_success_bags env left) (query_success_bags env right))
      (lift_possible_bag_binary
        (query_set_bag_relation operation left right)
        (query_success_bags env left') (query_success_bags env right')).
Proof.
intros; now apply lift_possible_bag_binary_congr.
Qed.

(** Packaged congruence for the actual [QExpr_Set] abstractions.  Unlike the
    lower-level input congruence above, this theorem also transports the
    syntax-indexed set-operation relation, whose schema check changes when the
    child syntax changes. *)
Theorem query_set_success_bags_congr :
  forall env operation left left' right right',
    query_expr_sort left =S= query_expr_sort left' ->
    query_expr_sort right =S= query_expr_sort right' ->
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (query_success_bags env (QExpr_Set operation left right))
      (query_success_bags env (QExpr_Set operation left' right')).
Proof.
intros env operation left left' right right'
  Hleft_sort Hright_sort Hleft Hright output_bag.
pose proof (query_set_success_bags env operation left right output_bag)
  as Hsource.
pose proof (query_set_success_bags env operation left' right' output_bag)
  as Htarget.
pose proof
  (query_set_lift_inputs_congr (env := env) operation
    (left := left) (left' := left') (right := right) (right' := right')
    Hleft Hright output_bag) as Hinputs.
pose proof
  (lift_possible_bag_binary_operation_congr
    (left_operation := query_set_bag_relation operation left right)
    (right_operation := query_set_bag_relation operation left' right')
    (query_success_bags env left') (query_success_bags env right')
    (query_set_bag_relation_sort_congr operation left left' right right'
      Hleft_sort Hright_sort) output_bag) as Hoperation.
split; intro Hresult.
- apply (proj2 Htarget), (proj1 Hoperation), (proj1 Hinputs),
    (proj1 Hsource), Hresult.
- apply (proj2 Hsource), (proj2 Hinputs), (proj2 Hoperation),
    (proj1 Htarget), Hresult.
Qed.

Lemma query_distinct_success_bags_congr :
  forall env left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (lift_possible_bag_unary query_distinct_bag_relation
        (query_success_bags env left))
      (lift_possible_bag_unary query_distinct_bag_relation
        (query_success_bags env right)).
Proof.
intros; now apply lift_possible_bag_unary_congr.
Qed.

Lemma query_rank_lift_success_bags_congr :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (lift_possible_bag_unary
        (query_rank_bag_relation
          partition_keys order_keys rank_attribute rank_value)
        (query_success_bags env left))
      (lift_possible_bag_unary
        (query_rank_bag_relation
          partition_keys order_keys rank_attribute rank_value)
        (query_success_bags env right)).
Proof.
intros; now apply lift_possible_bag_unary_congr.
Qed.

(** A native Rank reset consumes its child only through the possible-bag
    abstraction.  Thus any bag-theory proof for an order-insensitive child
    can be reused below Rank without identifying ordered child lists. *)
Theorem query_rank_success_bags_congr :
  forall env partition_keys order_keys rank_attribute rank_value left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (query_success_bags env
        (QExpr_Rank
          partition_keys order_keys rank_attribute rank_value left))
      (query_success_bags env
        (QExpr_Rank
          partition_keys order_keys rank_attribute rank_value right)).
Proof.
intros env partition_keys order_keys rank_attribute rank_value
  left right Hinputs output_bag.
pose proof
  (query_rank_success_bags env partition_keys order_keys
    rank_attribute rank_value left output_bag) as Hleft.
pose proof
  (query_rank_success_bags env partition_keys order_keys
    rank_attribute rank_value right output_bag) as Hright.
pose proof
  (query_rank_lift_success_bags_congr
    (env := env) partition_keys order_keys rank_attribute rank_value
    Hinputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

(** A declarative cumulative window is also a bag reset.  Its legal peer
    orderings and correlated item results depend only on the child bag, so
    bag-theory rewrites remain reusable below it. *)
Theorem query_window_success_bags_congr :
  forall env partition_keys order_keys items left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (query_success_bags env
        (QExpr_Window partition_keys order_keys items left))
      (query_success_bags env
        (QExpr_Window partition_keys order_keys items right)).
Proof.
intros env partition_keys order_keys items left right Hinputs output_bag.
pose proof
  (query_window_success_bags env partition_keys order_keys items
    left output_bag) as Hleft.
pose proof
  (query_window_success_bags env partition_keys order_keys items
    right output_bag) as Hright.
pose proof
  (lift_possible_bag_unary_congr
    (query_window_bag_relation env partition_keys order_keys items)
    Hinputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

(** Ordinary grouping consumes its child only through the possible-bag
    abstraction.  Hence replacing the child by one with the same possible
    bags preserves the actual grouped possible-bag relation. *)
Theorem query_group_success_bags_congr :
  forall env select_list group_terms having left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (query_success_bags env
        (QExpr_Group select_list group_terms having left))
      (query_success_bags env
        (QExpr_Group select_list group_terms having right)).
Proof.
intros env select_list group_terms having left right Hinputs output_bag.
pose proof
  (query_group_success_bags env select_list group_terms having left output_bag)
  as Hleft.
pose proof
  (query_group_success_bags env select_list group_terms having right output_bag)
  as Hright.
pose proof
  (lift_possible_bag_unary_congr
    (query_group_bag_relation env select_list group_terms having)
    Hinputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

Lemma query_natural_join_success_bags_congr :
  forall env left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (lift_possible_bag_binary query_natural_join_bag_relation
        (query_success_bags env left) (query_success_bags env right))
      (lift_possible_bag_binary query_natural_join_bag_relation
        (query_success_bags env left') (query_success_bags env right')).
Proof.
intros; now apply lift_possible_bag_binary_congr.
Qed.

Lemma query_cross_join_success_bags_congr :
  forall env left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (lift_possible_bag_binary query_cross_join_bag_relation
        (query_success_bags env left) (query_success_bags env right))
      (lift_possible_bag_binary query_cross_join_bag_relation
        (query_success_bags env left') (query_success_bags env right')).
Proof.
intros; now apply lift_possible_bag_binary_congr.
Qed.

(** Packaged congruences for the actual reset-point queries.  These combine
    each exact success-bag characterization with the pointwise lifted bag
    congruence, so clients need not unfold the intermediate abstract term. *)
Theorem query_distinct_actual_success_bags_congr :
  forall env left right,
    rel_equiv (query_success_bags env left)
              (query_success_bags env right) ->
    rel_equiv
      (query_success_bags env (QExpr_Distinct left))
      (query_success_bags env (QExpr_Distinct right)).
Proof.
intros env left right Hinputs output_bag.
pose proof (query_distinct_success_bags env left output_bag) as Hleft.
pose proof (query_distinct_success_bags env right output_bag) as Hright.
pose proof
  (query_distinct_success_bags_congr (env := env) Hinputs output_bag)
  as Hlift.
split; intro Hresult.
- apply (proj2 Hright), (proj1 Hlift), (proj1 Hleft), Hresult.
- apply (proj2 Hleft), (proj2 Hlift), (proj1 Hright), Hresult.
Qed.

Theorem query_natural_join_actual_success_bags_congr :
  forall env left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (query_success_bags env (QExpr_NaturalJoin left right))
      (query_success_bags env (QExpr_NaturalJoin left' right')).
Proof.
intros env left left' right right' Hleft_inputs Hright_inputs output_bag.
pose proof
  (query_natural_join_success_bags env left right output_bag) as Hsource.
pose proof
  (query_natural_join_success_bags env left' right' output_bag) as Htarget.
pose proof
  (query_natural_join_success_bags_congr (env := env)
    Hleft_inputs Hright_inputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Htarget), (proj1 Hlift), (proj1 Hsource), Hresult.
- apply (proj2 Hsource), (proj2 Hlift), (proj1 Htarget), Hresult.
Qed.

Theorem query_cross_join_actual_success_bags_congr :
  forall env left left' right right',
    rel_equiv (query_success_bags env left)
              (query_success_bags env left') ->
    rel_equiv (query_success_bags env right)
              (query_success_bags env right') ->
    rel_equiv
      (query_success_bags env (QExpr_CrossJoin left right))
      (query_success_bags env (QExpr_CrossJoin left' right')).
Proof.
intros env left left' right right' Hleft_inputs Hright_inputs output_bag.
pose proof
  (query_cross_join_success_bags env left right output_bag) as Hsource.
pose proof
  (query_cross_join_success_bags env left' right' output_bag) as Htarget.
pose proof
  (query_cross_join_success_bags_congr (env := env)
    Hleft_inputs Hright_inputs output_bag) as Hlift.
split; intro Hresult.
- apply (proj2 Htarget), (proj1 Hlift), (proj1 Hsource), Hresult.
- apply (proj2 Hsource), (proj2 Hlift), (proj1 Htarget), Hresult.
Qed.

(** Exact inversion principles for the order-sensitive constructors. *)
Lemma eval_query_expr_order_by_success_iff :
  forall env keys input output,
    eval_query_expr env (QExpr_OrderBy keys input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      order_by_rows value_is_null keys input_rows output.
Proof.
intros env keys input output; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [input_rows [Hinput Horder]].
  now apply EQuery_OrderBySuccess with input_rows.
Qed.

Theorem eval_query_expr_order_by_has_success :
  forall env keys input input_rows,
    eval_query_expr env input (SqlSuccess input_rows) ->
    exists output,
      eval_query_expr env (QExpr_OrderBy keys input) (SqlSuccess output).
Proof.
intros env keys input input_rows Hinput.
destruct (@order_by_rows_has_observation T value_is_null keys input_rows)
  as [output Horder].
exists output; now apply EQuery_OrderBySuccess with input_rows.
Qed.

Lemma eval_query_expr_order_by_error_iff :
  forall env keys input error,
    eval_query_expr env (QExpr_OrderBy keys input) (SqlError error) <->
    eval_query_expr env input (SqlError error).
Proof.
intros env keys input error; split; intro Heval.
- inversion Heval; subst; assumption.
- now apply EQuery_OrderByChildError.
Qed.

Lemma eval_query_expr_offset_success_iff :
  forall env offset input output,
    eval_query_expr env (QExpr_Offset offset input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      output = skipn offset input_rows.
Proof.
intros env offset input output; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [input_rows [Hinput ->]].
  now apply EQuery_OffsetSuccess.
Qed.

Lemma eval_query_expr_offset_error_iff :
  forall env offset input error,
    eval_query_expr env (QExpr_Offset offset input) (SqlError error) <->
    eval_query_expr env input (SqlError error).
Proof.
intros env offset input error; split; intro Heval.
- inversion Heval; subst; assumption.
- now apply EQuery_OffsetChildError.
Qed.

Lemma eval_query_expr_fetch_success_iff :
  forall env count input output,
    eval_query_expr env (QExpr_Fetch count input) (SqlSuccess output) <->
    exists input_rows,
      eval_query_expr env input (SqlSuccess input_rows) /\
      output = firstn count input_rows.
Proof.
intros env count input output; split; intro Heval.
- inversion Heval; subst; eauto.
- destruct Heval as [input_rows [Hinput ->]].
  now apply EQuery_FetchSuccess.
Qed.

Lemma eval_query_expr_fetch_error_iff :
  forall env count input error,
    eval_query_expr env (QExpr_Fetch count input) (SqlError error) <->
    eval_query_expr env input (SqlError error).
Proof.
intros env count input error; split; intro Heval.
- inversion Heval; subst; assumption.
- now apply EQuery_FetchChildError.
Qed.

End Sec.
