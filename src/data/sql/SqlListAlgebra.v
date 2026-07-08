(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                    List observations over bag-valued SQL algebra                *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import Bool List Arith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet
        FiniteSet FiniteBag FiniteCollection FlatData Env Bool3 Sql SqlAlgebra SqlOrder.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.

Import Tuple.

Local Definition attribute := attribute T.
Local Definition tuple := tuple T.
Local Definition setA := Fset.set (Tuple.A T).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.

(**
  SQL's bag algebra intentionally forgets output order.  This module embeds
  that bag semantics into a relational list semantics and defines ORDER
  BY/OFFSET/FETCH at the list layer.

  The relation is intentionally nondeterministic.  A base bag-valued query may
  be observed through any list with the same multiplicities.  ORDER BY then
  restricts the legal observations to lists satisfying the requested ordering.
  Ties remain nondeterministic unless the sort keys determine a total order.

  As in the base SQL algebra, evaluation is total over syntax.  Proofs and
  lowerings that rely on this layer should carry [well_formed_list_query]
  together with the usual FormalSQL well-formedness assumptions.
 *)

Inductive list_query : Type :=
  | L_Bag : @query T relname -> list_query
  | L_OrderBy : list (sort_key T) -> list_query -> list_query
  | L_Offset : nat -> list_query -> list_query
  | L_Fetch : nat -> list_query -> list_query.

Fixpoint list_query_sort (q : list_query) : setA :=
  match q with
  | L_Bag q => @sort T relname basesort q
  | L_OrderBy _ q
  | L_Offset _ q
  | L_Fetch _ q => list_query_sort q
  end.

Definition sort_key_in_scope (scope : setA) (key : sort_key T) : Prop :=
  sort_key_attribute key inS scope.

Definition sort_keys_in_scope (scope : setA) (keys : list (sort_key T)) : Prop :=
  forall key, In key keys -> sort_key_in_scope scope key.

Fixpoint well_formed_list_query (q : list_query) : Prop :=
  match q with
  | L_Bag _ => True
  | L_OrderBy keys q =>
      well_formed_list_query q /\ sort_keys_in_scope (list_query_sort q) keys
  | L_Offset _ q
  | L_Fetch _ q => well_formed_list_query q
  end.

Definition bag_of_rows (rows : list tuple) : bagT :=
  Febag.mk_bag BTupleT rows.

Definition same_rows_as_bag (rows : list tuple) (bag : bagT) : Prop :=
  bag_of_rows rows =BE= bag.

Definition order_by_rows
    (value_is_null : Tuple.value T -> bool)
    (keys : list (sort_key T))
    (input output : list tuple) : Prop :=
  same_rows_as_bag output (bag_of_rows input) /\
  ordered_rows value_is_null keys output.

Fixpoint eval_list_query
    (value_is_null : Tuple.value T -> bool)
    (env : Env.env T)
    (q : list_query)
    (rows : list tuple) : Prop :=
  match q with
  | L_Bag q =>
      same_rows_as_bag rows
        (@eval_query T relname basesort instance unknown contains_nulls env q)
  | L_OrderBy keys q =>
      exists input,
        eval_list_query value_is_null env q input /\
        order_by_rows value_is_null keys input rows
  | L_Offset n q =>
      exists input,
        eval_list_query value_is_null env q input /\
        rows = skipn n input
  | L_Fetch n q =>
      exists input,
        eval_list_query value_is_null env q input /\
        rows = firstn n input
  end.

Definition list_query_equiv
    (value_is_null : Tuple.value T -> bool)
    (env : Env.env T)
    (q1 q2 : list_query) : Prop :=
  forall rows,
    eval_list_query value_is_null env q1 rows <->
    eval_list_query value_is_null env q2 rows.

Lemma order_by_rows_preserves_bag :
  forall value_is_null keys input output,
    order_by_rows value_is_null keys input output ->
    bag_of_rows output =BE= bag_of_rows input.
Proof.
intros value_is_null keys input output H; exact (proj1 H).
Qed.

Lemma eval_order_by_preserves_bag :
  forall value_is_null env keys q output,
    eval_list_query value_is_null env (L_OrderBy keys q) output ->
    exists input,
      eval_list_query value_is_null env q input /\
      bag_of_rows output =BE= bag_of_rows input.
Proof.
intros value_is_null env keys q output [input [Hq Horder]].
exists input; split; [assumption | now apply order_by_rows_preserves_bag with value_is_null keys].
Qed.

Lemma order_by_empty_is_bag_preserving :
  forall value_is_null env q output,
    eval_list_query value_is_null env (L_OrderBy nil q) output ->
    exists input,
      eval_list_query value_is_null env q input /\
      bag_of_rows output =BE= bag_of_rows input.
Proof.
intros; now apply eval_order_by_preserves_bag in H.
Qed.

End Sec.
