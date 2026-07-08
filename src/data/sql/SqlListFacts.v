(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                  Facts connecting bag and list SQL semantics                    *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteSet FiniteBag FiniteCollection FlatData Env Bool3
        SqlAlgebra SqlListAlgebra.

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.

Import Tuple.

Local Definition tuple := tuple T.
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.

Definition bag_query_equiv
    (env : Env.env T)
    (q1 q2 : @query T relname) : Prop :=
  @eval_query T relname basesort instance unknown contains_nulls env q1 =BE=
  @eval_query T relname basesort instance unknown contains_nulls env q2.

Lemma list_equiv_l_bag_of_bag_query_equiv :
  forall value_is_null env q1 q2,
    bag_query_equiv env q1 q2 ->
    @list_query_equiv T relname basesort instance unknown contains_nulls
      value_is_null env (L_Bag q1) (L_Bag q2).
Proof.
intros value_is_null env q1 q2 Hbag rows; simpl.
unfold bag_query_equiv, same_rows_as_bag in Hbag |- *.
split; intro Hrows; rewrite Febag.nb_occ_equal in *; intro t.
- rewrite Hrows; now rewrite Hbag.
- rewrite Hrows; symmetry; now rewrite Hbag.
Qed.

Lemma bag_query_equiv_of_list_equiv_l_bag :
  forall value_is_null env q1 q2,
    @list_query_equiv T relname basesort instance unknown contains_nulls
      value_is_null env (L_Bag q1) (L_Bag q2) ->
    bag_query_equiv env q1 q2.
Proof.
intros value_is_null env q1 q2 Hlist.
unfold bag_query_equiv.
rewrite Febag.nb_occ_equal; intro t.
specialize
  (Hlist
     (Febag.elements BTupleT
        (@eval_query T relname basesort instance unknown contains_nulls env q1)))
  as [Hforward _].
assert (Hsource :
  same_rows_as_bag T
    (Febag.elements BTupleT
      (@eval_query T relname basesort instance unknown contains_nulls env q1))
    (@eval_query T relname basesort instance unknown contains_nulls env q1)).
{
  unfold same_rows_as_bag, bag_of_rows.
  apply Febag.elements_mk_bag.
}
specialize (Hforward Hsource).
simpl in Hforward.
unfold same_rows_as_bag, bag_of_rows in Hforward.
rewrite Febag.nb_occ_equal in Hforward.
rewrite <- Hforward.
rewrite Febag.nb_occ_mk_bag.
apply Febag.nb_occ_elements.
Qed.

Theorem list_equiv_l_bag_iff_bag_query_equiv :
  forall value_is_null env q1 q2,
    @list_query_equiv T relname basesort instance unknown contains_nulls
      value_is_null env (L_Bag q1) (L_Bag q2) <->
    bag_query_equiv env q1 q2.
Proof.
intros value_is_null env q1 q2; split.
- apply bag_query_equiv_of_list_equiv_l_bag.
- apply list_equiv_l_bag_of_bag_query_equiv.
Qed.

End Sec.
