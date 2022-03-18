(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                       LMF, CNRS & Université Paris-Saclay                       *)
(**                                                                                 *)
(**                        Copyright 2016-2022 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import Bool3 FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula Sql.

Import Tuple.
Require Import Values TuplesImpl GenericInstance.

Definition value := NullValues.value.
Definition Value_bool := NullValues.Value_bool.
Definition Value_Z := NullValues.Value_Z.
Definition Value_string := NullValues.Value_string.

Definition predicate := Values.predicate.
Definition Predicate := Values.Predicate.

Definition symbol := symbol value.
Definition Symbol := Symbol value.

Register symbol as datacert.syntax.symbol.
Register Symbol as datacert.syntax.Symbol.

Definition aggregate := Values.aggregate.
Definition Aggregate := Values.Aggregate.

Register aggregate as datacert.syntax.aggregate.
Register Aggregate as datacert.syntax.Aggregate.

Definition db_state := db_state_ TNull.
Definition init_db := init_db_ TNull.
Definition create_table := create_table_ TNull.
Definition insert_tuples_into := insert_tuples_into_ TNull.

Register db_state as datacert.syntax.db_state.
Register create_table as datacert.syntax.create_table.

Fixpoint mk_att att atts vals :=
  match atts, vals with
  | a::atts, v::vals => match attribute_compare a att with
                        | Eq => v
                        | _ => mk_att att atts vals
                        end
  | _, _ => match att with
                | Attr_string _ => Value_string None
                | Attr_Z _ => Value_Z None
                | Attr_bool _ => Value_bool None
                end
  end.

Definition mk_tuple_lists atts vals :=
  mk_tuple TNull (Fset.mk_set _ atts) (fun att => mk_att att atts vals).

Definition mk_insert db rel atts valss :=
  insert_tuples_into db (List.map (mk_tuple_lists atts) valss) rel.

Register mk_insert as datacert.syntax.mk_insert.

(** Again, for the constructs of the SQL framework *)
Definition _Select_Star := (@Select_Star TNull).

Register _Select_Star as datacert.syntax._Select_Star.

Definition __Select_List l := (@Select_List TNull (@_Select_List TNull l)).

Register __Select_List as datacert.syntax.__Select_List.

Definition _Select_As := (@Select_As TNull).

Register _Select_As as datacert.syntax._Select_As.

Definition _Att_Ren_Star := (@Att_Ren_Star TNull).

Register _Att_Ren_Star as datacert.syntax._Att_Ren_Star.

Definition _Att_Ren_List := (@Att_Ren_List TNull).

Definition _Att_As := (@Att_As TNull).

Register _Att_As as datacert.syntax._Att_As.

Definition _Sql_Table := (@Sql_Table TNull relname).

Register _Sql_Table as datacert.syntax._Sql_Table.

Definition _Sql_Set := (@Sql_Set TNull relname).

Register _Sql_Set as datacert.syntax._Sql_Set.

Definition _Sql_Select := (@Sql_Select TNull relname).

Register _Sql_Select as datacert.syntax._Sql_Select.

Definition _select := (@select TNull).

Register _select as datacert.syntax._select.

Definition _From_Item := (@From_Item TNull relname).

Register _From_Item as datacert.syntax._From_Item.

Definition _sql_from_item := (@sql_from_item TNull relname).

Register _sql_from_item as datacert.syntax._sql_from_item.

Definition _Group_Fine := (@Group_Fine TNull).

Register _Group_Fine as datacert.syntax._Group_Fine.

Definition __Sql_Dot a := (F_Dot TNull a).

Register __Sql_Dot as datacert.syntax.__Sql_Dot.

Definition _Sql_Dot a := (@A_Expr TNull (__Sql_Dot a)).

Definition _A_Expr := (@A_Expr TNull).

Register _A_Expr as datacert.syntax._A_Expr.

Definition _Group_By l := (@Group_By TNull (List.map _A_Expr l)).

Register _Group_By as datacert.syntax._Group_By.

Definition _A_fun := (@A_fun TNull).

Register _A_fun as datacert.syntax._A_fun.

Definition _A_agg := (@A_agg TNull).

Register _A_agg as datacert.syntax._A_agg.

Definition _F_Constant := (@F_Constant TNull).

Register _F_Constant as datacert.syntax._F_Constant.

Definition _CstZ z := _F_Constant (Value_Z z).

Definition CstZ z := (_A_Expr (_CstZ z)).

Definition _F_Expr := (@F_Expr TNull).

Register _F_Expr as datacert.syntax._F_Expr.

Definition _sql_query := (sql_query TNull relname). 

Definition _Sql_True := (@Sql_True TNull (sql_query TNull relname)).

Register _Sql_True as datacert.syntax._Sql_True.

Definition _Sql_Not := (@Sql_Not TNull (sql_query TNull relname)). 

Register _Sql_Not as datacert.syntax._Sql_Not.


Definition _Sql_Conj := (@Sql_Conj TNull (sql_query TNull relname)).

Register _Sql_Conj as datacert.syntax._Sql_Conj.

Definition _Sql_Pred := (@Sql_Pred TNull (sql_query TNull relname)).

Register _Sql_Pred as datacert.syntax._Sql_Pred.

Definition _Sql_Quant := (@Sql_Quant TNull (sql_query TNull relname)).

Register _Sql_Quant as datacert.syntax._Sql_Quant.

Definition _Sql_Exists := (@Sql_Exists TNull (sql_query TNull relname)).

Register _Sql_Exists as datacert.syntax._Sql_Exists.

Definition _Sql_In := (@Sql_In TNull (sql_query TNull relname)).

Register _Sql_In as datacert.syntax._Sql_In.

Definition _aggterm := (aggterm TNull).

Register _aggterm as datacert.syntax._aggterm.

Definition _funterm := (funterm TNull).

Register _funterm as datacert.syntax._funterm.

Definition _Union := Union.
Definition _Inter := Inter.
Definition _Diff := Diff.

Register _Union as datacert.syntax._Union.
Register _Inter as datacert.syntax._Inter.
Register _Diff as datacert.syntax._Diff.

Definition SortedTuplesT := TNull.

Register SortedTuplesT as datacert.syntax.SortedTuplesT.

Definition contains_nulls (t : tuple TNull) :=
 existsb (fun a => match dot TNull t a with
                   | NullValues.Value_string None
                   | NullValues.Value_Z None
                   | NullValues.Value_bool None => true
                   | NullValues.Value_string (Some _)
                   | NullValues.Value_Z (Some _)
                   | NullValues.Value_bool (Some _) => false
                   end) ({{{labels TNull t}}}).

Lemma contains_nulls_eq :
  forall t1 t2, t1 =t= t2 -> contains_nulls t1 = contains_nulls t2.
Proof.
intros t1 t2 Ht.
unfold contains_nulls.
rewrite tuple_eq in Ht.
rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Ht)).
apply existsb_eq.
intros a Ha; rewrite <- (proj2 Ht); [apply refl_equal | ].
apply Fset.in_elements_mem; assumption.
Qed.

(* Evaluation of SQL-COQ queries *)

Definition eval_sql_query_in_state (db : db_state) q :=
  show_bag_tuples _ (@eval_sql_query 
     TNull relname (_basesort _ db) (_instance _ db) unknown3 contains_nulls nil q).
