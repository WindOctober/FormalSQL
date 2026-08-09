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

Require Import NArith ZArith String List.
Require Import ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection 
        FlatData Values TuplesImpl.

(** * Definition of relation's names, and finite sets of relation's names *)

Inductive relname : Set := Rel : string -> relname.

Register relname as datacert.relname.type.
Register Rel as datacert.relname.Rel.

Definition ORN : Oset.Rcd relname.
split with (fun r1 r2 => match r1, r2 with Rel s1, Rel s2 => Oset.compare Ostring s1 s2 end).
- intros [s1] [s2].
  generalize (Oset.eq_bool_ok Ostring s1 s2).
  case (Oset.compare Ostring s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply Oset.compare_lt_trans.
- intros [s1] [s2]; apply Oset.compare_lt_gt.
Defined.

(** * Definition of attributes, and finite sets of attributes *)

(** There are several constructors for attributes, one for each type. This allows to have an infinite number of attributes, usefull for renaming for instance, but also to a generic function [type_of_attribute]. *)
Inductive attribute : Set :=
  | Attr_string : string -> string_typmod -> attribute
  | Attr_Z : string -> attribute
  | Attr_int32 : string -> attribute
  | Attr_int64 : string -> attribute
  | Attr_bool : string -> attribute
  | Attr_float : string -> attribute
  | Attr_double : string -> attribute
  | Attr_numeric : string -> attribute
  | Attr_decimal : string -> Z -> Z -> attribute
  | Attr_date : string -> attribute
  | Attr_time : string -> attribute
  | Attr_timestamp : string -> Z -> attribute
  | Attr_timestamptz : string -> Z -> attribute.

Register attribute as datacert.attribute.type.
Register Attr_string as datacert.attribute.Attr_string.
Register Attr_Z as datacert.attribute.Attr_Z.
Register Attr_int32 as datacert.attribute.Attr_int32.
Register Attr_int64 as datacert.attribute.Attr_int64.
Register Attr_bool as datacert.attribute.Attr_bool.
Register Attr_float as datacert.attribute.Attr_float.
Register Attr_double as datacert.attribute.Attr_double.
Register Attr_numeric as datacert.attribute.Attr_numeric.
Register Attr_decimal as datacert.attribute.Attr_decimal.
Register Attr_date as datacert.attribute.Attr_date.
Register Attr_time as datacert.attribute.Attr_time.
Register Attr_timestamp as datacert.attribute.Attr_timestamp.
Register Attr_timestamptz as datacert.attribute.Attr_timestamptz.

Definition type_of_attribute (a : attribute) :=
  match a with
    | Attr_string _ _ => type_string
    | Attr_Z _ => type_Z
    | Attr_int32 _ => type_int32
    | Attr_int64 _ => type_int64
    | Attr_bool _  => type_bool
    | Attr_float _ => type_float
    | Attr_double _ => type_double
    | Attr_numeric _ | Attr_decimal _ _ _ => type_numeric
    | Attr_date _ => type_date
    | Attr_time _ => type_time
    | Attr_timestamp _ _ => type_timestamp
    | Attr_timestamptz _ _ => type_timestamptz
  end.

Open Scope N_scope.

Definition N_of_attribute a := 
  match a with   
    | Attr_string _ _ => 0
    | Attr_Z _ => 1
    | Attr_int32 _ => 2
    | Attr_int64 _ => 3
    | Attr_bool _ => 4
    | Attr_float _ => 5
    | Attr_double _ => 6
    | Attr_numeric _ => 7
    | Attr_decimal _ _ _ => 8
    | Attr_date _ => 9
    | Attr_time _ => 10
    | Attr_timestamp _ _ => 11
    | Attr_timestamptz _ _ => 12
  end.

Definition N2_of_attribute a :=
  match a with
    | Attr_string s typmod =>
        (N_of_attribute a,
          (s, string_typmod_descriptor typmod))
    | Attr_Z s
    | Attr_int32 s
    | Attr_int64 s
    | Attr_bool s
    | Attr_float s
    | Attr_double s
    | Attr_numeric s
    | Attr_date s
    | Attr_time s => (N_of_attribute a, (s, (0%Z, 0%Z)))
    | Attr_decimal s p sc => (N_of_attribute a, (s, (p, sc)))
    | Attr_timestamp s p
    | Attr_timestamptz s p => (N_of_attribute a, (s, (p, 0%Z)))
  end.

Definition attribute_compare a1 a2 :=
  compareAB N.compare (compareAB string_compare (compareAB Z.compare Z.compare))
    (N2_of_attribute a1) (N2_of_attribute a2).

Lemma N2_of_attribute_injective :
  forall a1 a2, N2_of_attribute a1 = N2_of_attribute a2 -> a1 = a2.
Proof.
intros a1 a2 Heq.
destruct a1; destruct a2; cbn in Heq; try discriminate;
  inversion Heq; subst; try reflexivity.
f_equal.
apply string_typmod_descriptor_injective.
unfold string_typmod_descriptor.
now rewrite H1, H2.
Qed.

Definition OAN : Oset.Rcd attribute.
Proof.
split with attribute_compare.
- intros a1 a2; unfold attribute_compare.
  assert (match compareAB N.compare (compareAB string_compare (compareAB Z.compare Z.compare))
                           (N2_of_attribute a1) (N2_of_attribute a2) with
             | Eq => (N2_of_attribute a1) = (N2_of_attribute a2)
             | Lt => (N2_of_attribute a1) <> (N2_of_attribute a2)
             | Gt => (N2_of_attribute a1) <> (N2_of_attribute a2)
           end).
  {
    destruct (N2_of_attribute a1) as [n1 [s1 [p1 sc1]]];
    destruct (N2_of_attribute a2) as [n2 [s2 [p2 sc2]]].
    compareAB_eq_bool_ok_tac.
    - apply (Oset.eq_bool_ok ON).
    - compareAB_eq_bool_ok_tac.
      + apply (Oset.eq_bool_ok Ostring).
      + compareAB_eq_bool_ok_tac; apply (Oset.eq_bool_ok OZ).
  }
  destruct (compareAB
              N.compare (compareAB string_compare (compareAB Z.compare Z.compare))
              (N2_of_attribute a1) (N2_of_attribute a2)).
  + now apply N2_of_attribute_injective.
  + intro Ha; apply H; now subst.
  + intro Ha; apply H; now subst.
- intros a1 a2 a3; unfold attribute_compare.
  compareAB_tac.
  + apply (Oset.compare_eq_trans ON).
  + apply (Oset.compare_eq_lt_trans ON).
  + apply (Oset.compare_lt_eq_trans ON).
  + apply (Oset.compare_lt_trans ON).
  + compareAB_tac.
    * apply (Oset.compare_eq_trans Ostring).
    * apply (Oset.compare_eq_lt_trans Ostring).
    * apply (Oset.compare_lt_eq_trans Ostring).
    * apply (Oset.compare_lt_trans Ostring).
    * compareAB_tac.
      -- apply (Oset.compare_eq_trans OZ).
      -- apply (Oset.compare_eq_lt_trans OZ).
      -- apply (Oset.compare_lt_eq_trans OZ).
      -- apply (Oset.compare_lt_trans OZ).
      -- apply (Oset.compare_lt_trans OZ).
- intros a1 a2; unfold attribute_compare.
  compareAB_tac.
  + apply (Oset.compare_lt_gt ON).
  + compareAB_tac.
    * apply (Oset.compare_lt_gt Ostring).
    * compareAB_tac; apply (Oset.compare_lt_gt OZ).
Defined.

Definition FAN := Fset.build OAN.


Section Sec.

Hypothesis T : Tuple.Rcd.
Import Tuple.

Record db_state_ : Type :=
  mk_state
    {
      _relnames : list relname;
      _basesort : relname -> Fset.set (A T);
      _instance : relname -> Febag.bag (Fecol.CBag (CTuple T))
    }.

Definition init_db_ :=
  mk_state
    nil
    (fun _ => Fset.empty (A T))
    (fun _ => Febag.empty (Fecol.CBag (CTuple T))).

Definition create_table_
           (* old state *) db
           (* new table name *) t
           (* new table sort *) st
            :=
  mk_state
    (t :: _relnames db)
    (fun x =>
       match Oset.compare ORN x t with
         | Eq => Fset.mk_set (A T) st
         |_ => _basesort db x
       end)
    (_instance db).

Lemma relnames_init_db_ok :
  _relnames init_db_ = nil.
Proof.
reflexivity.
Qed.

Lemma basesort_init_db_ok :
  forall t, _basesort init_db_ t = Fset.empty (A T).
Proof.
intro t; reflexivity.
Qed.

Lemma instance_init_db_ok :
  forall t, _instance init_db_ t = Febag.empty (Fecol.CBag (CTuple T)).
Proof.
intro t; reflexivity.
Qed.

Lemma relnames_create_table_ok :
  forall db t st,
    _relnames (create_table_ db t st) = t :: _relnames db.
Proof.
intros db t st; reflexivity.
Qed.

Lemma basesort_create_table_eq :
  forall db t st,
    _basesort (create_table_ db t st) t = Fset.mk_set (A T) st.
Proof.
intros db t st; unfold create_table_.
cbn [_basesort].
rewrite Oset.compare_eq_refl; reflexivity.
Qed.

Lemma basesort_create_table_neq :
  forall db t st x,
    x <> t ->
    _basesort (create_table_ db t st) x = _basesort db x.
Proof.
intros db t st x Hneq; unfold create_table_.
cbn [_basesort].
destruct (Oset.compare ORN x t) eqn:Hcompare; try reflexivity.
apply Oset.compare_eq_iff in Hcompare; contradiction.
Qed.

Lemma instance_create_table_ok :
  forall db t st,
    _instance (create_table_ db t st) = _instance db.
Proof.
intros db t st; reflexivity.
Qed.

End Sec.


Definition TNull : Tuple.Rcd :=
  Tuple2.T attribute type NullValues.value 
           type_of_attribute 
           NullValues.type_of_value 
           NullValues.default_value 
           OAN FAN NullValues.OVal NullValues.FVal
           predicate scalar_operator aggregate
           scalar_operator_eq_dec aggregate_eq_dec Bool3.Bool3
           ValueCore.predicate_arity
           NullValues.interp_predicate
           NullValues.interp_scalar_operator
           NullValues.interp_aggregate.

Register TNull as datacert.syntax.TNull.
