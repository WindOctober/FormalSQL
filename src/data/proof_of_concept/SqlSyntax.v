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
        FiniteSet FiniteBag FiniteCollection Tree Formula.

Import Tuple.
Require Import Values TuplesImpl GenericInstance.

Definition value := NullValues.value.
Definition Value_bool := NullValues.Value_bool.
Definition Value_Z := NullValues.Value_Z.
Definition Value_int32 := NullValues.Value_int32.
Definition Value_int64 := NullValues.Value_int64.
Definition Value_string := NullValues.Value_string.
Definition Value_float := NullValues.Value_float.
Definition Value_double := NullValues.Value_double.
Definition Value_numeric := NullValues.Value_numeric.
Definition Value_date := NullValues.Value_date.
Definition Value_time := NullValues.Value_time.
Definition Value_timestamp := NullValues.Value_timestamp.
Definition Value_timestamptz := NullValues.Value_timestamptz.

Definition db_state := db_state_ TNull.
Definition init_db := init_db_ TNull.
Definition create_table := create_table_ TNull.

Register db_state as datacert.syntax.db_state.
Register create_table as datacert.syntax.create_table.

Fixpoint mk_att att atts vals :=
  match atts, vals with
  | a::atts, v::vals => match attribute_compare a att with
                        | Eq => v
                        | _ => mk_att att atts vals
                        end
  | _, _ => match att with
                | Attr_string _ typmod =>
                    Value_string (StringValue typmod None)
                | Attr_Z _ => Value_Z None
                | Attr_int32 _ => Value_int32 None
                | Attr_int64 _ => Value_int64 None
                | Attr_bool _ => Value_bool None
                | Attr_float _ => Value_float None
                | Attr_double _ => Value_double None
                | Attr_numeric _ | Attr_decimal _ _ _ => Value_numeric None
                | Attr_date _ => Value_date None
                | Attr_time _ => Value_time None
                | Attr_timestamp _ _ => Value_timestamp None
                | Attr_timestamptz _ _ => Value_timestamptz None
                end
  end.

Definition mk_tuple_lists atts vals :=
  mk_tuple TNull (Fset.mk_set _ atts) (fun att => mk_att att atts vals).

(**
  Database instances quantified by generated equivalence theorems must respect
  their declared SQL attributes.  In particular, a string payload cannot carry
  a typmod independent from the [Attr_string] used to retrieve it.  Requiring
  canonical, valid UTF-8 payloads also makes CHARACTER width and comparison
  semantics independent of malformed internal tuple representations.
 *)
Definition value_conforms_attribute (att : attribute) (val : value) : Prop :=
  match att, val with
  | Attr_string _ expected, NullValues.Value_string (actual, payload) =>
      expected = actual /\
      match payload with
      | None => True
      | Some text =>
          string_fits_typmod expected text = true /\
          string_canonical_value expected text = text
      end
  | Attr_decimal _ precision scale, NullValues.Value_numeric payload =>
      match payload with
      | None => True
      | Some value =>
          numeric_cast_typmod value precision scale = Some value
      end
  | Attr_date _, NullValues.Value_date payload =>
      match payload with
      | None => True
      | Some date => date_value_valid_bool date = true
      end
  | Attr_time _, NullValues.Value_time payload =>
      match payload with
      | None => True
      | Some time => time_in_range_bool time = true
      end
  | Attr_timestamp _ _, NullValues.Value_timestamp payload
  | Attr_timestamptz _ _, NullValues.Value_timestamptz payload =>
      match payload with
      | None => True
      | Some timestamp => timestamp_value_valid_bool timestamp = true
      end
  | Attr_Z _, NullValues.Value_Z _
  | Attr_int32 _, NullValues.Value_int32 _
  | Attr_int64 _, NullValues.Value_int64 _
  | Attr_bool _, NullValues.Value_bool _
  | Attr_float _, NullValues.Value_float _
  | Attr_double _, NullValues.Value_double _
  | Attr_numeric _, NullValues.Value_numeric _ => True
  | _, _ => False
  end.

Definition tuple_conforms_sort
    (sort : Fset.set (A TNull)) (row : tuple TNull) : Prop :=
  labels TNull row =S= sort /\
  forall att, att inS sort ->
    value_conforms_attribute att (dot TNull row att).

Definition database_values_conform (db : db_state) : Prop :=
  forall relation row,
    In row
      (Febag.elements
        (Fecol.CBag (CTuple TNull))
        (@_instance TNull db relation)) ->
    tuple_conforms_sort (@_basesort TNull db relation) row.

(** Again, for the constructs of the SQL framework *)
Definition contains_nulls (t : tuple TNull) :=
 existsb (fun a => match dot TNull t a with
                   | NullValues.Value_string (_, None)
                   | NullValues.Value_Z None
                   | NullValues.Value_int32 None
                   | NullValues.Value_int64 None
                   | NullValues.Value_bool None
                   | NullValues.Value_float None
                   | NullValues.Value_double None
                   | NullValues.Value_numeric None
                   | NullValues.Value_date None
                   | NullValues.Value_time None
                   | NullValues.Value_timestamp None
                   | NullValues.Value_timestamptz None => true
                   | NullValues.Value_string (_, Some _)
                   | NullValues.Value_Z (Some _)
                   | NullValues.Value_int32 (Some _)
                   | NullValues.Value_int64 (Some _)
                   | NullValues.Value_bool (Some _)
                   | NullValues.Value_float (Some _)
                   | NullValues.Value_double (Some _)
                   | NullValues.Value_numeric (Some _)
                   | NullValues.Value_date (Some _)
                   | NullValues.Value_time (Some _)
                   | NullValues.Value_timestamp (Some _)
                   | NullValues.Value_timestamptz (Some _) => false
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
