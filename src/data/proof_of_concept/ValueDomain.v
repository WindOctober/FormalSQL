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

Require Import ZArith String Bool.
Require Import OrderedSet.
Require Export ValueCore ValueFloat ValueInteger ValueNumericTypmod ValueString
  ValueTextInteger.

Module NullValueDomain.

(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : string_value -> value
  | Value_Z : option Z -> value
  | Value_int32 : option int32 -> value
  | Value_int64 : option int64 -> value
  | Value_bool : option bool -> value
  | Value_float : option float32 -> value
  | Value_double : option float64 -> value
  | Value_numeric : option numeric -> value
  | Value_date : option Z -> value
  | Value_time : option Z -> value
  | Value_timestamp : option Z -> value
  | Value_timestamptz : option Z -> value.

Register value as datacert.value.type.
Register Value_string as datacert.value.Value_string.
Register Value_Z as datacert.value.Value_Z.
Register Value_int32 as datacert.value.Value_int32.
Register Value_int64 as datacert.value.Value_int64.
Register Value_bool as datacert.value.Value_bool.
Register Value_float as datacert.value.Value_float.
Register Value_double as datacert.value.Value_double.
Register Value_numeric as datacert.value.Value_numeric.
Register Value_date as datacert.value.Value_date.
Register Value_time as datacert.value.Value_time.
Register Value_timestamp as datacert.value.Value_timestamp.
Register Value_timestamptz as datacert.value.Value_timestamptz.

Open Scope Z_scope.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_int32 _ => type_int32
  | Value_int64 _ => type_int64
  | Value_bool _ => type_bool
  | Value_float _ => type_float
  | Value_double _ => type_double
  | Value_numeric _ => type_numeric
  | Value_date _ => type_date
  | Value_time _ => type_time
  | Value_timestamp _ => type_timestamp
  | Value_timestamptz _ => type_timestamptz
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string (StringValue StringText None)
    | type_Z => Value_Z None
    | type_int32 => Value_int32 None
    | type_int64 => Value_int64 None
    | type_bool => Value_bool None
    | type_float => Value_float None
    | type_double => Value_double None
    | type_numeric => Value_numeric None
    | type_date => Value_date None
    | type_time => Value_time None
    | type_timestamp => Value_timestamp None
    | type_timestamptz => Value_timestamptz None
  end.

Definition is_null_value v :=
  match v with
  | Value_string (_, None)
  | Value_Z None
  | Value_int32 None
  | Value_int64 None
  | Value_bool None
  | Value_float None
  | Value_double None
  | Value_numeric None
  | Value_date None
  | Value_time None
  | Value_timestamp None
  | Value_timestamptz None => true
  | _ => false
  end.

Definition same_non_null_value v1 v2 :=
  let integral_value v :=
    match v with
    | Value_Z (Some z) => Some z
    | Value_int32 (Some z) => Some (int32_value z)
    | Value_int64 (Some z) => Some (int64_value z)
    | _ => None
    end in
  match integral_value v1, integral_value v2 with
  | Some a1, Some a2 =>
      match Z.compare a1 a2 with Eq => true | _ => false end
  | _, _ =>
    match v1, v2 with
  | Value_float (Some a1), Value_float (Some a2) =>
      float32_eqb a1 a2
  | Value_double (Some a1), Value_double (Some a2) =>
      float64_eqb a1 a2
  | Value_numeric (Some a1), Value_numeric (Some a2) =>
      numeric_eqb a1 a2
  | Value_string (typmod1, Some s1), Value_string (typmod2, Some s2) =>
      sql_string_eqb typmod1 s1 typmod2 s2
  | Value_bool (Some b1), Value_bool (Some b2) =>
      Bool.eqb b1 b2
  | Value_date (Some d1), Value_date (Some d2) =>
      match Z.compare d1 d2 with Eq => true | _ => false end
  | Value_time (Some t1), Value_time (Some t2) =>
      match Z.compare t1 t2 with Eq => true | _ => false end
  | Value_timestamp (Some t1), Value_timestamp (Some t2) =>
      match Z.compare t1 t2 with Eq => true | _ => false end
  | Value_timestamptz (Some t1), Value_timestamptz (Some t2) =>
      match Z.compare t1 t2 with Eq => true | _ => false end
  | _, _ => false
    end
  end.

End NullValueDomain.
