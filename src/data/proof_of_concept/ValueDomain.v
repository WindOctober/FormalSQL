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

Require Import ZArith String Floats Bool.
Require Import OrderedSet.
Require Export ValueCore ValueDecimal.

Module NullValueDomain.

(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : option string -> value
  | Value_Z : option Z -> value
  | Value_bool : option bool -> value
  | Value_float : option float -> value
  | Value_decimal : option decimal -> value
  | Value_date : option Z -> value
  | Value_timestamp : option Z -> value
  | Value_timestamptz : option Z -> value.

Register value as datacert.value.type.
Register Value_string as datacert.value.Value_string.
Register Value_Z as datacert.value.Value_Z.
Register Value_bool as datacert.value.Value_bool.
Register Value_float as datacert.value.Value_float.
Register Value_decimal as datacert.value.Value_decimal.
Register Value_date as datacert.value.Value_date.
Register Value_timestamp as datacert.value.Value_timestamp.
Register Value_timestamptz as datacert.value.Value_timestamptz.

Open Scope Z_scope.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  | Value_float _ => type_float
  | Value_decimal _ => type_decimal
  | Value_date _ => type_date
  | Value_timestamp _ => type_timestamp
  | Value_timestamptz _ => type_timestamptz
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string None
    | type_Z => Value_Z None
    | type_bool => Value_bool None
    | type_float => Value_float None
    | type_decimal => Value_decimal None
    | type_date => Value_date None
    | type_timestamp => Value_timestamp None
    | type_timestamptz => Value_timestamptz None
  end.

Definition is_null_value v :=
  match v with
  | Value_string None
  | Value_Z None
  | Value_bool None
  | Value_float None
  | Value_decimal None
  | Value_date None
  | Value_timestamp None
  | Value_timestamptz None => true
  | _ => false
  end.

Definition same_non_null_value v1 v2 :=
  match v1, v2 with
  | Value_Z (Some a1), Value_Z (Some a2) =>
      match Z.compare a1 a2 with Eq => true | _ => false end
  | Value_float (Some a1), Value_float (Some a2) =>
      float_eq_dec a1 a2
  | Value_decimal (Some a1), Value_decimal (Some a2) =>
      decimal_eqb a1 a2
  | Value_string (Some s1), Value_string (Some s2) =>
      match string_compare s1 s2 with Eq => true | _ => false end
  | Value_bool (Some b1), Value_bool (Some b2) =>
      Bool.eqb b1 b2
  | Value_date (Some d1), Value_date (Some d2) =>
      match Z.compare d1 d2 with Eq => true | _ => false end
  | Value_timestamp (Some t1), Value_timestamp (Some t2) =>
      match Z.compare t1 t2 with Eq => true | _ => false end
  | Value_timestamptz (Some t1), Value_timestamptz (Some t2) =>
      match Z.compare t1 t2 with Eq => true | _ => false end
  | _, _ => false
  end.

End NullValueDomain.
