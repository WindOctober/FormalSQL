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

Require Import ZArith String Floats List.
Require Import OrderedSet Bool3.
Require Export ValueCore ValueDomain.

Module NullPredicates.

Import NullValueDomain.

Definition interp_predicate p :=
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Lt => true3 | _ => false3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Lt => true3 | _ => false3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate "<." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_lt a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Gt => false3 | _ => true3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Gt => false3 | _ => true3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate "<=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_le a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Gt => true3 | _ => false3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Gt => true3 | _ => false3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate ">." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_lt a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Lt => false3 | _ => true3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Lt => false3 | _ => true3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate ">=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_le a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate "=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Eq => true3 | _ => false3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Eq => true3 | _ => false3 end
              | Value_float (Some a1), Value_float (Some a2) =>
                if float_eq_dec a1 a2 then true3 else false3
              | Value_string (Some s1), Value_string (Some s2) =>
                match string_compare s1 s2 with Eq => true3 | _ => false3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate "<>" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match v1, v2 with
              | Value_Z (Some a1), Value_Z (Some a2)
              | Value_date (Some a1), Value_date (Some a2)
              | Value_timestamp (Some a1), Value_timestamp (Some a2)
              | Value_timestamptz (Some a1), Value_timestamptz (Some a2) =>
                match Z.compare a1 a2 with Eq => false3 | _ => true3 end
              | Value_decimal (Some a1), Value_decimal (Some a2) =>
                match decimal_compare a1 a2 with Eq => false3 | _ => true3 end
              | Value_float (Some a1), Value_float (Some a2) =>
                if float_eq_dec a1 a2 then false3 else true3
              | Value_string (Some s1), Value_string (Some s2) =>
                match string_compare s1 s2 with Eq => false3 | _ => true3 end
              | _, _ => unknown3
            end
          | _ => unknown3
        end
    | Predicate "is_null" =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then true3 else false3
          | _ => unknown3
        end
    | Predicate "is_not_null" =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then false3 else true3
          | _ => unknown3
        end
    | Predicate "is_true" =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => true3
          | Value_bool (Some false) :: nil => false3
          | Value_bool None :: nil => unknown3
          | _ => unknown3
        end
    | Predicate "is_not_true" =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => false3
          | Value_bool (Some false) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | Predicate "is_false" =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => true3
          | Value_bool (Some true) :: nil => false3
          | Value_bool None :: nil => unknown3
          | _ => unknown3
        end
    | Predicate "is_not_false" =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => false3
          | Value_bool (Some true) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | Predicate "is_not_distinct_from" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
              if andb (is_null_value v1) (is_null_value v2)
              then true3
              else if orb (is_null_value v1) (is_null_value v2)
                   then false3
                   else if same_non_null_value v1 v2 then true3 else false3
          | _ => unknown3
        end
   | _ => fun _ => unknown3
  end.


End NullPredicates.
