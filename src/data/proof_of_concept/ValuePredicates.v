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

Require Import ZArith String List.
Require Import OrderedSet Bool3.
Require Export ValueCore ValueDomain.

Module NullPredicates.

Import NullValueDomain.

Definition integral_order_value v :=
  match v with
  | Value_Z (Some z) => Some z
  | Value_int32 (Some z) => Some (int32_value z)
  | Value_int64 (Some z) => Some (int64_value z)
  | _ => None
  end.

Definition date_order_value v :=
  match v with
  | Value_date (Some z) => Some z
  | _ => None
  end.

Definition time_order_value v :=
  match v with
  | Value_time (Some z) => Some z
  | _ => None
  end.

Definition timestamp_order_value v :=
  match v with
  | Value_timestamp (Some z) => Some z
  | _ => None
  end.

Definition timestamptz_order_value v :=
  match v with
  | Value_timestamptz (Some z) => Some z
  | _ => None
  end.

Definition order_value_compare v1 v2 :=
  match integral_order_value v1, integral_order_value v2 with
  | Some z1, Some z2 => Some (Z.compare z1 z2)
  | _, _ =>
    match date_order_value v1, date_order_value v2 with
    | Some z1, Some z2 => Some (Z.compare z1 z2)
    | _, _ =>
      match time_order_value v1, time_order_value v2 with
      | Some z1, Some z2 => Some (Z.compare z1 z2)
      | _, _ =>
        match timestamp_order_value v1, timestamp_order_value v2 with
        | Some z1, Some z2 => Some (Z.compare z1 z2)
        | _, _ =>
          match timestamptz_order_value v1, timestamptz_order_value v2 with
          | Some z1, Some z2 => Some (Z.compare z1 z2)
          | _, _ => None
          end
        end
      end
    end
  end.

Definition interp_predicate p :=
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Lt => true3
              | Some _ => false3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Lt => true3 | _ => false3 end
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | Predicate "<." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_ltb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate "<_double" =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_ltb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Gt => false3
              | Some _ => true3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Gt => false3 | _ => true3 end
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | Predicate "<=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_leb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate "<=_double" =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_leb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Gt => true3
              | Some _ => false3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Gt => true3 | _ => false3 end
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | Predicate ">." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_ltb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">_double" =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_ltb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Lt => false3
              | Some _ => true3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Lt => false3 | _ => true3 end
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | Predicate ">=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_leb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">=_double" =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_leb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate "=" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Eq => true3
              | Some _ => false3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Eq => true3 | _ => false3 end
              | Value_float (Some a1), Value_float (Some a2) =>
                if float32_eqb a1 a2 then true3 else false3
              | Value_double (Some a1), Value_double (Some a2) =>
                if float64_eqb a1 a2 then true3 else false3
              | Value_string (Some s1), Value_string (Some s2) =>
                match string_compare s1 s2 with Eq => true3 | _ => false3 end
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | Predicate "<>" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
            match order_value_compare v1 v2 with
              | Some Eq => false3
              | Some _ => true3
              | None =>
            match v1, v2 with
              | Value_numeric (Some a1), Value_numeric (Some a2) =>
                match numeric_compare a1 a2 with Eq => false3 | _ => true3 end
              | Value_float (Some a1), Value_float (Some a2) =>
                if float32_eqb a1 a2 then false3 else true3
              | Value_double (Some a1), Value_double (Some a2) =>
                if float64_eqb a1 a2 then false3 else true3
              | Value_string (Some s1), Value_string (Some s2) =>
                match string_compare s1 s2 with Eq => false3 | _ => true3 end
              | _, _ => unknown3
            end
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
