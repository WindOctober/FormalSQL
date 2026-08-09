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
Require Import OrderedSet Bool3 ValueTemporal.
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

(** PostgreSQL's SQL Boolean btree order is [false < true].  The library's
    generic [Obool] carrier order is intentionally the reverse, so SQL
    predicates must not reuse it. *)
Definition sql_bool_compare b1 b2 :=
  match b1, b2 with
  | false, false | true, true => Eq
  | false, true => Lt
  | true, false => Gt
  end.

Lemma sql_bool_compare_refl :
  forall value, sql_bool_compare value value = Eq.
Proof.
now intros [].
Qed.

Lemma sql_bool_compare_opposite :
  forall left right,
    sql_bool_compare left right =
    CompOpp (sql_bool_compare right left).
Proof.
now intros [] [].
Qed.

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
          | _, _ =>
            match v1, v2 with
            | Value_bool (Some b1), Value_bool (Some b2) =>
                Some (sql_bool_compare b1 b2)
            | Value_string (typmod1, Some s1),
              Value_string (typmod2, Some s2) =>
                Some (sql_string_compare typmod1 s1 typmod2 s2)
            | _, _ => None
            end
          end
        end
      end
    end
  end.

(** All three admitted integral carriers share the same mathematical ordering.
    The [Some] premises retain both non-NULLness and membership in that family,
    including mixed INTEGER/BIGINT comparisons. *)
Lemma order_value_compare_integral :
  forall left right left_integer right_integer,
    integral_order_value left = Some left_integer ->
    integral_order_value right = Some right_integer ->
    order_value_compare left right =
      Some (Z.compare left_integer right_integer).
Proof.
intros left right left_integer right_integer Hleft Hright.
unfold order_value_compare.
now rewrite Hleft, Hright.
Qed.

Definition interp_predicate p :=
  match p with
    | PredicateLt =>
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
    | PredicateFloatLt =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_ltb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | PredicateDoubleLt =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_ltb a1 a2 then true3 else false3
          | _ => unknown3
        end
    (** PostgreSQL's cross-type operator calls
        [date_cmp_timestamp_internal], not the checked DATE-to-TIMESTAMP cast.
        The predicate itself is total; SQL NULL and ill-typed observations
        produce UNKNOWN, while the error-aware evaluator independently
        propagates any child-expression error before invoking it. *)
    | PredicateDateLtTimestamp =>
      fun l =>
        match l with
          | Value_date (Some date) ::
            Value_timestamp (Some timestamp) :: nil =>
              if date_lt_timestamp_bool date timestamp
              then true3 else false3
          | _ => unknown3
        end
    | PredicateDateLteTimestamp =>
      fun l =>
        match l with
          | Value_date (Some date) ::
            Value_timestamp (Some timestamp) :: nil =>
              if date_lte_timestamp_bool date timestamp
              then true3 else false3
          | _ => unknown3
        end
    | PredicateDateGtTimestamp =>
      fun l =>
        match l with
          | Value_date (Some date) ::
            Value_timestamp (Some timestamp) :: nil =>
              if date_gt_timestamp_bool date timestamp
              then true3 else false3
          | _ => unknown3
        end
    | PredicateDateGteTimestamp =>
      fun l =>
        match l with
          | Value_date (Some date) ::
            Value_timestamp (Some timestamp) :: nil =>
              if date_gte_timestamp_bool date timestamp
              then true3 else false3
          | _ => unknown3
        end
    | PredicateLte =>
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
    | PredicateFloatLte =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_leb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | PredicateDoubleLte =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_leb a1 a2 then true3 else false3
          | _ => unknown3
        end
    | PredicateGt =>
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
    | PredicateFloatGt =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_ltb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | PredicateDoubleGt =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_ltb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | PredicateGte =>
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
    | PredicateFloatGte =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float32_leb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | PredicateDoubleGte =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            if float64_leb a2 a1 then true3 else false3
          | _ => unknown3
        end
    | PredicateEq =>
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
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | PredicateNeq =>
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
              | _, _ => unknown3
            end
            end
          | _ => unknown3
        end
    | PredicateLikePrefix =>
      fun l =>
        match l with
          | Value_string (input_typmod, Some input) ::
            Value_string (_, Some prefix) :: nil =>
              if string_like_prefix input_typmod input prefix
              then true3 else false3
          | _ => unknown3
        end
    | PredicateLikePercent =>
      fun l =>
        match l with
          | Value_string (input_typmod, Some input) ::
            Value_string (_, Some pattern) :: nil =>
              if string_like_percent input_typmod input pattern
              then true3 else false3
          | _ => unknown3
        end
    | PredicateIsNull =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then true3 else false3
          | _ => unknown3
        end
    | PredicateIsNotNull =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then false3 else true3
          | _ => unknown3
        end
    | PredicateIsTrue =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => true3
          | Value_bool (Some false) :: nil => false3
          | Value_bool None :: nil => false3
          | _ => unknown3
        end
    | PredicateIsNotTrue =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => false3
          | Value_bool (Some false) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | PredicateIsFalse =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => true3
          | Value_bool (Some true) :: nil => false3
          | Value_bool None :: nil => false3
          | _ => unknown3
        end
    | PredicateIsNotFalse =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => false3
          | Value_bool (Some true) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | PredicateIsNotDistinctFrom =>
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
  end.


End NullPredicates.
