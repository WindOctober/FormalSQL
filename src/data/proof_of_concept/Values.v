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

Require Import Arith NArith ZArith String Ascii List QArith Qcanon.
Require Import OrderedSet FiniteSet Bool3.
Require Import SqlOutcome.
Require Export ValueCore ValueTemporal ValuePredicates.

Open Scope string_scope.

Module NullValues.

Include NullValueDomain.

(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
*)


Definition value_compare x y :=
  match x, y with
    | Value_string s1, Value_string s2 => Oset.compare OStringValue s1 s2
    | Value_string _, Value_Z _
    | Value_string _, Value_int32 _
    | Value_string _, Value_int64 _
    | Value_string _, Value_bool _
    | Value_string _, Value_float _
    | Value_string _, Value_double _
    | Value_string _, Value_numeric _
    | Value_string _, Value_date _
    | Value_string _, Value_time _
    | Value_string _, Value_timestamp _
    | Value_string _, Value_timestamptz _ => Lt

    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => option_compare _ Z.compare z1 z2
    | Value_Z _, Value_int32 _
    | Value_Z _, Value_int64 _
    | Value_Z _, Value_bool _
    | Value_Z _, Value_float _
    | Value_Z _, Value_double _
    | Value_Z _, Value_numeric _
    | Value_Z _, Value_date _
    | Value_Z _, Value_time _
    | Value_Z _, Value_timestamp _
    | Value_Z _, Value_timestamptz _ => Lt

    | Value_int32 _, Value_string _
    | Value_int32 _, Value_Z _ => Gt
    | Value_int32 i1, Value_int32 i2 => option_compare _ (Oset.compare Oint32) i1 i2
    | Value_int32 _, Value_int64 _
    | Value_int32 _, Value_bool _
    | Value_int32 _, Value_float _
    | Value_int32 _, Value_double _
    | Value_int32 _, Value_numeric _
    | Value_int32 _, Value_date _
    | Value_int32 _, Value_time _
    | Value_int32 _, Value_timestamp _
    | Value_int32 _, Value_timestamptz _ => Lt

    | Value_int64 _, Value_string _
    | Value_int64 _, Value_Z _
    | Value_int64 _, Value_int32 _ => Gt
    | Value_int64 i1, Value_int64 i2 => option_compare _ (Oset.compare Oint64) i1 i2
    | Value_int64 _, Value_bool _
    | Value_int64 _, Value_float _
    | Value_int64 _, Value_double _
    | Value_int64 _, Value_numeric _
    | Value_int64 _, Value_date _
    | Value_int64 _, Value_time _
    | Value_int64 _, Value_timestamp _
    | Value_int64 _, Value_timestamptz _ => Lt

    | Value_bool _, Value_string _
    | Value_bool _, Value_Z _
    | Value_bool _, Value_int32 _
    | Value_bool _, Value_int64 _ => Gt
    | Value_bool b1, Value_bool b2 => option_compare _ bool_compare b1 b2
    | Value_bool _, Value_float _
    | Value_bool _, Value_double _
    | Value_bool _, Value_numeric _
    | Value_bool _, Value_date _
    | Value_bool _, Value_time _
    | Value_bool _, Value_timestamp _
    | Value_bool _, Value_timestamptz _ => Lt

    | Value_float _, Value_string _
    | Value_float _, Value_Z _
    | Value_float _, Value_int32 _
    | Value_float _, Value_int64 _
    | Value_float _, Value_bool _ => Gt
    | Value_float f1, Value_float f2 => option_compare _ (Oset.compare Ofloat32) f1 f2
    | Value_float _, Value_double _
    | Value_float _, Value_numeric _
    | Value_float _, Value_date _
    | Value_float _, Value_time _
    | Value_float _, Value_timestamp _
    | Value_float _, Value_timestamptz _ => Lt

    | Value_double _, Value_string _
    | Value_double _, Value_Z _
    | Value_double _, Value_int32 _
    | Value_double _, Value_int64 _
    | Value_double _, Value_bool _
    | Value_double _, Value_float _ => Gt
    | Value_double f1, Value_double f2 => option_compare _ (Oset.compare Ofloat64) f1 f2
    | Value_double _, Value_numeric _
    | Value_double _, Value_date _
    | Value_double _, Value_time _
    | Value_double _, Value_timestamp _
    | Value_double _, Value_timestamptz _ => Lt

    | Value_numeric _, Value_string _
    | Value_numeric _, Value_Z _
    | Value_numeric _, Value_int32 _
    | Value_numeric _, Value_int64 _
    | Value_numeric _, Value_bool _
    | Value_numeric _, Value_float _
    | Value_numeric _, Value_double _ => Gt
    | Value_numeric d1, Value_numeric d2 => option_compare _ (Oset.compare Onumeric) d1 d2
    | Value_numeric _, Value_date _
    | Value_numeric _, Value_time _
    | Value_numeric _, Value_timestamp _
    | Value_numeric _, Value_timestamptz _ => Lt

    | Value_date _, Value_string _
    | Value_date _, Value_Z _
    | Value_date _, Value_int32 _
    | Value_date _, Value_int64 _
    | Value_date _, Value_bool _
    | Value_date _, Value_float _
    | Value_date _, Value_double _
    | Value_date _, Value_numeric _ => Gt
    | Value_date d1, Value_date d2 => option_compare _ Z.compare d1 d2
    | Value_date _, Value_time _
    | Value_date _, Value_timestamp _
    | Value_date _, Value_timestamptz _ => Lt

    | Value_time _, Value_string _
    | Value_time _, Value_Z _
    | Value_time _, Value_int32 _
    | Value_time _, Value_int64 _
    | Value_time _, Value_bool _
    | Value_time _, Value_float _
    | Value_time _, Value_double _
    | Value_time _, Value_numeric _
    | Value_time _, Value_date _ => Gt
    | Value_time t1, Value_time t2 => option_compare _ Z.compare t1 t2
    | Value_time _, Value_timestamp _
    | Value_time _, Value_timestamptz _ => Lt

    | Value_timestamp _, Value_string _
    | Value_timestamp _, Value_Z _
    | Value_timestamp _, Value_int32 _
    | Value_timestamp _, Value_int64 _
    | Value_timestamp _, Value_bool _
    | Value_timestamp _, Value_float _
    | Value_timestamp _, Value_double _
    | Value_timestamp _, Value_numeric _
    | Value_timestamp _, Value_date _
    | Value_timestamp _, Value_time _ => Gt
    | Value_timestamp t1, Value_timestamp t2 => option_compare _ Z.compare t1 t2
    | Value_timestamp _, Value_timestamptz _ => Lt

    | Value_timestamptz _, Value_string _
    | Value_timestamptz _, Value_Z _
    | Value_timestamptz _, Value_int32 _
    | Value_timestamptz _, Value_int64 _
    | Value_timestamptz _, Value_bool _
    | Value_timestamptz _, Value_float _
    | Value_timestamptz _, Value_double _
    | Value_timestamptz _, Value_numeric _
    | Value_timestamptz _, Value_date _
    | Value_timestamptz _, Value_time _
    | Value_timestamptz _, Value_timestamp _ => Gt
    | Value_timestamptz t1, Value_timestamptz t2 => option_compare _ Z.compare t1 t2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [s1 | [z1 | ] | [i321 | ] | [i641 | ] | [b1 | ] | [f1 | ] | [dbl1 | ] | [dec1 | ] | [d1 | ] | [tm1 | ] | [t1 | ] | [tz1 | ]]
         [s2 | [z2 | ] | [i322 | ] | [i642 | ] | [b2 | ] | [f2 | ] | [dbl2 | ] | [dec2 | ] | [d2 | ] | [tm2 | ] | [t2 | ] | [tz2 | ]];
    try discriminate; simpl; trivial.
  + change
      (match Oset.compare OStringValue s1 s2 with
       | Eq => Value_string s1 = Value_string s2
       | Lt | Gt => Value_string s1 <> Value_string s2
       end).
    case_eq (Oset.compare OStringValue s1 s2); intro Hstring.
    * apply f_equal.
      apply (proj1 (Oset.compare_eq_iff OStringValue s1 s2)); exact Hstring.
    * intro Heq; injection Heq as Heq; subst.
      rewrite Oset.compare_eq_refl in Hstring; discriminate.
    * intro Heq; injection Heq as Heq; subst.
      rewrite Oset.compare_eq_refl in Hstring; discriminate.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply (f_equal (fun x => Value_Z (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Oint32 i321 i322); simpl.
    case_eq (int32_compare i321 i322); intro Hint.
    * intro H; apply (f_equal (fun x => Value_int32 (Some x))); apply H; reflexivity.
    * intros Hneq H; injection H; intro Heq; apply Hneq; exact Heq.
    * intros Hneq H; injection H; intro Heq; apply Hneq; exact Heq.
  + generalize (Oset.eq_bool_ok Oint64 i641 i642); simpl.
    case_eq (int64_compare i641 i642); intro Hint.
    * intro H; apply (f_equal (fun x => Value_int64 (Some x))); apply H; reflexivity.
    * intros Hneq H; injection H; intro Heq; apply Hneq; exact Heq.
    * intros Hneq H; injection H; intro Heq; apply Hneq; exact Heq.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply (f_equal (fun x => Value_bool (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Ofloat32 f1 f2); simpl.
    case (Oset.compare Ofloat32 f1 f2).
    * apply (f_equal (fun x => Value_float (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Ofloat64 dbl1 dbl2); simpl.
    case (Oset.compare Ofloat64 dbl1 dbl2).
    * apply (f_equal (fun x => Value_double (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + case_eq (Oset.compare Onumeric dec1 dec2); intro Hdec.
    * change (match Oset.compare Onumeric dec1 dec2 with
              | Eq => Value_numeric (Some dec1) = Value_numeric (Some dec2)
              | _ => Value_numeric (Some dec1) <> Value_numeric (Some dec2)
              end).
      rewrite Hdec.
      apply (f_equal (fun x => Value_numeric (Some x))).
      apply (proj1 (Oset.compare_eq_iff Onumeric dec1 dec2)); assumption.
    * change (match Oset.compare Onumeric dec1 dec2 with
              | Eq => Value_numeric (Some dec1) = Value_numeric (Some dec2)
              | _ => Value_numeric (Some dec1) <> Value_numeric (Some dec2)
              end).
      rewrite Hdec.
      intro H; inversion H; subst.
      rewrite Oset.compare_eq_refl in Hdec; discriminate.
    * change (match Oset.compare Onumeric dec1 dec2 with
              | Eq => Value_numeric (Some dec1) = Value_numeric (Some dec2)
              | _ => Value_numeric (Some dec1) <> Value_numeric (Some dec2)
              end).
      rewrite Hdec.
      intro H; inversion H; subst.
      rewrite Oset.compare_eq_refl in Hdec; discriminate.
  + generalize (Oset.eq_bool_ok OZ d1 d2); simpl; case (Z.compare d1 d2).
    * apply (f_equal (fun x => Value_date (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ tm1 tm2); simpl; case (Z.compare tm1 tm2).
    * apply (f_equal (fun x => Value_time (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ t1 t2); simpl; case (Z.compare t1 t2).
    * apply (f_equal (fun x => Value_timestamp (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ tz1 tz2); simpl; case (Z.compare tz1 tz2).
    * apply (f_equal (fun x => Value_timestamptz (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
- (* 1/2 *)
  intros [s1 | [z1 | ] | [i321 | ] | [i641 | ] | [b1 | ] | [f1 | ] | [dbl1 | ] | [dec1 | ] | [d1 | ] | [tm1 | ] | [t1 | ] | [tz1 | ]]
         [s2 | [z2 | ] | [i322 | ] | [i642 | ] | [b2 | ] | [f2 | ] | [dbl2 | ] | [dec2 | ] | [d2 | ] | [tm2 | ] | [t2 | ] | [tz2 | ]]
         [s3 | [z3 | ] | [i323 | ] | [i643 | ] | [b3 | ] | [f3 | ] | [dbl3 | ] | [dec3 | ] | [d3 | ] | [tm3 | ] | [t3 | ] | [tz3 | ]]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans OStringValue).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Oint32).
  + apply (Oset.compare_lt_trans Oint64).
  + apply (Oset.compare_lt_trans Obool).
  + apply (Oset.compare_lt_trans Ofloat32).
  + apply (Oset.compare_lt_trans Ofloat64).
  + apply (Oset.compare_lt_trans Onumeric).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
- (* 1/1 *)
  intros [s1 | [z1 | ] | [i321 | ] | [i641 | ] | [b1 | ] | [f1 | ] | [dbl1 | ] | [dec1 | ] | [d1 | ] | [tm1 | ] | [t1 | ] | [tz1 | ]]
         [s2 | [z2 | ] | [i322 | ] | [i642 | ] | [b2 | ] | [f2 | ] | [dbl2 | ] | [dec2 | ] | [d2 | ] | [tm2 | ] | [t2 | ] | [tz2 | ]]; trivial; simpl.
  + apply (Oset.compare_lt_gt OStringValue).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Oint32).
  + apply (Oset.compare_lt_gt Oint64).
  + apply (Oset.compare_lt_gt Obool).
  + apply (Oset.compare_lt_gt Ofloat32).
  + apply (Oset.compare_lt_gt Ofloat64).
  + apply (Oset.compare_lt_gt Onumeric).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt OZ).
Defined.

(** SQL ordering is not always the structural ordering used to build finite
    collections.  In particular PostgreSQL orders [false] before [true].
    All other currently admitted scalar families use the existing [OVal]
    order. *)
Definition sql_order_value_compare left right :=
  match left, right with
  | Value_bool (Some left_bool), Value_bool (Some right_bool) =>
      NullPredicates.sql_bool_compare left_bool right_bool
  | _, _ => Oset.compare OVal left right
  end.

Lemma sql_order_value_compare_opposite :
  forall left right,
    sql_order_value_compare left right =
    CompOpp (sql_order_value_compare right left).
Proof.
intros [s1 | [z1|] | [i321|] | [i641|] | [b1|] | [f1|] | [dbl1|]
          | [dec1|] | [d1|] | [tm1|] | [t1|] | [tz1|]]
       [s2 | [z2|] | [i322|] | [i642|] | [b2|] | [f2|] | [dbl2|]
          | [dec2|] | [d2|] | [tm2|] | [t2|] | [tz2|]];
  trivial; simpl [sql_order_value_compare].
- apply (Oset.compare_lt_gt OStringValue).
- apply (Oset.compare_lt_gt OZ).
- apply (Oset.compare_lt_gt Oint32).
- apply (Oset.compare_lt_gt Oint64).
- now destruct b1, b2.
- apply (Oset.compare_lt_gt Ofloat32).
- apply (Oset.compare_lt_gt Ofloat64).
- apply (Oset.compare_lt_gt Onumeric).
- apply (Oset.compare_lt_gt OZ).
- apply (Oset.compare_lt_gt OZ).
- apply (Oset.compare_lt_gt OZ).
- apply (Oset.compare_lt_gt OZ).
Qed.

Definition FVal := Fset.build OVal.


Definition is_z_value v :=
  match v with
  | Value_Z _ => true
  | _ => false
  end.

Definition is_int32_value v :=
  match v with
  | Value_int32 _ => true
  | _ => false
  end.

Definition is_int64_value v :=
  match v with
  | Value_int64 _ => true
  | _ => false
  end.

Definition is_float_value v :=
  match v with
  | Value_float _ => true
  | _ => false
  end.

Definition is_double_value v :=
  match v with
  | Value_double _ => true
  | _ => false
  end.

Definition is_numeric_value v :=
  match v with
  | Value_numeric _ => true
  | _ => false
  end.

(** PostgreSQL [text] values interpreted under the C collation.  Keeping this
    predicate specific to [StringText] prevents an aggregate operator selected
    for [max(text)] from silently accepting a different character type. *)
Definition is_text_value v :=
  match v with
  | Value_string (StringText, _) => true
  | _ => false
  end.

Fixpoint z_values l :=
  match l with
  | Value_Z (Some z) :: tl => z :: z_values tl
  | _ :: tl => z_values tl
  | nil => nil
  end.

Fixpoint int32_values l :=
  match l with
  | Value_int32 (Some z) :: tl => z :: int32_values tl
  | _ :: tl => int32_values tl
  | nil => nil
  end.

Fixpoint int64_values l :=
  match l with
  | Value_int64 (Some z) :: tl => z :: int64_values tl
  | _ :: tl => int64_values tl
  | nil => nil
  end.

Fixpoint float_values l :=
  match l with
  | Value_float (Some f) :: tl => f :: float_values tl
  | _ :: tl => float_values tl
  | nil => nil
  end.

Fixpoint double_values l :=
  match l with
  | Value_double (Some f) :: tl => f :: double_values tl
  | _ :: tl => double_values tl
  | nil => nil
  end.

Fixpoint numeric_values l :=
  match l with
  | Value_numeric (Some d) :: tl => d :: numeric_values tl
  | _ :: tl => numeric_values tl
  | nil => nil
  end.

Fixpoint text_values l :=
  match l with
  | Value_string (StringText, Some value) :: tl => value :: text_values tl
  | _ :: tl => text_values tl
  | nil => nil
  end.

Definition non_null_count l :=
  Z_of_nat (List.length (filter (fun v => negb (is_null_value v)) l)).

Definition row_count (l : list value) :=
  Z_of_nat (List.length l).

Lemma non_null_count_app : forall left right,
  non_null_count (left ++ right) =
    (non_null_count left + non_null_count right)%Z.
Proof.
intros left right.
unfold non_null_count.
rewrite filter_app, length_app, Nat2Z.inj_add.
reflexivity.
Qed.

Lemma row_count_app : forall left right,
  row_count (left ++ right) = (row_count left + row_count right)%Z.
Proof.
intros left right.
unfold row_count.
rewrite length_app, Nat2Z.inj_add.
reflexivity.
Qed.

Definition value_int64_checked z :=
  match int64_checked z with
  | Some value => Value_int64 (Some value)
  | None => Value_int64 None
  end.

Definition integral_value_as_z v :=
  match v with
  | Value_Z (Some z) => Some z
  | Value_int32 (Some z) => Some (int32_value z)
  | Value_int64 (Some z) => Some (int64_value z)
  | _ => None
  end.

Definition interp_sum_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values => Value_Z (Some (fold_left Z.add values 0%Z))
    end
  else Value_Z None.

Definition interp_sum_int32_as_int64 l :=
  if forallb is_int32_value l then
    match int32_values l with
    | nil => Value_int64 None
    | values =>
        value_int64_checked
          (fold_left
            (fun acc next => acc + int32_value next)
            values 0%Z)
    end
  else Value_int64 None.

Definition combine_nullable_state {A : Type} (op : A -> A -> A)
    (left right : option A) : option A :=
  match left, right with
  | None, state | state, None => state
  | Some x, Some y => Some (op x y)
  end.

Fixpoint fold_nullable_state {A : Type} (op : A -> A -> A)
    (values : list A) : option A :=
  match values with
  | nil => None
  | first :: rest =>
      combine_nullable_state op (Some first) (fold_nullable_state op rest)
  end.

Definition interp_bit_and_int32 l :=
  if forallb is_int32_value l then
    Value_int32 (fold_nullable_state int32_bit_and (int32_values l))
  else Value_int32 None.

Definition interp_bit_or_int32 l :=
  if forallb is_int32_value l then
    Value_int32 (fold_nullable_state int32_bit_or (int32_values l))
  else Value_int32 None.

Definition interp_bit_and_int64 l :=
  if forallb is_int64_value l then
    Value_int64 (fold_nullable_state int64_bit_and (int64_values l))
  else Value_int64 None.

Definition interp_bit_or_int64 l :=
  if forallb is_int64_value l then
    Value_int64 (fold_nullable_state int64_bit_or (int64_values l))
  else Value_int64 None.

Definition int32_avg_transition
    (state : Z * Z) (next : int32) : Z * Z :=
  let '(count, sum) := state in
  (count + 1, sum + int32_value next).

Definition int64_avg_transition
    (state : Z * Z) (next : int64) : Z * Z :=
  let '(count, sum) := state in
  (count + 1, sum + int64_value next).

(** Integral aggregate state is mathematical state, not an executor data
    structure.  Keeping the non-NULL count and sum in [Z] makes SUM/AVG
    independent of PostgreSQL's serial, parallel, or platform accumulator
    choice.  SQL result-range checks remain explicit at finalization. *)
Definition int64_sum_numeric_from_state
    (state : Z * Z) : option numeric :=
  let '(count, sum) := state in
  if count =? 0 then None else Some (numeric_of_Z sum).

Definition interp_sum_int64_as_numeric l :=
  if forallb is_int64_value l then
    Value_numeric
      (int64_sum_numeric_from_state
        (fold_left int64_avg_transition (int64_values l)
          (0%Z, 0%Z)))
  else Value_numeric None.

Definition interp_avg_int32_as_numeric l :=
  if forallb is_int32_value l then
    match int32_values l with
    | nil => Value_numeric None
    | values =>
        let '(count, sum) :=
          fold_left int32_avg_transition values
            (0%Z, 0%Z) in
        if count =? 0 then Value_numeric None else
        match numeric_div_by_Z
          (numeric_of_Z sum) count with
        | Some avg => Value_numeric (Some avg)
        | None => Value_numeric None
        end
    end
  else Value_numeric None.

Definition interp_avg_int64_as_numeric l :=
  if forallb is_int64_value l then
    match int64_values l with
    | nil => Value_numeric None
    | values =>
        let '(count, sum) :=
          fold_left int64_avg_transition values (0%Z, 0%Z) in
        if count =? 0 then Value_numeric None else
        match numeric_div_by_Z (numeric_of_Z sum) count with
        | Some avg => Value_numeric (Some avg)
        | None => Value_numeric None
        end
    end
  else Value_numeric None.

Definition integer_stats_state : Type := (Z * (Z * Z))%type.

Definition integer_stats_transition
    (state : integer_stats_state) (next : Z) : integer_stats_state :=
  let '(count, (sum, sum_squares)) := state in
  (count + 1,
   (sum + next,
    sum_squares + next * next)).

Definition interp_integer_statistic
    (values : list Z) (variance sample : bool) : value :=
  let '(count, (sum, sum_squares)) :=
    fold_left integer_stats_transition values (0%Z, (0%Z, 0%Z)) in
  match numeric_integer_statistic count sum sum_squares variance sample with
  | Some result => Value_numeric (Some result)
  | None => Value_numeric None
  end.

Definition interp_var_pop_int32 l :=
  if forallb is_int32_value l
  then interp_integer_statistic (map int32_value (int32_values l)) true false
  else Value_numeric None.

Definition interp_var_samp_int32 l :=
  if forallb is_int32_value l
  then interp_integer_statistic (map int32_value (int32_values l)) true true
  else Value_numeric None.

Definition interp_stddev_pop_int32 l :=
  if forallb is_int32_value l
  then interp_integer_statistic (map int32_value (int32_values l)) false false
  else Value_numeric None.

Definition interp_stddev_samp_int32 l :=
  if forallb is_int32_value l
  then interp_integer_statistic (map int32_value (int32_values l)) false true
  else Value_numeric None.

(** Preserve the runtime-selected display scale of AVG(int4), which is needed
    only while evaluating a following NUMERIC division.  The public SQL value
    remains [Value_numeric]; this helper does not make display scale part of
    numeric equality. *)
Definition int32_avg_numeric_with_scale
    (values : list int32) : option (numeric * Z) :=
  match values with
  | nil => None
  | _ =>
      let '(count, sum) :=
        fold_left int32_avg_transition values
          (0%Z, 0%Z) in
      if count =? 0 then None else
      let numerator := numeric_of_Z sum in
      let denominator := numeric_of_Z count in
      match numeric_pg_div_scale numerator 0 denominator 0,
            numeric_div_at_scales numerator 0 denominator 0 with
      | Some scale, Some average => Some (average, scale)
      | _, _ => None
      end
  end.

Definition int32_stddev_samp_numeric_with_scale
    (values : list int32) : option (numeric * Z) :=
  let '(count, (sum, sum_squares)) :=
    fold_left integer_stats_transition
      (map int32_value values) (0%Z, (0%Z, 0%Z)) in
  numeric_integer_stddev_samp_with_scale count sum sum_squares.

(** Runtime-selected display scale for an ordinary INTEGER NUMERIC aggregate.
    This metadata is consumed only by later scale-sensitive NUMERIC scalar
    operators; it is not a second SQL aggregate value. *)
Definition int32_numeric_aggregate_with_scale
    (aggregate : numeric_aggregate) (values : list int32)
    : option (numeric * Z) :=
  match aggregate with
  | NumericAverageInt32 => int32_avg_numeric_with_scale values
  | NumericStddevSampleInt32 =>
      int32_stddev_samp_numeric_with_scale values
  end.

Definition interp_numeric_aggregate_display_scale aggregate l :=
  if forallb is_int32_value l then
    match int32_numeric_aggregate_with_scale aggregate (int32_values l) with
    | Some (_, scale) => Value_Z (Some scale)
    | None => Value_Z None
    end
  else Value_Z None.

(** A decidable counterpart of the database-instance conformance condition
    for constrained NUMERIC values.  Equality is numeric equality: PostgreSQL
    display scale is supplied by the attribute/aggregate descriptor rather than
    stored in the ordered value carrier.  NaN conforms to NUMERIC(p,s), while
    either infinity is rejected by [numeric_cast_typmod]. *)
Definition numeric_conforms_typmod_bool
    (precision scale : Z) (number : numeric) : bool :=
  match numeric_cast_typmod number precision scale with
  | Some coerced => numeric_eqb coerced number
  | None => false
  end.

(** NUMERIC aggregate counters are logical cardinalities.  They count the
    finite and special observations exactly, independently of any executor's
    fixed-width transition representation. *)
Definition numeric_agg_total_count
    (finite_count nan_count pos_inf_count neg_inf_count : Z) : Z :=
  finite_count + nan_count + pos_inf_count + neg_inf_count.

(** The common special-value part of PostgreSQL's [numeric_sum] and
    [numeric_avg] finalizers.  Reachable counters are exact and nonnegative;
    the comparisons below directly encode NaN and mixed-infinity behavior. *)
Definition numeric_agg_special_result
    (nan_count pos_inf_count neg_inf_count : Z) : option numeric :=
  if 0 <? nan_count then Some NumericNaN
  else if andb (0 <? pos_inf_count) (0 <? neg_inf_count)
       then Some NumericNaN
  else if 0 <? pos_inf_count then Some NumericPosInfinity
  else if 0 <? neg_inf_count then Some NumericNegInfinity
  else None.

(** PostgreSQL [avg(numeric)] is modeled as one logical aggregate; it is not
    a composition of the separately observable SUM and COUNT aggregates.
    The finite sum and all cardinalities are exact.

    FormalSQL's numeric value carrier deliberately forgets display scale.  A
    fixed-scale aggregate therefore stores the exact integer coefficient of
    the finite sum.  For a schema-attested NUMERIC(p,s) input this is exactly
    [NumericSumAccum.sumX] at scale [s].  NaN and the two infinities have their
    own counters, just as in PostgreSQL's [NumericAggState]. *)
Record numeric_avg_scale_state : Type := NumericAvgScaleState {
  numeric_avg_finite_count : Z;
  numeric_avg_nan_count : Z;
  numeric_avg_pos_inf_count : Z;
  numeric_avg_neg_inf_count : Z;
  numeric_avg_sum_coeff : Z
}.

Definition numeric_avg_scale_initial : numeric_avg_scale_state :=
  NumericAvgScaleState 0 0 0 0 0.

Definition numeric_avg_scale_transition
    (input_scale : Z)
    (state : numeric_avg_scale_state) (next : numeric)
    : numeric_avg_scale_state :=
  match next with
  | NumericFinite q =>
      NumericAvgScaleState
        (numeric_avg_finite_count state + 1)
        (numeric_avg_nan_count state)
        (numeric_avg_pos_inf_count state)
        (numeric_avg_neg_inf_count state)
        (numeric_avg_sum_coeff state +
          numeric_finite_rounded_coeff q input_scale)
  | NumericNaN =>
      NumericAvgScaleState
        (numeric_avg_finite_count state)
        (numeric_avg_nan_count state + 1)
        (numeric_avg_pos_inf_count state)
        (numeric_avg_neg_inf_count state)
        (numeric_avg_sum_coeff state)
  | NumericPosInfinity =>
      NumericAvgScaleState
        (numeric_avg_finite_count state)
        (numeric_avg_nan_count state)
        (numeric_avg_pos_inf_count state + 1)
        (numeric_avg_neg_inf_count state)
        (numeric_avg_sum_coeff state)
  | NumericNegInfinity =>
      NumericAvgScaleState
        (numeric_avg_finite_count state)
        (numeric_avg_nan_count state)
        (numeric_avg_pos_inf_count state)
        (numeric_avg_neg_inf_count state + 1)
        (numeric_avg_sum_coeff state)
  end.

Definition numeric_avg_scale_total_count
    (state : numeric_avg_scale_state) : Z :=
  numeric_agg_total_count
    (numeric_avg_finite_count state)
    (numeric_avg_nan_count state)
    (numeric_avg_pos_inf_count state)
    (numeric_avg_neg_inf_count state).

Definition numeric_avg_from_scale_state
    (input_scale : Z)
    (state : numeric_avg_scale_state) : option numeric :=
  if numeric_avg_scale_total_count state =? 0 then None
  else match numeric_agg_special_result
         (numeric_avg_nan_count state)
         (numeric_avg_pos_inf_count state)
         (numeric_avg_neg_inf_count state) with
       | Some special => Some special
       | None =>
           numeric_div_at_scales
             (numeric_of_scaled (numeric_avg_sum_coeff state) input_scale)
             input_scale
             (numeric_of_Z (numeric_avg_finite_count state)) 0
       end.

(** Exact transition state for PostgreSQL [sum(numeric)].  [NumericSumAccum]
    accumulates only finite values and is not bounded by the SQL NUMERIC
    result range; the range check happens when [numeric_sum] materializes its
    result.  FormalSQL's canonical NUMERIC carrier forgets display scale, so
    its exact finite accumulator is a canonical rational. *)
Record numeric_sum_state : Type := NumericSumState {
  numeric_sum_finite_count : Z;
  numeric_sum_nan_count : Z;
  numeric_sum_pos_inf_count : Z;
  numeric_sum_neg_inf_count : Z;
  numeric_sum_finite_accumulator : Qc
}.

Definition numeric_sum_initial : numeric_sum_state :=
  NumericSumState 0 0 0 0 (Q2Qc (inject_Z 0)).

Definition numeric_sum_transition
    (state : numeric_sum_state) (next : numeric) : numeric_sum_state :=
  match next with
  | NumericFinite q =>
      NumericSumState
        (numeric_sum_finite_count state + 1)
        (numeric_sum_nan_count state)
        (numeric_sum_pos_inf_count state)
        (numeric_sum_neg_inf_count state)
        (Qcplus (numeric_sum_finite_accumulator state) q)
  | NumericNaN =>
      NumericSumState
        (numeric_sum_finite_count state)
        (numeric_sum_nan_count state + 1)
        (numeric_sum_pos_inf_count state)
        (numeric_sum_neg_inf_count state)
        (numeric_sum_finite_accumulator state)
  | NumericPosInfinity =>
      NumericSumState
        (numeric_sum_finite_count state)
        (numeric_sum_nan_count state)
        (numeric_sum_pos_inf_count state + 1)
        (numeric_sum_neg_inf_count state)
        (numeric_sum_finite_accumulator state)
  | NumericNegInfinity =>
      NumericSumState
        (numeric_sum_finite_count state)
        (numeric_sum_nan_count state)
        (numeric_sum_pos_inf_count state)
        (numeric_sum_neg_inf_count state + 1)
        (numeric_sum_finite_accumulator state)
  end.

Definition numeric_sum_total_count
    (state : numeric_sum_state) : Z :=
  numeric_agg_total_count
    (numeric_sum_finite_count state)
    (numeric_sum_nan_count state)
    (numeric_sum_pos_inf_count state)
    (numeric_sum_neg_inf_count state).

Definition numeric_sum_from_state
    (state : numeric_sum_state) : option numeric :=
  if numeric_sum_total_count state =? 0 then None
  else match numeric_agg_special_result
         (numeric_sum_nan_count state)
         (numeric_sum_pos_inf_count state)
         (numeric_sum_neg_inf_count state) with
       | Some special => Some special
       | None => Some (NumericFinite (numeric_sum_finite_accumulator state))
       end.

(** Exact PostgreSQL [stddev_samp(numeric)] for any schema-attested
    DECIMAL(precision, scale) family. NULLs are removed by [numeric_values].
    The transition retains an exact count, sumX, and sumX2 coefficient state;
    the finalizer performs PostgreSQL's division-scale choice and square-root
    rounding. Unconstrained NUMERIC remains outside this operator because its
    per-value display scale is absent from SQL numeric equality. *)
Definition interp_stddev_samp_numeric_fixed precision scale l :=
  if numeric_typmod_valid_bool precision scale &&
     forallb is_numeric_value l then
    let numbers := numeric_values l in
    if forallb (numeric_conforms_typmod_bool precision scale) numbers then
      match numeric_stddev_samp_from_scale_state scale
        (fold_left (numeric_scale_stats_transition scale) numbers
          numeric_scale_stats_initial) with
      | Some result => Value_numeric (Some result)
      | None => Value_numeric None
      end
    else Value_numeric None
  else Value_numeric None.

(** AVG for any schema-attested DECIMAL(precision, scale) family. The
    parameterized aggregate constructor delegates to this reusable fixed-
    typmod semantics. *)
Definition interp_avg_numeric_fixed precision scale l :=
  if numeric_typmod_valid_bool precision scale &&
     forallb is_numeric_value l then
    let numbers := numeric_values l in
    if forallb (numeric_conforms_typmod_bool precision scale) numbers then
      match numeric_avg_from_scale_state scale
        (fold_left
          (numeric_avg_scale_transition scale)
          numbers numeric_avg_scale_initial) with
      | Some result => Value_numeric (Some result)
      | None => Value_numeric None
      end
    else Value_numeric None
  else Value_numeric None.

(** AVG for an expression whose lowering carries exact fixed display-scale
    provenance even though its SQL result type is unconstrained NUMERIC.
    Unlike [interp_avg_numeric_fixed], no input precision is asserted here.

    This is an internal, provenance-sensitive operator: it checks that [scale]
    is a legal PostgreSQL display scale, but does not verify that every finite
    input was originally represented at exactly that scale.  That precondition
    must be established by frontend/lowering attestation.  Calling this helper
    for arbitrary unconstrained NUMERIC values is unsound, because the
    transition reconstructs each finite input's coefficient at [scale]. *)
Definition interp_avg_numeric_at_scale scale l :=
  if numeric_display_scale_valid_bool scale && forallb is_numeric_value l then
    match numeric_avg_from_scale_state scale
      (fold_left
        (numeric_avg_scale_transition scale)
        (numeric_values l) numeric_avg_scale_initial) with
    | Some result => Value_numeric (Some result)
    | None => Value_numeric None
    end
  else Value_numeric None.

Definition interp_sum_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | values => Value_float (Some (fold_left float32_add values float32_zero))
    end
  else Value_float None.

Definition interp_sum_double l :=
  if forallb is_double_value l then
    match double_values l with
    | nil => Value_double None
    | values => Value_double (Some (fold_left float64_add values float64_zero))
    end
  else Value_double None.

Definition interp_sum_numeric l :=
  if forallb is_numeric_value l then
    Value_numeric
      (numeric_sum_from_state
        (fold_left
          numeric_sum_transition
          (numeric_values l) numeric_sum_initial))
  else Value_numeric None.

Definition fold_nonempty {A : Type} (operation : A -> A -> A) (values : list A)
    : option A :=
  match values with
  | nil => None
  | first :: rest => Some (fold_left operation rest first)
  end.

Definition interp_max_z l :=
  if forallb is_z_value l then
    Value_Z (fold_nonempty Z.max (z_values l))
  else Value_Z None.

Definition interp_max_int32 l :=
  if forallb is_int32_value l then
    Value_int32 (fold_nonempty int32_maximum (int32_values l))
  else Value_int32 None.

Definition interp_max_int64 l :=
  if forallb is_int64_value l then
    Value_int64 (fold_nonempty int64_maximum (int64_values l))
  else Value_int64 None.

Definition interp_max_float l :=
  if forallb is_float_value l then
    Value_float (fold_nonempty float32_max (float_values l))
  else Value_float None.

Definition interp_max_double l :=
  if forallb is_double_value l then
    Value_double (fold_nonempty float64_max (double_values l))
  else Value_double None.

Definition interp_max_numeric l :=
  if forallb is_numeric_value l then
    Value_numeric (fold_nonempty numeric_max (numeric_values l))
  else Value_numeric None.

(** Under PostgreSQL's UTF8/C environment, text comparison is the
    lexicographic comparison of the encoded bytes.  Rocq strings are byte
    strings and [string_compare] is exactly that comparison. *)
Definition text_c_max (left right : string) : string :=
  match string_compare left right with
  | Lt => right
  | Eq | Gt => left
  end.

Definition interp_max_string l :=
  if forallb is_text_value l then
    Value_string
      (StringValue StringText (fold_nonempty text_c_max (text_values l)))
  else Value_string (StringValue StringText None).

Definition interp_min_z l :=
  if forallb is_z_value l then
    Value_Z (fold_nonempty Z.min (z_values l))
  else Value_Z None.

Definition interp_min_int32 l :=
  if forallb is_int32_value l then
    Value_int32 (fold_nonempty int32_minimum (int32_values l))
  else Value_int32 None.

Definition interp_min_int64 l :=
  if forallb is_int64_value l then
    Value_int64 (fold_nonempty int64_minimum (int64_values l))
  else Value_int64 None.

Definition interp_min_float l :=
  if forallb is_float_value l then
    Value_float (fold_nonempty float32_min (float_values l))
  else Value_float None.

Definition interp_min_double l :=
  if forallb is_double_value l then
    Value_double (fold_nonempty float64_min (double_values l))
  else Value_double None.

Definition interp_min_numeric l :=
  if forallb is_numeric_value l then
    Value_numeric (fold_nonempty numeric_min (numeric_values l))
  else Value_numeric None.

(** Calcite's [SINGLE_VALUE] is the aggregate form of scalar-subquery
    cardinality: the empty group produces a typed NULL, a singleton group
    preserves that row's value (including NULL), and a larger group raises a
    cardinality violation.  The value interpreter supplies a typed placeholder
    on the error branch; [single_value_int32_runtime_error] below makes that
    branch unobservable in the error-aware query semantics. *)
Definition interp_single_value_int32 (values : list value) : value :=
  match values with
  | nil => Value_int32 None
  | value :: nil =>
      match value with
      | Value_int32 integer => Value_int32 integer
      | _ => Value_int32 None
      end
  | _ :: _ :: _ => Value_int32 None
  end.

Definition interp_avg_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values =>
        let sum := fold_left Z.add values 0%Z in
        Value_Z (Some (Z.quot sum (Z_of_nat (List.length values))))
    end
  else Value_Z None.

(** PostgreSQL AVG over REAL and DOUBLE PRECISION uses a float8 transition
    state.  The count is itself accumulated in float8, rather than converted
    once from the final mathematical list length. *)
Definition interp_avg_float64_values (values : list float64) :=
  match values with
  | nil => Value_double None
  | _ =>
      let sum := fold_left float64_add values float64_zero in
      let count :=
        fold_left
          (fun count _ => float64_add count (float64_of_Z 1))
          values float64_zero in
      Value_double (Some (float64_div sum count))
  end.

Definition interp_avg_float l :=
  if forallb is_float_value l then
    interp_avg_float64_values (map float32_to_float64 (float_values l))
  else Value_double None.

Definition interp_avg_double l :=
  if forallb is_double_value l then
    interp_avg_float64_values (double_values l)
  else Value_double None.

Definition interp_predicate := NullPredicates.interp_predicate.

Definition bool3_to_value_bool b :=
  match b with
  | true3 => Value_bool (Some true)
  | false3 => Value_bool (Some false)
  | unknown3 => Value_bool None
  end.

Definition value_bool_to_bool3 v :=
  match v with
  | Value_bool (Some true) => true3
  | Value_bool (Some false) => false3
  | Value_bool None => unknown3
  | _ => unknown3
  end.

Definition interp_boolean_predicate p l :=
  bool3_to_value_bool (interp_predicate p l).

Definition interp_int32_binary (f : int32 -> int32 -> option int32) l :=
  match l with
  | Value_int32 (Some a1) :: Value_int32 (Some a2) :: nil =>
      match f a1 a2 with
      | Some result => Value_int32 (Some result)
      | None => Value_int32 None
      end
  | _ => Value_int32 None
  end.

Definition interp_int64_binary (f : Z -> Z -> Z) l :=
  match l with
  | v1 :: v2 :: nil =>
      match integral_value_as_z v1, integral_value_as_z v2 with
      | Some a1, Some a2 => value_int64_checked (f a1 a2)
      | _, _ => Value_int64 None
      end
  | _ => Value_int64 None
  end.

Definition interp_int64_div l :=
  match l with
  | v1 :: v2 :: nil =>
      match integral_value_as_z v1, integral_value_as_z v2 with
      | Some a1, Some a2 =>
          if Z.eqb a2 0 then Value_int64 None else value_int64_checked (Z.quot a1 a2)
      | _, _ => Value_int64 None
      end
  | _ => Value_int64 None
  end.

Definition interp_bool_and l :=
  match l with
  | v1 :: v2 :: nil =>
      bool3_to_value_bool (andb3 (value_bool_to_bool3 v1) (value_bool_to_bool3 v2))
  | _ => Value_bool None
  end.

Definition interp_bool_or l :=
  match l with
  | v1 :: v2 :: nil =>
      bool3_to_value_bool (orb3 (value_bool_to_bool3 v1) (value_bool_to_bool3 v2))
  | _ => Value_bool None
  end.

Definition interp_bool_not l :=
  match l with
  | v :: nil => bool3_to_value_bool (negb3 (value_bool_to_bool3 v))
  | _ => Value_bool None
  end.

Fixpoint interp_case_values l :=
  match l with
  | condition :: then_value :: rest =>
      match value_bool_to_bool3 condition with
      | true3 => then_value
      | false3 => interp_case_values rest
      | unknown3 => interp_case_values rest
      end
  | else_value :: nil => else_value
  | nil => Value_Z None
  end.

Definition ascii_to_upper c :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 97 n) (Nat.leb n 122)
  then ascii_of_nat (n - 32)
  else c.

Definition ascii_to_lower c :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 65 n) (Nat.leb n 90)
  then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map (f : ascii -> ascii) s :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (string_map f rest)
  end.

Definition interp_upper_string l :=
  match l with
  | Value_string (_, Some s) :: nil =>
      Value_string (StringValue StringText (Some (string_map ascii_to_upper s)))
  | Value_string (_, None) :: nil =>
      Value_string (StringValue StringText None)
  | _ => Value_string (StringValue StringText None)
  end.

Definition interp_lower_string l :=
  match l with
  | Value_string (_, Some s) :: nil =>
      Value_string (StringValue StringText (Some (string_map ascii_to_lower s)))
  | Value_string (_, None) :: nil =>
      Value_string (StringValue StringText None)
  | _ => Value_string (StringValue StringText None)
  end.

Definition interp_extract_year_date l :=
  match l with
  | Value_date (Some date) :: nil =>
      if date_is_neg_infinity_bool date
      then Value_numeric (Some NumericNegInfinity)
      else if date_is_pos_infinity_bool date
           then Value_numeric (Some NumericPosInfinity)
           else Value_numeric (Some (numeric_of_Z (date_extract_year date)))
  | Value_date None :: nil => Value_numeric None
  | _ => Value_numeric None
  end.

Definition interp_extract_month_date l :=
  match l with
  | Value_date (Some date) :: nil =>
      if date_is_infinity_bool date
      then Value_numeric None
      else Value_numeric (Some (numeric_of_Z (date_extract_month date)))
  | Value_date None :: nil => Value_numeric None
  | _ => Value_numeric None
  end.

Definition interp_cast_string_explicit l :=
  match l with
  | Value_string (source_typmod, payload) ::
    Value_Z (Some tag) :: Value_Z (Some length) :: nil =>
      match string_typmod_from_codes tag length with
      | Some target_typmod =>
          match payload with
          | Some value => Value_string
              (StringValue target_typmod
                (Some (string_cast_value source_typmod target_typmod value)))
          | None => Value_string (StringValue target_typmod None)
          end
      | None => Value_string (StringValue StringText None)
      end
  | _ => Value_string (StringValue StringText None)
  end.

(** PostgreSQL common-type coercions use the same source/target conversion
    for the unconstrained character targets admitted by the frontend.  The
    separate operator keeps implicit coercion distinct in generated syntax. *)
Definition interp_coerce_string_implicit := interp_cast_string_explicit.

Definition interp_cast_string_to_int32 l :=
  match l with
  | Value_string (source_typmod, Some input) :: nil =>
      match parse_text_int32 (string_cast_source_value source_typmod input) with
      | TextIntegerValue value => Value_int32 (Some value)
      | TextIntegerInvalid | TextIntegerOutOfRange => Value_int32 None
      end
  | Value_string (_, None) :: nil => Value_int32 None
  | _ => Value_int32 None
  end.

Definition interp_cast_string_to_int64 l :=
  match l with
  | Value_string (source_typmod, Some input) :: nil =>
      match parse_text_int64 (string_cast_source_value source_typmod input) with
      | TextIntegerValue value => Value_int64 (Some value)
      | TextIntegerInvalid | TextIntegerOutOfRange => Value_int64 None
      end
  | Value_string (_, None) :: nil => Value_int64 None
  | _ => Value_int64 None
  end.

(** PostgreSQL's [int4 -> float8] cast is total.  Every signed 32-bit
    integer is exactly representable by IEEE-754 binary64, and SQL NULL is
    preserved.  [float64_of_Z] performs the binary64 round-to-nearest-even
    conversion used by the rest of this value model. *)
Definition interp_cast_int32_to_double l :=
  match l with
  | Value_int32 (Some value) :: nil =>
      Value_double (Some (float64_of_Z (int32_value value)))
  | Value_int32 None :: nil => Value_double None
  | _ => Value_double None
  end.

(** PostgreSQL's [integer -> bigint] cast is an exact, total widening and
    preserves SQL NULL. *)
Definition interp_cast_int32_to_int64 l :=
  match l with
  | Value_int32 (Some value) :: nil =>
      Value_int64 (Some (int32_to_int64 value))
  | Value_int32 None :: nil => Value_int64 None
  | _ => Value_int64 None
  end.

(** PostgreSQL's explicit [bigint -> integer] cast is checked and preserves
    NULL.  The total interpreter returns NULL on overflow while the paired
    runtime-error classifier exposes [NumericValueOutOfRange] as the outer SQL
    outcome. *)
Definition interp_cast_int64_to_int32 l :=
  match l with
  | Value_int64 (Some value) :: nil =>
      Value_int32 (int32_checked (int64_value value))
  | Value_int64 None :: nil => Value_int32 None
  | _ => Value_int32 None
  end.

(** PostgreSQL rounds a finite NUMERIC to the nearest integer, with ties away
    from zero, before checking the signed int4 range.  The checked conversion
    deliberately returns [None] both for overflow and for special NUMERIC
    values; the paired runtime-error classifier below distinguishes those SQL
    outcomes from NULL and from one another. *)
Definition numeric_to_int32_checked (value : numeric) : option int32 :=
  match numeric_rounded_coeff value 0 with
  | Some rounded => int32_checked rounded
  | None => None
  end.

Definition interp_cast_numeric_to_int32 l :=
  match l with
  | Value_numeric (Some value) :: nil =>
      Value_int32 (numeric_to_int32_checked value)
  | Value_numeric None :: nil => Value_int32 None
  | _ => Value_int32 None
  end.

(** PostgreSQL's string concatenation operators return [text].  Converting a
    CHARACTER operand to text removes its semantically insignificant trailing
    padding before concatenation; VARCHAR and text operands retain every
    character.  The operator is strict, so one NULL argument makes the whole
    result NULL. *)
Fixpoint string_concat_payload (values : list value) : option string :=
  match values with
  | nil => Some EmptyString
  | Value_string (typmod, Some value) :: rest =>
      match string_concat_payload rest with
      | Some suffix =>
          Some (String.append (string_cast_source_value typmod value) suffix)
      | None => None
      end
  | Value_string (_, None) :: _ => None
  | _ => None
  end.

Definition interp_string_concat (values : list value) : value :=
  Value_string (StringValue StringText (string_concat_payload values)).

(** The frontend emits this operator only after proving that the source operand
    has a bounded character typmod, [start >= 1], and [count >= 0].  PostgreSQL
    first coerces CHARACTER input to text (removing trailing blank padding),
    then slices in Unicode code points.  The fallback cases preserve strict
    SQL NULL behavior; invalid integer values cannot occur in an emitted term. *)
Definition interp_substring_nonnegative (values : list value) : value :=
  match values with
  | Value_string (input_typmod, Some input) ::
    Value_int32 (Some start) :: Value_int32 (Some count) :: nil =>
      if andb (Z.leb 1 (int32_value start))
               (Z.leb 0 (int32_value count))
      then
        Value_string
          (StringValue StringText
            (Some
              (string_substring_nonnegative input_typmod input
                (Z.to_nat (Z.sub (int32_value start) 1))
                (Z.to_nat (int32_value count)))))
      else Value_string (StringValue StringText None)
  | _ => Value_string (StringValue StringText None)
  end.

Definition interp_scalar_operator f :=
  match f with
    | ScalarPredicateValue predicate => fun values =>
        interp_boolean_predicate predicate values
    | ScalarBoolean ScalarAnd => interp_bool_and
    | ScalarBoolean ScalarOr => interp_bool_or
    | ScalarBoolean ScalarNot => interp_bool_not
    | ScalarCase => interp_case_values
    | ScalarStringCase ScalarUpper => interp_upper_string
    | ScalarStringCase ScalarLower => interp_lower_string
    | ScalarExtractDate ScalarYear => interp_extract_year_date
    | ScalarExtractDate ScalarMonth => interp_extract_month_date
    | ScalarCast ScalarCastStringExplicit => interp_cast_string_explicit
    | ScalarCast ScalarCoerceStringImplicit => interp_coerce_string_implicit
    | ScalarAdd ScalarInt32 => interp_int32_binary int32_add
    | ScalarAdd ScalarInt64 => interp_int64_binary Z.add
    | ScalarAdd ScalarFloat =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float32_add a1 a2))
          | _ => Value_float None end
    | ScalarAdd ScalarDouble =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            Value_double (Some (float64_add a1 a2))
          | _ => Value_double None end
    | ScalarAdd ScalarNumeric =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_numeric (Some a2) :: nil =>
            Value_numeric (Some (numeric_add a1 a2))
          | _ => Value_numeric None end
    | ScalarMultiply ScalarInt32 => interp_int32_binary int32_mul
    | ScalarMultiply ScalarInt64 => interp_int64_binary Z.mul
    | ScalarMultiply ScalarFloat =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float32_mul a1 a2))
          | _ => Value_float None end
    | ScalarMultiply ScalarDouble =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            Value_double (Some (float64_mul a1 a2))
          | _ => Value_double None end
    | ScalarDivide ScalarFloat =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float32_div a1 a2))
          | _ => Value_float None end
    | ScalarDivide ScalarDouble =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            Value_double (Some (float64_div a1 a2))
          | _ => Value_double None end
    | ScalarDivide ScalarInt32 => interp_int32_binary int32_div
    | ScalarDivide ScalarInt64 => interp_int64_div
    | ScalarMultiply ScalarNumeric =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_numeric (Some a2) :: nil =>
            Value_numeric (Some (numeric_mul a1 a2))
          | _ => Value_numeric None end
    | ScalarDivide ScalarNumeric =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_Z (Some scale1) ::
            Value_numeric (Some a2) :: Value_Z (Some scale2) :: nil =>
            match numeric_div_at_scales a1 scale1 a2 scale2 with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarNumericDivideResultScale =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_Z (Some scale1) ::
            Value_numeric (Some a2) :: Value_Z (Some scale2) :: nil =>
            Value_Z (numeric_div_result_dscale a1 scale1 a2 scale2)
          | _ => Value_Z None end
    | ScalarNumericDivideTypmod =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_Z (Some scale1) ::
            Value_numeric (Some a2) :: Value_Z (Some scale2) ::
            Value_Z (Some result_precision) :: Value_Z (Some result_scale) :: nil =>
            match numeric_div_with_typmod
              a1 scale1 a2 scale2 result_precision result_scale with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumericTypmod ScalarSourceNumeric) =>
      fun l =>
        match l with
          | Value_numeric (Some d) ::
            Value_Z (Some result_precision) :: Value_Z (Some result_scale) :: nil =>
            match numeric_cast_typmod d result_precision result_scale with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumeric ScalarSourceNumeric) =>
      fun l =>
        match l with
          | Value_numeric value :: nil => Value_numeric value
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumeric ScalarSourceZ) =>
      fun l =>
        match l with
          | Value_Z (Some z) :: nil => Value_numeric (Some (numeric_of_Z z))
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumeric ScalarSourceInt32) =>
      fun l =>
        match l with
          | Value_int32 (Some z) :: nil =>
            Value_numeric (Some (numeric_of_Z (int32_value z)))
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumeric ScalarSourceInt64) =>
      fun l =>
        match l with
          | Value_int64 (Some z) :: nil =>
            Value_numeric (Some (numeric_of_Z (int64_value z)))
          | _ => Value_numeric None end
    | ScalarCast ScalarCastInt32ToDouble => interp_cast_int32_to_double
    | ScalarCast ScalarCastInt32ToInt64 => interp_cast_int32_to_int64
    | ScalarCast ScalarCastInt64ToInt32 => interp_cast_int64_to_int32
    | ScalarCast ScalarCastNumericToInt32 => interp_cast_numeric_to_int32
    | ScalarCast ScalarCastStringToInt32 => interp_cast_string_to_int32
    | ScalarCast ScalarCastStringToInt64 => interp_cast_string_to_int64
    | ScalarStringConcat => interp_string_concat
    | ScalarSubstringNonnegative => interp_substring_nonnegative
    | ScalarCast (ScalarCastToNumericTypmod ScalarSourceZ) =>
      fun l =>
        match l with
          | Value_Z (Some z) ::
            Value_Z (Some result_precision) :: Value_Z (Some result_scale) :: nil =>
            match numeric_cast_typmod
              (numeric_of_Z z) result_precision result_scale with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumericTypmod ScalarSourceInt32) =>
      fun l =>
        match l with
          | Value_int32 (Some z) ::
            Value_Z (Some result_precision) :: Value_Z (Some result_scale) :: nil =>
            match numeric_cast_typmod
              (numeric_of_Z (int32_value z)) result_precision result_scale with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarCast (ScalarCastToNumericTypmod ScalarSourceInt64) =>
      fun l =>
        match l with
          | Value_int64 (Some z) ::
            Value_Z (Some result_precision) :: Value_Z (Some result_scale) :: nil =>
            match numeric_cast_typmod
              (numeric_of_Z (int64_value z)) result_precision result_scale with
            | Some result => Value_numeric (Some result)
            | None => Value_numeric None
            end
          | _ => Value_numeric None end
    | ScalarSubtract ScalarInt32 => interp_int32_binary int32_sub
    | ScalarSubtract ScalarInt64 => interp_int64_binary Z.sub
    | ScalarSubtract ScalarFloat =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float32_sub a1 a2))
          | _ => Value_float None end
    | ScalarSubtract ScalarDouble =>
      fun l =>
        match l with
          | Value_double (Some a1) :: Value_double (Some a2) :: nil =>
            Value_double (Some (float64_sub a1 a2))
          | _ => Value_double None end
    | ScalarSubtract ScalarNumeric =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: Value_numeric (Some a2) :: nil =>
            Value_numeric (Some (numeric_sub a1 a2))
          | _ => Value_numeric None end
    | ScalarTimestampAdd ScalarTimestampMicrosecond =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some micros) :: nil =>
            Value_timestamp (timestamp_add_microseconds_checked t micros)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampSecond =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some seconds) :: nil =>
            Value_timestamp (timestamp_add_seconds_checked t seconds)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampMinute =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some minutes) :: nil =>
            Value_timestamp (timestamp_add_minutes_checked t minutes)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampHour =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some hours) :: nil =>
            Value_timestamp (timestamp_add_hours_checked t hours)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampDay =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some days) :: nil =>
            Value_timestamp (timestamp_add_days_checked t days)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampMonth =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some months) :: nil =>
            Value_timestamp (timestamp_add_months_checked t months)
          | _ => Value_timestamp None end
    | ScalarTimestampAdd ScalarTimestampYear =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some years) :: nil =>
            Value_timestamp (timestamp_add_years_checked t years)
          | _ => Value_timestamp None end
    | ScalarCast ScalarCastIdentity =>
      fun l =>
        match l with
          | v :: nil => v
          | _ => Value_string (StringValue StringText None) end
    | ScalarCast ScalarCastDateToTimestamp =>
      fun l =>
        match l with
          | Value_date (Some d) :: nil =>
            Value_timestamp (cast_date_to_timestamp_checked d)
          | _ => Value_timestamp None end
    | ScalarCast ScalarCastTimestampToDate =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: nil =>
            Value_date (cast_timestamp_to_date_checked t)
          | _ => Value_date None end
    | ScalarNegate ScalarInt32 =>
      fun l =>
        match l with
          | Value_int32 (Some a1) :: nil =>
            match int32_opp a1 with
            | Some result => Value_int32 (Some result)
            | None => Value_int32 None
            end
          | _ => Value_int32 None end
    | ScalarNegate ScalarInt64 =>
      fun l =>
        match l with
          | v :: nil =>
            match integral_value_as_z v with
            | Some z => value_int64_checked (- z)
            | None => Value_int64 None
            end
          | _ => Value_int64 None end
    | ScalarNegate ScalarFloat =>
      fun l =>
        match l with
          | Value_float (Some a1) :: nil =>
            Value_float (Some (float32_opp a1))
          | _ => Value_float None end
    | ScalarNegate ScalarDouble =>
      fun l =>
        match l with
          | Value_double (Some a1) :: nil =>
            Value_double (Some (float64_opp a1))
          | _ => Value_double None end
    | ScalarNegate ScalarNumeric =>
      fun l =>
        match l with
          | Value_numeric (Some a1) :: nil =>
            Value_numeric (Some (numeric_opp a1))
          | _ => Value_numeric None end
  end.

Fixpoint distinct_values l :=
  match l with
    | nil => nil
    | v :: l' =>
      if Oset.mem_bool OVal v l'
      then distinct_values l'
      else v :: distinct_values l'
  end.

(** DISTINCT is evaluated by deduplicating the aggregate input before both
    value computation and local runtime-error classification. *)
Definition aggregate_input_values
    (quantifier : ValueCore.aggregate_quantifier)
    (values : list value) : list value :=
  match quantifier with
  | ValueCore.AggregateAll => values
  | ValueCore.AggregateDistinct => distinct_values values
  end.

Definition interp_aggregate_function
    (function : aggregate_function) (values : list value) :=
  match function with
  | AggregateCount => value_int64_checked (non_null_count values)
  | AggregateSumZ => interp_sum_z values
  | AggregateSumInt32 => interp_sum_int32_as_int64 values
  | AggregateSumInt64Numeric => interp_sum_int64_as_numeric values
  | AggregateSumFloat => interp_sum_float values
  | AggregateSumDouble => interp_sum_double values
  | AggregateSumNumeric => interp_sum_numeric values
  | AggregateBitAndInt32 => interp_bit_and_int32 values
  | AggregateBitOrInt32 => interp_bit_or_int32 values
  | AggregateBitAndInt64 => interp_bit_and_int64 values
  | AggregateBitOrInt64 => interp_bit_or_int64 values
  | AggregateMaxZ => interp_max_z values
  | AggregateMaxInt32 => interp_max_int32 values
  | AggregateMaxInt64 => interp_max_int64 values
  | AggregateMaxFloat => interp_max_float values
  | AggregateMaxDouble => interp_max_double values
  | AggregateMaxNumeric => interp_max_numeric values
  | AggregateMaxString => interp_max_string values
  | AggregateMinZ => interp_min_z values
  | AggregateMinInt32 => interp_min_int32 values
  | AggregateMinInt64 => interp_min_int64 values
  | AggregateMinFloat => interp_min_float values
  | AggregateMinDouble => interp_min_double values
  | AggregateMinNumeric => interp_min_numeric values
  | AggregateSingleValueInt32 => interp_single_value_int32 values
  | AggregateAverageZ => interp_avg_z values
  | AggregateAverageInt32Numeric => interp_avg_int32_as_numeric values
  | AggregateNumericDisplayScale aggregate =>
      interp_numeric_aggregate_display_scale aggregate values
  | AggregateAverageInt64Numeric => interp_avg_int64_as_numeric values
  | AggregateVariancePopulationInt32 => interp_var_pop_int32 values
  | AggregateVarianceSampleInt32 => interp_var_samp_int32 values
  | AggregateStddevPopulationInt32 => interp_stddev_pop_int32 values
  | AggregateStddevSampleInt32 => interp_stddev_samp_int32 values
  | AggregateStddevSampleNumericFixed precision scale =>
      interp_stddev_samp_numeric_fixed precision scale values
  | AggregateAverageFloat => interp_avg_float values
  | AggregateAverageDouble => interp_avg_double values
  | AggregateAverageNumericFixed precision scale =>
      interp_avg_numeric_fixed precision scale values
  | AggregateAverageNumericAtScale scale =>
      interp_avg_numeric_at_scale scale values
  end.

Definition interp_aggregate (call : aggregate) (values : list value) :=
  match call with
  | AggregateCall function quantifier =>
      interp_aggregate_function function
        (aggregate_input_values quantifier values)
  | AggregateCountStar => value_int64_checked (row_count values)
  end.

(** Runtime-error classification for the error-aware SQL evaluator. *)

Definition numeric_value_out_of_range : option sql_runtime_error :=
  Some (DataException NumericValueOutOfRange).

Definition invalid_text_representation : option sql_runtime_error :=
  Some (DataException InvalidTextRepresentation).

Definition cast_string_to_int32_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_string (source_typmod, Some input) :: nil =>
      match parse_text_int32 (string_cast_source_value source_typmod input) with
      | TextIntegerValue _ => None
      | TextIntegerInvalid => invalid_text_representation
      | TextIntegerOutOfRange => numeric_value_out_of_range
      end
  | _ => None
  end.

Definition cast_string_to_int64_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_string (source_typmod, Some input) :: nil =>
      match parse_text_int64 (string_cast_source_value source_typmod input) with
      | TextIntegerValue _ => None
      | TextIntegerInvalid => invalid_text_representation
      | TextIntegerOutOfRange => numeric_value_out_of_range
      end
  | _ => None
  end.

Definition division_by_zero : option sql_runtime_error :=
  Some (DataException DivisionByZero).

Definition datetime_field_overflow : option sql_runtime_error :=
  Some (DataException DatetimeFieldOverflow).

Fixpoint first_observation_error
    (observations : list (option sql_runtime_error * value))
    : option sql_runtime_error :=
  match observations with
  | nil => None
  | (Some error, _) :: _ => Some error
  | (None, _) :: rest => first_observation_error rest
  end.

Definition observation_values
    (observations : list (option sql_runtime_error * value)) : list value :=
  map snd observations.

Lemma observation_values_app : forall left right,
  observation_values (left ++ right) =
    List.app (observation_values left) (observation_values right).
Proof.
intros left right.
unfold observation_values.
apply map_app.
Qed.

Definition int32_binary_runtime_error
    (operation : int32 -> int32 -> option int32) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_int32 (Some lhs) :: Value_int32 (Some rhs) :: nil =>
      match operation lhs rhs with
      | Some _ => None
      | None => numeric_value_out_of_range
      end
  | _ => None
  end.

Definition int32_div_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_int32 (Some lhs) :: Value_int32 (Some rhs) :: nil =>
      if Z.eqb (int32_value rhs) 0
      then division_by_zero
      else
        match int32_div lhs rhs with
        | Some _ => None
        | None => numeric_value_out_of_range
        end
  | _ => None
  end.

Definition int64_binary_runtime_error
    (operation : Z -> Z -> Z) (values : list value)
    : option sql_runtime_error :=
  match values with
  | lhs :: rhs :: nil =>
      match integral_value_as_z lhs, integral_value_as_z rhs with
      | Some lhs, Some rhs =>
          match int64_checked (operation lhs rhs) with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | _, _ => None
      end
  | _ => None
  end.

Definition int64_div_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | lhs :: rhs :: nil =>
      match integral_value_as_z lhs, integral_value_as_z rhs with
      | Some lhs, Some rhs =>
          if Z.eqb rhs 0
          then division_by_zero
          else
            match int64_checked (Z.quot lhs rhs) with
            | Some _ => None
            | None => numeric_value_out_of_range
            end
      | _, _ => None
      end
  | _ => None
  end.

Definition int32_opp_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_int32 (Some value) :: nil =>
      match int32_opp value with
      | Some _ => None
      | None => numeric_value_out_of_range
      end
  | _ => None
  end.

Definition int64_opp_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | value :: nil =>
      match integral_value_as_z value with
      | Some value =>
          match int64_checked (- value) with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | None => None
      end
  | _ => None
  end.

(** These checks mirror PostgreSQL's float4/float8 arithmetic guards. *)
Definition float32_add_runtime_error
    (operation : float32 -> float32 -> float32) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_float (Some lhs) :: Value_float (Some rhs) :: nil =>
      let result := operation lhs rhs in
      if andb (float32_is_infinite result)
              (andb (negb (float32_is_infinite lhs))
                    (negb (float32_is_infinite rhs)))
      then numeric_value_out_of_range
      else None
  | _ => None
  end.

Definition float64_add_runtime_error
    (operation : float64 -> float64 -> float64) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_double (Some lhs) :: Value_double (Some rhs) :: nil =>
      let result := operation lhs rhs in
      if andb (float64_is_infinite result)
              (andb (negb (float64_is_infinite lhs))
                    (negb (float64_is_infinite rhs)))
      then numeric_value_out_of_range
      else None
  | _ => None
  end.

Definition float32_mul_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_float (Some lhs) :: Value_float (Some rhs) :: nil =>
      let result := float32_mul lhs rhs in
      if andb (float32_is_infinite result)
              (andb (negb (float32_is_infinite lhs))
                    (negb (float32_is_infinite rhs)))
      then numeric_value_out_of_range
      else if andb (float32_is_zero result)
                      (andb (negb (float32_is_zero lhs))
                            (negb (float32_is_zero rhs)))
           then numeric_value_out_of_range
           else None
  | _ => None
  end.

Definition float64_mul_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_double (Some lhs) :: Value_double (Some rhs) :: nil =>
      let result := float64_mul lhs rhs in
      if andb (float64_is_infinite result)
              (andb (negb (float64_is_infinite lhs))
                    (negb (float64_is_infinite rhs)))
      then numeric_value_out_of_range
      else if andb (float64_is_zero result)
                      (andb (negb (float64_is_zero lhs))
                            (negb (float64_is_zero rhs)))
           then numeric_value_out_of_range
           else None
  | _ => None
  end.

Definition float32_div_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_float (Some lhs) :: Value_float (Some rhs) :: nil =>
      if andb (float32_is_zero rhs) (negb (float32_is_nan lhs))
      then division_by_zero
      else
        let result := float32_div lhs rhs in
        if andb (float32_is_infinite result)
                (negb (float32_is_infinite lhs))
        then numeric_value_out_of_range
        else if andb (float32_is_zero result)
                        (andb (negb (float32_is_zero lhs))
                              (negb (float32_is_infinite rhs)))
             then numeric_value_out_of_range
             else None
  | _ => None
  end.

Definition float64_div_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_double (Some lhs) :: Value_double (Some rhs) :: nil =>
      if andb (float64_is_zero rhs) (negb (float64_is_nan lhs))
      then division_by_zero
      else
        let result := float64_div lhs rhs in
        if andb (float64_is_infinite result)
                (negb (float64_is_infinite lhs))
        then numeric_value_out_of_range
        else if andb (float64_is_zero result)
                        (andb (negb (float64_is_zero lhs))
                              (negb (float64_is_infinite rhs)))
             then numeric_value_out_of_range
             else None
  | _ => None
  end.

Definition numeric_result_runtime_error (result : numeric)
    : option sql_runtime_error :=
  if numeric_runtime_fits_bool result then None else numeric_value_out_of_range.

Definition numeric_binary_runtime_error
    (operation : numeric -> numeric -> numeric) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_numeric (Some lhs) :: Value_numeric (Some rhs) :: nil =>
      numeric_result_runtime_error (operation lhs rhs)
  | _ => None
  end.

Definition numeric_unary_runtime_error
    (operation : numeric -> numeric) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_numeric (Some input) :: nil =>
      numeric_result_runtime_error (operation input)
  | _ => None
  end.

Definition numeric_div_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_numeric (Some lhs) :: Value_Z (Some left_scale) ::
    Value_numeric (Some rhs) :: Value_Z (Some right_scale) :: nil =>
      if orb (numeric_is_nan lhs) (numeric_is_nan rhs)
      then None
      else if numeric_eqb rhs numeric_zero
      then division_by_zero
      else if andb (numeric_display_scale_valid_bool left_scale)
                      (numeric_display_scale_valid_bool right_scale)
           then
             match numeric_div_at_scales lhs left_scale rhs right_scale with
             | Some result => numeric_result_runtime_error result
             | None => numeric_value_out_of_range
             end
           else numeric_value_out_of_range
  | _ => None
  end.

Definition numeric_typmod_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_numeric (Some value) ::
    Value_Z (Some precision) :: Value_Z (Some scale) :: nil =>
      match numeric_cast_typmod value precision scale with
      | Some _ => None
      | None => numeric_value_out_of_range
      end
  | _ => None
  end.

Definition numeric_div_typmod_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_numeric (Some lhs) :: Value_Z (Some left_scale) ::
    Value_numeric (Some rhs) :: Value_Z (Some right_scale) ::
    Value_Z (Some precision) :: Value_Z (Some scale) :: nil =>
      if orb (numeric_is_nan lhs) (numeric_is_nan rhs)
      then None
      else if numeric_eqb rhs numeric_zero
      then division_by_zero
      else if andb (numeric_display_scale_valid_bool left_scale)
                      (numeric_display_scale_valid_bool right_scale)
      then
        match numeric_div_with_typmod
          lhs left_scale rhs right_scale precision scale with
        | Some _ => None
        | None => numeric_value_out_of_range
        end
      else numeric_value_out_of_range
  | _ => None
  end.

Definition timestamp_binary_runtime_error
    (operation : Z -> Z -> option Z) (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_timestamp (Some timestamp) :: Value_Z (Some amount) :: nil =>
      match operation timestamp amount with
      | Some _ => None
      | None => datetime_field_overflow
      end
  | _ => None
  end.

Definition cast_date_to_timestamp_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_date (Some date) :: nil =>
      match cast_date_to_timestamp_checked date with
      | Some _ => None
      | None => datetime_field_overflow
      end
  | _ => None
  end.

Definition cast_timestamp_to_date_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | Value_timestamp (Some timestamp) :: nil =>
      match cast_timestamp_to_date_checked timestamp with
      | Some _ => None
      | None => datetime_field_overflow
      end
  | _ => None
  end.

Definition scalar_operator_local_runtime_error
    (function : ValueCore.scalar_operator) (values : list value)
    : option sql_runtime_error :=
  match function with
  | ScalarAdd ScalarInt32 => int32_binary_runtime_error int32_add values
  | ScalarSubtract ScalarInt32 => int32_binary_runtime_error int32_sub values
  | ScalarMultiply ScalarInt32 => int32_binary_runtime_error int32_mul values
  | ScalarDivide ScalarInt32 => int32_div_runtime_error values
  | ScalarNegate ScalarInt32 => int32_opp_runtime_error values
  | ScalarAdd ScalarInt64 => int64_binary_runtime_error Z.add values
  | ScalarSubtract ScalarInt64 => int64_binary_runtime_error Z.sub values
  | ScalarMultiply ScalarInt64 => int64_binary_runtime_error Z.mul values
  | ScalarDivide ScalarInt64 => int64_div_runtime_error values
  | ScalarNegate ScalarInt64 => int64_opp_runtime_error values
  | ScalarAdd ScalarFloat => float32_add_runtime_error float32_add values
  | ScalarSubtract ScalarFloat => float32_add_runtime_error float32_sub values
  | ScalarMultiply ScalarFloat => float32_mul_runtime_error values
  | ScalarDivide ScalarFloat => float32_div_runtime_error values
  | ScalarAdd ScalarDouble => float64_add_runtime_error float64_add values
  | ScalarSubtract ScalarDouble => float64_add_runtime_error float64_sub values
  | ScalarMultiply ScalarDouble => float64_mul_runtime_error values
  | ScalarDivide ScalarDouble => float64_div_runtime_error values
  | ScalarAdd ScalarNumeric => numeric_binary_runtime_error numeric_add values
  | ScalarSubtract ScalarNumeric => numeric_binary_runtime_error numeric_sub values
  | ScalarMultiply ScalarNumeric => numeric_binary_runtime_error numeric_mul values
  | ScalarNegate ScalarNumeric => numeric_unary_runtime_error numeric_opp values
  | ScalarDivide ScalarNumeric => numeric_div_runtime_error values
  | ScalarNumericDivideResultScale => numeric_div_runtime_error values
  | ScalarNumericDivideTypmod => numeric_div_typmod_runtime_error values
  | ScalarCast (ScalarCastToNumericTypmod ScalarSourceNumeric) => numeric_typmod_runtime_error values
  | ScalarCast (ScalarCastToNumericTypmod ScalarSourceZ) =>
      match values with
      | Value_Z (Some value) ::
        Value_Z (Some precision) :: Value_Z (Some scale) :: nil =>
          match numeric_cast_typmod (numeric_of_Z value) precision scale with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | _ => None
      end
  | ScalarCast (ScalarCastToNumericTypmod ScalarSourceInt32) =>
      match values with
      | Value_int32 (Some value) ::
        Value_Z (Some precision) :: Value_Z (Some scale) :: nil =>
          match numeric_cast_typmod
            (numeric_of_Z (int32_value value)) precision scale with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | _ => None
      end
  | ScalarCast (ScalarCastToNumericTypmod ScalarSourceInt64) =>
      match values with
      | Value_int64 (Some value) ::
        Value_Z (Some precision) :: Value_Z (Some scale) :: nil =>
          match numeric_cast_typmod
            (numeric_of_Z (int64_value value)) precision scale with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | _ => None
      end
  | ScalarCast ScalarCastInt32ToDouble => None
  | ScalarCast ScalarCastInt32ToInt64 => None
  | ScalarCast ScalarCastInt64ToInt32 =>
      match values with
      | Value_int64 (Some value) :: nil =>
          match int32_checked (int64_value value) with
          | Some _ => None
          | None => numeric_value_out_of_range
          end
      | _ => None
      end
  | ScalarCast ScalarCastNumericToInt32 =>
      match values with
      | Value_numeric (Some value) :: nil =>
          match value with
          | NumericFinite _ =>
              match numeric_to_int32_checked value with
              | Some _ => None
              | None => numeric_value_out_of_range
              end
          | NumericNegInfinity | NumericPosInfinity | NumericNaN =>
              Some FeatureNotSupported
          end
      | _ => None
      end
  | ScalarCast ScalarCastStringToInt32 =>
      cast_string_to_int32_runtime_error values
  | ScalarCast ScalarCastStringToInt64 =>
      cast_string_to_int64_runtime_error values
  | ScalarTimestampAdd ScalarTimestampMicrosecond =>
      timestamp_binary_runtime_error timestamp_add_microseconds_checked values
  | ScalarTimestampAdd ScalarTimestampSecond =>
      timestamp_binary_runtime_error timestamp_add_seconds_checked values
  | ScalarTimestampAdd ScalarTimestampMinute =>
      timestamp_binary_runtime_error timestamp_add_minutes_checked values
  | ScalarTimestampAdd ScalarTimestampHour =>
      timestamp_binary_runtime_error timestamp_add_hours_checked values
  | ScalarTimestampAdd ScalarTimestampDay =>
      timestamp_binary_runtime_error timestamp_add_days_checked values
  | ScalarTimestampAdd ScalarTimestampMonth =>
      timestamp_binary_runtime_error timestamp_add_months_checked values
  | ScalarTimestampAdd ScalarTimestampYear =>
      timestamp_binary_runtime_error timestamp_add_years_checked values
  | ScalarCast ScalarCastDateToTimestamp =>
      cast_date_to_timestamp_runtime_error values
  | ScalarCast ScalarCastTimestampToDate =>
      cast_timestamp_to_date_runtime_error values
  | ScalarPredicateValue _
  | ScalarBoolean ScalarAnd
  | ScalarBoolean ScalarOr
  | ScalarBoolean ScalarNot
  | ScalarCase
  | ScalarStringCase ScalarUpper
  | ScalarStringCase ScalarLower
  | ScalarExtractDate ScalarYear
  | ScalarExtractDate ScalarMonth
  | ScalarCast ScalarCastStringExplicit
  | ScalarCast ScalarCoerceStringImplicit
  | ScalarCast (ScalarCastToNumeric ScalarSourceNumeric)
  | ScalarCast (ScalarCastToNumeric ScalarSourceZ)
  | ScalarCast (ScalarCastToNumeric ScalarSourceInt32)
  | ScalarCast (ScalarCastToNumeric ScalarSourceInt64)
  | ScalarStringConcat
  | ScalarSubstringNonnegative
  | ScalarCast ScalarCastIdentity
  | ScalarNegate ScalarFloat
  | ScalarNegate ScalarDouble => None
  end.

(** CASE evaluates conditions in order and only evaluates the selected arm. *)
Fixpoint case_runtime_error
    (observations : list (option sql_runtime_error * value))
    : option sql_runtime_error :=
  match observations with
  | (condition_error, condition) :: (then_error, _) :: rest =>
      match condition_error with
      | Some error => Some error
      | None =>
          match value_bool_to_bool3 condition with
          | true3 => then_error
          | false3 | unknown3 => case_runtime_error rest
          end
      end
  | (else_error, _) :: nil => else_error
  | _ => None
  end.

Definition interp_scalar_operator_runtime_error
    (function : ValueCore.scalar_operator)
    (observations : list (option sql_runtime_error * value))
    : option sql_runtime_error :=
  match function with
  | ScalarCase => case_runtime_error observations
  | _ =>
      match first_observation_error observations with
      | Some error => Some error
      | None => scalar_operator_local_runtime_error function (observation_values observations)
      end
  end.

Definition int64_result_runtime_error (value : Z) : option sql_runtime_error :=
  match int64_checked value with
  | Some _ => None
  | None => numeric_value_out_of_range
  end.

Definition count_runtime_error (values : list value) : option sql_runtime_error :=
  int64_result_runtime_error (row_count values).

Definition non_null_count_runtime_error (values : list value)
    : option sql_runtime_error :=
  int64_result_runtime_error (non_null_count values).

Definition sum_int32_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_int32_value values then
    match int32_values values with
    | nil => None
    | integers =>
        int64_result_runtime_error
          (fold_left
            (fun acc next => acc + int32_value next)
            integers 0%Z)
    end
  else None.

Fixpoint float32_sum_runtime_error_from
    (accumulator : float32) (values : list float32)
    : option sql_runtime_error :=
  match values with
  | nil => None
  | value :: rest =>
      match float32_add_runtime_error float32_add
        (Value_float (Some accumulator) :: Value_float (Some value) :: nil) with
      | Some error => Some error
      | None => float32_sum_runtime_error_from
                  (float32_add accumulator value) rest
      end
  end.

Fixpoint float64_sum_runtime_error_from
    (accumulator : float64) (values : list float64)
    : option sql_runtime_error :=
  match values with
  | nil => None
  | value :: rest =>
      match float64_add_runtime_error float64_add
        (Value_double (Some accumulator) :: Value_double (Some value) :: nil) with
      | Some error => Some error
      | None => float64_sum_runtime_error_from
                  (float64_add accumulator value) rest
      end
  end.

Definition sum_float_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_float_value values
  then float32_sum_runtime_error_from float32_zero (float_values values)
  else None.

Definition sum_double_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_double_value values
  then float64_sum_runtime_error_from float64_zero (double_values values)
  else None.

(** PostgreSQL AVG(REAL/float4) and AVG(float8) use the Youngs-Cramer
    [float4_accum]/[float8_accum]
    transition with state (N, Sx, Sxx), even though its final function reads
    only N and Sx.  A finite input can overflow the Sxx transition after Sx
    has cancelled back to a finite value, so checking only the final sum is
    unsound.  This follows src/backend/utils/adt/float.c in PostgreSQL. *)
Fixpoint float64_avg_accum_runtime_error_from
    (count sum sum_squares : float64)
    (has_value : bool)
    (values : list float64) : option sql_runtime_error :=
  match values with
  | nil => None
  | value :: rest =>
      let next_count := float64_add count (float64_of_Z 1) in
      let next_sum := float64_add sum value in
      if has_value then
        let temporary := float64_sub (float64_mul value next_count) next_sum in
        let next_sum_squares :=
          float64_add sum_squares
            (float64_div
              (float64_mul temporary temporary)
              (float64_mul next_count count)) in
        if orb (float64_is_infinite next_sum)
               (float64_is_infinite next_sum_squares)
        then
          if andb (negb (float64_is_infinite sum))
                  (negb (float64_is_infinite value))
          then numeric_value_out_of_range
          else float64_avg_accum_runtime_error_from
                 next_count next_sum Float64NaN true rest
        else float64_avg_accum_runtime_error_from
               next_count next_sum next_sum_squares true rest
      else
        let next_sum_squares :=
          if orb (float64_is_nan value) (float64_is_infinite value)
          then Float64NaN
          else sum_squares in
        float64_avg_accum_runtime_error_from
          next_count next_sum next_sum_squares true rest
  end.

Definition avg_float_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_float_value values
  then float64_avg_accum_runtime_error_from
         float64_zero float64_zero float64_zero false
         (map float32_to_float64 (float_values values))
  else None.

Definition avg_double_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_double_value values
  then float64_avg_accum_runtime_error_from
         float64_zero float64_zero float64_zero false (double_values values)
  else None.

Definition int64_sum_numeric_state_runtime_error
    (state : Z * Z) : option sql_runtime_error :=
  match int64_sum_numeric_from_state state with
  | None => None
  | Some result => numeric_result_runtime_error result
  end.

Definition sum_int64_numeric_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_int64_value values then
    int64_sum_numeric_state_runtime_error
      (fold_left int64_avg_transition (int64_values values)
        (0%Z, 0%Z))
  else None.

Definition numeric_sum_state_runtime_error
    (state : numeric_sum_state)
    : option sql_runtime_error :=
  match numeric_sum_from_state state with
  | None => None
  | Some result => numeric_result_runtime_error result
  end.

Definition sum_numeric_runtime_error (values : list value)
    : option sql_runtime_error :=
  if forallb is_numeric_value values then
    numeric_sum_state_runtime_error
      (fold_left
        numeric_sum_transition
        (numeric_values values) numeric_sum_initial)
  else None.

(** [do_numeric_accum] does not materialize a SQL NUMERIC result and its
    fixed-scale sum/count transition cannot raise a data exception.  Keeping
    this classifier separate prevents a caller from reusing SUM's eager
    result-range check or COUNT's checked-result behavior. *)
Definition numeric_avg_scale_transition_runtime_error
    (_input_scale : Z) (_state : numeric_avg_scale_state) (_next : numeric)
    : option sql_runtime_error := None.

Definition numeric_avg_scale_state_runtime_error
    (input_scale : Z)
    (state : numeric_avg_scale_state) : option sql_runtime_error :=
  if numeric_avg_scale_total_count state =? 0 then None
  else match numeric_agg_special_result
         (numeric_avg_nan_count state)
         (numeric_avg_pos_inf_count state)
         (numeric_avg_neg_inf_count state) with
       | Some _ => None
       | None =>
           let sum :=
             numeric_of_scaled (numeric_avg_sum_coeff state) input_scale in
           numeric_div_runtime_error
             (Value_numeric (Some sum) :: Value_Z (Some input_scale) ::
              Value_numeric
                (Some (numeric_of_Z
                  (numeric_avg_finite_count state))) ::
              Value_Z (Some 0) :: nil)
       end.

(** Runtime-error counterpart of [interp_avg_numeric_fixed].  It remains a
    reusable declarative helper and is not exposed as an aggregate constructor. *)
Definition avg_numeric_fixed_runtime_error precision scale
    (values : list value)
    : option sql_runtime_error :=
  if numeric_typmod_valid_bool precision scale &&
     forallb is_numeric_value values then
    let numbers := numeric_values values in
    if forallb (numeric_conforms_typmod_bool precision scale) numbers then
      numeric_avg_scale_state_runtime_error scale
        (fold_left
          (numeric_avg_scale_transition scale)
          numbers numeric_avg_scale_initial)
    else None
  else None.

Definition avg_numeric_at_scale_runtime_error scale (values : list value)
    : option sql_runtime_error :=
  if numeric_display_scale_valid_bool scale && forallb is_numeric_value values then
    numeric_avg_scale_state_runtime_error scale
      (fold_left
        (numeric_avg_scale_transition scale)
        (numeric_values values) numeric_avg_scale_initial)
  else None.

Definition avg_int32_numeric_runtime_error (values : list value)
    : option sql_runtime_error :=
  None.

Definition numeric_aggregate_display_scale_runtime_error
    (aggregate : numeric_aggregate) (values : list value)
    : option sql_runtime_error :=
  None.

Definition avg_int64_numeric_runtime_error (values : list value)
    : option sql_runtime_error :=
  None.

(** An INTEGER statistic is bounded by the mathematical input range, not by
    an executor transition width: variance is at most the square of the
    INT32 range and standard deviation at most that range.  Both fit
    PostgreSQL NUMERIC, so exact logical aggregation has no local range error. *)
Definition integer_statistic_runtime_error (values : list value)
    : option sql_runtime_error := None.

(** For well-typed DECIMAL(precision, scale) observations, every transition is exact and
    the final standard deviation is bounded by the finite input range.  Keep
    the result-limit check explicit so malformed direct uses of the internal
    aggregate descriptor cannot silently erase PostgreSQL NUMERIC overflow.  A
    constrained input outside its declared typmod is ruled out by schema conformance,
    and therefore is not reclassified as an aggregate-local SQL error here. *)
Definition stddev_samp_numeric_fixed_runtime_error precision scale
    (values : list value)
    : option sql_runtime_error :=
  if numeric_typmod_valid_bool precision scale &&
     forallb is_numeric_value values then
    let numbers := numeric_values values in
    if forallb (numeric_conforms_typmod_bool precision scale) numbers then
      let state := fold_left (numeric_scale_stats_transition scale) numbers
        numeric_scale_stats_initial in
      let '(finite_count,
            (special_count, (sum_coeff, sum_square_coeff))) := state in
      let total_count := numeric_scale_stats_total_count state in
      if total_count <=? 1 then None
      else if 0 <? special_count then None
      else
        let numerator_coeff :=
          finite_count * sum_square_coeff - sum_coeff * sum_coeff in
        if numerator_coeff <=? 0 then None
        else if finite_count * (finite_count - 1) =? 0
             then division_by_zero
             else
               match numeric_stddev_samp_from_scale_state scale state with
               | Some result => numeric_result_runtime_error result
               | None => numeric_value_out_of_range
               end
    else None
  else None.

Definition single_value_int32_runtime_error (values : list value)
    : option sql_runtime_error :=
  match values with
  | nil | _ :: nil => None
  | _ :: _ :: _ => Some CardinalityViolation
  end.

Definition aggregate_local_runtime_error_function
    (function : aggregate_function) (values : list value)
    : option sql_runtime_error :=
  match function with
  | AggregateCount => non_null_count_runtime_error values
  | AggregateSumInt32 => sum_int32_runtime_error values
  | AggregateSumInt64Numeric => sum_int64_numeric_runtime_error values
  | AggregateSumFloat => sum_float_runtime_error values
  | AggregateSumDouble => sum_double_runtime_error values
  | AggregateSumNumeric => sum_numeric_runtime_error values
  | AggregateAverageInt32Numeric => avg_int32_numeric_runtime_error values
  | AggregateNumericDisplayScale aggregate =>
      numeric_aggregate_display_scale_runtime_error aggregate values
  | AggregateAverageInt64Numeric => avg_int64_numeric_runtime_error values
  | AggregateVariancePopulationInt32
  | AggregateVarianceSampleInt32
  | AggregateStddevPopulationInt32
  | AggregateStddevSampleInt32 => integer_statistic_runtime_error values
  | AggregateStddevSampleNumericFixed precision scale =>
      stddev_samp_numeric_fixed_runtime_error precision scale values
  | AggregateAverageFloat => avg_float_runtime_error values
  | AggregateAverageDouble => avg_double_runtime_error values
  | AggregateAverageNumericFixed precision scale =>
      avg_numeric_fixed_runtime_error precision scale values
  | AggregateAverageNumericAtScale scale =>
      avg_numeric_at_scale_runtime_error scale values
  | AggregateBitAndInt32
  | AggregateBitOrInt32
  | AggregateBitAndInt64
  | AggregateBitOrInt64 => None
  | AggregateSingleValueInt32 => single_value_int32_runtime_error values
  | AggregateSumZ
  | AggregateMaxZ
  | AggregateMaxInt32
  | AggregateMaxInt64
  | AggregateMaxFloat
  | AggregateMaxDouble
  | AggregateMaxNumeric
  | AggregateMaxString
  | AggregateMinZ
  | AggregateMinInt32
  | AggregateMinInt64
  | AggregateMinFloat
  | AggregateMinDouble
  | AggregateMinNumeric
  | AggregateAverageZ => None
  end.

Definition aggregate_local_runtime_error
    (call : aggregate) (values : list value) : option sql_runtime_error :=
  match call with
  | AggregateCall function quantifier =>
      aggregate_local_runtime_error_function function
        (aggregate_input_values quantifier values)
  | AggregateCountStar => count_runtime_error values
  end.

Definition interp_aggregate_runtime_error
    (function : aggregate)
    (observations : list (option sql_runtime_error * value))
    : option sql_runtime_error :=
  match function with
  | AggregateCountStar =>
      count_runtime_error (observation_values observations)
  | AggregateCall _ _ =>
      match first_observation_error observations with
      | Some error => Some error
      | None =>
          aggregate_local_runtime_error function
            (observation_values observations)
      end
  end.

End NullValues.
