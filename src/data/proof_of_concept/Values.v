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

Require Import Arith NArith ZArith String List Floats.
Require Import OrderedSet FiniteSet Bool3.
Require Export ValueCore ValueTemporal ValuePredicates.

Definition predicate := ValueCore.predicate.
Definition Predicate := ValueCore.Predicate.
Definition aggregate := ValueCore.aggregate.
Definition Aggregate := ValueCore.Aggregate.

Module NullValues.

Include NullValueDomain.


(** injection of domain names into natural numbers in order to
    build an ordering on them.
*)


(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
*)


Definition value_compare x y :=
  match x, y with
    | Value_string s1, Value_string s2 => option_compare _ string_compare s1 s2
    | Value_string _, Value_Z _
    | Value_string _, Value_bool _
    | Value_string _, Value_float _
    | Value_string _, Value_date _
    | Value_string _, Value_timestamp _
    | Value_string _, Value_timestamptz _ => Lt

    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => option_compare _ Z.compare z1 z2
    | Value_Z _, Value_bool _
    | Value_Z _, Value_float _
    | Value_Z _, Value_date _
    | Value_Z _, Value_timestamp _
    | Value_Z _, Value_timestamptz _ => Lt

    | Value_bool _, Value_string _
    | Value_bool _, Value_Z _ => Gt
    | Value_bool b1, Value_bool b2 => option_compare _ bool_compare b1 b2
    | Value_bool _, Value_float _
    | Value_bool _, Value_date _
    | Value_bool _, Value_timestamp _
    | Value_bool _, Value_timestamptz _ => Lt

    | Value_float _, Value_string _
    | Value_float _, Value_Z _
    | Value_float _, Value_bool _ => Gt
    | Value_float f1, Value_float f2 => option_compare _ (Oset.compare Ofloat) f1 f2
    | Value_float _, Value_date _
    | Value_float _, Value_timestamp _
    | Value_float _, Value_timestamptz _ => Lt

    | Value_date _, Value_string _
    | Value_date _, Value_Z _
    | Value_date _, Value_bool _
    | Value_date _, Value_float _ => Gt
    | Value_date d1, Value_date d2 => option_compare _ Z.compare d1 d2
    | Value_date _, Value_timestamp _
    | Value_date _, Value_timestamptz _ => Lt

    | Value_timestamp _, Value_string _
    | Value_timestamp _, Value_Z _
    | Value_timestamp _, Value_bool _
    | Value_timestamp _, Value_float _
    | Value_timestamp _, Value_date _ => Gt
    | Value_timestamp t1, Value_timestamp t2 => option_compare _ Z.compare t1 t2
    | Value_timestamp _, Value_timestamptz _ => Lt

    | Value_timestamptz _, Value_string _
    | Value_timestamptz _, Value_Z _
    | Value_timestamptz _, Value_bool _
    | Value_timestamptz _, Value_float _
    | Value_timestamptz _, Value_date _
    | Value_timestamptz _, Value_timestamp _ => Gt
    | Value_timestamptz t1, Value_timestamptz t2 => option_compare _ Z.compare t1 t2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ] | [d1 | ] | [t1 | ] | [tz1 | ]]
         [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ] | [d2 | ] | [t2 | ] | [tz2 | ]];
    try discriminate; simpl; trivial.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
    * apply (f_equal (fun x => Value_string (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply (f_equal (fun x => Value_Z (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply (f_equal (fun x => Value_bool (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Ofloat f1 f2). change (Oset.compare Ofloat f1 f2) with (float_compare f1 f2). case (float_compare f1 f2).
    * intros ->; auto.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ d1 d2); simpl; case (Z.compare d1 d2).
    * apply (f_equal (fun x => Value_date (Some x))).
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
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ] | [d1 | ] | [t1 | ] | [tz1 | ]]
         [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ] | [d2 | ] | [t2 | ] | [tz2 | ]]
         [[s3 | ] | [z3 | ] | [b3 | ] | [f3 | ] | [d3 | ] | [t3 | ] | [tz3 | ]]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
  + apply (Oset.compare_lt_trans Ofloat).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
- (* 1/1 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ] | [d1 | ] | [t1 | ] | [tz1 | ]]
         [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ] | [d2 | ] | [t2 | ] | [tz2 | ]]; trivial; simpl.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
  + apply (Oset.compare_lt_gt Ofloat).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt OZ).
Defined.

Definition FVal := Fset.build OVal.


Definition is_z_value v :=
  match v with
  | Value_Z _ => true
  | _ => false
  end.

Definition is_float_value v :=
  match v with
  | Value_float _ => true
  | _ => false
  end.

Fixpoint z_values l :=
  match l with
  | Value_Z (Some z) :: tl => z :: z_values tl
  | _ :: tl => z_values tl
  | nil => nil
  end.

Fixpoint float_values l :=
  match l with
  | Value_float (Some f) :: tl => f :: float_values tl
  | _ :: tl => float_values tl
  | nil => nil
  end.

Definition non_null_count l :=
  Z_of_nat (List.length (filter (fun v => negb (is_null_value v)) l)).

Definition interp_sum_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values => Value_Z (Some (fold_left Z.add values 0%Z))
    end
  else Value_Z None.

Definition interp_sum_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | values => Value_float (Some (fold_left float_add values float_zero))
    end
  else Value_float None.

Definition interp_max_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | z :: values => Value_Z (Some (fold_left Z.max values z))
    end
  else Value_Z None.

Definition interp_max_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | f :: values => Value_float (Some (fold_left float_max values f))
    end
  else Value_float None.

Definition interp_min_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | z :: values => Value_Z (Some (fold_left Z.min values z))
    end
  else Value_Z None.

Definition interp_min_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | f :: values => Value_float (Some (fold_left float_min values f))
    end
  else Value_float None.

Definition interp_avg_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values =>
        let sum := fold_left Z.add values 0%Z in
        Value_Z (Some (Z.quot sum (Z_of_nat (List.length values))))
    end
  else Value_Z None.

Definition interp_avg_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | values =>
        let sum := fold_left float_add values float_zero in
        let count := Z.of_nat (List.length values) in
        Value_float (Some (float_div sum (float_of_int count)))
    end
  else Value_float None.

Definition interp_predicate := NullPredicates.interp_predicate.

Definition interp_symbol f :=
  match f with
    | Symbol _ "plus" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zplus a1 a2))
          | _ => Value_Z None end
    | Symbol _ "plus." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_add a1 a2))
          | _ => Value_float None end
    | Symbol _ "mult" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zmult a1 a2))
          | _ => Value_Z None end
    | Symbol _ "mult." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_mult a1 a2))
          | _ => Value_float None end
    | Symbol _ "minus" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zminus a1 a2))
          | _ => Value_Z None end
    | Symbol _ "minus." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_sub a1 a2))
          | _ => Value_float None end
    | Symbol _ "date_add_days" =>
      fun l =>
        match l with
          | Value_date (Some d) :: Value_Z (Some days) :: nil =>
            Value_date (Some (date_add_days d days))
          | _ => Value_date None end
    | Symbol _ "date_add_months" =>
      fun l =>
        match l with
          | Value_date (Some d) :: Value_Z (Some months) :: nil =>
            Value_date (Some (date_add_months d months))
          | _ => Value_date None end
    | Symbol _ "date_add_years" =>
      fun l =>
        match l with
          | Value_date (Some d) :: Value_Z (Some years) :: nil =>
            Value_date (Some (date_add_years d years))
          | _ => Value_date None end
    | Symbol _ "timestamp_add_microseconds" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some micros) :: nil =>
            Value_timestamp (Some (timestamp_add_microseconds t micros))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_seconds" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some seconds) :: nil =>
            Value_timestamp (Some (timestamp_add_seconds t seconds))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_minutes" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some minutes) :: nil =>
            Value_timestamp (Some (timestamp_add_minutes t minutes))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_hours" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some hours) :: nil =>
            Value_timestamp (Some (timestamp_add_hours t hours))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_days" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some days) :: nil =>
            Value_timestamp (Some (timestamp_add_days t days))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_months" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some months) :: nil =>
            Value_timestamp (Some (timestamp_add_months t months))
          | _ => Value_timestamp None end
    | Symbol _ "timestamp_add_years" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: Value_Z (Some years) :: nil =>
            Value_timestamp (Some (timestamp_add_years t years))
          | _ => Value_timestamp None end
    | Symbol _ "cast_identity" =>
      fun l =>
        match l with
          | v :: nil => v
          | _ => Value_string None end
    | Symbol _ "cast_date_to_timestamp" =>
      fun l =>
        match l with
          | Value_date (Some d) :: nil =>
            Value_timestamp (Some (cast_date_to_timestamp d))
          | _ => Value_timestamp None end
    | Symbol _ "cast_timestamp_to_date" =>
      fun l =>
        match l with
          | Value_timestamp (Some t) :: nil =>
            Value_date (Some (cast_timestamp_to_date t))
          | _ => Value_date None end
    | Symbol _ "opp" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: nil => Value_Z (Some (Z.opp a1))
          | _ => Value_Z None end
    | Symbol _ "opp." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: nil =>
            Value_float (Some (float_sub float_zero a1))
          | _ => Value_float None end
    | CstVal _ v =>
      fun l =>
        match l with
          | nil => v
          | _ => default_value (type_of_value v)
        end
    | _ => fun _ => Value_Z None
  end.

Definition interp_aggregate a l :=
  match a with
    | ValueCore.Aggregate "count" => Value_Z (Some (non_null_count l))
    | ValueCore.Aggregate "sum" => interp_sum_z l
    | ValueCore.Aggregate "sum." => interp_sum_float l
    | ValueCore.Aggregate "max" => interp_max_z l
    | ValueCore.Aggregate "max." => interp_max_float l
    | ValueCore.Aggregate "min" => interp_min_z l
    | ValueCore.Aggregate "min." => interp_min_float l
    | ValueCore.Aggregate "avg" => interp_avg_z l
    | ValueCore.Aggregate "avg." => interp_avg_float l
    | ValueCore.Aggregate _ => Value_Z None
  end.

End NullValues.
