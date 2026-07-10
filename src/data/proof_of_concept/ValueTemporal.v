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

Require Import ZArith Bool.

Open Scope Z_scope.

Definition z_le_bool x y :=
  match Z.compare x y with Gt => false | _ => true end.

Definition is_leap_year y :=
  andb (Z.eqb (Z.modulo y 4) 0)
       (orb (negb (Z.eqb (Z.modulo y 100) 0))
            (Z.eqb (Z.modulo y 400) 0)).

Definition days_in_month y m :=
  match m with
  | 1 => 31
  | 2 => if is_leap_year y then 29 else 28
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0
  end%Z.

Definition valid_ymd y m d :=
  andb (andb (z_le_bool 1 m) (z_le_bool m 12))
       (andb (z_le_bool 1 d) (z_le_bool d (days_in_month y m))).

Definition days_from_civil y m d :=
  let y := if z_le_bool m 2 then y - 1 else y in
  let era := Z.div y 400 in
  let yoe := y - era * 400 in
  let mp := if z_le_bool 3 m then m - 3 else m + 9 in
  let doy := Z.div (153 * mp + 2) 5 + d - 1 in
  let doe := yoe * 365 + Z.div yoe 4 - Z.div yoe 100 + doy in
  era * 146097 + doe - 719468.

Definition date_from_ymd y m d :=
  if valid_ymd y m d then Some (days_from_civil y m d) else None.

Definition civil_from_days z :=
  let z := z + 719468 in
  let era := Z.div z 146097 in
  let doe := z - era * 146097 in
  let yoe := Z.div (doe - Z.div doe 1460 + Z.div doe 36524 - Z.div doe 146096) 365 in
  let y := yoe + era * 400 in
  let doy := doe - (365 * yoe + Z.div yoe 4 - Z.div yoe 100) in
  let mp := Z.div (5 * doy + 2) 153 in
  let d := doy - Z.div (153 * mp + 2) 5 + 1 in
  let m := mp + if z_le_bool mp 9 then 3 else -9 in
  let y := y + if z_le_bool m 2 then 1 else 0 in
  (y, m, d).

Definition date_add_days date days := date + days.

Definition date_add_months date months :=
  let '(y, m, d) := civil_from_days date in
  let month_index := y * 12 + (m - 1) + months in
  let y' := Z.div month_index 12 in
  let m' := Z.modulo month_index 12 + 1 in
  days_from_civil y' m' (Z.min d (days_in_month y' m')).

Definition date_add_years date years := date_add_months date (years * 12).

Definition micros_per_second := 1000000.
Definition micros_per_minute := 60 * micros_per_second.
Definition micros_per_hour := 60 * micros_per_minute.
Definition micros_per_day := 24 * micros_per_hour.

Definition valid_time h m s micros :=
  andb (andb (z_le_bool 0 h) (z_le_bool h 23))
       (andb (andb (z_le_bool 0 m) (z_le_bool m 59))
             (andb (andb (z_le_bool 0 s) (z_le_bool s 59))
                   (andb (z_le_bool 0 micros) (z_le_bool micros 999999)))).

Definition valid_day_time h m s micros :=
  orb (valid_time h m s micros)
      (andb (Z.eqb h 24)
            (andb (Z.eqb m 0) (andb (Z.eqb s 0) (Z.eqb micros 0)))).

Definition time_from_hms h minute s micros :=
  if valid_day_time h minute s micros
  then Some (h * micros_per_hour
             + minute * micros_per_minute
             + s * micros_per_second
             + micros)
  else None.

Definition timestamp_from_ymdhms y m d h minute s micros :=
  if andb (valid_ymd y m d) (valid_time h minute s micros)
  then Some (days_from_civil y m d * micros_per_day
             + h * micros_per_hour
             + minute * micros_per_minute
             + s * micros_per_second
             + micros)
  else None.

Definition timestamp_add_microseconds timestamp micros := timestamp + micros.
Definition timestamp_add_seconds timestamp seconds :=
  timestamp_add_microseconds timestamp (seconds * micros_per_second).
Definition timestamp_add_minutes timestamp minutes :=
  timestamp_add_microseconds timestamp (minutes * micros_per_minute).
Definition timestamp_add_hours timestamp hours :=
  timestamp_add_microseconds timestamp (hours * micros_per_hour).
Definition timestamp_add_days timestamp days :=
  timestamp_add_microseconds timestamp (days * micros_per_day).

Definition timestamp_add_months timestamp months :=
  let date := Z.div timestamp micros_per_day in
  let time_of_day := Z.modulo timestamp micros_per_day in
  date_add_months date months * micros_per_day + time_of_day.

Definition timestamp_add_years timestamp years :=
  timestamp_add_months timestamp (years * 12).

Definition cast_date_to_timestamp date := date * micros_per_day.

Definition cast_timestamp_to_date timestamp := Z.div timestamp micros_per_day.
